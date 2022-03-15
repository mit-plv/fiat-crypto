Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.CastLemmas.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldMap.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.ListUtil.Split.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.LandLorBounds.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ClearHead.
Require Import Crypto.Assembly.EquivalenceProofs.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.WithBedrock.SymbolicProofs.
Import Assembly.Symbolic.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope list_scope.

(* TODO: move to global settings *)
Local Set Keyed Unification.

Local Lemma land_ones_eq_of_bounded v n
      (H : (0 <= v < 2 ^ (Z.of_N n))%Z)
  : Z.land v (Z.ones (Z.of_N n)) = v.
Proof.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Import Map.Interface Map.Separation. (* for coercions *)
Require Import bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import Rupicola.Lib.Tactics. (* for sepsimpl *)
Import LittleEndianList.
Import coqutil.Word.Interface.
Definition cell64 wa (v : Z) : Semantics.mem_state -> Prop :=
  Lift1Prop.ex1 (fun bs => sep (emp (
      length bs = 8%nat /\ v = le_combine bs))
                               (eq (OfListWord.map.of_list_word_at wa bs))).

Definition R_scalar_or_array {dereference_scalar:bool}
           (val : Z + list Z) (asm_val : Naive.word 64)
  := match val with
     | inr array_vals => array cell64 (word.of_Z 8) asm_val array_vals
     | inl scalar_val => if dereference_scalar
                         then cell64 asm_val scalar_val
                         else emp (word.unsigned asm_val = scalar_val)
     end.
Definition R_list_scalar_or_array_nolen {dereference_scalar:bool}
           (Z_vals : list (Z + list Z)) (asm_vals : list (Naive.word 64))
  := List.fold_right
       sep
       (emp True)
       (List.map
          (fun '(val, asm_val) => R_scalar_or_array (dereference_scalar:=dereference_scalar) val asm_val)
          (List.combine Z_vals asm_vals)).
Definition R_list_scalar_or_array {dereference_scalar:bool}
           (Z_vals : list (Z + list Z)) (asm_vals : list (Naive.word 64))
  := sep (emp (List.length Z_vals = List.length asm_vals))
         (R_list_scalar_or_array_nolen (dereference_scalar:=dereference_scalar) Z_vals asm_vals).

Definition get_asm_reg (m : Semantics.reg_state) (reg_available : list REG) : list Z
  := List.map (Semantics.get_reg m) reg_available.

Definition R_runtime_input_mem
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (runtime_reg : list Z)
           (m : Semantics.mem_state)
  : Prop
  := exists (stack_placeholder_values : list Z) (output_placeholder_values : list (Z + list Z)),
    Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ Forall2 val_or_list_val_matches_spec output_placeholder_values output_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) output_placeholder_values
    /\ (* it must be the case that all the scalars in output_placeholder_values match what's in registers / the calling convention *)
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => if output_scalars_are_pointers
                                 then True
                                 else v = v2
                      | inr _ => True
                      end)
        output_placeholder_values
        (firstn (length output_types) runtime_reg)
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) output_placeholder_values asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) runtime_inputs asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m.

Definition R_runtime_input
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (reg_available : list REG) (runtime_reg : list Z)
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ (Nat.min (List.length output_types + List.length runtime_inputs) (List.length reg_available) <= List.length runtime_reg)%nat
    /\ get_asm_reg m reg_available = runtime_reg
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.length asm_arguments_out = List.length output_types
    /\ List.map word.unsigned (asm_arguments_out ++ asm_arguments_in)
       = List.firstn (List.length output_types + List.length runtime_inputs) runtime_reg
    /\ (Semantics.get_reg m rsp - 8 * Z.of_nat stack_size)%Z = word.unsigned stack_base
    /\ (* it must be the case that all the scalars in the real input values match what's in registers / the calling convention *)
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => v = v2
                      | inr _ => True
                      end)
        runtime_inputs
        (firstn (length runtime_inputs) (skipn (length output_types) runtime_reg))
    /\ R_runtime_input_mem frame output_types runtime_inputs stack_size stack_base asm_arguments_out asm_arguments_in runtime_reg m.

(* TODO : should we preserve inputs? *)
Definition R_runtime_output_mem
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (m : Semantics.mem_state)
  : Prop
  := exists (stack_placeholder_values : list Z) (input_placeholder_values : list (Z + list Z)),
    Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ Forall2 val_or_list_val_matches_spec input_placeholder_values input_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) input_placeholder_values
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) runtime_outputs asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) input_placeholder_values asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m.

Definition R_runtime_output
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
     /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
     /\ R_runtime_output_mem frame runtime_outputs input_types stack_size stack_base asm_arguments_out asm_arguments_in m.

Definition word_args_to_Z_args
  : list (Naive.word 64 + list (Naive.word 64)) -> list (Z + list Z)
  := List.map (fun v => match v with
                        | inl v => inl (word.unsigned v)
                        | inr vs => inr (List.map word.unsigned vs)
                        end).

Lemma word_args_to_Z_args_bounded args
  : Forall (fun v => match v with
                     | inl v => (0 <= v < 2^64)%Z
                     | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                     end) (word_args_to_Z_args args).
Proof.
  cbv [word_args_to_Z_args].
  repeat first [ progress intros
               | rewrite Forall_map_iff, Forall_forall
               | progress break_innermost_match
               | apply Word.Properties.word.unsigned_range ].
Qed.

Lemma word_args_to_Z_args_length args
  : length (word_args_to_Z_args args) = length args.
Proof. apply map_length. Qed.

Definition init_symbolic_state_G (m : machine_state)
  : (symbol -> option Z) * dag -> (symbol -> option Z) * symbolic_state
  := fun st
     => let vals := Tuple.to_list _ (m.(machine_reg_state)) in
        let '(initial_reg_idxs, (G, d)) := dag_gensym_n_G vals st in
        (G,
         {| dag_state := d
            ; symbolic_reg_state := Tuple.from_list_default None 16 (List.map Some initial_reg_idxs)
            ; symbolic_flag_state := Tuple.repeat None 6
            ; symbolic_mem_state := []
         |}).

Lemma init_symbolic_state_eq_G G d m
  : init_symbolic_state d = snd (init_symbolic_state_G m (G, d)).
Proof.
  cbv [init_symbolic_state init_symbolic_state_G].
  pose proof (@dag_gensym_n_eq_G G d (Tuple.to_list 16 m.(machine_reg_state))) as H.
  rewrite Tuple.length_to_list in H; rewrite H; clear H.
  eta_expand; cbn [fst snd].
  reflexivity.
Qed.

Lemma init_symbolic_state_G_ok m G d G' ss
      (frame : Semantics.mem_state -> Prop)
      (Hd : gensym_dag_ok G d)
      (H : init_symbolic_state_G m (G, d) = (G', ss))
      (d' := ss.(dag_state))
      (Hframe : frame m)
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list 16 m.(machine_reg_state)))
  : R frame G' ss m
    /\ (forall reg, Option.is_Some (Symbolic.get_reg ss.(symbolic_reg_state) (reg_index reg)) = true)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [init_symbolic_state_G] in *.
  eta_expand; cbn [fst snd] in *; inversion_prod; subst.
  pose proof (dag_gensym_n_G_ok _ _ _ _ _ _ ltac:(eassumption) ltac:(repeat rewrite <- surjective_pairing; reflexivity) ltac:(eassumption)).
  destruct_head'_and; cbv [R].
  repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
  2: { cbv [Tuple.repeat R_flags Tuple.append Tuple.fieldwise Tuple.fieldwise' R_flag]; cbn [fst snd];
       repeat apply conj; congruence. }
  2: { intros; cbn [List.map]; cbv [Symbolic.get_reg symbolic_reg_state].
       unshelve erewrite <- Tuple.nth_default_to_list, Tuple.from_list_default_eq, Tuple.to_list_from_list.
       { rewrite map_length.
         erewrite length_Forall2, Tuple.length_to_list
           by (eapply dag_gensym_n_G_ok; [ | eta_expand; reflexivity | ]; assumption).
         reflexivity. }
       erewrite map_nth_default with (x:=0%N); [ reflexivity | ].
       erewrite length_Forall2, Tuple.length_to_list
         by (eapply dag_gensym_n_G_ok; [ | eta_expand; reflexivity | ]; assumption).
       clear; cbv [reg_index]; break_innermost_match; lia. }
  set (v := dag_gensym_n_G _ _) in *; clearbody v; destruct_head'_prod; cbn [fst snd] in *.
  eassert (H' : Tuple.to_list 16 m.(machine_reg_state) = _).
  { repeat match goal with H : _ |- _ => clear H end.
      cbv [Tuple.to_list Tuple.to_list'].
      set_evars; eta_expand; subst_evars; reflexivity. }
  generalize dependent (Tuple.to_list 16 m.(machine_reg_state)); intros; subst.
  repeat match goal with H : context[?x :: _] |- _ => assert_fails is_var x; set x in * end.
  repeat match goal with H : Forall2 _ ?v (_ :: _) |- _ => is_var v; inversion H; clear H; subst end.
  repeat match goal with H : Forall2 _ ?v nil |- _ => is_var v; inversion H; clear H; subst end.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
  cbv [List.map Tuple.from_list_default Tuple.from_list_default'].
  cbv [R_regs R_reg Tuple.fieldwise Tuple.fieldwise' eval_idx_Z] in *; cbn [fst snd].
  repeat apply conj; intros; inversion_option; subst; try assumption.
  all: change 64%Z with (Z.of_N 64).
  all: rewrite land_ones_eq_of_bounded; [ reflexivity | ].
  all: assumption.
Qed.

Lemma init_symbolic_state_ok m G d
      (frame : Semantics.mem_state -> Prop)
      (Hd : gensym_dag_ok G d)
      (ss := init_symbolic_state d)
      (d' := ss.(dag_state))
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list 16 m.(machine_reg_state)))
      (Hframe : frame m)
  : exists G',
    R frame G' ss m
    /\ (forall reg, Option.is_Some (Symbolic.get_reg ss.(symbolic_reg_state) (reg_index reg)) = true)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  subst ss d'; erewrite init_symbolic_state_eq_G.
  eexists; eapply init_symbolic_state_G_ok; try eassumption.
  eta_expand; reflexivity.
Qed.

Lemma Forall2_get_reg_of_R G d r mr regs
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (Hreg : R_regs G d r mr)
  : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G d idx' v)
            (List.map (Symbolic.get_reg r) (List.map reg_index regs))
            (List.map (Semantics.get_reg mr) regs).
Proof.
  induction regs as [|reg regs IH]; cbn [List.map] in *;
    inversion Hwide; clear Hwide; subst;
    constructor; auto; clear dependent regs; [].
  assert (reg_offset reg = 0%N) by now destruct reg.
  assert (reg_index reg < length (Tuple.to_list _ r))
    by now rewrite Tuple.length_to_list; destruct reg; cbv [reg_index]; lia.
  cbv [Symbolic.get_reg Semantics.get_reg R_regs] in *.
  rewrite Tuple.fieldwise_to_list_iff in Hreg.
  erewrite @Forall2_forall_iff in Hreg by now rewrite !Tuple.length_to_list.
  specialize (Hreg (reg_index reg) ltac:(assumption)); rewrite !@Tuple.nth_default_to_list in *.
  cbv [index_and_shift_and_bitcount_of_reg] in *.
  generalize dependent (reg_size reg); intros; subst.
  generalize dependent (reg_offset reg); intros; subst.
  change (Z.of_N 0) with 0%Z.
  change (Z.of_N 64) with 64%Z.
  rewrite Z.shiftr_0_r.
  do 2 match goal with
       | [ H : context[Tuple.nth_default ?d ?i ?l], H' : context[Tuple.nth_default ?d' ?i' ?l] |- _ ]
         => is_evar d; unify d d'; unify i i'
       | [ H : context[Tuple.nth_default ?d ?i ?l] |- context[Tuple.nth_default ?d' ?i' ?l] ]
         => is_evar d; unify d d'; unify i i'
       end.
  cbv [R_reg] in Hreg.
  destruct Hreg as [Hreg Hreg'].
  rewrite <- Hreg'.
  now apply Hreg.
Qed.

Lemma get_reg_bounded mr regs
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z)
           (List.map (Semantics.get_reg mr) regs).
Proof.
  rewrite Forall_map, Forall_forall; intros reg ?.
  assert ((reg_size reg <= 64)%N)
    by now clear; destruct reg; cbv [reg_index reg_size]; lia.
  cbv [Semantics.get_reg index_and_shift_and_bitcount_of_reg] in *.
  rewrite Z.land_nonneg, Z.shiftr_nonneg.
  split; [ right; apply Z.ones_nonneg; lia | ].
  eapply Z.le_lt_trans;
    [ rewrite Z.land_comm; apply Z.land_le; intros; apply Z.ones_nonneg
    | rewrite Z.ones_equiv, Z.lt_pred_le; Z.peel_le ];
    lia.
Qed.

Lemma load_eval_R_mem_eval G d idx idx' mem_st m' frame
      (Hmem : R_mem frame G d mem_st m')
      (Hload : load idx mem_st = Some idx')
  : exists val,
    eval_idx_Z G d idx' val.
Proof.
  cbv [load option_map] in *.
  break_innermost_match_hyps; inversion_option; subst; destruct_head'_prod.
  revert dependent m'; induction mem_st as [|m mem_st IH]; cbn [R_mem find] in *; intros.
  all: repeat first [ progress inversion_option
                    | progress inversion_pair
                    | progress cbn [fst snd] in *
                    | progress reflect_hyps
                    | progress subst
                    | progress specialize_by_assumption
                    | progress break_innermost_match_hyps ].
  all: repeat first [ progress cbv [sep R_cell64 Lift1Prop.ex1 emp eval_idx_Z] in *
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | now eauto ].
Qed.

Lemma load_eval_R_mem_eval_Forall2 G d idxs l n z mem_st m' frame l1
      (Hmem : R_mem frame G d mem_st m')
      (Hl : Forall2 (eval_idx_Z G d) l
                    (List.map (fun i => Z.land (z + 8 * Z.of_nat i) (Z.ones 64))
                              (seq 0 n)))
      (Hmem_all : Option.List.lift (List.map (fun a => load a mem_st) idxs) = Some l1)
  : exists vals,
    Forall2 (eval_idx_Z G d) l1 vals.
Proof.
  revert dependent l1.
  induction idxs as [|idx idxs IH],
      l1 as [|x xs];
    try specialize (IH xs); intros.
  all: repeat first [ progress cbn [List.map fold_right] in *
                    | progress cbv [Crypto.Util.Option.bind Option.List.lift] in *
                    | progress inversion_option
                    | progress inversion_list
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress specialize_by reflexivity
                    | progress subst
                    | progress break_match_hyps
                    | match goal with
                      | [ H : load _ _ = Some _ |- _ ] => eapply load_eval_R_mem_eval in H; [ | eassumption ]
                      end
                    | now eexists nil; eauto
                    | now eexists (_ :: _); eauto ].
Qed.

Definition R_regs_preserved_v rn (m : Semantics.reg_state)
  := Z.land (Tuple.nth_default 0%Z rn m) (Z.ones 64).

Definition R_regs_preserved G d (m : Semantics.reg_state) rs rs'
  := forall rn idx, Symbolic.get_reg rs' rn = Some idx -> exists idx', Symbolic.get_reg rs rn = Some idx' /\ let v := R_regs_preserved_v rn m in eval_idx_Z G d idx' v -> eval_idx_Z G d idx v.

Global Instance R_regs_preserved_Reflexive G d m : Reflexive (R_regs_preserved G d m) | 100.
Proof. intro; cbv [R_regs_preserved]; eauto. Qed.

Lemma R_regs_subsumed_get_reg_same_eval G d rs rs' rm
      (H : R_regs G d rs rm)
      (H_impl : R_regs_preserved G d rm rs rs')
  : R_regs G d rs' rm.
Proof.
  cbv [R_regs Symbolic.get_reg R_regs_preserved R_regs_preserved_v] in *.
  rewrite @Tuple.fieldwise_to_list_iff, @Forall2_forall_iff_nth_error in *.
  intro i; specialize (H i); specialize (H_impl i).
  rewrite <- !@Tuple.nth_default_to_list in *.
  cbv [nth_default option_eq] in *.
  repeat first [ progress destruct_head'_and
               | progress destruct_head'_ex
               | rewrite @Tuple.length_to_list in *
               | progress cbv [R_reg eval_idx_Z] in *
               | progress break_innermost_match
               | progress break_innermost_match_hyps
               | now auto
               | progress intros
               | progress subst
               | match goal with
                 | [ H : nth_error _ _ = None |- _ ] => apply nth_error_error_length in H
                 | [ H : ?i >= ?n, H' : context[nth_error (Tuple.to_list ?n _) ?i] |- _ ]
                   => rewrite nth_error_length_error in H' by now rewrite Tuple.length_to_list; lia
                 | [ H : forall x, Some _ = Some x -> _ |- _ ]
                   => specialize (H _ eq_refl)
                 | [ H : ?x = ?y, H' : context[?y] |- _ ] => is_var x; rewrite <- H in H'
                 end
               | apply conj; auto; [] ].
Qed.

Lemma R_regs_preserved_set_reg G d rs rs' ri rm v
      (H : R_regs_preserved G d rm rs rs')
      (H_same : (ri < 16)%nat -> exists idx, Symbolic.get_reg rs ri = Some idx /\ let v' := R_regs_preserved_v ri rm in eval_idx_Z G d idx v' -> eval_idx_Z G d v v')
  : R_regs_preserved G d rm rs (Symbolic.set_reg rs' ri v).
Proof.
  cbv [R_regs_preserved] in *.
  intros rn idx; specialize (H rn).
  rewrite get_reg_set_reg_full; intro.
  repeat first [ progress break_innermost_match_hyps
               | progress inversion_option
               | progress subst
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress destruct_head'_ex
               | progress specialize_by_assumption
               | progress specialize_by lia
               | rewrite @Bool.andb_true_iff in *
               | rewrite @Bool.andb_false_iff in *
               | solve [ eauto ]
               | progress reflect_hyps
               | match goal with
                 | [ H : forall v, ?k = Some v -> _, H' : ?k = Some _ |- _ ]
                   => specialize (H _ H')
                 end ].
Qed.

Lemma R_regs_preserved_fold_left_set_reg_index {T} G d rs rs' rm (r_idxs : list (_ * (_ + _ * T)))
      (H : R_regs_preserved G d rm rs rs')
      (H_same : Forall (fun '(r, v) => let v := match v with inl v => v | inr (v, _) => v end in exists idx, Symbolic.get_reg rs (reg_index r) = Some idx /\ let v' := R_regs_preserved_v (reg_index r) rm in eval_idx_Z G d idx v' -> eval_idx_Z G d v v') r_idxs)
  : R_regs_preserved
      G d rm
      rs
      (fold_left (fun rst '(r, idx')
                  => Symbolic.set_reg rst (reg_index r)
                             match idx' with
                             | inl idx' => idx'
                             | inr (base_idx', idxs') => base_idx'
                             end)
                 r_idxs rs').
Proof.
  revert dependent rs'; induction r_idxs as [|[r v] r_idxs IH]; cbn [fold_left];
    inversion_one_head Forall; auto; intros; [].
  apply IH; clear IH; auto; [].
  apply R_regs_preserved_set_reg; auto.
Qed.

Lemma Semantics_get_reg_eq_nth_default_of_R_regs G d ss ms r
      (Hsz : reg_size r = 64%N)
      (HR : R_regs G d ss ms)
  : Semantics.get_reg ms r = Tuple.nth_default 0%Z (reg_index r) (ms : Semantics.reg_state).
Proof.
  assert (Hro : reg_offset r = 0%N) by now revert Hsz; clear; cbv; destruct r; lia.
  cbv [R_regs R_reg] in HR.
  rewrite Tuple.fieldwise_to_list_iff, Forall2_forall_iff_nth_error in HR.
  specialize (HR (reg_index r)).
  cbv [Semantics.get_reg index_and_shift_and_bitcount_of_reg].
  rewrite Hro, Hsz; change (Z.of_N 0) with 0%Z; change (Z.of_N 64) with 64%Z.
  rewrite Z.shiftr_0_r, <- Tuple.nth_default_to_list; cbv [nth_default option_eq] in *.
  break_innermost_match_hyps; break_innermost_match; inversion_option; destruct_head'_and; try congruence; try tauto.
Qed.

Lemma Semantics_get_reg_eq_nth_default_of_R frame G ss ms r
      (Hsz : reg_size r = 64%N)
      (HR : R frame G ss ms)
  : Semantics.get_reg ms r = Tuple.nth_default 0%Z (reg_index r) (ms : Semantics.reg_state).
Proof.
  destruct ss, ms; eapply Semantics_get_reg_eq_nth_default_of_R_regs; try eassumption; apply HR.
Qed.

Lemma Forall2_R_regs_preserved_same_helper G d reg_available idxs m rs
      (Hreg_wide_enough
        : Forall
            (fun reg : REG =>
               let
                 '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in
               sz = 64%N) reg_available)
      (H : Forall2 (fun (idx' : idx + idx * list idx) v
                    => match idx' with
                       | inl idx' => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                       | inr (base', _) => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                       end)
                   idxs (firstn (List.length idxs) (get_asm_reg m reg_available)))
      (HR : R_regs G d rs m)
      (Hex : forall n r, (n < List.length idxs)%nat -> nth_error reg_available n = Some r -> exists idx, Symbolic.get_reg rs (reg_index r) = Some idx)
  : Forall (fun '(r, v)
            => let v := match v with inl v => v | inr (v, _) => v end in
               exists idx, Symbolic.get_reg rs (reg_index r) = Some idx
                           /\ let v' := R_regs_preserved_v (reg_index r) m in eval_idx_Z G d idx v' -> eval_idx_Z G d v v')
           (List.combine reg_available idxs).
Proof.
  cbv [get_asm_reg] in *.
  rewrite firstn_map, Forall2_map_r_iff in H.
  apply Forall2_flip in H.
  rewrite Forall2_forall_iff_nth_error in H.
  rewrite @Forall_forall in *.
  intros [r ?] H'; apply In_nth_error_value in H'.
  specialize (Hreg_wide_enough r).
  specialize (fun v pf => Hreg_wide_enough (nth_error_In _ v pf)).
  destruct H' as [n H'].
  specialize (H n).
  rewrite ListUtil.nth_error_firstn in H.
  rewrite nth_error_combine in H'.
  cbv [option_eq] in H.
  cbv [R_regs_preserved_v].
  repeat first [ progress break_innermost_match_hyps
               | progress inversion_option
               | progress subst
               | progress inversion_pair
               | progress cbv [index_and_shift_and_bitcount_of_reg] in *
               | solve [ eauto ]
               | match goal with
                 | [ H : (forall reg, Option.is_Some (Symbolic.get_reg ?s (reg_index reg)) = true)
                     |- context[Symbolic.get_reg ?s (reg_index ?ri)] ]
                   => generalize (H ri); cbv [Option.is_Some]; break_innermost_match;
                      try congruence
                 | [ H : forall v, nth_error ?ls v = Some _ -> _ |- _ ]
                   => specialize (H _ ltac:(eassumption))
                 end ].
  all: specialize (Hex _ _ ltac:(eassumption) ltac:(eassumption)).
  all: destruct_head'_ex.
  all: erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by eassumption.
  all: eauto.
Qed.

Lemma R_list_scalar_or_array_cons_iff dereference_scalar i1 i2 w1 w2
  : Lift1Prop.iff1
      (@R_list_scalar_or_array dereference_scalar (i1 :: i2) (w1 :: w2))
      (@R_scalar_or_array dereference_scalar i1 w1 * @R_list_scalar_or_array dereference_scalar i2 w2)%sep.
Proof.
  cbv [R_list_scalar_or_array R_list_scalar_or_array_nolen]; cbn [List.length List.combine List.map fold_right].
  SeparationLogic.cancel; cbn [seps]; split; cbv [emp]; intros; sepsimpl; inversion_nat_eq; subst; congruence.
Qed.

Lemma R_list_scalar_or_array_nolen_app_iff dereference_scalar i1 i2 w1 w2
      (H : List.length i1 = List.length w1)
  : Lift1Prop.iff1
      (@R_list_scalar_or_array_nolen dereference_scalar (i1 ++ i2) (w1 ++ w2))
      (@R_list_scalar_or_array_nolen dereference_scalar i1 w1 * @R_list_scalar_or_array_nolen dereference_scalar i2 w2)%sep.
Proof.
  cbv [R_list_scalar_or_array_nolen].
  rewrite !combine_app_samelength, map_app, fold_right_app by assumption.
  generalize (List.combine i1 w1).
  intro l; induction l as [|?? IH]; cbn [List.map fold_right]; [ | rewrite IH ];
    SeparationLogic.cancel; cbn [seps].
Qed.

Lemma R_list_scalar_or_array_app_iff dereference_scalar i1 i2 w1 w2
      (H : List.length i1 = List.length w1)
  : Lift1Prop.iff1
      (@R_list_scalar_or_array dereference_scalar (i1 ++ i2) (w1 ++ w2))
      (@R_list_scalar_or_array dereference_scalar i1 w1 * @R_list_scalar_or_array dereference_scalar i2 w2)%sep.
Proof.
  cbv [R_list_scalar_or_array].
  rewrite R_list_scalar_or_array_nolen_app_iff by assumption.
  rewrite !app_length.
  SeparationLogic.cancel; cbn [seps].
  rewrite SeparationLogic.sep_emp_emp.
  split; cbv [emp]; intros; sepsimpl; subst; try congruence; lia.
Qed.

Lemma R_mem_frame_cps_id {P : Prop} (HP : P) frame G d s
  : Lift1Prop.iff1 (R_mem frame G d s) (frame * (R_mem (emp P) G d s))%sep.
Proof.
  induction s as [|[? ?] s IH]; cbn [R_mem]; [ | rewrite IH ];
    SeparationLogic.cancel.
  cbn [seps]; apply SeparationLogic.Proper_emp_iff; tauto.
Qed.

Lemma R_mem_nil_iff G d P
  : Lift1Prop.iff1 (R_mem (emp P) G d nil) (emp P).
Proof. reflexivity. Qed.

Lemma R_mem_cons_iff G d v s P
  : Lift1Prop.iff1 (R_mem (emp P) G d (v :: s))
                   (R_cell64 G d (fst v) (snd v) * R_mem (emp P) G d s)%sep.
Proof. destruct v; reflexivity. Qed.

Lemma R_mem_app_iff G d s1 s2 P
  : Lift1Prop.iff1 (R_mem (emp P) G d (s1 ++ s2))
                   (R_mem (emp P) G d s1 * R_mem (emp P) G d s2)%sep.
Proof.
  induction s1 as [|? ? IH]; cbn [List.app].
  all: rewrite ?R_mem_nil_iff, ?R_mem_cons_iff, ?IH, ?(R_mem_frame_cps_id I (emp P)).
  { intro; rewrite ?SeparationLogic.sep_emp_l; tauto. }
  { SeparationLogic.ecancel. }
Qed.

Lemma R_mem_rev_iff G d s P
  : Lift1Prop.iff1 (R_mem (emp P) G d (List.rev s))
                   (R_mem (emp P) G d s).
Proof.
  induction s as [|? ? IH]; cbn [List.rev].
  all: rewrite ?R_mem_app_iff, ?R_mem_cons_iff, ?R_mem_nil_iff, ?IH, ?(R_mem_frame_cps_id I (emp P)).
  { SeparationLogic.cancel. }
  { assert (H : @Lift1Prop.iff1 Semantics.mem_state (emp P) (emp (P /\ P)))
      by (apply SeparationLogic.Proper_emp_iff; tauto).
    rewrite H at 3.
    SeparationLogic.cancel.
    cbn [seps]; intro.
    rewrite ?SeparationLogic.sep_emp_l; cbv [emp]; tauto. }
Qed.

Lemma R_cell64_ex_cell64_iff G d ia iv
  : Lift1Prop.iff1 (R_cell64 G d ia iv)
                   (Lift1Prop.ex1
                      (fun a
                       => Lift1Prop.ex1
                            (fun v
                             => emp (eval_idx_Z G d ia (word.unsigned a) /\ eval_idx_Z G d iv v /\ 0 <= v < 2^64)%Z * cell64 a v)%sep)).
Proof.
  apply Lift1Prop.Proper_ex1_iff1; intro.
  split; intros.
  all: repeat
         repeat
         first [ progress subst
               | reflexivity
               | eassumption
               | progress sepsimpl
               | progress cbv [cell64] in *
               | match goal with
                 | [ H : le_combine _ = le_combine _ |- _ ] => apply le_combine_inj in H; [ | congruence ]
                 | [ |- Lift1Prop.ex1 _ _ ] => eexists
                 end ].
  all: sepsimpl; subst; [ > apply le_combine_bound | eapply Z.lt_le_trans; [ apply le_combine_bound | ] ].
  rewrite (ltac:(eassumption) : List.length _ = _); reflexivity.
Qed.

Lemma bounded_of_cell64 wa v m
      (H : cell64 wa v m)
  : (0 <= v < 2^64)%Z.
Proof.
  cbv [cell64] in H.
  sepsimpl; subst; [ apply le_combine_bound | eapply Z.lt_le_trans; [ apply le_combine_bound | ] ].
  rewrite H; reflexivity.
Qed.

Lemma bounded_of_array_cell64 v
  : forall wa base m
           (H : array cell64 base wa v m),
    Forall (fun v => 0 <= v < 2^64)%Z v.
Proof.
  induction v as [|v vs IH]; cbn [array]; constructor; cbv [sep] in *; sepsimpl.
  all: try now eapply bounded_of_cell64; eassumption.
  eauto.
Qed.

(* TODO: move? *)
Lemma sep_emp_holds_r (p : Semantics.mem_state -> Prop) (P : Prop)
      (H : forall m, p m -> P)
  : Lift1Prop.iff1 (sep p (emp P)) p.
Proof.
  split; intro; sepsimpl; eauto.
Qed.
Lemma sep_emp_holds_l (p : Semantics.mem_state -> Prop) (P : Prop)
      (H : forall m, p m -> P)
  : Lift1Prop.iff1 (sep (emp P) p) p.
Proof.
  split; intro; sepsimpl; eauto.
Qed.

Lemma R_mem_combine_ex_array_iff frame G d n addrs val_idxs base_value base_word_value init
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq init n)))
      (*(Hn : List.length val_idxs = n)*)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.iff1
      (R_mem frame G d (List.combine addrs val_idxs))
      (Lift1Prop.ex1 (fun vals
                      => emp (Forall2 (eval_idx_Z G d) (firstn n val_idxs) vals /\ Forall (fun v => 0 <= v < 2^64)%Z vals) * frame * array cell64 (word.of_Z 8) (word.add base_word_value (word.of_Z (8 * Z.of_nat init))) vals))%sep.
Proof.
  subst.
  revert val_idxs n init Haddrs.
  induction addrs as [|addr addrs IH], val_idxs as [|val_idx val_idxs], n as [|n];
    intro init; cbn [List.combine List.length seq List.map R_mem array]; intros;
    try (specialize (IH val_idxs n (S init)); rewrite IH; clear IH);
    rewrite ?firstn_O, ?firstn_nil, ?firstn_cons;
    try now inversion_one_head Forall2.
  all: lazymatch goal with
       | [ |- Lift1Prop.iff1 ?frame (Lift1Prop.ex1 _) ]
         => (tryif is_var frame
              then let x := fresh in intro x; split; revert x; refine (_ : Lift1Prop.impl1 _ _)
              else idtac)
       end.
  all: try (apply Lift1Prop.impl1_ex1_l; intro).
  all: try solve [ apply Lift1Prop.impl1_ex1_r with (x:=nil); cbn [array];
                   unshelve erewrite (_ : (Forall2 _ _ _ /\ _) <-> True); [ intuition | ];
                   SeparationLogic.cancel; cbn [seps]; reflexivity ].
  all: rewrite ?SeparationLogic.sep_assoc, ?SeparationLogic.impl1_l_sep_emp; intros.
  all: rewrite ?Forall2_nil_l_iff, ?Forall2_nil_r_iff in *; destruct_head'_and; subst; cbn [array].
  all: try solve [ hnf; intros; sepsimpl; trivial ].
  { rewrite !@Forall2_cons_cons_iff in *; destruct_head'_and.
    rewrite R_cell64_ex_cell64_iff.
    rewrite SeparationLogic.sep_ex1_r.
    intro x; split; revert x; refine (_ : Lift1Prop.impl1 _ _).
    all: repeat first [ progress intros
                      | progress destruct_head'_and
                      | progress destruct_head'_ex
                      | progress subst
                      | rewrite Lift1Prop.impl1_ex1_l
                      | rewrite !SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp
                      | rewrite SeparationLogic.sep_ex1_l
                      | rewrite !SeparationLogic.sep_emp_emp
                      | rewrite <- !SeparationLogic.sep_assoc
                      | rewrite !SeparationLogic.sep_comm_emp_r
                      | rewrite Forall2_cons_l_ex_iff in *
                      | rewrite Forall_cons_iff in * ].
    all: [ > eapply (Lift1Prop.impl1_ex1_r _ _ (_ :: _))
         | eapply (Lift1Prop.impl1_ex1_r _ _ _) ];
      cbn [array].
    all: repeat first [ progress intros
                      | progress destruct_head'_and
                      | rewrite Forall2_cons_cons_iff
                      | set_evars; rewrite Forall_cons_iff; subst_evars
                      | rewrite Lift1Prop.impl1_ex1_l
                      | rewrite !SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp
                      | rewrite SeparationLogic.sep_ex1_l
                      | rewrite !SeparationLogic.sep_emp_emp
                      | rewrite <- !SeparationLogic.sep_assoc
                      | rewrite !SeparationLogic.sep_comm_emp_r
                      | lazymatch goal with
                        | [ |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun h : ?T => _)) ]
                          => lazymatch T with word.rep => idtac | Z => idtac end;
                             eapply Lift1Prop.impl1_ex1_r
                        end ].
    all: rewrite !SeparationLogic.sep_assoc; apply SeparationLogic.impl1_r_sep_emp.
    all: repeat first [ solve [ eauto 10 ]
                      | match goal with
                        | [ |- _ /\ _ ] => split
                        | [ H : eval_idx_Z ?G ?d ?i ?v |- eval_idx_Z ?G ?d ?i (word.unsigned ?v') ]
                          => let _ := open_constr:(eq_refl : v' = word.of_Z v) in
                             replace (word.unsigned v') with v; [ exact H | rewrite ?Z.land_ones by lia; ZnWords ]
                        end ].
    all: match goal with |- Lift1Prop.impl1 ?A ?B => cut (Lift1Prop.iff1 A B); [ intros ->; reflexivity | ] end.
    all: repeat first [ rewrite Z.land_ones in * by lia
                      | match goal with
                        | [ H : eval_idx_Z ?G ?d ?x ?y, H' : eval_idx_Z ?G ?d ?x ?y' |- _ ]
                          => eapply eval_eval in H; [ | exact H' ]
                        | [ |- ?R (sep (cell64 ?x ?y) _) (sep (cell64 ?x' ?y') _) ]
                          => progress (replace x with x' by ZnWords; replace y with y' by ZnWords)
                        | [ |- ?R (array _ _ ?x _) (array _ _ ?x' _) ]
                          => progress replace x with x' by ZnWords
                        end
                      | progress (SeparationLogic.cancel; cbn [seps]) ]. }
Qed.

Lemma R_mem_combine_array_impl1 frame G d n addrs val_idxs base_value base_word_value init
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq init n)))
      (*(Hn : List.length val_idxs = n)*)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.impl1
      (R_mem frame G d (List.combine addrs val_idxs))
      (Lift1Prop.ex1 (fun vals
                      => emp (Forall2 (eval_idx_Z G d) (firstn n val_idxs) vals /\ Forall (fun v => 0 <= v < 2^64)%Z vals) * frame * array cell64 (word.of_Z 8) (word.add base_word_value (word.of_Z (8 * Z.of_nat init))) vals))%sep.
Proof. rewrite R_mem_combine_ex_array_iff by eassumption; reflexivity. Qed.

Lemma R_mem_combine_array_iff_helper frame G d addrs val_idxs base_value base_word_value vals init
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq init (List.length vals))))
      (Hvals : Forall2 (eval_idx_Z G d) val_idxs vals)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.iff1 (R_mem frame G d (List.combine addrs val_idxs))
                   (frame * (emp (Forall (fun v => 0 <= v < 2^64)%Z vals) * array cell64 (word.of_Z 8) (word.add base_word_value (word.of_Z (8 * Z.of_nat init))) vals))%sep.
Proof.
  rewrite (@sep_emp_holds_l _ _ (@bounded_of_array_cell64 _ _ _)).
  rewrite R_mem_combine_ex_array_iff by eassumption.
  subst.
  cbv [Lift1Prop.iff1 Lift1Prop.ex1]; split; intros; [ | exists vals ]; sepsimpl; eauto.
  all: rewrite ?@firstn_all in * by eauto using eq_length_Forall2, eq_sym.
  all: repeat first [ match goal with
                      | [ H1 : Forall2 (eval_idx_Z _ _) ?l1 ?l2, H2 : Forall2 (eval_idx_Z _ _) ?l1 ?l2' |- _ ]
                        => eapply eval_eval_idx_Z_Forall2 in H2; [ | exact H1 ]
                      end
                    | progress subst
                    | solve [ eauto ] ].
  cbv [sep] in *; sepsimpl.
  eapply bounded_of_array_cell64; eassumption.
Qed.

Lemma R_mem_combine_array_iff frame G d n addrs val_idxs base_value base_word_value vals
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 n)))
      (Hvals : Forall2 (eval_idx_Z G d) val_idxs vals)
      (Hn : n = List.length vals)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.iff1 (R_mem frame G d (List.combine addrs val_idxs))
                   (frame * (emp (Forall (fun v => 0 <= v < 2^64)%Z vals) * array cell64 (word.of_Z 8) base_word_value vals))%sep.
Proof.
  subst n.
  rewrite R_mem_combine_array_iff_helper by eassumption.
  SeparationLogic.cancel; cbn [seps].
  match goal with
  | [ |- Lift1Prop.iff1 (array ?cell ?sz ?init ?val) (array ?cell ?sz ?init' ?val) ]
    => cut (init = init');
       [ intros ->; reflexivity | ]
  end.
  ZnWords.
Qed.

Local Ltac saturate_lengths_step :=
  let do_with ls :=
    lazymatch ls with
    | @List.map ?A ?B ?f ?x
      => unique pose proof (@map_length A B f x)
    | @firstn ?A ?n ?x
      => unique pose proof (@firstn_length A n x)
    | @skipn ?A ?n ?x
      => unique pose proof (@skipn_length A n x)
    | @seq ?start ?len
      => unique pose proof (@seq_length start len)
    | @List.app ?A ?l ?l'
      => unique pose proof (@app_length A l l')
    | @List.combine ?A ?B ?l1 ?l2
      => unique pose proof (@combine_length A B l1 l2)
    end in
  match goal with
  | [ |- context[length (?x ++ ?y)] ]
    => rewrite (app_length x y)
  | [ H : Forall2 _ ?y ?x |- _ ]
    => unique assert (length y = length x) by eapply eq_length_Forall2, H
  | [ |- context[length ?ls] ]
    => do_with ls
  | [ H : context[length ?ls] |- _ ]
    => do_with ls
  | [ H : nth_error _ _ = None |- _ ]
    => unique pose proof (@nth_error_error_length _ _ _ H)
  | [ H : nth_error _ _ = Some _ |- _ ]
    => unique pose proof (@nth_error_value_length _ _ _ _ H)
  end.
Local Ltac saturate_lengths := repeat saturate_lengths_step.
Local Ltac cleanup_min :=
  repeat match goal with
         | [ H : context[Nat.min ?x ?y] |- _ ]
           => lazymatch x with context[Nat.min] => fail | _ => idtac end;
              lazymatch y with context[Nat.min] => fail | _ => idtac end;
              (assert ((x <= y)%nat) + assert ((y <= x)%nat));
              [ repeat match goal with H : context[Nat.min] |- _ => clear dependent H end;
                lia
              | ];
              first [ rewrite (Nat.min_l x y) in * by assumption
                    | rewrite (Nat.min_r x y) in * by assumption ]
         end.

Lemma bounded_of_R_scalar_or_array {dereference_scalar:bool} v
  : forall ws m
           (H : R_scalar_or_array (dereference_scalar:=dereference_scalar) v ws m),
    match v with
    | inl v => 0 <= v < 2^64
    | inr vs => Forall (fun v => 0 <= v < 2^64) vs
    end%Z.
Proof.
  cbv [R_scalar_or_array]; intros *; break_innermost_match; cbv [emp]; intros; destruct_head'_and; subst.
  all: try solve [ eapply bounded_of_cell64; eassumption
                 | apply Properties.word.unsigned_range
                 | eapply bounded_of_array_cell64; eassumption ].
Qed.

Lemma bounded_of_R_list_scalar_nolen_or_array {dereference_scalar:bool} v
  : forall ws m
           (Hlen : List.length ws = List.length v)
           (H : R_list_scalar_or_array_nolen (dereference_scalar:=dereference_scalar) v ws m),
    Forall (fun v => match v with
                     | inl v => 0 <= v < 2^64
                     | inr vs => Forall (fun v => 0 <= v < 2^64) vs
                     end%Z) v.
Proof.
  cbv [R_list_scalar_or_array_nolen].
  induction v as [|v vs IH], ws as [|? ws];
    try specialize (IH ws);
    cbn [fold_right List.combine List.map List.length] in *; constructor; cbv [sep] in *; sepsimpl; inversion_nat_eq.
  all: try solve [ eapply bounded_of_R_scalar_or_array; eassumption
                 | eapply IH; eassumption ].
Qed.

Lemma bounded_of_R_list_scalar_or_array {dereference_scalar:bool} v
  : forall ws m
           (H : R_list_scalar_or_array (dereference_scalar:=dereference_scalar) v ws m),
    Forall (fun v => match v with
                     | inl v => 0 <= v < 2^64
                     | inr vs => Forall (fun v => 0 <= v < 2^64) vs
                     end%Z) v.
Proof.
  cbv [R_list_scalar_or_array].
  intros; sepsimpl.
  eapply bounded_of_R_list_scalar_nolen_or_array; try eassumption; congruence.
Qed.

Lemma R_mem_flat_map_ex_R_list_scalar_or_array_iff_emp {dereference_scalar:bool} G d
  : forall (idxs : list (idx + idx * list idx)) base_vals addr_idxs base_vals_words
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl idx'
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs' : Forall2 (fun idx addr_idx
                              => match idx, addr_idx with
                                 | inl idx, inl addr_idx
                                   => if dereference_scalar
                                      then True
                                      else forall v, eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v
                                 | inr (base, idxs), inr addr_idxs
                                   => List.length idxs = List.length addr_idxs
                                 | inl _, inr _ | inr _, inl _ => False
                                 end)
                             idxs addr_idxs)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (Lift1Prop.ex1
         (fun addr_vals
          => emp (Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals
                  /\ Forall (fun v => match v with
                                      | inl v => 0 <= v < 2^64
                                      | inr vs => Forall (fun v => 0 <= v < 2^64) vs
                                      end%Z) addr_vals)
              * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words))%sep.
Proof.
  pose dereference_scalar as dereference_scalar'.
  induction idxs as [|idx idxs IH],
      base_vals as [|base_val base_vals],
        addr_idxs as [|addr_idx addr_idxs],
          base_vals_words as [|base_vals_word base_vals_words];
    try specialize (IH base_vals addr_idxs base_vals_words);
    do 2 (intro H; inversion H; clear H); subst.
  all: cbv [R_list_scalar_or_array R_list_scalar_or_array_nolen] in *; cbn [List.map flat_map R_mem fold_right List.combine List.length]; intros; inversion_nat_eq; inversion_list.
  all: SeparationLogic.cancel; cbn [seps].
  all: try (rewrite R_mem_app_iff, IH by assumption; clear IH).
  { intro x; split; revert x; refine (_ : Lift1Prop.impl1 _ _).
    all: [ > apply Lift1Prop.impl1_ex1_r with (x:=nil) | apply Lift1Prop.impl1_ex1_l; intro ].
    all: cbn [List.length].
    all: rewrite Forall2_nil_l_iff.
    all: rewrite ?Forall_nil_iff.
    all: rewrite <- ?SeparationLogic.sep_assoc, ?SeparationLogic.sep_emp_emp.
    all: try (apply SeparationLogic.impl1_r_sep_emp; split; trivial).
    all: try apply SeparationLogic.impl1_l_sep_emp; intros; destruct_head'_and; subst.
    all: cbn [List.combine List.map fold_right].
    all: eauto; try reflexivity. }
  all: [ > ].
  all: intro x; split; revert x; refine (_ : Lift1Prop.impl1 _ _).
  all: repeat
         repeat
         first [ progress intros
               | exfalso; assumption
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress subst
               | progress cbn [List.combine List.map fold_right R_scalar_or_array R_mem List.length]
               | rewrite SeparationLogic.sep_emp_emp
               | rewrite SeparationLogic.sep_ex1_l
               | rewrite SeparationLogic.sep_ex1_r
               (*| let P := lazymatch goal with |- Lift1Prop.impl1 ?P _ => P end in
                 lazymatch P with
                 | context[sep (Lift1Prop.ex1 ?q) ?p]
                   => rewrite (SeparationLogic.sep_ex1_l p q)
                 | context[sep ?p (Lift1Prop.ex1 ?q)]
                   => rewrite (SeparationLogic.sep_ex1_r p q)
                 end*)
               | rewrite SeparationLogic.impl1_l_sep_emp
               | rewrite Lift1Prop.impl1_ex1_l
               | rewrite !SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp
               | rewrite <- !SeparationLogic.sep_assoc
               | rewrite !SeparationLogic.sep_comm_emp_r
               | rewrite Forall2_cons_cons_iff in *
               | set_evars; rewrite Forall_cons_iff in *; subst_evars
               | rewrite Forall2_cons_l_ex_iff in * |-
               | rewrite Forall2_cons_r_ex_iff in * |-
               | rewrite R_mem_combine_array_impl1 by (eassumption + reflexivity)
               | rewrite R_cell64_ex_cell64_iff
               | match goal with
                 | [ H : Forall2 _ ?addr_idxs ?v |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun h => sep _ (sep (emp (Forall2 _ ?addr_idxs h /\ _)) _))) ]
                   => apply (Lift1Prop.impl1_ex1_r _ _ v)
                 | [ |- Lift1Prop.impl1 ?A (Lift1Prop.ex1 ?B0) ]
                   => lazymatch B0 with
                      | fun h => sep (emp (Forall2 ?R (?addr_idx :: ?addr_idxs) h /\ _)) (@?B h)
                        => lazymatch goal with
                           | [ H : Forall2 _ addr_idxs ?rest |- _ ]
                             => cut (Lift1Prop.impl1 A (Lift1Prop.ex1 (fun h0 => Lift1Prop.ex1 (fun h1 => Lift1Prop.ex1 (fun h2 => B0 (match addr_idx with inl _ => inl (if dereference_scalar then h0 else h1) | inr _ => inr h2 end :: rest))))));
                                [ (intros ->);
                                  let h0 := fresh in
                                  let h1 := fresh in
                                  let h2 := fresh in
                                  rewrite Lift1Prop.impl1_ex1_l; intro h0;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h1;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h2;
                                  apply (Lift1Prop.impl1_ex1_r _ _ (match addr_idx with inl _ => inl (if dereference_scalar then h0 else h1) | inr _ => inr h2 end :: rest));
                                  reflexivity
                                | break_innermost_match; break_innermost_match_hyps; cbn [R_mem] ]
                           end
                      end
                 | [ |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun _ => ?A)) ]
                   => unshelve eapply Lift1Prop.impl1_ex1_r; try solve [ constructor ]; []
                 | [ H : eval_idx_or_list_idx _ _ (inr _) _ |- _ ]
                   => cbv [eval_idx_or_list_idx] in H; break_innermost_match_hyps
                 | [ H : eval_idx_or_list_idx _ _ (inl _) _ |- _ ]
                   => cbv [eval_idx_or_list_idx] in H; break_innermost_match_hyps
                 | [ H : eval_idx_or_list_idx _ _ _ (inr _) |- _ ]
                   => cbv [eval_idx_or_list_idx] in H; break_innermost_match_hyps
                 | [ H : eval_idx_or_list_idx _ _ _ (inl _) |- _ ]
                   => cbv [eval_idx_or_list_idx] in H; break_innermost_match_hyps
                 end
               | progress break_innermost_match
               | match goal with
                 | [ |- Lift1Prop.impl1 ?A ?B ]
                   => lazymatch B with
                      | context[R_mem _ _ _ (List.combine _ _)]
                        => rewrite R_mem_combine_array_iff
                          by solve [ eassumption | reflexivity | saturate_lengths; congruence ]
                      end
                 | [ |- Lift1Prop.impl1 _ ?B ]
                   => lazymatch B with
                      | context[sep (emp _) _]
                        => rewrite ?SeparationLogic.sep_assoc;
                           apply SeparationLogic.impl1_r_sep_emp; split; [ solve [ eauto ] | ]
                      end
                 end
               | reflexivity ].
  all: repeat first [ rewrite Z.land_ones in * by lia
                    | progress subst
                    | match goal with
                      | [ H1 : eval_idx_Z ?G ?d ?i _, H2 : eval_idx_Z ?G ?d ?i _ |- _ ]
                        => eapply eval_eval in H2; [ | exact H1 ]
                      | [ H : context[(?v mod ?m)%Z] |- _ ]
                        => lazymatch v with
                           |  word.unsigned ?x
                              => replace ((v mod m)%Z) with v in * by ZnWords
                           end
                      | [ H : word.unsigned _ = word.unsigned _ |- _ ]
                        => apply Properties.word.unsigned_inj in H
                      | [ H : context[firstn ?n ?l] |- _ ]
                        => rewrite firstn_all in H by congruence
                      | [ |- context[?v] ]
                        => lazymatch v with
                           | word.add ?x (word.of_Z 0)
                             => replace v with x by ZnWords
                           end
                      end
                    | progress autorewrite with zsimplify_const ].
  all: repeat match goal with
              | [ H : context[word.unsigned ?x] |- _ ]
                => unique pose proof (Properties.word.unsigned_range x)
              | [ |- context[word.unsigned ?x] ]
                => unique pose proof (Properties.word.unsigned_range x)
              end.
  all: repeat first [ match goal with
                      | [ |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun _ => ?A)) ]
                        => unshelve eapply Lift1Prop.impl1_ex1_r; try solve [ constructor ]; []
                      | [ |- Lift1Prop.impl1 _ (Lift1Prop.ex1 _) ]
                        => eapply Lift1Prop.impl1_ex1_r
                      | [ |- Lift1Prop.impl1 _ ?B ]
                        => lazymatch B with
                           | context[sep (emp _) _]
                             => rewrite ?SeparationLogic.sep_assoc;
                                apply SeparationLogic.impl1_r_sep_emp; split; [ solve [ eauto 10 ] | ]
                           end
                      end
                    | reflexivity
                    | rewrite SeparationLogic.sep_ex1_l
                    | rewrite <- !SeparationLogic.sep_assoc
                    | rewrite SeparationLogic.sep_emp_emp
                    | rewrite Forall2_cons_cons_iff
                    | set_evars; rewrite Forall_cons_iff; subst_evars
                    | progress cbn [eval_idx_or_list_idx List.length] in * ].
Qed.

Lemma R_mem_flat_map_ex_R_list_scalar_or_array_impl_emp {dereference_scalar:bool} G d
  : forall (idxs : list (idx + idx * list idx)) base_vals addr_idxs base_vals_words
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl idx'
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs' : Forall2 (fun idx addr_idx
                              => match idx, addr_idx with
                                 | inl idx, inl addr_idx
                                   => if dereference_scalar
                                      then True
                                      else forall v, eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v
                                 | inr (base, idxs), inr addr_idxs
                                   => List.length idxs = List.length addr_idxs
                                 | inl _, inr _ | inr _, inl _ => False
                                 end)
                             idxs addr_idxs)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.impl1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (Lift1Prop.ex1
         (fun addr_vals
           => emp (Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals
                   /\ Forall (fun v => match v with
                                       | inl v => 0 <= v < 2^64
                                       | inr vs => Forall (fun v => 0 <= v < 2^64) vs
                                       end%Z) addr_vals)
              * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words))%sep.
Proof.
  intros; rewrite R_mem_flat_map_ex_R_list_scalar_or_array_iff_emp by eassumption.
  reflexivity.
Qed.

Lemma R_mem_flat_map_R_list_scalar_or_array_iff_emp {dereference_scalar:bool} G d
  : forall (idxs : list (idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
           (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl idx'
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs' : Forall2 (fun idx addr_idx
                              => match idx, addr_idx with
                                 | inl idx, inl addr_idx
                                   => if dereference_scalar
                                      then True
                                      else forall v, eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v
                                 | inr (base, idxs), inr addr_idxs
                                   => List.length idxs = List.length addr_idxs
                                 | inl _, inr _ | inr _, inl _ => False
                                 end)
                             idxs addr_idxs)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words)%sep.
Proof.
  intros; rewrite R_mem_flat_map_ex_R_list_scalar_or_array_iff_emp by eassumption.
  cbv [Lift1Prop.iff1 Lift1Prop.ex1]; split; intros; [ | eexists ]; sepsimpl; eauto.
  eapply eval_eval_idx_or_list_idx_Forall2 in Haddrs; [ | clear Haddrs; eassumption ].
  { subst; assumption. }
  { eapply bounded_of_R_list_scalar_or_array; eassumption. }
Qed.


Lemma R_mem_flat_map_R_list_scalar_or_array_iff {dereference_scalar:bool} frame G d
      (idxs : list (idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
      (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
      (Hidxs : Forall2 (fun idx' v
                        => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                           match idx' with
                           | inl idx'
                             => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                           | inr (base', addrs')
                             => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                           end)
                       idxs base_vals)
      (Hidxs' : Forall2 (fun idx addr_idx
                         => match idx, addr_idx with
                            | inl idx, inl addr_idx
                              => if dereference_scalar
                                 then True
                                 else forall v, eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v
                            | inr (base, idxs), inr addr_idxs
                              => List.length idxs = List.length addr_idxs
                            | inl _, inr _ | inr _, inl _ => False
                            end)
                        idxs addr_idxs)
      (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals)
  : Lift1Prop.iff1
      (R_mem frame G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words)%sep.
Proof.
  intros.
  rewrite ?(R_mem_frame_cps_id I frame).
  erewrite R_mem_flat_map_R_list_scalar_or_array_iff_emp by eassumption.
  reflexivity.
Qed.

Definition same_mem_addressed (s1 s2 : Symbolic.mem_state) : Prop
  := List.map fst s1 = List.map fst s2.

Lemma update_nth_fst_mem_same m1 n y
  : same_mem_addressed m1 (update_nth n (fun ptsto : idx * idx => (fst ptsto, y)) m1).
Proof.
  revert n m1.
  cbv [same_mem_addressed]; induction n as [|n IH], m1 as [|? m1]; cbn [update_nth List.map fst]; f_equal; eauto.
Qed.

(* TODO: move? *)
Lemma store_mem_same x y m1 m2 (H : store x y m1 = Some m2)
  : same_mem_addressed m1 m2.
Proof.
  cbv [store Crypto.Util.Option.bind] in *; break_innermost_match_hyps; inversion_option; subst.
  apply update_nth_fst_mem_same.
Qed.

Class same_mem_addressed_of_success {T} (f : M T)
  := success_same_mem : forall v s s', f s = Success (v, s') -> same_mem_addressed s s'.

Local Ltac same_mem_addressed_of_success_t_step_normal_nobreak :=
  first [ progress cbv [same_mem_addressed_of_success] in *
        | progress intros
        | reflexivity
        | assumption
        | progress inversion_ErrorT
        | progress destruct_head'_prod
        | progress cbn [fst snd Symbolic.symbolic_mem_state] in *
        | progress cbv [update_dag_with update_mem_with update_flag_with update_reg_with Symbolic.bind Symbolic.ret Symbolic.err some_or ErrorT.bind] in *
        | progress inversion_pair
        | progress subst
        | match goal with
          | [ H : store _ _ _ = Some _ |- _ ] => apply store_mem_same in H
          | [ H : _ = Success _ |- _ ] => apply success_same_mem in H
          end
        | cbv [same_mem_addressed] in *; congruence ].

Local Ltac same_mem_addressed_of_success_t_step_normal :=
  first [ same_mem_addressed_of_success_t_step_normal_nobreak
        | break_innermost_match_hyps_step ].

Local Ltac same_mem_addressed_of_success_t_step_unfold :=
  match goal with
  | [ H : ?f = Success _ |- _ ]
    => let f' := head f in
       (*idtac f';*)
       progress unfold f' in H
  end.

Local Ltac same_mem_addressed_of_success_t_step_unfold_go :=
  repeat same_mem_addressed_of_success_t_step_normal;
  same_mem_addressed_of_success_t_step_unfold;
  repeat same_mem_addressed_of_success_t_step_normal.

Local Ltac same_mem_addressed_of_success_t := repeat first [ same_mem_addressed_of_success_t_step_normal | same_mem_addressed_of_success_t_step_unfold ].

(* TODO: move? *)
Local Instance Merge_mem_same x : same_mem_addressed_of_success (Symbolic.Merge x).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance App_mem_same x : same_mem_addressed_of_success (Symbolic.App x).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance GetReg_mem_same r : same_mem_addressed_of_success (GetReg r).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance Address_mem_same sa a : same_mem_addressed_of_success (@Address sa a).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance GetOperand_mem_same sz sa arg : same_mem_addressed_of_success (@GetOperand sz sa arg).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance GetFlag_mem_same f : same_mem_addressed_of_success (GetFlag f).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance SetOperand_mem_same sz sa arg v : same_mem_addressed_of_success (@SetOperand sz sa arg v).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance SetFlag_mem_same f v : same_mem_addressed_of_success (SetFlag f v).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance RevealConst_mem_same v : same_mem_addressed_of_success (RevealConst v).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance Reveal_mem_same v1 v2 : same_mem_addressed_of_success (Reveal v1 v2).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance HavocFlags_mem_same : same_mem_addressed_of_success HavocFlags.
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance ret_mem_same {T} (v : T) : same_mem_addressed_of_success (ret v).
Proof. same_mem_addressed_of_success_t. Qed.

(* TODO: move? *)
Local Instance bind_mem_same {A B} f v
      {H0 : same_mem_addressed_of_success v}
      {H1 : forall v', same_mem_addressed_of_success (f v')}
  : same_mem_addressed_of_success (@Symbolic.bind A B v f).
Proof.
  same_mem_addressed_of_success_t.
  specialize (H0 _ _ _ ltac:(eassumption)).
  specialize (H1 _ _ _ _ ltac:(eassumption)).
  cbv [same_mem_addressed] in *; congruence.
Qed.

(* TODO: move? *)
Local Instance mapM_mem_same {A B} f ls
      {H1 : forall v', same_mem_addressed_of_success (f v')}
  : same_mem_addressed_of_success (@mapM A B f ls).
Proof.
  induction ls as [|?? IH]; cbn [mapM];
    same_mem_addressed_of_success_t.
  specialize (IH _ _ _ ltac:(eassumption)).
  specialize (H1 _ _ _ _ ltac:(eassumption)).
  same_mem_addressed_of_success_t.
Defined.

(* TODO: move? *)
Fixpoint Symeval_mem_same sz sa args {struct args} : same_mem_addressed_of_success (@Symeval sz sa args).
Proof.
  destruct args; cbn [Symeval] in *; typeclasses eauto.
Qed.
Local Existing Instance Symeval_mem_same.
Typeclasses Opaque Symeval.
Typeclasses Transparent AddressSize OperationSize.

(* TODO: move? *)
Local Instance SymexNormalInstruction_mem_same instr : same_mem_addressed_of_success (SymexNormalInstruction instr).
Proof.
  destruct instr; cbv [SymexNormalInstruction err Symbolic.bind ret Syntax.op Syntax.args ErrorT.bind same_mem_addressed_of_success] in *; intros.
  same_mem_addressed_of_success_t.
Qed.

(* TODO: move? *)
Local Instance SymexLine_mem_same line : same_mem_addressed_of_success (SymexLine line).
Proof.
  cbv [SymexLine SymexRawLine err ret] in *; break_innermost_match; try congruence.
  typeclasses eauto.
Qed.

(* TODO: move? *)
Lemma SymexLines_mem_same lines s s'
      (H : SymexLines lines s = Success (tt, s'))
  : same_mem_addressed s s'.
Proof.
  revert s H.
  induction lines as [|line lines IH]; cbn [SymexLines]; cbv [Symbolic.ret Symbolic.bind ErrorT.bind]; intros *; break_innermost_match; intros; inversion_ErrorT; inversion_pair; subst; try reflexivity.
  specialize (IH _ ltac:(eassumption)).
  same_mem_addressed_of_success_t.
Qed.

Lemma same_mem_addressed_alt l1 l2
      (H : same_mem_addressed l1 l2)
  : exists l2b, List.combine (List.map fst l1) l2b = l2 /\ List.length l2b = List.length l1.
Proof.
  cbv [same_mem_addressed] in *.
  rewrite H.
  pose proof (split_combine l2) as H'.
  rewrite split_alt in H'.
  eexists; split; [ now eauto | ].
  apply (f_equal (@List.length _)) in H.
  rewrite !map_length in *; congruence.
Qed.

Lemma same_mem_addressed_app_ex_r l1 l2 l3
      (H : same_mem_addressed (l1 ++ l2) l3)
  : exists l3a l3b, l3a ++ l3b = l3 /\ same_mem_addressed l1 l3a /\ same_mem_addressed l2 l3b.
Proof.
  cbv [same_mem_addressed] in *.
  rewrite map_app in H.
  exists (firstn (List.length l1) l3), (skipn (List.length l1) l3).
  rewrite <- firstn_map, <- skipn_map, <- H, firstn_app, skipn_app, map_length, Nat.sub_diag, firstn_O, skipn_O, firstn_skipn, firstn_all, (skipn_all (List.length l1)), app_nil_l, app_nil_r by now rewrite map_length; lia.
  auto.
Qed.

Lemma same_mem_addressed_rev_ex_r l1 l2
      (H : same_mem_addressed (List.rev l1) l2)
  : exists l3, List.rev l3 = l2 /\ same_mem_addressed l1 l3.
Proof.
  cbv [same_mem_addressed] in *.
  exists (List.rev l2).
  rewrite map_rev, <- H, map_rev, !rev_involutive.
  auto.
Qed.

Lemma same_mem_addressed_combine_ex_r_helper1 l1a l1b l2
      (H : same_mem_addressed (List.combine l1a l1b) l2)
  : exists l2b, List.combine (firstn (List.length l1b) l1a) l2b = l2 /\ List.length l2b = List.length l2.
Proof.
  cbv [same_mem_addressed] in *.
  exists (List.map snd l2); split; [ | distr_length; lia ].
  rewrite map_fst_combine in H.
  pose proof (split_combine l2) as H'.
  rewrite split_alt, <- H in H'.
  now eauto.
Qed.

Lemma same_mem_addressed_combine_ex_r_helper2 l1a l1b l2
      (H : same_mem_addressed (List.combine l1a l1b) l2)
  : exists l2b, List.combine l1a l2b = l2 /\ List.length l2b = Nat.min (List.length l1b) (List.length l1a).
Proof.
  pose proof (f_equal (@List.length _) H).
  apply same_mem_addressed_combine_ex_r_helper1 in H.
  destruct H as [l2b [H ?] ].
  exists (firstn (List.length l1b) l2b).
  subst.
  split; [ | distr_length; lia ].
  etransitivity; rewrite combine_truncate_l, combine_truncate_r; [ | reflexivity ].
  rewrite ?firstn_app, ?firstn_firstn_min.
  autorewrite with distr_length in *.
  do 2 f_equal; lia.
Qed.

Lemma same_mem_addressed_combine_ex_r l1a l1b l2
      (H : same_mem_addressed (List.combine l1a l1b) l2)
  : exists l2b, List.combine l1a l2b = l2 /\ List.length l2b = List.length l1b.
Proof.
  apply same_mem_addressed_combine_ex_r_helper2 in H.
  destruct H as [l2b [H H'] ].
  exists (l2b ++ skipn (List.length l1a) l1b).
  autorewrite with distr_length in *.
  split; [ | lia ].
  rewrite combine_truncate_r, firstn_app.
  rewrite <- (firstn_skipn (List.length l1a) l2b) in H.
  rewrite H'; subst.
  do 2 (apply f_equal2; try reflexivity; []).
  generalize dependent (List.length l1a); clear l1a; intros.
  revert H'; apply Nat.min_case_strong; intros H0 H1; subst.
  all: autorewrite with natsimplify.
  all: rewrite ?firstn_O, ?skipn_all, ?firstn_nil by lia.
  all: reflexivity.
Qed.

Lemma same_mem_addressed_nil ls
      (H : same_mem_addressed nil ls)
  : nil = ls.
Proof.
  destruct ls; cbv in H; congruence.
Qed.

Lemma symbolic_mem_state_nil d
  : symbolic_mem_state (init_symbolic_state d) = nil.
Proof.
  cbv [init_symbolic_state]; break_innermost_match; reflexivity.
Qed.

Lemma same_mem_addressed_init_symbolic_state d ls
      (H : same_mem_addressed (init_symbolic_state d) ls)
  : symbolic_mem_state (init_symbolic_state d) = ls.
Proof.
  rewrite symbolic_mem_state_nil in *.
  apply same_mem_addressed_nil, H.
Qed.

Lemma same_mem_addressed_flat_map_combine_addrs_ex_r {dereference_scalar:bool} {T} (ls1 : list (_ + T * _)) ls2 ls'
      (H : same_mem_addressed (List.flat_map
                                 (fun '(idx', idx)
                                  => match idx', idx with
                                     | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                                     | inl _, _ | _, inl _ => []
                                     | inr (base', addrs'), inr items
                                       => List.combine addrs' items
                                     end)
                                 (List.combine ls1 ls2))
                              ls')
  : exists ls'2, List.flat_map
                   (fun '(idx', idx)
                    => match idx', idx with
                       | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                       | inl _, _ | _, inl _ => []
                       | inr (base', addrs'), inr items
                         => List.combine addrs' items
                       end)
                   (List.combine ls1 ls'2) = ls'
                 /\ Forall2 (fun idx idx' => match idx, idx' with
                                             | inl val, inl val'
                                               => if dereference_scalar then True else val = val'
                                             | inr items, inr items' => List.length items = List.length items'
                                             | inl _, inr _ | inr _, inl _ => False
                                             end) ls2 ls'2.
Proof.
  revert dependent ls'.
  revert ls1 ls2.
  induction ls1 as [|?? IH], ls2 as [|? ls2];
    try specialize (IH ls2);
    cbn [List.combine List.map List.flat_map]; intros.
  all: repeat first [ progress subst
                    | progress destruct_head'_and
                    | progress destruct_head'_ex
                    | (now exists nil)
                    | reflexivity
                    | specialize (IH _ ltac:(eassumption))
                    | match goal with
                      | [ H : same_mem_addressed nil _ |- _ ] => apply same_mem_addressed_nil in H
                      | [ H : same_mem_addressed (_ ++ _) _ |- _ ] => apply same_mem_addressed_app_ex_r in H
                      | [ H : nil = List.map _ ?ls |- _ ] => is_var ls; destruct ls
                      | [ H : same_mem_addressed match _ with _ => _ end ?x |- _ ]
                        => is_var x; apply same_mem_addressed_alt in H
                      | [ |- exists ls, nil = nil /\ Forall2 _ ?lsv ls ]
                        => exists lsv; split; [ | apply Reflexive_forall2; intro; break_innermost_match ]
                      end ].
  eexists (_ :: _); cbn [flat_map]; split; [ apply f_equal2; [ | reflexivity ] | constructor; [ | assumption ] ].
  2: lazymatch goal with
     | [ |- match ?s with
            | inl _
              => match ?ev with
                 | inr _ => False
                 | _ => _
                 end
            | _ => _
            end ]
       => let __ := open_constr:(eq_refl : ev = match s with inl val => inl (if dereference_scalar then _ else _) | inr items => inr (firstn (List.length items) ?[ls] ++ skipn (List.length ?ls) items)%list end) in
          break_innermost_match; autorewrite with distr_length; try exact I; try reflexivity; set_evars; lia
     end.
  repeat first [ match goal with
                 | [ |- match ?x with _ => _ end = List.combine (List.map _ match ?x with _ => _ end) _ ]
                   => destruct x
                 | [ |- match ?ev with inl _ => _ | inr _ => nil end = List.combine (List.map _ match ?x with inl _ => _ | inr _ => nil end) _ ]
                   => is_evar ev;
                      is_var x;
                      let __ := open_constr:(eq_refl : ev = match x with inl _ => inl _ | inr _ => inr _ end) in
                      destruct x
                 | [ |- [(_, ?ev)] = match ?x with _ => _ end ]
                   => is_evar ev;
                      is_var x;
                      let __ := open_constr:(eq_refl : ev = match x with nil => _ | _ :: _ => _ end) in
                      destruct x
                 | [ |- List.combine ?ls ?ev = List.combine (firstn (List.length ?ls') ?ls) ?x ]
                   => is_evar ev; unify ev (firstn (List.length ls') x)
                 end
               | exfalso; discriminate
               | reflexivity
               | rewrite map_fst_combine
               | progress cbn [List.map List.combine fst List.length] in *
               | break_innermost_match_step ].
  match goal with
  | [ |- List.combine _ (firstn _ ?ev ++ skipn _ _) = List.combine _ ?ls ]
    => is_evar ev; unify ev ls
  end.
  etransitivity; rewrite combine_truncate_l, combine_truncate_r; [ | reflexivity ].
  rewrite ?firstn_app, ?firstn_firstn_min.
  autorewrite with distr_length in *.
  repeat first [ rewrite Nat.sub_diag
               | rewrite firstn_O
               | rewrite app_nil_r
               | reflexivity
               | match goal with
                 | [ |- context[(Nat.min ?x ?y + (?x - ?y))%nat] ]
                   => replace (Nat.min x y + (x - y))%nat with x by lia
                 | [ |- context[Nat.min (Nat.min ?x ?y) ?x] ]
                   => replace (Nat.min (Nat.min x y) x) with (Nat.min x y) by lia
                 | [ H : ?x = Nat.min ?y ?z |- context[Nat.min ?x ?z] ]
                   => replace (Nat.min x z) with (Nat.min y z) by lia
                 | [ H : ?x = Nat.min ?y ?z |- context[Nat.min ?z ?x] ]
                   => replace (Nat.min z x) with (Nat.min y z) by lia
                 | [ |- context[(Nat.min ?x ?y - Nat.min ?y ?x)%nat] ]
                   => rewrite (Nat.min_comm x y)
                 | [ |- context[firstn ?n ?x] ]
                   => rewrite (@firstn_all _ n x) by lia
                 | [ |- context[firstn (Nat.min (List.length ?x) _) ?x] ]
                   => rewrite (Nat.min_comm (List.length x)), <- (@firstn_firstn_min _ (List.length x) _ x)
                 end ].
  Unshelve.
  constructor.
Qed.

Lemma update_update_dag_with s d0 d1
  : update_dag_with (update_dag_with s d0) d1 = update_dag_with s (fun d => d1 (d0 d)).
Proof. reflexivity. Qed.

(* TODO: move? *)
Local Lemma eq_list_of_filter_nil A (l : list A) l1 l2
      (H : (List.length l1 = List.length l2) /\ (List.length l1 <= List.length l)%nat)
      (H'' : filter (fun '(_, (init, final)) => negb (init =? final)%N)
                    (List.combine l (List.combine l2 l1)) = [])
  : l1 = l2.
Proof.
  apply List.nth_error_ext; intro i.
  rewrite eq_filter_nil_Forall_iff, Forall_forall_iff_nth_error_match in H''.
  specialize (H'' i).
  rewrite !nth_error_combine in H''.
  break_innermost_match_hyps; reflect_hyps; subst; try congruence.
  all: repeat first [ exfalso; lia
                    | reflexivity
                    | match goal with
                      | [ H : nth_error _ _ = None |- _ ]
                        => apply nth_error_error_length in H
                      | [ H : nth_error _ _ = Some _ |- _ ]
                        => apply nth_error_value_length in H
                      end
                    | rewrite nth_error_length_error by lia ].
Qed.

Lemma bounded_of_R_regs G d s m
      (H : R_regs G d s m)
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) (Tuple.to_list _ m).
Proof.
  cbv [R_regs R_reg] in H.
  rewrite Tuple.fieldwise_to_list_iff in H.
  rewrite Forall_forall_iff_nth_error_match.
  rewrite Forall2_forall_iff_nth_error in H.
  intro i; specialize (H i).
  cbv [option_eq] in *.
  break_innermost_match; break_innermost_match_hyps; inversion_option; destruct_head'_and; trivial.
  rewrite Z.land_ones in * by lia.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma reg_bounded_of_R frame G s m
      (H : R frame G s m)
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) (Tuple.to_list _ m.(machine_reg_state)).
Proof.
  destruct s; cbv [R] in H.
  eapply bounded_of_R_regs, H.
Qed.

Lemma eq_lift_to_Forall2_rets_inner mem_st idxs rets
      (Hrets : Some rets = Option.List.lift (List.map (fun a => load a mem_st) idxs))
  : Forall2 (fun rv idx => load idx mem_st = Some rv) rets idxs.
Proof.
  revert idxs rets Hrets; cbv [Option.List.lift option_map Crypto.Util.Option.bind].
  induction idxs as [|idx idxs IH], rets as [|ret rets];
    try specialize (IH rets); cbn [List.map fold_right]; intros.
  all: repeat first [ progress inversion_option
                    | progress inversion_list
                    | progress subst
                    | progress break_match_hyps
                    | solve [ eauto ]
                    | constructor ].
Qed.

Lemma eq_lift_to_Forall2_rets {A} mem_st idxs (rets : list (A + _))
      (Hrets : Some rets
               = Option.List.lift
                   (List.map (fun idxs
                              => match idxs : idx + list idx with
                                 | inr idxs => option_map inr (Option.List.lift (List.map (fun a => load a mem_st) idxs))
                                 | inl idx => None (* Some (inl idx) ?? *)
                                 end)
                             idxs))
  : Forall2 (fun rv idxs
             => match idxs, rv with
                | inl idx, inl _ => False
                | inr idxs, inr rets => Forall2 (fun rv idx => load idx mem_st = Some rv) rets idxs
                | inl _, inr _ | inr _, inl _ => False
                end)
            rets idxs.
Proof.
  revert idxs rets Hrets; cbv [Option.List.lift option_map Crypto.Util.Option.bind].
  induction idxs as [|idx idxs IH], rets as [|ret rets];
    try specialize (IH rets); cbn [List.map fold_right]; intros.
  all: repeat first [ progress inversion_option
                    | progress inversion_list
                    | progress subst
                    | break_innermost_match_hyps_step
                    | break_innermost_match_step
                    | progress break_match_hyps
                    | progress specialize_by reflexivity
                    | eapply eq_lift_to_Forall2_rets_inner; (idtac + symmetry); eassumption
                    | solve [ eauto ]
                    | constructor ].
Qed.

Import Coq.Strings.String.
Import Coq.Lists.List.
Import Crypto.Util.Option.
Axiom TODO : string -> Prop.
Axiom todo : forall s, TODO s.
Lemma Forall2_rets_of_R_mem {A} G frame d mem_st m' idxs base_len_base_vals rets
      (Hbase : Forall2 (fun idxs '((base, len), base_val)
                        => match idxs, (base:option A), len with
                           | inr idxs, Some base, Some len
                             => Forall2 (eval_idx_Z G d) idxs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
                           | _, _, _ => False
                           end)
                       idxs
                       base_len_base_vals)
      (Hmem : R_mem frame G d mem_st m')
      (Hrets : Some rets
               = Option.List.lift
                   (List.map (fun idxs
                              => match idxs : idx + list idx with
                                 | inr idxs => option_map inr (Option.List.lift (List.map (fun a => load a mem_st) idxs))
                                 | inl idx => None (* Some (inl idx) ?? *)
                                 end)
                             idxs))
  : exists runtime_rets,
    TODO "Forall2_rets_of_R_mem runtime_rets R_mem postcondition"%string
    /\ Forall2 (eval_idx_or_list_idx G d) rets runtime_rets.
Proof.
  revert dependent idxs; revert base_len_base_vals.
  induction rets as [|ret rets IH],
      base_len_base_vals as [|base_len_base_val base_len_base_vals],
        idxs as [|idx idxs];
    try specialize (IH base_len_base_vals idxs).
  all: repeat first [ progress cbn [List.map fold_right]
                    | progress cbv [Option.List.lift Crypto.Util.Option.bind option_map] in *
                    | progress intros
                    | progress subst
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress inversion_option
                    | progress inversion_list
                    | progress specialize_by_assumption
                    | progress specialize_by reflexivity
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ nil _ |- _ ] => inversion H; clear H
                      | [ H : fold_right _ (Some nil) (List.map (fun a => load a _) _) = Some _ |- _ ]
                        => eapply load_eval_R_mem_eval_Forall2 in H; [ | eassumption .. ]
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | now eexists nil; split; auto using todo
                    | now eexists (inr _ :: _); eauto ].
Qed.

Local Lemma connect_Forall2_app_connect {A B C R1 R2 R3 R4 ls1 ls1' ls2 ls2' ls3}
      (H1 : @Forall2 A B R1 ls1 ls1')
      (H2 : @Forall2 A B R2 ls2 ls2')
      (H3 : @Forall2 _ C R3 (ls1' ++ ls2') ls3)
      (Ha : forall a1 b1 c, R1 a1 b1 -> R3 b1 c -> R4 a1 c : Prop)
      (Hb : forall a2 b2 c, R2 a2 b2 -> R3 b2 c -> R4 a2 c : Prop)
  : @Forall2 _ C R4 (ls1 ++ ls2) ls3.
Proof.
  saturate_lengths.
  rewrite app_length in *.
  rewrite !@Forall2_forall_iff_nth_error in *; intro i.
  repeat first [ progress rewrite ?@nth_error_app in *
               | match goal with
                 | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                   => specialize (H i); lazymatch type of H with context[nth_error ls i] => idtac end
                 | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                   => specialize (H i); lazymatch type of H with context[nth_error ls i] => idtac end
                 end ].
  all: repeat first [ progress cbv [option_eq] in *
                    | progress cbn [List.length] in *
                    | progress inversion_option
                    | progress subst
                    | lia
                    | solve [ eauto ]
                    | match goal with
                      | [ H : ?x < ?y, H' : context[(?x - ?y)%nat] |- _ ]
                        => rewrite (@not_le_minus_0 x y) in H' by lia
                      | [ H : nth_error ?l 0 = _ |- _ ] => is_var l; destruct l; cbn [nth_error] in H
                      | [ H : nth_error ?ls ?i = Some _, H' : ~?i < length ?ls |- _ ]
                        => rewrite nth_error_length_error in H by lia
                      | [ H : nth_error ?ls ?i = _, H' : nth_error ?ls ?i' = _ |- _ ]
                        => let H'' := fresh in
                           assert (H'' : i = i') by lia; rewrite H'' in *; rewrite H in H'
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step ].
Qed.

(* turn off once proof is finished *)
Local Ltac debug_run tac := tac ().
Local Ltac handle_R_regs _ :=
  lazymatch goal with
  | [ H : R _ _ (update_dag_with (init_symbolic_state _) _) ?m
      |- R_regs _ _ (Symbolic.set_reg (fold_left _ _ (Symbolic.symbolic_reg_state (init_symbolic_state _))) _ _) ?m' ]
    => debug_run ltac:(fun _ => idtac "R => R_regs set_reg start");
       (*in_evars_do ltac:(destruct_head' symbolic_state; cbn [Symbolic.symbolic_reg_state Symbolic.dag_state] in * );*)
      eapply R_regs_subsumed_get_reg_same_eval;
      [ eapply R_regs_subsumed;
        [ apply H | now eauto ]
      | let finish_some_reg _ :=
          cbv [R_regs_preserved_v];
          match goal with
          | [ H : (forall reg, Option.is_Some (Symbolic.get_reg ?s (reg_index reg)) = true)
              |- context[Symbolic.get_reg ?s (reg_index ?ri)] ]
            => generalize (H ri); cbv [Option.is_Some]; break_innermost_match;
               try congruence
          end;
          eauto using lift_eval_idx_Z_impl in
        let rec do_stuff _
          := lazymatch goal with
             | [ |- R_regs_preserved _ _ _ ?x ?x ] => reflexivity
             | [ |- R_regs_preserved _ _ _ _ (Symbolic.set_reg _ _ _) ]
               => apply R_regs_preserved_set_reg;
                  [ do_stuff ()
                  | solve [ intros; finish_some_reg () ] ]
             | [ |- R_regs_preserved _ _ _ _ (fold_left _ _ _) ]
               => apply R_regs_preserved_fold_left_set_reg_index;
                  [ do_stuff ()
                  | lazymatch goal with
                    | [ H : Forall2 _ ?x (firstn (List.length ?x) (get_asm_reg _ ?reg_available))
                        |- Forall _ (List.combine ?reg_available ?x) ]
                      => eapply Forall2_R_regs_preserved_same_helper;
                         lazymatch goal with
                         | [ |- Forall2 _ x (firstn (List.length x) (get_asm_reg _ reg_available)) ]
                           => eapply Forall2_weaken; [ | exact H ];
                              cbv beta; intros *; break_innermost_match;
                              intros; destruct_head'_and; eauto using lift_eval_idx_Z_impl
                         | [ H : R _ _ _ _ |- R_regs _ _ _ _ ] => eapply R_regs_subsumed; [ apply H | eauto ]
                         | _ => first [ assumption
                                      | intros; finish_some_reg ()
                                      | idtac ]
                         end
                    end ]
             end in
        do_stuff () ];
      [ match goal with |- ?G => idtac "TODO" G end .. ];
      debug_run ltac:(fun _ => idtac "R => R_regs set_reg end")
  end.

Local Ltac handle_same_mem :=
  repeat first [ progress subst
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | match goal with
                 | [ H : same_mem_addressed nil _ |- _ ] => apply same_mem_addressed_nil in H
                 | [ H : same_mem_addressed (_ ++ _)%list _ |- _ ] => apply same_mem_addressed_app_ex_r in H
                 | [ H : same_mem_addressed (List.rev _) _ |- _ ] => apply same_mem_addressed_rev_ex_r in H
                 | [ H : same_mem_addressed (List.flat_map _ _) _ |- _ ]
                   => apply (same_mem_addressed_flat_map_combine_addrs_ex_r (dereference_scalar:=false)) in H
                 | [ H : same_mem_addressed (List.flat_map _ _) _ |- _ ]
                   => apply (same_mem_addressed_flat_map_combine_addrs_ex_r (dereference_scalar:=true)) in H
                 | [ H : same_mem_addressed (symbolic_mem_state (init_symbolic_state _)) _ |- _ ]
                   => apply same_mem_addressed_init_symbolic_state in H
                 | [ H : same_mem_addressed (List.combine _ _) _ |- _ ]
                   => apply same_mem_addressed_combine_ex_r in H
                 end ].

Local Ltac cleanup_G_dag_state Gfrom from Gto to :=
  repeat match goal with
         | [ H : gensym_dag_ok Gfrom from, H' : gensym_dag_ok Gto to |- _ ]
           => clear H
         | [ H : forall e n, eval ?G0 ?from0 e n -> eval Gfrom from e n, H' : forall e n, eval ?G0 ?from0 e n -> eval Gto to e n |- _ ]
           => clear H
         | [ H : forall e n, eval Gfrom from e n -> eval Gto to e n |- _ ]
           => clear H
         end;
  clear Gfrom from.

Local Ltac forward_dag_state from to :=
  is_var from;
  lazymatch goal with
  | [ Heval : forall e n, eval ?Gfrom from e n -> eval ?Gto to e n |- _ ]
    => repeat match goal with
              | [ H : Forall2 ?P _ _ |- _ ]
                => lazymatch P with
                   | context P'[from]
                     => let P' := context P'[to] in
                        lazymatch P' with
                        | context P'[Gfrom]
                          => let P' := context P'[Gto] in
                             apply (@Forall2_weaken _ _ P P') in H;
                             [ | now intros *; break_innermost_match; eauto 10 using lift_eval_idx_Z_impl, lift_eval_idx_or_list_idx_impl ]
                        end
                   end
              | [ H : R ?frame Gfrom (update_dag_with ?s (fun _ => from)) ?m |- _ ]
                => apply (fun H => @R_subsumed frame Gfrom Gto _ m H to) in H;
                   [ rewrite update_update_dag_with in H; cbv beta in H
                   | clear H; now eauto 10 using lift_eval_idx_Z_impl, lift_eval_idx_or_list_idx_impl .. ]
              | [ H : forall e n, eval ?G0 ?from0 e n -> eval Gfrom from e n |- _ ]
                => unique assert (forall e n, eval G0 from0 e n -> eval Gto to e n) by now eauto 10
              end;
       cleanup_G_dag_state Gfrom from Gto to
  end.

Local Ltac forward_one_dag_state :=
  match goal with
  | [ H : forall e n, eval ?G ?d e n -> eval ?G' ?d' e n |- _ ]
    => is_var G; is_var d; forward_dag_state d d'
  end.

Local Ltac forward_all_dag_state := repeat forward_one_dag_state.

Local Ltac clear_Prop :=
  repeat match goal with
         | [ H : ?T |- _ ]
           => lazymatch type of T with
              | Prop => clear H
              end
         end.

Local Ltac revert_Forall_step ls :=
  match goal with
  | [ H : Forall2 _ ls _ |- _ ] => revert H
  | [ H : Forall2 _ _ ls |- _ ] => revert H
  | [ H : Forall _ ls |- _ ] => revert H
  end.

Local Ltac revert_Foralls :=
  repeat match goal with
         | [ |- context[Forall2 _ ?ls _] ]
           => revert_Forall_step ls
         | [ |- context[Forall2 _ _ ?ls] ]
           => revert_Forall_step ls
         | [ |- context[Forall _ ?ls] ]
           => revert_Forall_step ls
         end.
Theorem symex_asm_func_M_correct
        d frame asm_args_out asm_args_in (G : symbol -> option Z) (s := init_symbolic_state d)
        (s' : symbolic_state) (m : machine_state) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (H : symex_asm_func_M callee_saved_registers output_types stack_size inputs reg_available asm s = Success (Success rets, s'))
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (*(Hasm_reg : get_asm_reg m reg_available = runtime_reg)*)
        (runtime_callee_saved_registers : list Z)
        (*(Hasm_callee_saved_registers : get_asm_reg m callee_saved_registers = runtime_callee_saved_registers)*)
        (HR : R_runtime_input frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (Hd_ok : gensym_dag_ok G d)
        (d' := s'.(dag_state))
        (H_enough_reg : (List.length output_types + List.length runtime_inputs <= List.length reg_available)%nat)
        (Hcallee_saved_reg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) callee_saved_registers)
        (Hreg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : exists m' G'
           (runtime_rets : list (Z + list Z)),
    (DenoteLines m asm = Some m'
     /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
     /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  pose proof (word_args_to_Z_args_bounded word_runtime_inputs).
  cbv [symex_asm_func_M Symbolic.bind ErrorT.bind lift_dag] in H.
  break_match_hyps; destruct_head'_prod; destruct_head'_unit; cbn [fst snd] in *; try discriminate; [].
  repeat first [ progress subst
               | match goal with
                 | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                 | [ x := ?y |- _ ] => subst x
                 end ].
  cbv [R_runtime_output].
  cbv [R_runtime_input R_runtime_input_mem] in HR; repeat (destruct_head'_ex; destruct_head'_and).
  let HR := lazymatch goal with HR : sep _ _ (machine_mem_state m) |- _ => HR end in
  destruct (init_symbolic_state_ok m G _ _ ltac:(eassumption) ltac:(eassumption) HR) as [G1 ?]; destruct_head'_and.
  let in_evars_do tac :=
    let do_with ev :=
      let H := fresh in
      pose ev as H;
      (instantiate (1:=ltac:(progress tac)) in (value of H)); subst H in
    repeat match goal with
           | [ H : context[?ev] |- _ ] => is_evar ev; do_with ev
           | [ H := context[?ev] |- _ ] => is_evar ev; do_with ev
           | [ |- context[?ev] ] => is_evar ev; do_with ev
           end in
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *
               | solve [ auto ]
               | match goal with
                 | [ H : filter _ (List.combine _ (List.combine ?l1 ?l2))  = [] |- _ ]
                   => is_var l1; is_var l2; apply eq_list_of_filter_nil in H;
                      [ try (subst l1 || subst l2)
                      | cbv [idx] in *; saturate_lengths;
                        generalize dependent (List.length l1);
                        generalize dependent (List.length l2);
                        intros; subst; rewrite ?map_length; split; try reflexivity; try congruence; lia ]
                 | [ H : Forall2 (eval_idx_Z _ _) ?l ?v, H' : Forall2 (eval_idx_Z _ _) ?l ?v' |- _ ]
                   => unique assert (v = v')
                     by (eapply eval_eval_idx_Z_Forall2; eapply Forall2_weaken; [ | eassumption | | eassumption ];
                         intros *; apply lift_eval_idx_Z_impl;
                         now typeclasses eauto with core)
                 | [ H : R _ _ _ ?m |- _ ]
                   => is_var m; unique pose proof (@reg_bounded_of_R _ _ _ _ H)
                 end
               | match reverse goal with
                 | [ H : build_inputs _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_inputs start");
                      move H at bottom; eapply build_inputs_ok in H;
                      [
                      | lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | [ |- Forall2 val_or_list_val_matches_spec _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | assumption ];
                      debug_run ltac:(fun _ => idtac "build_inputs end")
                 | [ H : R _ _ (init_symbolic_state _) _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "update R start");
                      eapply R_subsumed in H; [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "update R end")
                 | [ H : build_merge_base_addresses _ _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_base_addresses start");
                      move H at bottom;
                      eapply build_merge_base_addresses_ok
                        with (runtime_reg := runtime_reg (*get_asm_reg m reg_available*))
                        in H;
                      [
                      | clear H;
                        lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | try assumption .. ];
                      [ | repeat first [ match goal with
                                         | [ H1 : Forall2 ?R1 ?l1 (firstn ?n1 (get_asm_reg ?m ?reg_available)),
                                               H2 : Forall2 ?R2 ?l2 (firstn ?n2 (skipn ?n1 (get_asm_reg ?m ?reg_available)))
                                             |- Forall2 ?R3 (?l1 ++ ?l2) (firstn ?n3 (get_asm_reg ?m ?reg_available)) ]
                                           => replace n3 with (n1 + n2) by lia;
                                              rewrite <- (firstn_skipn n1 (firstn (n1 + n2) (get_asm_reg m reg_available))), firstn_firstn, skipn_firstn, minus_plus, Nat.min_l by lia;
                                              apply Forall2_app; eapply Forall2_weaken; [ | exact H1 | | exact H2 ];
                                              cbv beta; intros *;
                                              [ refine (fun x => or_introl x)
                                              | refine (fun x => or_intror x) ]
                                         end
                                       | lia
                                       | saturate_lengths_step
                                       | progress intros *
                                       | break_innermost_match_step
                                       | progress subst
                                       | progress destruct_head'_or
                                       | progress intros
                                       | eapply connect_Forall2_app_connect; [ eassumption | eassumption | try eassumption | .. ]
                                       | solve [ eauto using lift_eval_idx_Z_impl ]
                                       | progress cbv [eval_idx_or_list_idx] in * ] .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_base_addresses end")
                 | [ H : build_merge_stack_placeholders _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders start");
                      subst stack_size;
                      move H at bottom; eapply build_merge_stack_placeholders_ok with (rsp_val:=ltac:(clear_Prop; clear_head (@symbolic_state))) in H;
                      [ destruct H as [G_final H]
                      | lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | try assumption .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders end")
                 | [ H : mapM _ callee_saved_registers _ = _ |- @ex ?T _ ]
                   => lazymatch T with
                      | (*runtime_rets*) list (Z + list Z) => idtac
                      | (*m'*) machine_state => idtac
                      end;
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers start");
                      eapply (@mapM_GetReg_ok_bounded G_final) in H;
                      [ | clear H; try assumption .. ];
                      [
                      | lazymatch goal with
                        | [ |- Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z _ _ idx' v)
                                       (List.map (Symbolic.get_reg _) (List.map reg_index _))
                                       _ ]
                          => destruct_head' symbolic_state; cbn [Symbolic.symbolic_reg_state Symbolic.dag_state] in *; subst;
                             eapply Forall2_get_reg_of_R;
                             [ lazymatch goal with
                               | [ |- R_regs _ _ _ _ ]
                                 => try match goal with H : R _ _ _ _ |- _ => eapply H end
                               | _ => idtac
                               end .. ];
                             repeat first [ assumption
                                          | reflexivity
                                          | rewrite map_length ]
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z)
                                      (List.map (Semantics.get_reg _) _) ]
                          => apply get_reg_bounded
                        | _ => idtac
                        end;
                        repeat first [ assumption
                                     | reflexivity
                                     | rewrite map_length ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- R_regs _ _ _ _ ] => handle_R_regs ()
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers end")
                 | [ H : SymexLines _ _ = Success _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "SymexLines start");
                      let H' := fresh in
                      pose proof H as H'; apply SymexLines_mem_same in H';
                      eapply SymexLines_R in H;
                      [ destruct H as [m' H];
                        exists m', G_final;
                        repeat (destruct_head'_ex; destruct_head'_and);
                        repeat match goal with
                               | [ H : R _ ?G ?s _ |- _ ]
                                 => unique assert (gensym_dag_ok G s) by (destruct s; apply H)
                               end
                      | clear H;
                        lazymatch goal with
                        | [ H : R _ _ _ ?m |- R ?frame' _ _ ?m' ]
                          => move H at bottom; unify frame frame'; unify m m'; cbv [update_dag_with R];
                             destruct_head' symbolic_state;
                             cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *;
                             subst;
                             destruct_head'_and;
                             repeat first [ solve [ auto ]
                                          | progress cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *
                                          | progress subst
                                          | eapply R_flags_subsumed; [ eassumption | now eauto ]
                                          | match goal with
                                            | [ |- _ /\ _ ] => split
                                            | [ |- R_flags _ _ _ _ ]
                                              => progress
                                                   (cbv [R update_dag_with] in *;
                                                    destruct_head'_and)
                                            | [ |- gensym_dag_ok _ _ ]
                                              => progress destruct_head' symbolic_state
                                            end ]
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- R_regs _ _ _ _ ] => handle_R_regs ()
                        | _ => auto
                        end .. ];
                      [ | match goal with |- ?G => idtac "TODO" G end .. ];
                      debug_run ltac:(fun _ => idtac "SymexLines end")
                 | [ H : LoadOutputs _ _ _ = _ |- exists runtime_rets : list (Z + list Z), _ ]
                   => debug_run ltac:(fun _ => idtac "LoadOutputs start");
                      eapply LoadOutputs_ok in H;
                      [ | clear H; try eassumption .. ];
                      [
                      | match goal with
                        | [ |- Forall2 _ (firstn _ _) _ ]
                          => eapply Forall2_firstn;
                             eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *; break_innermost_match; eauto using lift_eval_idx_Z_impl
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadOutputs end")
                 | [ H : Some ?rets = Option.List.lift (List.map (fun idxs => match idxs with inr idxs' => option_map inr (Option.List.lift (List.map (fun a => load a _) idxs')) | inl _ => _ end) ?ls) |- exists runtime_rets : list (Z + list Z), _ ]
                   => debug_run ltac:(fun _ => idtac "Forall2_rets_of_R_mem start");
                      assert (List.length rets = List.length ls) by (symmetry in H; rewrite Option.List.lift_Some_nth_error_all_iff, map_length in H; destruct_head'_and; congruence);
                      let H' := fresh in
                      pose proof H as H'; apply eq_lift_to_Forall2_rets in H';
                      eapply Forall2_rets_of_R_mem in H;
                      [ destruct H as [runtime_rets H]; exists runtime_rets
                      | clear H H';
                        lazymatch goal with
                        | [ |- Forall2 _ _ _ ] => eassumption
                        | [ |- R_mem _ _ _ _ _ ]
                          => eapply R_mem_subsumed;
                             lazymatch goal with
                             | [ H : R ?frame ?G ?ss ?ms |- R_mem ?frame' ?G' ?d ?ss' ?ms' ]
                               => let unif_or_eq x y := first [ unify x y | let H := fresh in assert (H : y = x) by congruence; rewrite H ] in
                                  unif_or_eq frame frame'; unif_or_eq G G';
                                  unif_or_eq (Symbolic.dag_state ss) d;
                                  unif_or_eq (Symbolic.symbolic_mem_state ss) ss';
                                  unif_or_eq (machine_mem_state ms) ms';
                                  cbv [R] in H;
                                  destruct_head' symbolic_state; apply H
                             | _ => eauto
                             end
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "Forall2_rets_of_R_mem end")
                 end
               | progress repeat (apply conj; eauto 10; []) ].
  all: destruct_head' symbolic_state; cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *; subst; handle_same_mem.
  all: cbv [get_asm_reg]; repeat (apply conj; eauto 10; []).
  all: cbv [R update_dag_with] in *; destruct_head'_and.
  all: destruct_head' machine_state; cbn [Semantics.machine_reg_state Semantics.machine_flag_state Semantics.machine_mem_state] in *.
  all: rewrite ?symbolic_mem_state_nil in *; cbn [R_mem] in *.
  all: repeat match goal with H : ?T, H' : ?T |- _ => clear H' end.
  all: repeat match goal with H : DenoteLines _ _ = Some _ |- _ => clear H end.
  all: lazymatch goal with
       | [ H : ?P ?m |- R_mem ?frame' ?G' ?d' ?l' ?m ]
         => is_var m;
            revert m H; change (Lift1Prop.impl1 P (R_mem frame' G' d' l'))
       | [ H : R_mem ?frame ?G ?d ?l ?m |- ?P ?m ]
         => is_var m;
            revert m H; change (Lift1Prop.impl1 (R_mem frame G d l) P)
       end.
  all: saturate_lengths.
  all: repeat first [ progress cbn [R_mem]
                    | match goal with
                      | [ |- context[R_mem ?frame _ _ _] ]
                        => lazymatch frame with
                           | emp _ => fail
                           | _ => rewrite !(R_mem_frame_cps_id I frame)
                           end
                      | [ |- context[R_mem (emp _) _ _ (_ ++ _)] ]
                        => rewrite R_mem_app_iff
                      | [ |- context[R_mem (emp _) _ _ (List.rev _)] ]
                        => rewrite R_mem_rev_iff
                      | [ |- context[R_mem (emp _) _ _ (List.combine _ _)] ]
                        => rewrite R_mem_combine_ex_array_iff;
                           [
                           | lazymatch goal with
                             | [ |- Forall2 _ _ _ ] => eapply Forall2_weaken; [ | eassumption ]; eauto using lift_eval_idx_Z_impl
                             | [ |- (Tuple.nth_default 0 (reg_index _) _ - 8 * Z.of_nat (Datatypes.length _))%Z = word.unsigned _ ]
                               => erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by (eassumption + reflexivity); (*try*) eassumption
                             end .. ]
                      | [ |- Lift1Prop.impl1 ?P _ ]
                        => match P with
                           | context[sep ?p (Lift1Prop.ex1 ?q)]
                             => rewrite (SeparationLogic.sep_ex1_r p q)
                           | context[sep (Lift1Prop.ex1 ?q) ?p]
                             => rewrite (SeparationLogic.sep_ex1_l p q)
                           | Lift1Prop.ex1 _
                             => rewrite Lift1Prop.impl1_ex1_l; intro
                           end
                      | [ H : Forall2 _ _ (_ ++ _) |- _ ] => rewrite Forall2_app_r_iff in H
                      | [ |- context[List.flat_map _ (_ ++ _)] ]
                        => rewrite flat_map_app
                      | [ |- context[List.combine ?ls (?l1 ++ ?l2)] ]
                        => is_var ls; is_var l1;
                           rewrite <- (firstn_skipn (List.length l1) ls), combine_app_samelength
                             by (saturate_lengths; lia)
                      | [ H : Forall2 _ (firstn ?n ?l1) _ |- context[List.combine ?l1 ?l2] ]
                        => is_var l1;
                           rewrite <- (firstn_skipn n l1), <- (firstn_skipn n l2), combine_app_samelength by (saturate_lengths; congruence)
                      | [ H : Forall2 _ ?ls _ |- context[firstn ?n' ?ls] ]
                        => let H' := fresh in
                           pose proof H as H';
                           apply (Forall2_firstn (n:=n')) in H;
                           apply (Forall2_skipn (n:=n')) in H'
                      end
                    | progress destruct_head'_and
                    | rewrite !SeparationLogic.sep_emp_emp
                    | rewrite <- ?SeparationLogic.sep_assoc;
                      progress repeat first [ rewrite !SeparationLogic.sep_emp_emp | rewrite SeparationLogic.sep_comm_emp_r ]
                    | rewrite ?SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp; intro ].
  all: saturate_lengths.
  all: let update_Forall2_in n' H :=
         (let H' := fresh in
          pose proof H as H';
          apply (Forall2_firstn (n:=n')) in H;
          apply (Forall2_skipn (n:=n')) in H') in
       let update_Forall2 n' ls :=
         lazymatch ls with
         | context[n'] => fail
         | _
           => progress repeat match goal with
                              | [ H : Forall2 _ ls _ |- _ ]
                                => update_Forall2_in n' H
                              | [ H : Forall2 _ _ ls |- _ ]
                                => update_Forall2_in n' H
                              end
         end in
       let update_Forall2_ls ls :=
         lazymatch ls with
         | firstn ?n' ?ls => update_Forall2 n' ls
         | skipn ?n' ?ls => update_Forall2 n' ls
         end in
       let update_Forall2_ls2 ls1 ls2 :=
         progress (try update_Forall2_ls ls1; try update_Forall2_ls ls2) in
       let adjust_ns n x n' x' :=
         (let H := fresh in
          constr_eq x x'; (* work around https://github.com/coq/coq/issues/15554 *)
          (tryif constr_eq n n' then fail else idtac);
          lazymatch n with List.length ?ls => is_var ls end;
          lazymatch goal with
          | [ _ := n' <> n |- _ ] => fail
          | _
            => first [ assert (H : n' = n) by congruence; rewrite H in *
                     | pose (n' <> n); pose (n <> n') ]
          end) in
       let adjust_firstn_skipns :=
         repeat match goal with
                | [ _ : context[firstn ?n ?x], _ : context[firstn ?n' ?x'] |- _ ]
                  => adjust_ns n x n' x'
                | [ _ : context[skipn ?n ?x], _ : context[skipn ?n' ?x'] |- _ ]
                  => adjust_ns n x n' x'
                end in
       let tac _ :=
         repeat first [ rewrite @firstn_app in *
                      | rewrite @firstn_skipn_add in *
                      | rewrite Nat.sub_diag in *
                      | rewrite firstn_O in *
                      | rewrite app_nil_r in *
                      | rewrite @firstn_all in *
                      | rewrite @skipn_all in *
                      | match goal with
                        | [ H : context[skipn (List.length ?x) (?x ++ _)] |- _ ]
                          => rewrite skipn_app_sharp in H by reflexivity
                        | [ |- context[List.combine ?ls1 ?ls2] ]
                          => update_Forall2_ls2 ls1 ls2
                        | [ H : Forall2 _ ?ls1 ?ls2 |- _ ]
                          => update_Forall2_ls2 ls1 ls2
                        end ] in
       do 2 (tac ();
             repeat first [ progress saturate_lengths
                          | progress adjust_firstn_skipns ]).
  all: rewrite !(R_mem_flat_map_ex_R_list_scalar_or_array_iff_emp (dereference_scalar:=false));
       [
       | lazymatch goal with
         | [ |- Forall2 _ _ _ ] => try solve [ eapply Forall2_weaken; [ | eassumption ]; cbv zeta beta; intros *; break_innermost_match; intuition eauto using Forall2_weaken, lift_eval_idx_Z_impl ]
         | [ |- (Tuple.nth_default 0 (reg_index _) _ - 8 * Z.of_nat (Datatypes.length _))%Z = word.unsigned _ ]
           => erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by (eassumption + reflexivity); try eassumption
         | [ H : List.map word.unsigned _ = ?ls |- List.map word.unsigned ?ls' = firstn ?n' ?ls ]
           => rewrite <- H, firstn_map; reflexivity
         | [ H : List.map word.unsigned _ = ?ls |- List.map word.unsigned ?ls' = skipn ?n' ?ls ]
           => rewrite <- H, skipn_map; reflexivity
         | _ => idtac
         end .. ].
  all: lazymatch goal with
       | [ |- Forall2 _ _ _ ]
         => revert_Foralls;
            rewrite !@Forall2_forall_iff_nth_error, ?@Forall_forall_iff_nth_error_match;
            cbv [option_eq];
            intros;
            repeat match goal with
                   | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                     => specialize (H i)
                   | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                     => specialize (H i)
                   end;
            repeat first [ exfalso; assumption
                         | assumption
                         | progress subst
                         | progress cbv [eval_idx_or_list_idx] in *
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | progress intros
                         | progress destruct_head'_and; saturate_lengths
                         | congruence
                         | match goal with
                           | [ H : ?x = Some ?y, H' : ?x = Some ?y' |- _ ]
                             => is_var y;
                                assert (y = y') by congruence;
                                (subst y || subst y')
                           | [ H : eval_idx_Z _ _ ?x ?v, H' : eval_idx_Z _ _ ?x ?v' |- _ ]
                             => unique assert (v = v')
                               by (eapply eval_eval_idx_Z; (eapply lift_eval_idx_Z_impl; [ | eassumption ]);
                                   typeclasses eauto with core)
                           | [ H : (0 <= ?z)%Z, H' : (?z < 2^?bw)%Z, H'' : context[Z.land ?z (Z.ones ?bw)] |- _ ]
                             => progress
                                  replace (Z.land z (Z.ones bw)) with z in *
                                 by (rewrite Z.land_ones, Z.mod_small; clear -H H'; lia)
                           end
                         | eapply lift_eval_idx_Z_impl; [ | eassumption ]; solve [ eauto 10 ]
                         | rewrite @nth_error_firstn in * ]
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- Lift1Prop.impl1 _ _ ] => idtac
       end.
  all: [ > | ].
  all: saturate_lengths.
  all: repeat first [ match goal with
                      | [ |- Lift1Prop.impl1 ?P _ ]
                        => match P with
                           | context[sep ?p (Lift1Prop.ex1 ?q)]
                             => rewrite (SeparationLogic.sep_ex1_r p q)
                           | context[sep (Lift1Prop.ex1 ?q) ?p]
                             => rewrite (SeparationLogic.sep_ex1_l p q)
                           | Lift1Prop.ex1 _
                             => rewrite Lift1Prop.impl1_ex1_l; intro
                           end
                      end
                    | progress destruct_head'_and
                    | rewrite !SeparationLogic.sep_emp_emp
                    | rewrite <- ?SeparationLogic.sep_assoc;
                      progress repeat first [ rewrite !SeparationLogic.sep_emp_emp | rewrite SeparationLogic.sep_comm_emp_r ]
                    | rewrite ?SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp; intro
                    | rewrite SeparationLogic.sep_emp_True_l
                    | rewrite SeparationLogic.sep_emp_True_r ].
  all: repeat first [ rewrite @firstn_app in *
                    | rewrite @firstn_all in *
                    | rewrite @skipn_all in *
                    | rewrite Nat.sub_diag in *
                    | rewrite firstn_O in *
                    | rewrite app_nil_r in *
                    | match goal with
                      | [ |- context[firstn ?n ?ls] ]
                        => replace n with (List.length ls) by congruence; rewrite firstn_all
                      | [ |- context[skipn (List.length ?x) (?x ++ _)] ]
                        => rewrite skipn_app_sharp by reflexivity
                      end ].
  all: cbv [R_runtime_output_mem].
  1: let P := lazymatch goal with |- Lift1Prop.impl1 ?P _ => P end in
     let stack_placeholder_values := lazymatch P with context[array _ _ _ ?vals] => vals end in
     apply (Lift1Prop.impl1_ex1_r _ _ stack_placeholder_values).
  1: let P := lazymatch goal with |- Lift1Prop.impl1 ?P _ => P end in
     let input_placeholder_values := lazymatch P with context[R_list_scalar_or_array ?vals asm_args_in] => vals end in
     apply (Lift1Prop.impl1_ex1_r _ _ input_placeholder_values).
  1: lazymatch goal with
     | [ |- Lift1Prop.impl1 ?P ?Q ]
       => lazymatch P with
          | context[array _ _ ?base' ?vals]
            => lazymatch Q with
               | context[array _ _ ?base vals]
                 => cut (base' = base); [ intros -> | now clear; ZnWords ]
               end
          end
     end.
  all: repeat first [ match goal with
                      | [ |- Lift1Prop.impl1 _ (fun m => ?P /\ (@?Q m)) ]
                        => cut (Lift1Prop.iff1 (fun m => P /\ Q m) (sep (emp P) Q));
                           [ intros -> | now clear; split; intros; sepsimpl ]
                      | [ |- context[sep _ (fun m => ?P /\ (@?Q m))] ]
                        => cut (Lift1Prop.iff1 (fun m => P /\ Q m) (sep (emp P) Q));
                           [ intros -> | now clear; split; intros; sepsimpl ]
                      end
                    | rewrite !SeparationLogic.sep_emp_emp
                    | rewrite <- ?SeparationLogic.sep_assoc;
                      progress repeat first [ rewrite !SeparationLogic.sep_emp_emp | rewrite SeparationLogic.sep_comm_emp_r ]
                    | rewrite ?SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp; intro
                    | rewrite SeparationLogic.sep_emp_True_l
                    | rewrite SeparationLogic.sep_emp_True_r
                    | rewrite <- ?SeparationLogic.sep_assoc;
                      lazymatch goal with
                      | [ |- Lift1Prop.impl1 ?P (sep ?p (Lift1Prop.ex1 ?q)) ]
                        => rewrite (SeparationLogic.sep_ex1_r p q);
                           lazymatch q with
                           | fun vals => sep _ (R_list_scalar_or_array vals ?ref)
                             => lazymatch P with
                                | context[R_list_scalar_or_array ?vals' ref]
                                  => apply (Lift1Prop.impl1_ex1_r _ _ vals')
                                end
                           | fun vals => sep _ (array _ _ ?base vals)
                             => lazymatch P with
                                | context[array _ _ ?base' ?vals']
                                  => cut (base = base');
                                     [ intros ->; apply (Lift1Prop.impl1_ex1_r _ _ vals')
                                     | now clear; ZnWords ]
                                end
                           end
                      end
                    | rewrite ?SeparationLogic.sep_assoc;
                      progress repeat match goal with
                                      | [ |- context[sep (Lift1Prop.ex1 ?p) ?q] ]
                                        => lazymatch q with
                                           | context[Lift1Prop.ex1 _] => fail
                                           | _ => rewrite (SeparationLogic.sep_comm (Lift1Prop.ex1 p) q)
                                           end
                                      end ].
  all: rewrite ?SeparationLogic.sep_assoc;
    lazymatch goal with
    | [ |- Lift1Prop.impl1 ?p (sep (emp ?P) ?q) ]
      => cut (Lift1Prop.iff1 p q);
         [ intros ->; apply SeparationLogic.impl1_r_sep_emp; split; [ | reflexivity ]
         | SeparationLogic.cancel; cbn [seps] ]
    end.
  all: saturate_lengths.
  all: repeat first [ solve [ eauto 10 ]
                    | congruence
                    | rewrite Nat.min_id
                    | match goal with
                      | [ |- _ /\ _ ] => split
                      | [ |- _ = _ :> nat ]
                        => repeat match goal with
                                  | [ |- context[@List.length ?A ?x] ]
                                    => generalize dependent (@List.length A x); intros; subst
                                  end
                      | [ H : Forall2 _ (firstn ?n ?ls) ?ls' |- Forall2 _ ?ls ?ls' ]
                        => rewrite firstn_all2 in H by lia
                      end
                    | eapply Forall2_weaken; [ | eassumption ]; intros *;
                      first [ apply lift_eval_idx_Z_impl | apply lift_eval_idx_or_list_idx_impl ];
                      now eauto 10 ].
  all: cbv [val_or_list_val_matches_spec type_spec_of_runtime] in *.
  all: let rec tac _ :=
         revert_Foralls;
         rewrite !@Forall2_forall_iff_nth_error, ?@Forall_forall_iff_nth_error_match;
         cbv [option_eq];
         intros;
         repeat match goal with
                | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                  => specialize (H i)
                | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                  => specialize (H i)
                end;
         rewrite ?@nth_error_map in *; cbv [option_map] in *;
         repeat first [ exfalso; assumption
                      | assumption
                      | progress subst
                      | progress cbv [eval_idx_or_list_idx] in *
                      | break_innermost_match_step
                      | break_innermost_match_hyps_step
                      | progress intros
                      | progress destruct_head'_and; saturate_lengths
                      | congruence
                      | match goal with
                        | [ H : eval_idx_Z _ _ ?x ?v, H' : eval_idx_Z _ _ ?x ?v' |- _ ]
                          => unique assert (v = v')
                            by (eapply eval_eval_idx_Z; (eapply lift_eval_idx_Z_impl; [ | eassumption ]);
                                typeclasses eauto with core)
                        | [ |- (0 <= word.unsigned _ < _)%Z ]
                          => now clear; ZnWords
                        | [ |- Forall2 _ _ _ ]
                          => tac ()
                        | [ |- Forall _ _ ]
                          => tac ()
                        end ]
       in
       lazymatch goal with
       | [ |- Forall2 _ _ _ ]
         => tac ()
       | [ |- Forall _ _ ]
         => tac ()
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- Lift1Prop.iff1 (R_list_scalar_or_array ?zval ?val) (R_list_scalar_or_array ?zval' ?val) ]
         => cut (zval = zval'); [ intros ->; reflexivity | ]
       end.
  all: [ > ].
  apply Forall2_eq.
  let rec tac _ :=
    (revert_Foralls;
     rewrite !@Forall2_forall_iff_nth_error, ?@Forall_forall_iff_nth_error_match;
     cbv [option_eq];
     intros;
     repeat match goal with
            | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
              => specialize (H i)
            | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
              => specialize (H i)
            end;
     repeat rewrite ?@nth_error_combine, ?@nth_error_firstn, ?@nth_error_map, ?@nth_error_seq in *;
     cbv [option_map] in *;
     repeat first [ exfalso; assumption
                  | assumption
                  | progress subst
                  | progress cbv [eval_idx_or_list_idx] in *
                  | progress inversion_option
                  | progress destruct_head'_and
                  | break_innermost_match_step
                  | break_innermost_match_hyps_step
                  | match goal with
                    | [ |- inr _ = inr _ ] => apply f_equal
                    | [ |- _ = _ :> list _ ] => apply Forall2_eq; tac ()
                    | [ |- Some _ = None ] => exfalso
                    end ])
  in
  tac ().
  all: lazymatch goal with
       | [ |- False ] => saturate_lengths
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- False ]
         => repeat match goal with
                   | [ H : _ = _ :> nat |- _ ] => revert H
                   | [ H : (_ < _)%nat |- _ ] => revert H
                   | [ H : (_ >= _)%nat |- _ ] => revert H
                   | [ H : ~ (_ < _)%nat |- _ ] => revert H
                   end;
            clear; autorewrite with distr_length; intros
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- False ]
         => repeat first [ match goal with
                           | [ H : ?T, H' : ?T |- _ ] => clear H'
                           | [ H : ?x = ?x |- _ ] => clear H
                           | [ H : context[@List.length ?A ?x] |- _ ]
                             => is_var x; generalize dependent (@List.length A x)
                           | [ |- context[@List.length ?A ?x] ]
                             => is_var x; generalize dependent (@List.length A x)
                           end
                         | progress subst
                         | progress intros ]
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- False ] => try lia
       | _ => idtac
       end.
  all: [ > ].
  move z0 at bottom.
  move z at bottom.
  revert H71 H131.
  move i4 at bottom.
  move i3 at bottom.
  revert Heqo12.
  revert H70.
  move i5 at bottom.
  move l2 at bottom.
  revert Heqo1 H62.
  move x10 at bottom.
  rewrite Nat.add_0_l.
  move i5 at bottom.
  move l9 at bottom.
  revert Heqo14.
  move x9 at bottom.
  revert Heqo9.
  move x9 at bottom.
  move x3 at bottom.
  revert Heqo4.
  move i0 at bottom.
  move l7 at bottom.
  (* What remains:
  ============================
 x14 = runtime_rets

OR:
  ============================
  nth_error x3 i = Some (inr (i0, l7)) ->
  nth_error x9 i = Some (inr l9) ->
  nth_error l9 i2 = Some i5 ->
  nth_error x10 i = Some (inr l2) ->
  eval_idx_Z G_final dag_state4 i5
    (Z.land (Semantics.get_reg machine_reg_state0 r + 8 * Z.of_nat i2) (Z.ones 64)) ->
  load i5
    (rev (List.combine x4 x11) ++
     rev
       (flat_map
          (fun pat : (idx + idx * list idx) * (idx + list idx) =>
           match pat with
           | (inr (_, addrs'), inl _) => []
           | (inr (_, addrs'), inr items) => List.combine addrs' items
           | _ => []
           end) (List.combine x3 x10))) = Some i4 ->
  nth_error l2 i2 = Some i3 ->
  eval_idx_Z G_final dag_state4 i4 z0 ->
  eval_idx_Z G_final dag_state0 i3 z -> z = z0

*)

Admitted.

Theorem symex_asm_func_correct
        frame asm_args_out asm_args_in (G : symbol -> option Z) (d : dag) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (s' : symbolic_state)
        (H : symex_asm_func d callee_saved_registers output_types stack_size inputs reg_available asm = Success (rets, s'))
        (d' := s'.(dag_state))
        (m : machine_state)
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (runtime_callee_saved_registers : list Z)
        (Hasm_reg : get_asm_reg m reg_available = runtime_reg)
        (HR : R_runtime_input frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (HG_ok : gensym_dag_ok G d)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : (exists m' G'
            (runtime_rets : list (Z + list Z)),
        DenoteLines m asm = Some m'
        /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
        /\ (forall e n, eval G d e n -> eval G' d' e n)
        /\ gensym_dag_ok G' d'
        /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets).
Proof.
  cbv [symex_asm_func] in H; break_innermost_match_hyps; inversion_ErrorT; inversion_prod; subst; reflect_hyps.
  cbv [R]; break_innermost_match.
  let H := multimatch goal with H : _ = Success _ |- _ => H end in
  eapply symex_asm_func_M_correct in H; try eassumption; try apply surjective_pairing; try reflexivity.
  { destruct_head'_ex; destruct_head'_and.
    do 3 eexists; repeat match goal with |- _ /\ _ => apply conj end; try eassumption. }
  { subst runtime_inputs; apply eq_length_Forall2 in Hinputs; lia. }
Qed.

Theorem check_equivalence_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (frame : Semantics.mem_state -> Prop)
        (asm : Lines)
        (expr : API.Expr t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (Hwf : API.Wf expr)
        (H : check_equivalence asm expr arg_bounds out_bounds = Success tt)
        (st : machine_state)
        (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
        (word_args : list (Naive.word 64 + list (Naive.word 64)))
        (args := word_args_to_Z_args word_args)
        (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
        (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
        (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
        (asm_args_out asm_args_in : list (Naive.word 64))
        (runtime_regs := get_asm_reg st assembly_calling_registers)
        (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers)
        (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
        (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
        (HR : R_runtime_input frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st)
  : exists asm' st' (retvals : list (Z + list Z)),
    strip_ret asm = Success asm'
    /\ DenoteLines st asm' = Some st'
    /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
    /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st'.
Proof.
  subst stack_size.
  cbv beta delta [check_equivalence ErrorT.bind] in H.
  repeat match type of H with
         | (let n := ?v in _) = _
           => set v as n in H;
                lazymatch type of H with
                | (let n := ?v in ?rest) = ?rhs
                  => change (match v with n => rest end = rhs) in H
                end
         | match ?v with Success n => @?S n | Error e => @?E e end = ?rhs
           => let n := fresh n in
              let e := fresh e in
              destruct v as [n|e] eqn:?; [ change (S n = rhs) in H | change (E e = rhs) in H ];
                cbv beta in H
         | match ?v with pair a b => @?P a b end = ?rhs
           => let a := fresh a in
              let b := fresh b in
              destruct v as [a b] eqn:?; change (P a b = rhs) in H;
                cbv beta in H
         | match ?v with true => ?T | false => ?F end = ?rhs
           => let a := fresh a in
              let b := fresh b in
              destruct v eqn:?; [ change (T = rhs) in H | change (F = rhs) in H ];
                cbv beta in H
         end; try discriminate; [].
  reflect_hyps.
  subst.
  pose proof empty_gensym_dag_ok.
  let H := fresh in pose proof Hargs as H; eapply build_input_runtime_ok_nil in H; [ | eassumption .. ].
  pose proof (word_args_to_Z_args_bounded word_args).
  repeat first [ assumption
               | match goal with
                 | [ H : build_inputs _ _ = _ |- _ ] => move H at bottom; eapply build_inputs_ok in H; [ | eassumption .. ]
                 | [ H : symex_PHOAS ?expr ?inputs ?d = Success _, H' : build_input_runtime _ ?ri = Some _ |- _ ]
                   => move H at bottom; eapply symex_PHOAS_correct with (runtime_inputs:=ri) in H; [ | eassumption .. ]
                 | [ H : symex_asm_func _ _ _ _ _ _ _ = Success _ |- _ ]
                   => move H at bottom; eapply symex_asm_func_correct in H;
                      [ | try (eassumption + apply surjective_pairing + reflexivity) .. ];
                      [ | clear H; eapply Forall2_weaken; [ apply lift_eval_idx_or_list_idx_impl | eassumption ] ]
                 end
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress inversion_prod
               | progress inversion_ErrorT
               | progress subst
               | match goal with
                 | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                   => rewrite H in H'; inversion_option
                 | [ H : forall args, Forall2 ?P args ?v -> Forall2 _ _ _, H' : Forall2 ?P _ ?v |- _ ]
                   => specialize (H _ H')
                 | [ Himpl : forall e n, eval ?G1 ?d1 e n -> eval ?G2 ?d2 e n,
                       H1 : Forall2 (eval_idx_or_list_idx ?G1 ?d1) ?PHOAS_output ?r1,
                       H2 : Forall2 (eval_idx_or_list_idx ?G2 ?d2) ?PHOAS_output ?r2
                       |- _ ]
                   => assert_fails constr_eq r1 r2;
                      assert (r1 = r2) by (eapply eval_eval_idx_or_list_idx_Forall2_gen; eassumption);
                      subst
                 | [ H := _ |- _ ] => subst H
                 end ].
  do 3 eexists; repeat first [ eassumption | apply conj ]; trivial.
Qed.

Theorem generate_assembly_of_hinted_expr_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (asm : Lines)
        (expr : API.Expr t)
        (f : type.interp _ t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (asm_out : Lines)
        (* Phrased this way to line up with the bounds pipeline exactly *)
        (Hbounded
         : (forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
               ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (API.Interp expr) arg1) = true
               /\ type.app_curried (API.Interp expr) arg1 = type.app_curried f arg2)
           /\ API.Wf expr)
        (H : generate_assembly_of_hinted_expr asm expr arg_bounds out_bounds = Success asm_out)
  : asm = asm_out
    /\ forall (st : machine_state)
              (frame : Semantics.mem_state -> Prop)
              (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
              (word_args : list (Naive.word 64 + list (Naive.word 64)))
              (args := word_args_to_Z_args word_args)
              (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
              (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
              (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
              (asm_args_out asm_args_in : list (Naive.word 64))
              (runtime_regs := get_asm_reg st assembly_calling_registers)
              (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers)
              (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
              (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
              (HR : R_runtime_input frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st),
      (* Should match check_equivalence_correct exactly *)
      exists asm' st' (retvals : list (Z + list Z)),
             strip_ret asm = Success asm'
        /\ DenoteLines st asm' = Some st'
        /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
        /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st'.
Proof.
  cbv [generate_assembly_of_hinted_expr] in H.
  break_innermost_match_hyps; inversion H; subst; destruct_head'_and; split; [ reflexivity | intros ].
  eapply check_equivalence_correct; eassumption.
Qed.

(* Some theorems about the result of calling generate_assembly_of_hinted_expr_correct on various Pipeline functions *)
