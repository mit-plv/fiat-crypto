Require Import Coq.Sorting.Permutation.
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
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ListUtil.PermutationCompat.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.ListUtil.Filter.
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
Require Import Crypto.Util.Tactics.RevertUntil.
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
           {output_scalars_are_pointers:bool}
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
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_pointer_arguments_out asm_pointer_arguments_in : list (Naive.word 64))
           (reg_available : list REG) (runtime_reg : list Z)
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := exists (asm_arguments_out asm_arguments_in : list (Naive.word 64)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ (Nat.min (List.length output_types + List.length runtime_inputs) (List.length reg_available) <= List.length runtime_reg)%nat
    /\ get_asm_reg m reg_available = runtime_reg
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.length asm_arguments_out = List.length output_types
    /\ List.map word.unsigned asm_arguments_out = List.firstn (List.length output_types) runtime_reg
    /\ List.map word.unsigned asm_arguments_in = List.firstn (List.length runtime_inputs) (List.skipn (List.length output_types) runtime_reg)
    /\ List.map fst (List.filter (fun '(_, v) => output_scalars_are_pointers || Option.is_Some v)%bool (List.combine asm_arguments_out output_types)) = asm_pointer_arguments_out
    /\ List.map fst (List.filter (fun '(_, v) => match v with inl _ => false | inr _ => true end)%bool (List.combine asm_arguments_in runtime_inputs)) = asm_pointer_arguments_in
    /\ (Semantics.get_reg m rsp - 8 * Z.of_nat stack_size)%Z = word.unsigned stack_base
    /\ (* it must be the case that all the scalars in the real input values match what's in registers / the calling convention *)
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => v = v2
                      | inr _ => True
                      end)
        runtime_inputs
        (firstn (length runtime_inputs) (skipn (length output_types) runtime_reg))
    /\ R_runtime_input_mem (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types runtime_inputs stack_size stack_base asm_arguments_out asm_arguments_in runtime_reg m.

(* TODO : should we preserve inputs? *)
Definition R_runtime_output_mem
           {output_scalars_are_pointers:bool}
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
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_pointer_arguments_out asm_pointer_arguments_in : list (Naive.word 64))
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := exists (asm_arguments_out asm_arguments_in : list (Naive.word 64)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.map fst (List.filter (fun '(_, v) => output_scalars_are_pointers || match v with inl _ => false | inr _ => true end)%bool (List.combine asm_arguments_out runtime_outputs)) = asm_pointer_arguments_out
    /\ List.map fst (List.filter (fun '(_, v) => Option.is_Some v)%bool (List.combine asm_arguments_in input_types)) = asm_pointer_arguments_in
    /\ R_runtime_output_mem (output_scalars_are_pointers:=output_scalars_are_pointers) frame runtime_outputs input_types stack_size stack_base asm_arguments_out asm_arguments_in m.

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
     => let _ := init_symbolic_state_descr in
        let vals := Tuple.to_list _ (m.(machine_reg_state)) in
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
  epose proof (dag_gensym_n_eq_G G d (Tuple.to_list 16 m.(machine_reg_state))) as H.
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
  epose proof (dag_gensym_n_G_ok) as H. (* COQBUG(https://github.com/coq/coq/issues/15927) *)
  specialize (H _ _ _ _ _ _ ltac:(eassumption) ltac:(repeat rewrite <- surjective_pairing; reflexivity) ltac:(eassumption)).
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

Lemma get_reg_of_R_regs G d r mr reg
      (Hwide : let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N)
      (Hreg : R_regs G d r mr)
  : forall idx', Symbolic.get_reg r (reg_index reg) = Some idx' -> eval_idx_Z G d idx' (Semantics.get_reg mr reg).
Proof.
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

Lemma Forall2_get_reg_of_R_regs G d r mr regs
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (Hreg : R_regs G d r mr)
  : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G d idx' v)
            (List.map (Symbolic.get_reg r) (List.map reg_index regs))
            (List.map (Semantics.get_reg mr) regs).
Proof.
  induction regs as [|reg regs IH]; cbn [List.map] in *;
    inversion Hwide; clear Hwide; subst;
    constructor; auto; clear dependent regs; [].
  now apply get_reg_of_R_regs.
Qed.

Lemma get_reg_of_R frame G s m reg
      (Hwide : let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N)
      (Hreg : R frame G s m)
  : forall idx', Symbolic.get_reg s (reg_index reg) = Some idx' -> eval_idx_Z G s idx' (Semantics.get_reg m reg).
Proof.
  apply get_reg_of_R_regs; cbv [R] in *; destruct s; tauto.
Qed.

Lemma Forall2_get_reg_of_R frame G s m regs
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (Hreg : R frame G s m)
  : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G s idx' v)
            (List.map (Symbolic.get_reg s) (List.map reg_index regs))
            (List.map (Semantics.get_reg m) regs).
Proof.
  apply Forall2_get_reg_of_R_regs; cbv [R] in *; destruct s; tauto.
Qed.

Lemma get_reg_bounded mr reg
  : (0 <= Semantics.get_reg mr reg < 2 ^ 64)%Z.
Proof.
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

Lemma get_reg_bounded_Forall mr regs
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z)
           (List.map (Semantics.get_reg mr) regs).
Proof.
  rewrite Forall_map, Forall_forall; intros; apply get_reg_bounded.
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

Definition R_regs_preserved G d G' d' (m : Semantics.reg_state) rs rs'
  := forall rn idx, Symbolic.get_reg rs' rn = Some idx -> exists idx', Symbolic.get_reg rs rn = Some idx' /\ let v := R_regs_preserved_v rn m in eval_idx_Z G d idx' v -> eval_idx_Z G' d' idx v.

Global Instance R_regs_preserved_Reflexive G d m : Reflexive (R_regs_preserved G d G d m) | 100.
Proof. intro; cbv [R_regs_preserved]; eauto. Qed.

Lemma R_regs_subsumed_get_reg_same_eval G d G' d' rs rs' rm
      (H : R_regs G d rs rm)
      (H_impl : R_regs_preserved G d G' d' rm rs rs')
  : R_regs G' d' rs' rm.
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

Lemma R_regs_preserved_set_reg G d G' d' rs rs' ri rm v
      (H : R_regs_preserved G d G' d' rm rs rs')
      (H_same : (ri < 16)%nat -> exists idx, Symbolic.get_reg rs ri = Some idx /\ let v' := R_regs_preserved_v ri rm in eval_idx_Z G d idx v' -> eval_idx_Z G' d' v v')
  : R_regs_preserved G d G' d' rm rs (Symbolic.set_reg rs' ri v).
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

Lemma R_regs_preserved_fold_left_set_reg_index {T1 T2} G d G' d' rs rs' rm (r_idxs : list (_ * (_ * T1 + _ * T2)))
      (H : R_regs_preserved G d G' d' rm rs rs')
      (H_same : Forall (fun '(r, v) => let v := match v with inl (v, _) => v | inr (v, _) => v end in exists idx, Symbolic.get_reg rs (reg_index r) = Some idx /\ let v' := R_regs_preserved_v (reg_index r) rm in eval_idx_Z G d idx v' -> eval_idx_Z G' d' v v') r_idxs)
  : R_regs_preserved
      G d G' d' rm
      rs
      (fold_left (fun rst '(r, idx')
                  => Symbolic.set_reg rst (reg_index r)
                             match idx' with
                             | inl (idx', _) => idx'
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
      (H : Forall2 (fun (idx' : idx * option idx + idx * list idx) v
                    => match idx' with
                       | inl (idx', _) => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                       | inr (base', _) => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                       end)
                   idxs (firstn (List.length idxs) (get_asm_reg m reg_available)))
      (HR : R_regs G d rs m)
      (Hex : forall n r, (n < List.length idxs)%nat -> nth_error reg_available n = Some r -> exists idx, Symbolic.get_reg rs (reg_index r) = Some idx)
  : Forall (fun '(r, v)
            => let v := match v with inl (v, _) => v | inr (v, _) => v end in
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
  : forall (idxs : list (idx * option idx + idx * list idx)) base_vals addr_idxs base_vals_words
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl (idx', addr')
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                     /\ option_eq (eval_idx_Z G d) addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs_array : Forall2 (fun idx addr_idx
                                   => match idx, addr_idx with
                                      | inl _, inl _ => True
                                      | inr (base, idxs), inr addr_idxs
                                        => List.length idxs = List.length addr_idxs
                                      | inl _, inr _ | inr _, inl _ => False
                                      end)
                             idxs addr_idxs)
           (Hidxs_scalar : Forall2 (fun idx addr_idx
                                    => match idx, addr_idx with
                                       | inl (_, addr), inl addr_idx
                                         => Option.is_Some addr = dereference_scalar
                                       | inr _, inr _ => True
                                       | inl _, inr _ | inr _, inl _ => False
                                       end)
                                   idxs addr_idxs)
           (Haddr_vals : Forall2 (fun idx v
                                     => match idx with
                                        | inl base => if dereference_scalar then True else eval_idx_Z G d base v
                                        | _ => True
                                        end)
                                 addr_idxs base_vals)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl (_, Some addr), inl val => if dereference_scalar then [(addr, val)] else []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    | _, _ => []
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
               | progress inversion_option
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress subst
               | progress cbn [List.combine List.map fold_right R_scalar_or_array R_mem List.length List.app Option.is_Some] in *
               | progress cbv [option_eq] in *
               | rewrite SeparationLogic.sep_emp_emp
               | rewrite SeparationLogic.sep_ex1_l
               | rewrite SeparationLogic.sep_ex1_r
               | rewrite R_mem_app_iff
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
               | progress specialize_by_assumption
               | progress specialize_by reflexivity
               | match goal with
                 | [ H : Lift1Prop.iff1 _ _ |- _ ] => rewrite H; clear H
                 | [ H : Forall2 _ ?addr_idxs ?v |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun h => sep _ (sep (emp (Forall2 _ ?addr_idxs h /\ _)) _))) ]
                   => apply (Lift1Prop.impl1_ex1_r _ _ v)
                 | [ |- Lift1Prop.impl1 ?A (Lift1Prop.ex1 ?B0) ]
                   => lazymatch B0 with
                      | fun h => sep (emp (Forall2 ?R (?addr_idx :: ?addr_idxs) h /\ _)) (@?B h)
                        => lazymatch goal with
                           | [ H : Forall2 _ addr_idxs ?rest |- _ ]
                             => cut (Lift1Prop.impl1 A (Lift1Prop.ex1 (fun h0 => Lift1Prop.ex1 (fun h1 => Lift1Prop.ex1 (fun h2 => B0 (match addr_idx with inl _ => inl (if dereference_scalar' then h0 else h1) | inr _ => inr h2 end :: rest))))));
                                [ (intros ->);
                                  let h0 := fresh in
                                  let h1 := fresh in
                                  let h2 := fresh in
                                  rewrite Lift1Prop.impl1_ex1_l; intro h0;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h1;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h2;
                                  apply (Lift1Prop.impl1_ex1_r _ _ (match addr_idx with inl _ => inl (if dereference_scalar' then h0 else h1) | inr _ => inr h2 end :: rest));
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
               | reflexivity
               | break_innermost_match_hyps_step ].
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
                    | progress cbn [eval_idx_or_list_idx List.length] in *
                    | apply SeparationLogic.impl1_r_sep_emp; split; [ | reflexivity ] ].
Qed.

Lemma R_mem_flat_map_ex_R_list_scalar_or_array_impl_emp {dereference_scalar:bool} G d
  : forall (idxs : list (idx * option idx + idx * list idx)) base_vals addr_idxs base_vals_words
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl (idx', addr')
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                     /\ option_eq (eval_idx_Z G d) addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs_array : Forall2 (fun idx addr_idx
                                   => match idx, addr_idx with
                                      | inl _, inl _ => True
                                      | inr (base, idxs), inr addr_idxs
                                        => List.length idxs = List.length addr_idxs
                                      | inl _, inr _ | inr _, inl _ => False
                                      end)
                             idxs addr_idxs)
           (Hidxs_scalar : Forall2 (fun idx addr_idx
                                    => match idx, addr_idx with
                                       | inl (_, addr), inl addr_idx
                                         => Option.is_Some addr = dereference_scalar
                                       | inr _, inr _ => True
                                       | inl _, inr _ | inr _, inl _ => False
                                       end)
                                   idxs addr_idxs)
           (Haddr_vals : Forall2 (fun idx v
                                     => match idx with
                                        | inl base => if dereference_scalar then True else eval_idx_Z G d base v
                                        | _ => True
                                        end)
                                 addr_idxs base_vals)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.impl1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl (_, Some addr), inl val => if dereference_scalar then [(addr, val)] else []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    | _, _ => []
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
  : forall (idxs : list (idx * option idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
           (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl (idx', addr')
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                     /\ option_eq (eval_idx_Z G d) addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs_array : Forall2 (fun idx addr_idx
                                   => match idx, addr_idx with
                                      | inl _, inl _ => True
                                      | inr (base, idxs), inr addr_idxs
                                        => List.length idxs = List.length addr_idxs
                                      | inl _, inr _ | inr _, inl _ => False
                                      end)
                             idxs addr_idxs)
           (Hidxs_scalar : Forall2 (fun idx addr_idx
                                    => match idx, addr_idx with
                                       | inl (_, addr), inl addr_idx
                                         => Option.is_Some addr = dereference_scalar
                                       | inr _, inr _ => True
                                       | inl _, inr _ | inr _, inl _ => False
                                       end)
                                   idxs addr_idxs)
           (Haddr_vals : Forall2 (fun idx v
                                     => match idx with
                                        | inl base => if dereference_scalar then True else eval_idx_Z G d base v
                                        | _ => True
                                        end)
                                 addr_idxs base_vals)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl (_, Some addr), inl val => if dereference_scalar then [(addr, val)] else []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    | _, _ => []
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
      (idxs : list (idx * option idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
      (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
      (Hidxs : Forall2 (fun idx' v
                        => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                           match idx' with
                           | inl (idx', addr')
                             => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                /\ option_eq (eval_idx_Z G d) addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                           | inr (base', addrs')
                             => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                           end)
                       idxs base_vals)
      (Hidxs_array : Forall2 (fun idx addr_idx
                              => match idx, addr_idx with
                                 | inl _, inl _ => True
                                 | inr (base, idxs), inr addr_idxs
                                   => List.length idxs = List.length addr_idxs
                                 | inl _, inr _ | inr _, inl _ => False
                                 end)
                             idxs addr_idxs)
      (Hidxs_scalar : Forall2 (fun idx addr_idx
                               => match idx, addr_idx with
                                  | inl (_, addr), inl addr_idx
                                    => Option.is_Some addr = dereference_scalar
                                  | inr _, inr _ => True
                                  | inl _, inr _ | inr _, inl _ => False
                                  end)
                              idxs addr_idxs)
      (Haddr_vals : Forall2 (fun idx v
                             => match idx with
                                | inl base => if dereference_scalar then True else eval_idx_Z G d base v
                                | _ => True
                                end)
                            addr_idxs base_vals)
      (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals)
  : Lift1Prop.iff1
      (R_mem frame G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl (_, Some addr), inl val => if dereference_scalar then [(addr, val)] else []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    | _, _ => []
                    end)
                (List.combine idxs addr_idxs)))
      (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words)%sep.
Proof.
  intros.
  rewrite ?(R_mem_frame_cps_id I frame).
  erewrite R_mem_flat_map_R_list_scalar_or_array_iff_emp by eassumption.
  reflexivity.
Qed.

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

Lemma eq_lift_to_Forall2_rets mem_st idxs rets
      (Hrets : Some rets
               = Option.List.lift
                   (List.map (fun idxs
                              => match idxs : idx + list idx with
                                 | inr idxs => option_map inr (Option.List.lift (List.map (fun a => load a mem_st) idxs))
                                 | inl idx => Some (inl idx)
                                 end)
                             idxs))
  : Forall2 (fun rv idxs
             => match idxs, rv with
                | inl idx, inl v => idx = v
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

Lemma build_inputs_ok_R {descr:description} G ss types inputs args d' frame ms
      (d := ss.(dag_state))
      (H : build_inputs types d = (inputs, d'))
      (HR : R frame G ss ms)
      (Hargs : Forall2 val_or_list_val_matches_spec args types)
      (Hbounds : Forall (fun v => match v with
                                  | inl v => (0 <= v < 2^64)%Z
                                  | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                  end) args)
  : exists G',
    Forall2 (eval_idx_or_list_idx G' d') inputs args
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' (update_dag_with ss (fun _ => d')) ms.
Proof.
  eapply build_inputs_ok in H; [ | try eassumption .. ]; [ | destruct ss; apply HR .. ]; [].
  destruct H as [G' H]; exists G'.
  intuition idtac.
  eapply R_subsumed; eassumption.
Qed.

Lemma build_merge_stack_placeholders_ok_R {descr:description} G s s' frame frame' ms
      (rsp_val : Z) (stack_vals : list Z) base_stack base_stack_word_val
      (H : build_merge_stack_placeholders (List.length stack_vals) s = Success (base_stack, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hstack_vals_bounded : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_vals)
      (stack_addr_vals := List.map (fun i => Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals) + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length stack_vals)))
      (HR : R frame' G s ms)
      (Hrsp : (rsp_val - 8 * Z.of_nat (List.length stack_vals))%Z = word.unsigned base_stack_word_val)
      (Hframe : Lift1Prop.iff1 frame' (frame * array cell64 (word.of_Z 8) base_stack_word_val stack_vals)%sep)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (Hrsp_val : Z.land rsp_val (Z.ones 64) = Z.land (Semantics.get_reg ms rsp) (Z.ones 64))
  : exists G',
    ((exists rsp_idx,
         set_reg r (reg_index rsp) rsp_idx = r'
         /\ eval_idx_Z G' d' rsp_idx (Z.land rsp_val (Z.ones 64)))
     /\ f = f'
     /\ (exists stack_addr_idxs stack_idxs,
            Forall2 (eval_idx_Z G' d') stack_addr_idxs stack_addr_vals
            /\ Forall2 (eval_idx_Z G' d') stack_idxs stack_vals
            /\ (* TODO: Is this too specific a spec? *) List.rev (List.combine stack_addr_idxs stack_idxs) ++ m = m'))
    /\ eval_idx_Z G' d' base_stack (Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals)) (Z.ones 64))
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).

Proof.
  eapply build_merge_stack_placeholders_ok in H; [ | try eassumption .. ]; [ | destruct s; apply HR .. ]; [].
  destruct H as [G' H]; exists G'.
  intuition try eassumption.
  all: destruct_head'_ex; destruct_head'_and.
  all: subst m m' f f' r r' d d'.
  all: destruct s, s'; cbv [R] in *; cbn [Symbolic.dag_state Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *.
  all: subst.
  all: destruct_head'_and.
  1: intuition eauto using R_flags_subsumed.
  { eapply R_regs_subsumed_get_reg_same_eval;
      [ eapply R_regs_subsumed; now eauto | ].
    apply R_regs_preserved_set_reg; [ reflexivity | ].
    specialize (Hreg_good rsp).
    cbv [Option.is_Some] in *; break_innermost_match_hyps; try congruence.
    eexists; split; [ reflexivity | ].
    cbv [R_regs_preserved_v] in *.
    erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by first [ reflexivity | eassumption ].
    congruence. }
  { destruct ms; cbn [Semantics.machine_mem_state] in *.
    clear Hrsp_val.
    lazymatch goal with
    | [ H : R_mem ?frame _ _ ?ss ?m |- R_mem ?frame' ?G' ?d' ?ss' ?m ]
      => eapply R_mem_subsumed in H;
         [ revert m H;
           refine (_ : Lift1Prop.impl1 (R_mem frame G' d' ss) (R_mem frame' G' d' ss'))
         | now eauto ]
    end.
    rewrite (R_mem_frame_cps_id I frame), (R_mem_frame_cps_id I frame'), R_mem_app_iff, Hframe.
    rewrite R_mem_rev_iff, R_mem_combine_ex_array_iff by eassumption.
    repeat rewrite ?SeparationLogic.sep_ex1_r, ?SeparationLogic.sep_ex1_l.
    unshelve eapply Lift1Prop.impl1_ex1_r; try exact stack_vals.
    match goal with
    | [ |- Lift1Prop.impl1 ?P ?Q ]
      => let v1 := lazymatch P with
                   | context[array _ _ ?base] => base
                   end in
         let v2 := lazymatch Q with
                   | context[array _ _ ?base] => base
                   end in
         replace v2 with v1 by ZnWords
    end.
    match goal with
      [ |- Lift1Prop.impl1 ?P ?Q ]
      => cut (Lift1Prop.iff1 P Q); [ intros ->; reflexivity | ]
    end.
    SeparationLogic.cancel; cbn [seps].
    apply SeparationLogic.Proper_emp_iff; split; trivial; intros.
    intuition idtac.
    saturate_lengths.
    rewrite ListUtil.firstn_all by congruence.
    assumption. }
  { rewrite get_reg_set_reg_full; break_innermost_match; eauto. }
Qed.

Local Ltac find_list_in ls in_ls :=
  lazymatch in_ls with
  | ls => idtac
  | firstn _ ?ls' => find_list_in ls ls'
  | List.combine ?lsa ?lsb => first [ find_list_in ls lsa | find_list_in ls lsb ]
  | List.map _ ?ls' => find_list_in ls ls'
  end.

Local Ltac find_sublist_in ls in_ls :=
  first [ find_list_in ls in_ls
        | lazymatch ls with
          | firstn _ ?ls => find_sublist_in ls in_ls
          | List.combine ?lsa ?lsb => first [ find_sublist_in lsa in_ls | find_sublist_in lsb in_ls ]
          | List.map _ ?ls => find_sublist_in ls in_ls
          end ].

Local Ltac revert_Forall_step ls :=
  match goal with
  | [ H : Forall2 _ ?lsa ?lsb |- _ ]
    => first [ find_list_in ls lsa | find_list_in ls lsb ];
       revert H
  | [ H : Forall _ ?ls' |- _ ]
    => find_list_in ls ls';
       revert H
  | [ H : context[nth_error ?ls' _] |- _ ]
    => find_list_in ls ls';
       revert H
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

Local Ltac intros_then_revert tac :=
  let H := fresh in
  pose proof I as H;
  intros;
  tac ();
  revert_until H;
  clear H.

Local Ltac reverted_Foralls_to_nth_error :=
  rewrite ?@Forall2_forall_iff_nth_error, ?@Forall_forall_iff_nth_error_match;
  cbv [option_eq];
  intros_then_revert
    ltac:(fun _
          => repeat match goal with
                    | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                      => specialize (H i)
                    | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                      => specialize (H i)
                    | [ H : context[nth_error ?ls _] |- context[nth_error ?ls' ?i] ]
                      => first [ find_list_in ls ls' | find_list_in ls' ls ];
                         specialize (H i)
                    | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls' ?i] |- _ ]
                      => find_list_in ls ls'; specialize (H i)
                    end).

Local Ltac revert_Foralls_to_nth_error := revert_Foralls; reverted_Foralls_to_nth_error.

Ltac adjust_Foralls_firstn_skipn :=
  let rep a a' :=
    tryif constr_eq a a'
    then idtac
    else (let H' := fresh in
          assert (H' : a' = a) by congruence;
          rewrite H' in * ) in
  let check_H H :=
    lazymatch type of H with
    | Forall _ _ => idtac
    | Forall2 _ _ _ => idtac
    end in
  repeat match goal with
         | [ H : context[firstn ?n ?ls] |- context[firstn ?n' ?ls] ]
           => check_H H; progress rep n n'
         | [ H : context[skipn ?n ?ls] |- context[skipn ?n' ?ls] ]
           => check_H H; progress rep n n'
         end.

Local Ltac Foralls_to_nth_error_rewrites :=
  repeat rewrite ?@nth_error_combine, ?@nth_error_firstn, ?@nth_error_skipn, ?@nth_error_map, ?@nth_error_seq; cbv [option_map].

Local Ltac Foralls_to_nth_error_destructs :=
  let cleanup _ :=
    try match goal with
        | [ |- context[False -> _] ] => intros; exfalso; assumption
        | [ |- context[Some _ = None -> _] ] => intros; now inversion_option
        | [ |- context[None = Some _ -> _] ] => intros; now inversion_option
        | [ |- context[_ -> True] ] => intros; exact I
        | [ |- context[_ -> ?x = ?x] ] => intros; reflexivity
        end in
  let match_free v :=
    lazymatch v with
    | context[match _ with _ => _ end] => fail
    | _ => idtac
    end in
  let do_destruct v :=
    first [ is_var v; destruct v
          | lazymatch type of v with
            | sumbool _ _ => destruct v
            | _ => let H := fresh in
                   destruct v eqn:H; revert H
            end ] in
  let find_v P :=
    match P with
    | context[False]
      => lazymatch P with
         | match ?v with _ => _ end => v
         end
    | match ?v with _ => _ end = ?RHS
      => let LHS := lazymatch P with ?LHS = _ => LHS end in
         lazymatch RHS with
         | None
           => lazymatch LHS with
              | context[None] => v
              end
         | Some _
           => lazymatch LHS with
              | context[Some _] => v
              end
         end
    end in
  repeat (first [ match goal with
                  | [ |- context[?P -> _] ]
                    => let v := find_v P in
                       match_free v; do_destruct v
                  | [ |- context[?P -> _] ]
                    => let v := find_v P in
                       do_destruct v
                  end
                | break_innermost_match_step
                | progress Foralls_to_nth_error_rewrites ];
          cleanup ()).

Local Ltac Foralls_to_nth_error_cleanup :=
  intros_then_revert
    ltac:(fun _
          => repeat first [ assumption
                          | exact I
                          | exfalso; assumption
                          | progress subst
                          | progress destruct_head'_and
                          | progress inversion_option
                          | progress inversion_pair
                          | progress inversion_sum
                          | discriminate ]).

Local Ltac Foralls_to_nth_error :=
  revert_Foralls_to_nth_error;
  intros *;
  Foralls_to_nth_error_rewrites;
  Foralls_to_nth_error_destructs;
  Foralls_to_nth_error_cleanup.

Local Ltac handle_simple_R_mem :=
  repeat first [ progress cbn [R_mem]
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
               | rewrite ?SeparationLogic.sep_assoc, SeparationLogic.impl1_l_sep_emp; intro
               | progress autorewrite with zsimplify_const ].

Local Ltac handle_eval_eval :=
  repeat match goal with
         | [ H : eval_idx_Z _ _ ?i _, H' : eval_idx_Z _ _ ?i _ |- _ ]
           => eapply eval_eval_idx_Z in H'; [ | eapply lift_eval_idx_Z_impl; [ | exact H ]; now eauto ]
         end.

Lemma build_merge_base_addresses_ok_R
      {descr:description} {dereference_scalar:bool}
      (idxs : list (idx + list idx))
      (reg_available : list REG)
      (runtime_reg : list Z)
      G s frame frame' ms
      (d := s.(dag_state))
      (Hvals : Forall2 (fun it rv
                        => match it with
                           | inl idx => if dereference_scalar
                                        then True
                                        else eval_idx_Z G d idx rv
                           | inr _ => True
                           end)
                       idxs (List.firstn (List.length idxs) runtime_reg))
      (Hreg : Nat.min (List.length idxs) (List.length reg_available) <= List.length runtime_reg)
      (Henough_reg : List.length idxs <= List.length reg_available)
      s'
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      outputaddrs
      (H : build_merge_base_addresses (dereference_scalar:=dereference_scalar) idxs reg_available s = Success (outputaddrs, s'))
      (Hreg_available_wide : Forall (fun reg => let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
      (HR : R frame' G s ms)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (Hruntime_reg : get_asm_reg ms reg_available = runtime_reg)
      addr_vals addr_ptr_vals
      (Haddr_ptr_vals : List.map word.unsigned addr_ptr_vals = List.firstn (List.length idxs) runtime_reg)
      (Hframe : Lift1Prop.iff1 frame' (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals addr_ptr_vals)%sep)
      (Heval_addr_vals : Forall2 (eval_idx_or_list_idx G d) idxs addr_vals)
      (Hruntime_reg_bounded : Forall (fun v => (0 <= v < 2^64)%Z) runtime_reg)
  : exists G',
    ((exists (outputaddrs' : list (idx * option idx + idx * list idx)),
         let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
         fold_left (fun rst '(r, idx')
                    => set_reg rst (reg_index r)
                               match idx' with
                               | inl (idx', _) => idx'
                               | inr (base_idx', idxs') => base_idx'
                               end)
                   (List.combine reg_available outputaddrs')
                   r
         = r'
         /\ ((* TODO: Is this too specific a spec? *)
             List.rev (List.flat_map
                         (fun '(idx', idx)
                          => match idx', idx with
                             | inl (reg_val, Some addr), inl val => if dereference_scalar then [(addr, val)] else []

                             | inl _, _ | _, inl _ => []
                             | inr (base', addrs'), inr items
                               => List.combine addrs' items
                             end)
                         (List.combine outputaddrs' idxs))
                      ++ m)
            = m'
         /\ (* outputaddrs' base / array *)
           Forall2
             (fun idx' v =>
                match idx' with
                | inl (idx', addr') (* scalars *)
                  => eval_idx_Z G' d' idx' (Z.land v (Z.ones 64))
                     /\ option_eq (eval_idx_Z G' d') addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                | inr (base', addrs')
                  (* arrays: (exists base',
                    (* set_reg r rn base' = r'
                    /\ *) eval_idx_Z G' d' base' (Z.land base_reg_val (Z.ones 64))) *)
                  => eval_idx_Z G' d' base' (Z.land v (Z.ones 64))
                     /\ (* arrays : Forall2 (eval_idx_Z G' d') addrs addrs_vals *)
                       Forall2 (eval_idx_Z G' d') addrs' (addrs_vals_of v addrs')
                end)
             outputaddrs'
             (List.firstn (List.length outputaddrs') runtime_reg)
         /\ (* outputaddrs base:
              arrays: eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64)) *)
           Forall2
             (fun idx base_reg_val =>
                match idx with
                | inr base => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | inl (inr base) => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | inl (inl r) => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) runtime_reg)
         /\ (* outputaddrs reg: *)
           Forall2
             (fun idx r =>
                match idx with
                | inl (inl r') => r = r'
                | inl (inr _) | inr _ => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) reg_available)
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl (idx, _), inl val_idx
                         => if dereference_scalar
                            then True
                            else forall v, (0 <= v < 2^64)%Z -> eval_idx_Z G' d' idx v <-> eval_idx_Z G' d' val_idx v
                       | inr (_, ls), inr ls' => List.length ls = List.length ls'
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs' idxs
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl (inl _), inl (_, None) => dereference_scalar = false
                       | inl (inr addr), inl (_, Some addr') => dereference_scalar = true /\ addr = addr'
                       | inr _, inr _ => True
                       | inl (inl _), inl (_, Some _) | inl (inr _), inl (_, None) => False
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs outputaddrs')
     /\ f = f')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Proof.
  eapply build_merge_base_addresses_ok in H; [ | try eassumption .. ]; [ | destruct s; apply HR .. ]; [].
  destruct H as [G' H]; exists G'.
  intuition idtac.
  all: destruct_head'_ex; destruct_head'_and.
  all: subst m m' f f' r r' d d'.
  all: destruct s, s'; cbv [R] in *; cbn [Symbolic.dag_state Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *.
  all: destruct_head'_and.
  1: intuition idtac.
  all: try solve [ subst; eapply R_flags_subsumed; eauto ].
  { subst.
    eapply R_regs_subsumed_get_reg_same_eval;
      [ eapply R_regs_subsumed; now eauto | ].
    apply R_regs_preserved_fold_left_set_reg_index; [ reflexivity | ].
    eapply Forall2_R_regs_preserved_same_helper; try assumption.
    all: eauto using R_regs_subsumed.
    all: destruct_head'_and.
    { Foralls_to_nth_error; intuition idtac. }
    { intros.
      match goal with
      | [ H : (forall reg, Option.is_Some (Symbolic.get_reg ?s (reg_index reg)) = true)
          |- context[Symbolic.get_reg ?s (reg_index ?ri)] ]
        => generalize (H ri); cbv [Option.is_Some]; break_innermost_match;
           try congruence
      end; eauto. } }
  { destruct ms; cbn [Semantics.machine_mem_state] in *.
    subst.
    lazymatch goal with
    | [ H : R_mem ?frame _ _ ?ss ?m |- R_mem ?frame' ?G' ?d' ?ss' ?m ]
      => eapply R_mem_subsumed in H;
         [ revert H; generalize m;
           refine (_ : Lift1Prop.impl1 (R_mem frame G' d' ss) (R_mem frame' G' d' ss'))
         | now eauto ]
    end.
    rewrite (R_mem_frame_cps_id I frame), (R_mem_frame_cps_id I frame'), R_mem_app_iff, Hframe.
    rewrite R_mem_rev_iff, (R_mem_flat_map_ex_R_list_scalar_or_array_iff_emp (dereference_scalar:=dereference_scalar)).
    all: [ >
         | try first [ eassumption
                     | etransitivity; [ eassumption | saturate_lengths; congruence ] ] .. ].
    { repeat rewrite ?SeparationLogic.sep_ex1_r, ?SeparationLogic.sep_ex1_l.
      unshelve eapply Lift1Prop.impl1_ex1_r; try exact addr_vals.
      handle_simple_R_mem.
      rewrite !SeparationLogic.sep_assoc.
      rewrite sep_emp_holds_l.
      { reflexivity. }
      { cbv [sep]; intros; repeat (destruct_head'_ex; destruct_head'_and).
        intuition eauto using bounded_of_R_list_scalar_or_array.
        eapply Forall2_weaken; [ | eassumption ].
        eauto using lift_eval_idx_or_list_idx_impl. } }
    { Foralls_to_nth_error.
      all: discriminate. }
    { saturate_lengths.
      adjust_Foralls_firstn_skipn.
      repeat (revert Hreg_available_wide; Foralls_to_nth_error; intros).
      all: cbv [eval_idx_or_list_idx] in *.
      all: break_innermost_match_hyps; try now exfalso.
      all: intros; handle_eval_eval; subst.
      all: eauto using lift_eval_idx_Z_impl. }
    { cbn [Semantics.machine_reg_state] in *.
      saturate_lengths.
      progress adjust_Foralls_firstn_skipn.
      Foralls_to_nth_error.
      all: intuition try congruence.
      split_iff.
      repeat match goal with
             | [ |- context[Semantics.get_reg ?m ?r] ]
               => unique pose proof (@get_reg_bounded m r)
             end.
      eauto using lift_eval_idx_Z_impl. } }
  { subst.
    let H := fresh in
    match goal with
    | [ |- Option.is_Some (get_reg (fold_left ?f ?ls ?s) ?r) = true ]
      => unshelve (epose proof (reg_all_set_fold_left s [r] f ls _ _) as H;
                   inversion H; subst; assumption)
    end.
    all: cbn [List.map]; intros; invlist Forall; constructor; try solve [ constructor ]; eauto with nocore.
    all: destruct_head'_prod.
    all: rewrite get_reg_set_reg_full.
    all: break_innermost_match; try reflexivity.
    all: eauto with nocore. }
Qed.

Lemma mapM_GetReg_ok_R_full {descr:description} G regs idxs reg_vals s s' frame ms
      (H : mapM GetReg regs s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (Hregval : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G s idx' v) (List.map (get_reg r) (List.map reg_index regs)) reg_vals)
      (Hbounded : Forall (fun v => (0 <= v < 2^64)%Z) reg_vals)
      (Hregval_len : List.length regs = List.length reg_vals)
      (HR : R frame G s ms)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : ((exists reg_idxs,
         List.map (get_reg r) (List.map reg_index regs) = List.map Some reg_idxs
         /\ Forall2 (eval_idx_Z G s') reg_idxs reg_vals)
     /\ Forall2 (eval_idx_Z G s') idxs reg_vals
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ R frame G s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Proof.
  eapply mapM_GetReg_ok_bounded in H; [ | try eassumption .. ]; [ | destruct s; apply HR .. ]; [].
  all: intuition idtac.
  all: destruct s, s'; cbv [R Symbolic.symbolic_reg_state Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state] in *; intuition subst.
  all: eauto using R_regs_subsumed, R_flags_subsumed, R_mem_subsumed.
Qed.

Lemma mapM_GetReg_ok_R {descr:description} G regs idxs s s' frame (ms : machine_state)
      (H : mapM GetReg regs s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (reg_vals := List.map (Semantics.get_reg ms) regs)
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (HR : R frame G s ms)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : ((exists reg_idxs,
         List.map (get_reg r) (List.map reg_index regs) = List.map Some reg_idxs
         /\ Forall2 (eval_idx_Z G s') reg_idxs reg_vals)
     /\ Forall2 (eval_idx_Z G s') idxs reg_vals
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ R frame G s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Proof.
  subst reg_vals.
  eapply mapM_GetReg_ok_R_full in H; [ eassumption | try eassumption .. ].
  all: rewrite ?map_length.
  all: intuition idtac.
  all: try apply get_reg_bounded_Forall.
  all: cbv [R] in HR.
  all: try solve [ destruct s; apply HR ].
  all: try solve [ cbv [R] in HR; destruct s; eapply Forall2_get_reg_of_R_regs; try assumption; try apply HR ].
Qed.

Lemma SymexLines_ok_R frame G s m asm _tt s'
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (H : Symbolic.SymexLines asm s = Success (_tt, s'))
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (HR : R frame G s m)
  : exists m',
    Semantics.DenoteLines m asm = Some m'
    /\ gensym_dag_ok G d
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ R frame G s' m'
    /\ same_mem_addressed s s'
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Proof.
  destruct _tt.
  pose proof H as H'; eapply SymexLines_mem_same in H'.
  pose proof H as H''; eapply SymexLines_reg_same in H''.
  cbv [same_reg_some] in *.
  eapply SymexLines_R in H; [ | eassumption .. ].
  destruct H as [m' H]; exists m'.
  intuition eauto with nocore.
  all: cbv [R] in *.
  all: try solve [ destruct s; apply HR ].
Qed.

Local Instance R_mem_Proper_Permutation_iff1
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> Lift1Prop.iff1) R_mem | 10.
Proof.
  cbv [Proper respectful]; intros; subst.
  let H := match goal with H : Permutation _ _ |- _ => H end in
  induction H; cbn [R_mem]; break_innermost_match.
  all: repeat first [ reflexivity
                    | assumption
                    | progress (SeparationLogic.cancel; cbn [seps])
                    | etransitivity; eassumption ].
Qed.

Local Instance R_mem_Proper_Permutation_iff
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> eq ==> iff) R_mem | 10.
Proof.
  repeat intro; subst; eapply R_mem_Proper_Permutation_iff1; (reflexivity + eassumption).
Qed.

Local Instance R_mem_Proper_Permutation_impl
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> eq ==> Basics.impl) R_mem | 10.
Proof.
  repeat intro; subst; eapply R_mem_Proper_Permutation_iff; (idtac + symmetry); (eassumption + reflexivity).
Qed.

Local Instance R_mem_Proper_Permutation_flip_impl
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> eq ==> Basics.flip Basics.impl) R_mem | 10.
Proof.
  repeat intro; subst; eapply R_mem_Proper_Permutation_iff; (idtac + symmetry); (eassumption + reflexivity).
Qed.

Local Instance R_mem_Proper_Permutation_impl1
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> Lift1Prop.impl1) R_mem | 10.
Proof.
  repeat intro; eapply R_mem_Proper_Permutation_impl; (reflexivity + eassumption).
Qed.

Local Instance R_mem_Proper_Permutation_flip_impl1
  : Proper (eq ==> eq ==> eq ==> @Permutation _ ==> Basics.flip Lift1Prop.impl1) R_mem | 10.
Proof.
  repeat intro; eapply R_mem_Proper_Permutation_flip_impl; (reflexivity + eassumption).
Qed.

Lemma get_asm_reg_bounded s rs : Forall (fun v => (0 <= v < 2 ^ 64)%Z) (get_asm_reg s rs).
Proof. apply get_reg_bounded_Forall. Qed.

Lemma LoadArray_ok_R {descr:description} frame G s ms s' base base_val base_word_val len idxs
      (H : LoadArray base len s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (HR : R frame G s ms)
      (Hbase : eval_idx_Z G d base (Z.land base_val (Z.ones 64)))
      (Hbase_word_val : base_val = word.unsigned base_word_val)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : ((exists (addrs : list idx),
         Permutation m (List.combine addrs idxs ++ m')
         /\ List.length idxs = len
         /\ Forall2 (eval_idx_Z G d') addrs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
         /\ Forall (fun addr => Forall (fun x => (fst x =? addr)%N = false) m') addrs)
     /\ r = r'
     /\ f = f')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ ((exists vals,
            Forall2 (eval_idx_Z G d') idxs vals
            /\ Forall (fun v => 0 <= v < 2^64)%Z vals
            /\ R (frame * array cell64 (word.of_Z 8) base_word_val vals)%sep G s' ms)
        /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true)).
Proof.
  replace (Z.land base_val (Z.ones 64)) with base_val in Hbase
      by now (subst; rewrite Z.land_ones by lia; rewrite Z.mod_small by apply Properties.word.unsigned_range).
  eapply LoadArray_ok in H; [ | try eassumption .. ]; [ | destruct s; apply HR .. ].
  repeat (destruct_head'_and; destruct_head'_ex).
  subst r r'.
  repeat (split; eauto 10 using ex_intro, conj with nocore; []).
  split; try solve [ destruct s, s'; cbn [Symbolic.symbolic_reg_state] in *; subst; eauto ]; [].
  move ms at bottom.
  subst d d' f f' m m'.
  destruct s, s'; cbv [R] in *; cbn [Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *; subst.
  destruct_head'_and.
  all: [ > ].
  match goal with
  | [ H : Permutation ?s _, H' : R_mem _ _ _ ?s _ |- _ ] => is_var s; rewrite H in H'
  end.
  match goal with
  | [ H : R_mem _ _ _ _ _ |- _ ]
    => eapply R_mem_subsumed in H; [ | eassumption ];
       let T := open_constr:(_) in
       evar (R' : T);
       let P := lazymatch type of H with ?P _ => P end in
       let H' := fresh in
       assert (H' : Lift1Prop.iff1 P R');
       [
       | hnf in H'; rewrite H' in H; subst R'; clear H' ]
  end.
  { erewrite (R_mem_frame_cps_id I frame), R_mem_app_iff, R_mem_combine_ex_array_iff by (eassumption + reflexivity).
    repeat rewrite ?SeparationLogic.sep_ex1_r, ?SeparationLogic.sep_ex1_l.
    subst R'; reflexivity. }
  cbv [Lift1Prop.ex1] in *; destruct_head'_ex.
  match goal with
  | [ H : sep _ _ _ |- _ ]
    => let T := open_constr:(_) in
       evar (R' : T);
       let P := lazymatch type of H with ?P _ => P end in
       let H' := fresh in
       assert (H' : Lift1Prop.impl1 P R');
       [
       | hnf in H'; apply H' in H; subst R'; clear H' ]
  end.
  { repeat rewrite <- ?SeparationLogic.sep_assoc, ?SeparationLogic.sep_emp_emp, ?SeparationLogic.sep_comm_emp_r.
    rewrite ?SeparationLogic.sep_assoc.
    rewrite <- ?SeparationLogic.sep_comm_emp_r.
    rewrite <- ?SeparationLogic.sep_assoc.
    erewrite <- (R_mem_frame_cps_id I).
    subst R'; reflexivity. }
  destruct_head' (@sep).
  cbv [emp] in *.
  destruct_head'_ex; destruct_head'_and.
  subst.
  rewrite @Properties.map.split_empty_r in * by typeclasses eauto.
  subst.
  rewrite @firstn_all in * by reflexivity.
  eexists; repeat (apply conj; eauto using R_flags_subsumed, R_regs_subsumed; []).
  match goal with
  | [ H : context[array _ _ ?n] |- context[array _ _ ?n'] ]
    => replace n with n' in H by ZnWords
  end.
  assumption.
Qed.

Lemma R_mem_flat_map_no_opt_ex_R_list_scalar_or_array_iff_emp {dereference_scalar:bool} G d
  : forall (addr_idxs : list (idx + list idx)) base_vals base_vals_words val_idxs
           (Haddr_idxs : Forall2 (fun idx' v
                                  => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                     match idx' with
                                     | inl idx'
                                       => eval_idx_Z G d idx' v
                                     | inr addrs'
                                       => Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                     end)
                                 addr_idxs base_vals)
           (Hidxs_array : Forall2 (fun idx val_idx
                                   => match idx, val_idx with
                                      | inl idx, inl val_idx
                                        => if dereference_scalar
                                           then True
                                           else forall v, (0 <= v < 2^64)%Z -> eval_idx_Z G d idx v <-> eval_idx_Z G d val_idx v
                                      | inr idxs, inr val_idxs
                                        => List.length idxs = List.length val_idxs
                                      | inl _, inr _ | inr _, inl _ => False
                                      end)
                             addr_idxs val_idxs)
           (*(Haddr_vals : Forall2 (fun idx v
                                     => match idx with
                                        | inl base => TODO2 (dereference_scalar, base, v) /\ if dereference_scalar then eval_idx_Z G d base v else True
                                        | _ => True
                                        end)
                                 val_idxs base_vals)*)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inr addrs', inr items
                      => List.combine addrs' items
                    | _, _ => []
                    end)
                (List.combine addr_idxs val_idxs)))
      (Lift1Prop.ex1
         (fun vals
          => emp (Forall2 (eval_idx_or_list_idx G d) val_idxs vals
                  /\ Forall (fun v => match v with
                                      | inl v => 0 <= v < 2^64
                                      | inr vs => Forall (fun v => 0 <= v < 2^64) vs
                                      end%Z) vals)
              * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) vals base_vals_words))%sep.
Proof.
  pose dereference_scalar as dereference_scalar'.
  induction addr_idxs as [|addr_idx addr_idxs IH],
      base_vals as [|base_val base_vals],
        base_vals_words as [|base_vals_word base_vals_words],
          val_idxs as [|val_idx val_idxs];
    try specialize (IH base_vals base_vals_words val_idxs);
    do 2 (intro H; inversion H; clear H); subst.
  all: cbv [R_list_scalar_or_array R_list_scalar_or_array_nolen] in *; cbn [List.map flat_map R_mem fold_right List.combine List.length] in *; intros; inversion_nat_eq; inversion_list.
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
               | progress inversion_option
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress subst
               | progress cbn [List.combine List.map fold_right R_scalar_or_array R_mem List.length List.app Option.is_Some] in *
               | progress cbv [option_eq] in *
               | rewrite SeparationLogic.sep_emp_emp
               | rewrite SeparationLogic.sep_ex1_l
               | rewrite SeparationLogic.sep_ex1_r
               | rewrite R_mem_app_iff
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
               | progress specialize_by_assumption
               | progress specialize_by reflexivity
               | match goal with
                 | [ H : Lift1Prop.iff1 _ _ |- _ ] => rewrite H; clear H
                 | [ H : Forall2 _ ?addr_idxs ?v |- Lift1Prop.impl1 _ (Lift1Prop.ex1 (fun h => sep _ (sep (emp (Forall2 _ ?addr_idxs h /\ _)) _))) ]
                   => apply (Lift1Prop.impl1_ex1_r _ _ v)
                 | [ |- Lift1Prop.impl1 ?A (Lift1Prop.ex1 ?B0) ]
                   => lazymatch B0 with
                      | fun h => sep (emp (Forall2 ?R (?addr_idx :: ?addr_idxs) h /\ _)) (@?B h)
                        => lazymatch goal with
                           | [ H : Forall2 _ addr_idxs ?rest |- _ ]
                             => cut (Lift1Prop.impl1 A (Lift1Prop.ex1 (fun h0 => Lift1Prop.ex1 (fun h1 => Lift1Prop.ex1 (fun h2 => B0 (match addr_idx with inl _ => inl (if dereference_scalar' then h0 else h1) | inr _ => inr h2 end :: rest))))));
                                [ (intros ->);
                                  let h0 := fresh in
                                  let h1 := fresh in
                                  let h2 := fresh in
                                  rewrite Lift1Prop.impl1_ex1_l; intro h0;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h1;
                                  rewrite Lift1Prop.impl1_ex1_l; intro h2;
                                  apply (Lift1Prop.impl1_ex1_r _ _ (match addr_idx with inl _ => inl (if dereference_scalar' then h0 else h1) | inr _ => inr h2 end :: rest));
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
               | reflexivity
               | break_innermost_match_hyps_step ].
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
  all: repeat first [ progress split_iff
                    | match goal with
                      | [ H' : eval_idx_Z _ _ ?i ?v, H'' : (0 <= ?v < _)%Z, H : forall v', (0 <= v' < _)%Z -> eval_idx_Z _ _ ?i v' -> eval_idx_Z _ _ _ _ |- _ ]
                        => specialize (H _ H'' H')
                      end ].
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
                    | progress cbn [eval_idx_or_list_idx List.length] in *
                    | apply SeparationLogic.impl1_r_sep_emp; split; [ | reflexivity ] ].
Qed.

Lemma LoadOutputs_ok_R {descr:description} {dereference_scalar:bool} frame G s ms s' outputaddrs output_types output_vals idxs
      (H : LoadOutputs (dereference_scalar:=dereference_scalar) outputaddrs output_types s = Success (Success idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (HR : R frame G s ms)
      (Houtputaddrs : Forall2 (fun idx val
                               => match idx with
                                  | inl (inr base) | inr base => eval_idx_Z G d base (Z.land val (Z.ones 64))
                                  | inl (inl _)
                                    => True
                                  end) outputaddrs output_vals)
      (Houtputaddrs_reg : Forall (fun idx
                                  => match idx with
                                     | inl (inl r)
                                       => (let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in sz = 64%N)
                                          /\ dereference_scalar = false
                                     | inl (inr _)
                                       => dereference_scalar = true
                                     | _ => True
                                     end) outputaddrs)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : (exists output_vals_words (output_vals' : list Z) (outputaddrs' : list (idx + list idx)) vals,
        output_vals' = List.map word.unsigned output_vals_words
        /\ Forall (fun v => (0 <= v < 2^64)%Z) output_vals'
        /\ List.length output_vals = List.length output_vals'
        /\ (Forall2 (fun idxs '((base, len), (base_val, base_val'))
                     => match idxs, base, len with
                        | inr idxs, inr base, Some len
                          => Forall2 (eval_idx_Z G d') idxs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
                             /\ Z.land base_val (Z.ones 64) = base_val'
                        | inl idx, inl (inl r), None
                          => (exists idx',
                                 get_reg s' (reg_index r) = Some idx'
                                 /\ eval_idx_Z G d' idx' base_val')
                             /\ eval_idx_Z G d' idx base_val'
                             /\ dereference_scalar = false
                        | inl idx, inl (inr addr), None
                          => idx = addr
                             /\ eval_idx_Z G d' addr base_val'
                             /\ dereference_scalar = true
                        | _, _, _ => False
                        end)
                    outputaddrs'
                    (List.combine (List.combine outputaddrs output_types) (List.combine output_vals output_vals'))
            /\ Permutation m (List.flat_map
                                (fun '(addrs, idxs)
                                 => match addrs, idxs with
                                    | inr addrs, inr idxs
                                      => List.combine addrs idxs
                                    | inl addr, inl idx
                                      => if dereference_scalar
                                         then [(addr, idx)]
                                         else []
                                    | inl _, inr _ | inr _, inl _ => []
                                    end)
                                (List.combine outputaddrs' idxs)
                                ++ m')
            /\ Forall2
                 (fun addrs idxs
                  => match addrs, idxs with
                     | inl idx, inl val_idx
                       => if dereference_scalar
                          then True
                          else forall v, (0 <= v < 2^64)%Z -> eval_idx_Z G d' idx v <-> eval_idx_Z G d' val_idx v
                     | inr addrs, inr idxs
                       => List.length idxs = List.length addrs
                     | inl _, inr _ | inr _, inl _ => False
                     end)
                 outputaddrs'
                 idxs
            /\ Forall (fun addrs => match addrs with
                                    | inl idx => True
                                    | inr addrs
                                      => Forall (fun addr => Forall (fun x => (fst x =? addr)%N = false) m') addrs
                                    end)
                      outputaddrs'
            /\ List.length output_types = List.length outputaddrs)
        /\ (Forall2 (eval_idx_or_list_idx G d') idxs vals
            /\ Forall (fun v => match v with
                                | inl v => (0 <= v < 2^64)%Z
                                | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                end) vals
            /\ R (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) vals output_vals_words)%sep G s' ms))
    /\ r = r'
    /\ f = f'
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Proof.
  pose dereference_scalar as dereference_scalar'.
  pose proof (fun (*i*) rv (*(H : nth_error outputaddrs i = Some (inl (inl rv)))*) H1 => @Forall2_get_reg_of_R_regs G d r ms [rv] (Forall_cons _ H1 (Forall_nil _)) ltac:(destruct s; apply HR)).
  pose proof (fun i rv (H : nth_error outputaddrs i = Some (inl (inl rv))) H1 => @Forall2_get_reg_of_R_regs G d r ms [rv] (Forall_cons _ H1 (Forall_nil _)) ltac:(destruct s; apply HR)) as Houtputaddrs_reg_nth_error.
  eapply LoadOutputs_ok in H; [ | try eassumption .. ]; [ | try (destruct s; apply HR) .. ].
  all: [ >
       | lazymatch goal with
         | [ |- Forall _ _ ]
           => Foralls_to_nth_error;
              repeat first [ break_innermost_match_hyps_step
                           | progress destruct_head'_and
                           | progress intros
                           | progress inversion_pair
                           | progress subst
                           | progress specialize_by reflexivity
                           | progress cbn [List.map] in *
                           | progress invlist Forall2
                           | match goal with
                             | [ H : forall x, Some _ = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
                             | [ H : context[eval_idx_Z _ _ _ (Semantics.get_reg ?m ?r)] |- _ ]
                               => replace (Semantics.get_reg m r) with (Z.land (Semantics.get_reg m r) (Z.ones 64)) in H
                                   by now rewrite Z.land_ones by lia; rewrite Z.mod_small by now apply get_reg_bounded
                             end
                           | solve [ eauto ]
                           | solve [ repeat (intuition (inversion_option; subst; eauto) || esplit) ] ]
         | [ |- Forall2 _ _ _ ]
           => eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *; break_innermost_match; eauto
         end .. ].
  all: [ > ].
  subst r r' d d' f f' m m'.
  cbv [R] in *.
  destruct_head' symbolic_state; cbn [Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *.
  repeat (destruct_head'_and; destruct_head'_ex; subst).
  repeat (apply conj; eauto; []).
  match goal with
  | [ H : Permutation ?s _, H' : R_mem _ _ _ ?s _ |- _ ] => is_var s; rewrite H in H'; setoid_rewrite H; clear s H
  end.
  setoid_rewrite (R_mem_frame_cps_id I (sep frame _) G _ _ ms).
  let H := match goal with H : R_mem _ _ _ _ _ |- _ => H end in
  let P := lazymatch type of H with ?P _ => P end in
  let Q := open_constr:(_) in
  assert (H' : Lift1Prop.impl1 P Q); [ | apply H' in H; clear H' ];
  move H at bottom.
  { rewrite (R_mem_frame_cps_id I frame), R_mem_app_iff, <- SeparationLogic.sep_assoc.
    reflexivity. }
  cbv [sep R_list_scalar_or_array] in *.
  repeat (destruct_head'_and; destruct_head'_ex).
  match goal with
  | [ |- exists (a : ?A) b c (d : ?D), @?P a b c d ]
    => let Q := open_constr:(_ /\ exists (a : A) (d : D), _) in
       cut Q
  end.
  { intros [H'0 [output_vals_words [vals H'1] ] ].
    eexists output_vals_words, (List.map word.unsigned output_vals_words), _, vals.
    repeat match goal with |- _ /\ _ => split | |- ex _ => esplit end.
    all: lazymatch goal with
         | [ |- List.length _ = List.length (List.map _ _) ]
           => rewrite map_length
         | [ |- Forall (fun v => (0 <= v < _)%Z) (List.map word.unsigned _) ]
           => rewrite Forall_map_iff, Forall_forall; intros; ZnWords
         | [ |- Permutation _ _ ] => reflexivity
         | [ |- ?x = ?x ] => reflexivity
         | [ |- ?x = ?y ]
           => first [ is_evar x; tryif has_evar y then fail 1 else reflexivity
                    | idtac ]
         | _ => idtac
         end.
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: match goal with
         | [ H : R_mem _ _ _ _ _ |- R_mem _ _ _ _ _ ] => eapply R_mem_subsumed; [ exact H | auto ]
         | [ H : ?frame ?x |- ?frame ?ev ] => is_var frame; is_evar ev; is_var x; exact H
         | [ H : R_mem _ _ _ (flat_map _ (List.combine _ _)) ?m |- R_list_scalar_or_array_nolen _ _ ?m' ]
           => unify m m'
         | _ => cbv [emp]
         end.
    all: repeat match goal with
                | [ H : ?T |- map.split _ _ _ ] => is_evar T; clear H
                end.
    all: lazymatch goal with
         | [ |- map.split _ _ _ ] => try eassumption
         | [ |- ?x = map.empty /\ _ ] => is_evar x; split; [ reflexivity | ]
         | _ => idtac
         end.
    all: lazymatch goal with
         | [ |- map.split _ map.empty _ ] => rewrite Properties.map.split_empty_l; try reflexivity
         | _ => idtac
         end.
    all: [ > lazymatch goal with |- List.length _ = List.length _ => idtac end | lazymatch goal with |- R_list_scalar_or_array_nolen _ _ _ => idtac end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    all: [ > first [ refine (proj1 H'0) | refine (proj1 H'1) ] | .. ]; shelve_unifiable;
      repeat first [ match type of H'1 with
                     | _ /\ _ => destruct H'1 as [? H'1]
                     end
                   | match type of H'0 with
                     | _ /\ _ => destruct H'0 as [? H'0]
                     end ].
    Unshelve.
    all: exact True. }
  split.
  { intuition eauto using R_regs_subsumed, R_flags_subsumed.
    all: [ > ].
    Foralls_to_nth_error.
    all: intros; repeat (destruct_head'_ex; destruct_head'_and).
    all: split; intros.
    all: handle_eval_eval; subst; eauto. }
  clear Houtputaddrs_reg_nth_error.
  repeat match goal with
         | [ m : @map.rep _ _ Semantics.mem_state |- _ ] => clear dependent m
         | [ m : Symbolic.mem_state |- _ ] => clear dependent m
         end.
  exactly_once multimatch goal with
               | [ m : @map.rep _ _ Semantics.mem_state |- _ ] => revert dependent m
               end.
  intro m; revert m.
  lazymatch goal with
  | [ |- context[R_mem _ _ _ (flat_map _ (List.combine ?addrs _))] ]
    => is_var addrs; revert dependent addrs
  end.
  intro outputaddrs'.
  revert dependent output_types; intro.
  revert dependent outputaddrs; intro.
  revert dependent idxs; intro.
  revert dependent output_vals; intro.
  revert outputaddrs' outputaddrs output_types output_vals idxs.
  cbv [R_list_scalar_or_array_nolen].
  induction outputaddrs' as [|outputaddr' outputaddrs' IH],
      outputaddrs as [|outputaddr outputaddrs],
        output_types as [|output_type output_types],
          output_vals as [|output_val output_vals],
            idxs as [|idx idxs];
    try specialize (IH outputaddrs output_types output_vals idxs);
    cbn [List.combine List.flat_map List.length List.map R_mem fold_right];
    intros; inversion_nat_eq; invlist Forall2; invlist Forall.
  { exists nil, nil; eauto 10. }
  all: [ > ].
  specialize_by_assumption.
  let H := match goal with H : R_mem _ _ _ _ _ |- _ => H end in
  rewrite (R_mem_app_iff _ _ _ _ _ _) in H; cbv [sep] in H.
  repeat (destruct_head'_ex; destruct_head'_and).
  lazymatch type of IH with
  | forall m, R_mem _ _ _ (flat_map _ (List.combine _ _)) m -> _ => idtac
  end.
  specialize (IH _ ltac:(eassumption)).
  lazymatch type of IH with
  | ex _ => idtac
  end.
  destruct IH as [output_vals_words [vals IH] ].
  pose outputaddr as outputaddrv.
  all: repeat first [ progress destruct_head'_and
                    | progress destruct_head'_ex
                    | exfalso; discriminate
                    | exfalso; assumption
                    | progress subst
                    | progress cbn [R_mem] in *
                    | progress cbv [emp sep Lift1Prop.ex1] in *
                    | progress inversion_prod
                    | progress handle_eval_eval
                    | match goal with
                      | [ H : R_cell64 _ _ _ _ _ |- _ ]
                        => rewrite (R_cell64_ex_cell64_iff _ _ _ _ _) in H
                      | [ H : map.split _ map.empty _ |- _ ]
                        => rewrite Properties.map.split_empty_l in H
                      | [ H : map.split _ _ map.empty |- _ ]
                        => rewrite Properties.map.split_empty_r in H
                      | [ H : R_mem _ _ _ (List.combine _ _) _ |- _ ]
                        => (idtac + (eapply R_mem_subsumed in H; [ | eassumption ]));
                           let H' := fresh in
                           pose R_mem_combine_ex_array_iff as H';
                           cbv [Lift1Prop.iff1] in H';
                           rewrite H' in H;
                           clear H';
                           [
                           | clear H; try reflexivity .. ];
                           [
                           | rewrite ?@Forall2_map_r_iff in *;
                             (eapply Forall2_weaken; [ | eassumption ]); cbv beta; intros *;
                             match goal with
                             | [ |- ?f ?x -> ?f ?y ] => cut (x = y); [ intros ->; exact id | ]
                             end;
                             rewrite !Z.land_ones by (clear; lia); push_Zmod;
                             rewrite (Z.mod_small (word.unsigned _)) by apply Properties.word.unsigned_range;
                             rewrite Properties.word.unsigned_of_Z_nowrap; [ reflexivity | apply Z.mod_pos_bound; lia ] .. ];
                           []
                      | [ H : context[word.add ?x (word.of_Z (8 * Z.of_nat 0))] |- _ ]
                        => replace (word.add x (word.of_Z (8 * Z.of_nat 0))) with x in * |- by ZnWords
                      end
                    | rewrite <- !Z.land_ones in * |-  by (clear; lia)
                    | break_innermost_match_hyps_step ].
  all: let v := lazymatch (eval cbv delta [outputaddrv] in outputaddrv) with
                | inl _ => open_constr:(inl _)
                | inr _ => open_constr:(inr _)
                end in
       eexists (_ :: output_vals_words), (v :: vals);
       subst outputaddrv.
  all: cbn [List.length List.combine fold_right List.map List.flat_map eval_idx_or_list_idx R_scalar_or_array R_mem] in *.
  all: rewrite !Forall2_cons_cons_iff.
  all: rewrite Forall_cons_iff.
  all: cbv [eval_idx_or_list_idx] in *.
  all: repeat first [ match goal with
                      | [ |- ?G ]
                        => tryif has_evar G then fail else solve [ cbv [eval_idx_Z] in *; eauto ]
                      end
                    | (idtac + rewrite -> !and_assoc + rewrite <- !and_assoc);
                      progress repeat match goal with
                                      | [ |- ?A /\ ?B ] => tryif (has_evar A; has_evar B) then fail else split
                                      | [ |- context[?A /\ ?B] ]
                                        => has_evar A; tryif has_evar B then fail else rewrite (and_comm A B)
                                      end
                    | match goal with
                      | [ |- context[?x = ?y] ] => first [ is_evar x | is_evar y ]; progress unify x y
                      | [ H : ?v = Some ?x |- context[exists y, ?v = Some y /\ @?P y ] ]
                        => rewrite <- (ex_intro _ x : Basics.impl _ (exists y, v = Some y /\ P y))
                      | [ H : array cell64 _ ?base ?len ?ma |- context[exists mp mq, map.split ?m mp mq /\ array cell64 _ ?base' ?len' mp /\ _] ]
                        => unify base base'; unify len len';
                           rewrite <- (ex_intro (fun mp => exists mq, map.split m mp mq /\ array cell64 _ base' len' mp /\ _) ma : Basics.impl _ _)
                      | [ H : map.split ?m ?mp ?mqv |- context[exists mq, map.split ?m ?mp mq /\ _ /\ _] ]
                        => rewrite <- (ex_intro (fun mq => map.split m mp mq /\ _ /\ _) mqv : Basics.impl _ _)
                      | [ |- context[?x = word.unsigned ?ev] ]
                        => lazymatch x with
                           | Z.land ?x (Z.ones ?n) => idtac
                           end;
                           is_evar ev;
                           let __unif := open_constr:(eq_refl : ev = word.of_Z x) in
                           rewrite Properties.word.unsigned_of_Z_nowrap
                             by (rewrite Z.land_ones by (clear; lia); apply Z.mod_pos_bound; clear; lia)
                      | [ H : eval_idx_Z _ _ ?i ?x |- context[eval_idx_Z _ _ ?i (word.unsigned ?ev)] ]
                        => is_evar ev;
                           let __unif := open_constr:(eq_refl : ev = word.of_Z x) in
                           rewrite Properties.word.unsigned_of_Z_nowrap by lia
                      | [ H : eval_idx_Z _ _ ?i ?x |- context[eval_idx_Z _ _ ?i ?y] ]
                        => has_evar y; progress unify x y
                      end ].
  all: lazymatch goal with |- ?G => tryif has_evar G then fail 0 G "has evar" else idtac end.
  all: repeat first [ match goal with
                      | [ |- exists mp mq, map.split ?m mp mq /\ emp _ mp /\ _ ]
                        => exists map.empty, m
                      | [ |- context[map.split _ map.empty _] ]
                        => rewrite Properties.map.split_empty_l
                      | [ |- context[map.split _ _ map.empty] ]
                        => rewrite Properties.map.split_empty_r
                      | [ H : Forall2 _ (firstn ?n ?ls) ?y |- Forall2 _ ?ls ?y ]
                        => saturate_lengths;
                           rewrite firstn_all in H by congruence
                      end
                    | solve [ cbv [emp]; auto ]
                    | rewrite !Z.land_ones by (clear; lia)
                    | rewrite Properties.word.unsigned_of_Z_nowrap by (apply Z.mod_pos_bound; clear; lia) ].
Qed.
(* turn off once proof is finished *)
Local Ltac debug_run tac := tac ().

Theorem symex_asm_func_M_correct
        {output_scalars_are_pointers:bool}
        d frame asm_args_out asm_args_in (G : symbol -> option Z) (s := init_symbolic_state d)
        (s' : symbolic_state) (m : machine_state) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (H : symex_asm_func_M (dereference_output_scalars:=output_scalars_are_pointers) callee_saved_registers output_types stack_size inputs reg_available asm s = Success (Success rets, s'))
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (*(Hasm_reg : get_asm_reg m reg_available = runtime_reg)*)
        (runtime_callee_saved_registers : list Z)
        (*(Hasm_callee_saved_registers : get_asm_reg m callee_saved_registers = runtime_callee_saved_registers)*)
        (HR : R_runtime_input (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (Hd_ok : gensym_dag_ok G d)
        (d' := s'.(dag_state))
        (H_enough_reg : (List.length output_types + List.length runtime_inputs <= List.length reg_available)%nat)
        (Hcallee_saved_reg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) callee_saved_registers)
        (Hreg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : exists m' G'
           (runtime_rets : list (Z + list Z)),
    (DenoteLines m asm = Some m'
     /\ R_runtime_output (output_scalars_are_pointers:=output_scalars_are_pointers) frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
     /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  pose proof (word_args_to_Z_args_bounded word_runtime_inputs).
  pose proof get_asm_reg_bounded.
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
  move Heqp at bottom.
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
                      move H at bottom; eapply build_inputs_ok_R in H;
                      [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "build_inputs end")
                 | [ H : build_merge_base_addresses _ ?reg_available _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_base_addresses start");
                      move H at bottom;
                      let runtime_regv := lazymatch reg_available with
                                          | firstn ?n _ => constr:(firstn n runtime_reg)
                                          | skipn ?n _ => constr:(skipn n runtime_reg)
                                          | _ => runtime_reg
                                          end in
                      eapply @build_merge_base_addresses_ok_R
                        with (runtime_reg := runtime_regv (*get_asm_reg m reg_available*))
                        in H;
                      [
                      | try solve [ eassumption | subst; eauto using Forall_skipn, Forall_firstn with nocore ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- (_ <= _)%nat ] => saturate_lengths; try lia
                        | [ |- ?G ]
                          => first [ has_evar G
                                   | try solve
                                         [ repeat
                                             first [ reflexivity
                                                   | progress subst
                                                   | progress cbv [get_asm_reg]
                                                   | rewrite skipn_map
                                                   | rewrite firstn_map ] ] ]
                        end .. ];
                      [
                      | try solve [ eapply Forall2_weaken; [ | eassumption ]; now eauto using lift_eval_idx_or_list_idx_impl ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- Lift1Prop.iff1 ?P ?Q ]
                          => match P with
                             | context[R_list_scalar_or_array ?p ?v]
                               => match Q with
                                  | context[R_list_scalar_or_array ?p' ?v']
                                    => tryif (is_evar p'; is_evar v')
                                      then fail
                                      else (unify p p'; unify v v')
                                  end
                             end;
                             SeparationLogic.cancel
                        | [ |- Forall2 _ _ _ ]
                          => saturate_lengths;
                             adjust_Foralls_firstn_skipn;
                             try solve [ Foralls_to_nth_error; eauto using lift_eval_idx_Z_impl ]
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- List.map word.unsigned _ = _ ]
                          => saturate_lengths;
                             adjust_Foralls_firstn_skipn;
                             try rewrite ListUtil.List.firstn_firstn, Min.min_idempotent;
                             try eassumption
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_base_addresses end")
                 | [ H : build_merge_stack_placeholders _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders start");
                      subst stack_size;
                      eapply build_merge_stack_placeholders_ok_R in H;
                      [ | try eassumption; auto .. ];
                      [
                      | lazymatch goal with
                        | [ |- Lift1Prop.iff1 _ _ ] => set_evars; SeparationLogic.cancel
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders end")
                 | [ H : mapM _ callee_saved_registers _ = _ |- @ex ?T _ ]
                   => lazymatch T with
                      | (*runtime_rets*) list (Z + list Z) => idtac
                      | (*m'*) machine_state => idtac
                      end;
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers start");
                      eapply mapM_GetReg_ok_R in H;
                      [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers end")
                 | [ H : SymexLines _ _ = Success _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "SymexLines start");
                      let H' := fresh in
                      eapply SymexLines_ok_R in H;
                      [ destruct H as [m' H];
                        exists m';
                        unshelve eexists;
                        lazymatch goal with
                        | [ |- symbol -> option Z ]
                          => repeat match goal with
                                    | [ H : ?T |- _ ]
                                      => lazymatch T with
                                         | symbol -> option Z => fail
                                         | _ => clear H
                                         end
                                    end;
                             shelve
                        | _ => idtac
                        end
                      | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "SymexLines end")
                 | [ H : LoadArray _ _ _ = Success _ |- _ ]
                   => debug_run ltac:(fun _ => idtac "LoadArray start");
                      eapply LoadArray_ok_R in H;
                      [ | eauto using lift_eval_idx_Z_impl .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadArray end")
                 | [ H : LoadOutputs _ _ _ = Success _ |- _ ]
                   => debug_run ltac:(fun _ => idtac "LoadOutputs start");
                      eapply LoadOutputs_ok_R in H;
                      [ | try eassumption .. ];
                      [
                      | try solve [ eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *;
                                    break_innermost_match; cbv [eval_idx_Z] in *; eauto 10
                                  | lazymatch goal with
                                    | [ |- Forall _ ?ls ]
                                      => rewrite Forall_forall_iff_nth_error in Hreg_wide_enough;
                                         cbv [get_asm_reg] in *;
                                         cbv [val_or_list_val_matches_spec] in *;
                                         subst;
                                         Foralls_to_nth_error;
                                         cbv [index_and_shift_and_bitcount_of_reg] in *; inversion_pair; subst;
                                         eauto
                                    end ] .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadOutputs end")
                 end ].
  all: [ > ].
  lazymatch reverse goal with
  | [ H : ?x = Success ?y |- _ ]
    => let T := type of H in
       fail 0 "A non-processed step remains:" T
  | _ => idtac
  end.
  all: destruct_head' symbolic_state; cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *; subst.
  all: cbv [R update_dag_with R_runtime_output_mem] in *; destruct_head'_and.
  all: destruct_head' machine_state; cbn [Semantics.machine_reg_state Semantics.machine_flag_state Semantics.machine_mem_state] in *.
  all: cbn [R_mem] in *.
  eexists.
  all: repeat first [ assumption
                    | match goal with
                      | [ |- _ /\ _ ] => split
                      | [ |- ex _ ] => eexists
                      end ].
  all: lazymatch goal with
       | [ |- gensym_dag_ok _ _ ] => eassumption
       | [ |- forall x y, eval _ _ _ _ -> eval _ _ _ _ ] => solve [ eauto 100 ]
       | [ |- Forall2 (eval_idx_or_list_idx _ _) _ _ ]
         => eapply Forall2_weaken; [ | eassumption ];
            eapply lift_eval_idx_or_list_idx_impl; eauto 100
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- sep _ _ ?m ]
         => let H := lazymatch goal with H : sep _ _ m |- _ => H end in
            set_evars;
            revert H; generalize m;
            refine (_ : Lift1Prop.impl1 _ _);
            subst_evars;
            lazymatch goal with
            | [ |- Lift1Prop.impl1 ?P ?Q ]
              => cut (Lift1Prop.iff1 P Q); [ intros ->; reflexivity | ]
            end;
            repeat first [ progress (SeparationLogic.cancel; cbn [seps])
                         | match goal with
                           | [ |- Lift1Prop.iff1 ?P ?Q ]
                             => match P with
                                | context[array ?c ?s ?base ?v]
                                  => match Q with
                                     | context[array c s base ?v']
                                       => assert_fails (constr_eq v v');
                                          cut (v' = v); [ intros -> | ]
                                     end
                                | context[R_list_scalar_or_array ?x ?v]
                                  => match Q with
                                     | context[R_list_scalar_or_array x ?v']
                                       => assert_fails (constr_eq v v');
                                          cut (v' = v); [ intros -> | ]
                                     end
                                end
                           | [ |- Lift1Prop.iff1 (R_list_scalar_or_array ?x ?v) (R_list_scalar_or_array ?x' ?v') ]
                             => unify x x';
                                cut (v' = v); [ intros -> | ]
                           end ]
       | _ => idtac
       end.
  all: let G := match goal with |- ?G => G end in
       tryif has_evar G
       then idtac
       else (try assumption;
             lazymatch goal with
             | [ |- List.length _ = List.length _ ]
               => saturate_lengths; congruence
             | [ |- ?x = ?x ] => reflexivity
             | _ => idtac
             end).
  all: lazymatch goal with
       | [ |- Forall2 val_or_list_val_matches_spec _ _ ]
         => cbv [eval_idx_or_list_idx val_or_list_val_matches_spec type_spec_of_runtime] in *;
            rewrite ?@Forall2_map_l_iff, ?@Forall2_map_r_iff in *;
            saturate_lengths;
            Foralls_to_nth_error;
            intros; saturate_lengths;
            try congruence;
            try match goal with
                | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
                  => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
                end
       | _ => idtac
       end.
  all: [ > | ].
  all: lazymatch goal with
       | [ |- List.map fst (filter _ (List.combine _ _)) = List.map fst (filter _ (List.combine _ _)) ]
         => idtac
       end.
  all: rewrite <- Forall2_eq, !Forall2_map_l_iff, !Forall2_map_r_iff.
  all: apply List.Forall2_filter_same.
  all: pose proof Hreg_wide_enough as Hreg_wide_enough'.
  all: rewrite Forall_forall_iff_nth_error in Hreg_wide_enough;
    cbv [get_asm_reg val_or_list_val_matches_spec] in *;
    rewrite <- !@Forall2_eq, ?@Forall2_map_l_iff, ?@Forall2_map_r_iff in *;
    saturate_lengths;
    Foralls_to_nth_error.
  all: cbn [fst].
  all: repeat (rewrite ?Bool.orb_true_l, ?Bool.orb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r in *; subst).
  all: try discriminate.
  all: try reflexivity.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: try specialize (Hreg_wide_enough _ _ ltac:(eassumption)).
  all: intros; saturate_lengths.
  all: try specialize (Hreg_wide_enough _ _ ltac:(eassumption)).
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: repeat match goal with
              | [ H : ?x = Some _, H' : ?x = None |- _ ]
                => rewrite H in H'; inversion_option
              | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
                => rewrite H in H'; inversion_option
              end.
  all: repeat match goal with
              | [ H : nth_error ?ls (?a + ?b) = _, H' : nth_error ?ls (?a' + ?b) = _ |- _ ]
                => replace a' with a in * by congruence;
                   rewrite H in H'
              end.
  all: inversion_option; subst.
  all: cbv [Option.is_Some] in *; break_innermost_match_hyps; inversion_option; inversion_sum.
  all: subst.
  all: try discriminate.
  all: lazymatch goal with
       | [ H : nth_error ?ls ?i = Some (Some _), H' : nth_error ?ls' ?i = Some (inl _) |- False ]
         => revert H H'
       | [ H : nth_error ?ls ?i = Some None, H' : nth_error ?ls' ?i = Some (inr _) |- False ]
         => revert H H'
       | [ H : nth_error _ _ = Some ?r, H' : nth_error _ _ = Some ?r0 |- ?r = ?r0 ]
         => apply Properties.word.unsigned_inj; revert H H'
       end.
  all: repeat match goal with
              | [ H : Forall2 _ ?x _ |- context[nth_error ?x _] ] => revert H
              | [ H : Forall2 _ _ (List.combine ?lsa ?lsb) |- context[nth_error ?ls] ]
                => first [ find_list_in ls lsa | find_list_in ls lsb ]; revert H
              end.
  all: revert dependent rets; intro.
  all: reverted_Foralls_to_nth_error;
    intros *; Foralls_to_nth_error_rewrites; Foralls_to_nth_error_destructs;
    Foralls_to_nth_error_cleanup.
  all: intros; saturate_lengths.
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: try congruence.
  all: repeat match goal with
              | [ H : context[nth_error (List.combine _ _)] |- _ ]
                => lazymatch type of H with
                   | forall i : nat, @?P i
                     => let T := open_constr:(forall i : nat, _) in
                        cut T;
                        [ clear H
                        | let i := fresh "i" in
                          intro i; specialize (H i);
                          set_evars; revert H; Foralls_to_nth_error_rewrites;
                          intro H; subst_evars; exact H ]
                   end
              end.
  all: Foralls_to_nth_error.
  all: intros; saturate_lengths.
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: rewrite ?(fun x y => Z.land_ones (Semantics.get_reg x y)) in * by (clear; lia).
  all: rewrite ?(fun x y => Z.mod_small (Semantics.get_reg x y)) in * by now apply get_reg_bounded.
  all: split_iff.
  all: repeat match goal with
              | [ H : forall v, (0 <= v < _)%Z -> eval_idx_Z _ _ ?a v -> _, H' : eval_idx_Z _ _ ?a ?v' |- _ ]
                => specialize (fun H1 H2 => H v' (conj H1 H2))
              end.
  all: specialize_by_assumption.
  all: specialize_by (cbv [eval_idx_Z] in *; eauto).
  all: specialize_by apply get_reg_bounded.
  all: specialize_by_assumption.
  all: handle_eval_eval.
  all: subst.
  all: try congruence.
  all: destruct_head'_ex.
  all: destruct_head'_and.
  all: handle_eval_eval.
  all: subst.
  all: try match goal with
           | [ H : Symbolic.get_reg _ _ = Some _ |- _ ]
             => eapply get_reg_of_R_regs in H; [ | eassumption .. ]
           end.
  all: lazymatch goal with
       | [ H : nth_error ?ls _ = Some (inl (inl ?r)), H' : Symbolic.get_reg _ (reg_index ?r) = _ |- _ ]
         => repeat match goal with
                   | [ H : Forall2 _ ls _ |- _ ]
                     => revert H
                   end
       | _ => idtac
       end.
  all: Foralls_to_nth_error.
  all: handle_eval_eval.
  all: repeat match goal with
              | [ H : eval_idx_Z ?G ?d ?e ?v, H' : forall a b, eval ?G ?d a b -> eval ?G' ?d' a b |- _ ]
                => apply H' in H; change (eval_idx_Z G' d' e v) in H
              end.
  all: handle_eval_eval.
  all: subst.
  all: try congruence.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: lazymatch goal with
       | [ H : eval_idx_Z _ _ ?i ?v, H' : nth_error _ _ = Some (inl ?i), H'' : nth_error _ _ = Some (inl (inr ?i)) |- ?v = _ ]
         => revert H' H''
       | [ H : eval_idx_Z _ _ ?i ?v, H' : nth_error ?ls _ = Some (inl ?i) |- ?v = _ ]
         => revert H'
       | [ H : nth_error _ _ = Some ?r |- word.unsigned ?r = _ ]
         => revert H
       end.
  all: repeat match goal with
              | [ H : Forall2 _ ?lsa ?lsb |- context[nth_error ?ls] ]
                => first [ find_list_in ls lsa | find_list_in ls lsb ];
                   revert H
              end.
  all: Foralls_to_nth_error.
  all: intros.
  all: cbv [eval_idx_or_list_idx] in *.
  all: rewrite ?(fun x y => Z.land_ones (Semantics.get_reg x y)) in * by (clear; lia).
  all: rewrite ?(fun x y => Z.mod_small (Semantics.get_reg x y)) in * by now apply get_reg_bounded.
  all: split_iff.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: repeat first [ match goal with
                      | [ H : forall v, (0 <= v < _)%Z -> eval_idx_Z _ _ ?a v -> _, H' : eval_idx_Z _ _ ?a ?v' |- _ ]
                        => specialize (fun H1 H2 => H v' (conj H1 H2))
                      | [ H : ?x = Some _, H' : ?x = None |- _ ]
                        => rewrite H in H'; inversion_option
                      | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
                        => rewrite H in H'; inversion_option
                      | [ H : Symbolic.get_reg _ _ = Some _ |- _ ]
                        => eapply get_reg_of_R_regs in H; [ | eassumption .. ]
                      end
                    | progress subst
                    | progress inversion_sum
                    | congruence
                    | progress specialize_by_assumption
                    | progress specialize_by (cbv [eval_idx_Z] in *; eauto)
                    | progress specialize_by apply get_reg_bounded
                    | progress handle_eval_eval ].
  all: repeat match goal with
              | [ H : eval_idx_Z ?G ?d ?e ?v, H' : forall a b, eval ?G ?d a b -> eval ?G' ?d' a b |- _ ]
                => apply H' in H; change (eval_idx_Z G' d' e v) in H
              end.
  all: handle_eval_eval.
  all: try congruence.
Time Qed. (* Finished transaction in 14.751 secs (14.751u,0.s) *)

Theorem symex_asm_func_correct
        {output_scalars_are_pointers:bool}
        frame asm_args_out asm_args_in (G : symbol -> option Z) (d : dag) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (s' : symbolic_state)
        (H : symex_asm_func (dereference_output_scalars:=output_scalars_are_pointers) d callee_saved_registers output_types stack_size inputs reg_available asm = Success (rets, s'))
        (d' := s'.(dag_state))
        (m : machine_state)
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (runtime_callee_saved_registers : list Z)
        (Hasm_reg : get_asm_reg m reg_available = runtime_reg)
        (HR : R_runtime_input (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (HG_ok : gensym_dag_ok G d)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : (exists m' G'
            (runtime_rets : list (Z + list Z)),
        DenoteLines m asm = Some m'
        /\ R_runtime_output (output_scalars_are_pointers:=output_scalars_are_pointers) frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
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
        (output_scalars_are_pointers:=false)
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (frame : Semantics.mem_state -> Prop)
        (asm : list (String.string (* fname *) * Lines))
        (expr : API.Expr t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (Hwf : API.Wf expr)
        (H : check_equivalence asm expr arg_bounds out_bounds = Success tt)
        (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
        (word_args : list (Naive.word 64 + list (Naive.word 64)))
        (args := word_args_to_Z_args word_args)
        (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
        (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
        (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
        (st : machine_state)
        (asm_args_out asm_args_in : list (Naive.word 64))
        (runtime_regs := get_asm_reg st assembly_calling_registers)
        (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers)
  : Forall
      (fun '(_fname, asm)
       => forall
           (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
           (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
           (HR : R_runtime_input (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st),
         exists asm' st' (retvals : list (Z + list Z)),
           strip_ret asm = Success asm'
           /\ DenoteLines st asm' = Some st'
           /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
           /\ R_runtime_output (output_scalars_are_pointers:=output_scalars_are_pointers) frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st')
      asm.
Proof.
  cbv beta delta [check_equivalence ErrorT.bind] in H.
  repeat
    first [ rewrite List.ErrorT.List.bind_list_cps_id, <- List.ErrorT.List.eq_bind_list_lift in H;
            cbv beta delta [ErrorT.bind] in H
          | match type of H with
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
            end ]; try discriminate; [].
  cbv beta delta [map_error ErrorT.map2 id] in *.
  break_innermost_match_hyps; inversion_ErrorT; subst.
  rewrite @List.ErrorT.List.lift_Success_Forall2_iff in *.
  progress rewrite ?@Forall2_map_l_iff, ?@Forall2_map_r_iff in *.
  Foralls_to_nth_error.
  intros; inversion_ErrorT; subst.
  progress reflect_hyps.
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
        (output_scalars_are_pointers:=false)
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (asm : list (String.string (* fname *) * Lines))
        (expr : API.Expr t)
        (f : type.interp _ t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (asm_out : list (String.string (* fname *) * Lines))
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
              (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers),
             Forall
         (fun '(_fname, asm)
          => forall (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
                    (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
                    (HR : R_runtime_input (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st),
            (* Should match check_equivalence_correct exactly *)
            exists asm' st' (retvals : list (Z + list Z)),
              strip_ret asm = Success asm'
              /\ DenoteLines st asm' = Some st'
              /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
              /\ R_runtime_output (output_scalars_are_pointers:=output_scalars_are_pointers) frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st')
         asm.
Proof.
  cbv [generate_assembly_of_hinted_expr] in H.
  break_innermost_match_hyps; inversion H; subst; destruct_head'_and; split; [ reflexivity | intros ].
  eapply check_equivalence_correct; eassumption.
Qed.

(* Some theorems about the result of calling generate_assembly_of_hinted_expr_correct on various Pipeline functions *)
