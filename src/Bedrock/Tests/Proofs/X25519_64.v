Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String. (* should go before lists *)
Require Import Coq.Lists.List.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Array.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Tactics.BreakMatch.
Require bedrock2.Map.SeparationLogic. (* if imported, list firstn/skipn get overwritten and it's annoying *)
Local Open Scope Z_scope.

Import Language.Compilers.
Import Associational Positional.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Crypto.Bedrock.Tests.X25519_64.
Import X25519_64.
Local Coercion name_of_func (f : bedrock_func) := fst f.

Section Proofs.
  Context (n : nat := 5%nat)
          (s : Z := 2^255)
          (c : list (Z * Z) := [(1,19)])
          (machine_wordsize : Z := 64).

  (* requires some kind of proof about decimal stringification *)
  Lemma decimal_varname_gen_unique :
    forall i j : nat, varname_gen i = varname_gen j <-> i = j.
  Admitted.

  Instance p_ok : Types.ok.
  Proof.
    constructor.
    { exact BasicC64Semantics.parameters_ok. }
    { reflexivity. }
    { exact decimal_varname_gen_unique. }
  Defined.

  Local Notation M := (s - Associational.eval c)%Z.
  Local Notation eval :=
    (eval (weight limbwidth_num limbwidth_den) n).

  Definition Bignum (addr : Semantics.word) (x : Z) :
    Semantics.mem -> Prop :=
    Lift1Prop.ex1
      (fun xs =>
         sep (emp (eval (map word.unsigned xs) = x))
             (sep (emp (length xs = n))
                  (array scalar (word.of_Z word_size_in_bytes)
                         addr xs))).

  Instance spec_of_mulmod_bedrock : spec_of mulmod_bedrock :=
    fun functions =>
      forall x y px py pout old_out t m
             (Ra Rr : Semantics.mem -> Prop),
        sep (sep (Bignum px x) (Bignum py y)) Ra m ->
        sep (Bignum pout old_out) Rr m ->
        WeakestPrecondition.call
          (p:=@semantics default_parameters)
          functions mulmod_bedrock t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             sep (Bignum pout ((x * y) mod M)%Z) Rr m').

  Lemma mulmod_valid_func :
    valid_func (mulmod (fun H3 : API.type => unit)).
  Proof.
    apply valid_func_bool_iff.
    vm_compute; reflexivity.
  Qed.

  (* TODO: ask Jason for help *)
  Lemma mulmod_Wf :
    Wf.Compilers.expr.Wf3 mulmod.
  Admitted.

  Lemma mulmod_length (x y : API.interp_type type_listZ) :
    length
      (expr.interp (@Compilers.ident_interp)
                   (mulmod API.interp_type)
                   x y) = n.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (* TODO: here's where we need to use the FC pipeline to say things about
         correctness *)
  (* this can be changed to use type.app_curried if that's easier *)
  Lemma mulmod_correct x y :
    eval
      (map word.wrap
           (expr.interp
              (@Compilers.ident_interp) (mulmod API.interp_type)
              (map word.unsigned x) (map word.unsigned y))) =
    ((eval (map word.unsigned x) * eval (map word.unsigned y)) mod M)%Z.
  Admitted.

  (* TODO : move *)
  Lemma substring_0_0 :
    forall s, substring 0 0 s = "".
  Proof.
    clear. destruct s; reflexivity.
  Qed.

  Lemma varname_gen_startswith v i :
    v = varname_gen i ->
    String.startswith "x" v = true.
  Proof.
    cbn [varname_gen default_parameters]. intro.
    subst. cbn. rewrite substring_0_0.
    reflexivity.
  Qed.

  (* TODO : move *)
  Lemma map_of_Z_unsigned x :
    map word.of_Z (map word.unsigned x) = x.
  Proof.
    rewrite map_map.
    rewrite map_ext with (g:=id);
      [ solve [apply map_id] | ].
    intros. rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  (* TODO : move *)
  Lemma map_unsigned_of_Z x :
    map word.unsigned (map word.of_Z x) = map word.wrap x.
  Proof.
    rewrite map_map. apply map_ext.
    exact word.unsigned_of_Z.
  Qed.

  (* TODO: move *)
  Lemma Forall_map_unsigned x :
    Forall (fun z : Z => 0 <= z < 2 ^ Semantics.width)
           (map word.unsigned x).
  Proof.
    induction x; intros; cbn [map]; constructor;
      auto using word.unsigned_range.
  Qed.

  Lemma mulmod_bedrock_correct :
    program_logic_goal_for_function! mulmod_bedrock.
  Proof.
    cbv [program_logic_goal_for spec_of_mulmod_bedrock].
    cbn [name_of_func mulmod_bedrock fst]. intros.
    cbv [mulmod_bedrock].
    intros. cbv [Bignum] in * |-. sepsimpl.
    eapply Proper_call.
    2:{
      let xs := match goal with
                  Hx : eval ?xs = x |- _ =>
                  xs end in
      let ys := match goal with
                  Hy : eval ?ys = y |- _ =>
                  ys end in
      apply translate_func_correct
        with (args:=(xs, (ys, tt)))
             (flat_args:=[px;py]%list)
             (out_ptrs:=[pout]%list)
             (Ra0:=Ra) (Rr0:=Rr).
      { apply mulmod_valid_func; eauto. }
      { apply mulmod_Wf; eauto. }
      { cbn [LoadStoreList.list_lengths_from_args
               LoadStoreList.list_lengths_from_value
               fst snd].
        rewrite !map_length.
        repeat match goal with H : length _ = n |- _ =>
                               rewrite H end.
        reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { intros.
        cbn [fst snd Types.varname_set_args Types.varname_set_base
                 Types.rep.varname_set Types.rep.listZ_mem
                 Types.rep.Z].
        cbv [PropSet.union PropSet.singleton_set PropSet.elem_of
                           PropSet.empty_set].
        destruct 1 as [? | [? | ?] ]; try tauto;
          match goal with H : _ = varname_gen _ |- _ =>
                          apply varname_gen_startswith in H;
                            vm_compute in H; congruence
          end. }
      { cbn [fst snd Types.equivalent_flat_args Types.rep.listZ_mem
                 Types.equivalent_flat_base Types.rep.equiv
                 Types.rep.Z]. sepsimpl.
        exists 1%nat. cbn [firstn skipn length hd].
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_assoc.
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_ex1_l.
        exists 1%nat. cbn [firstn skipn length hd].
        apply SeparationLogic.sep_assoc.
        sepsimpl; try reflexivity; [ ].
        eexists.
        sepsimpl;
          try match goal with
              | |- dexpr _ _ (Syntax.expr.literal _) _ => reflexivity
              | _ => apply word.unsigned_range
              end;
          eauto using Forall_map_unsigned; [ ].
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_assoc.
        apply SeparationLogic.sep_comm.
        sepsimpl; try reflexivity; [ ].
        eexists.
        sepsimpl;
          try match goal with
              | |- dexpr _ _ (Syntax.expr.literal _) _ => reflexivity
              | _ => apply word.unsigned_range
              end;
          eauto using Forall_map_unsigned; [ ].
        rewrite !map_of_Z_unsigned.
        rewrite !word.of_Z_unsigned in *.
        change BasicC64Semantics.parameters with semantics in *.
        SeparationLogic.ecancel_assumption. }
      { cbn. repeat constructor; cbn [In]; try tauto.
        destruct 1; congruence. }
      { intros.
        cbn [fst snd Types.varname_set_base type.final_codomain
                 Types.rep.varname_set Types.rep.listZ_mem
                 Types.rep.Z].
        cbv [PropSet.singleton_set PropSet.elem_of PropSet.empty_set].
        intro;
          match goal with H : _ = varname_gen _ |- _ =>
                          apply varname_gen_startswith in H;
                            vm_compute in H; congruence
          end. }
      { cbn. repeat constructor; cbn [In]; tauto. }
      { cbn. rewrite union_empty_r.
        apply disjoint_singleton_r_iff.
        cbv [PropSet.singleton_set PropSet.elem_of PropSet.union].
        destruct 1; congruence. }
      { cbn [LoadStoreList.lists_reserved_with_initial_context
               LoadStoreList.list_lengths_from_value
               LoadStoreList.extract_listnames
               LoadStoreList.lists_reserved
               Flatten.flatten_listonly_base_ltype
               Flatten.flatten_base_ltype
               Flatten.flatten_argnames List.app
               map.of_list_zip map.putmany_of_list_zip
               type.app_curried type.final_codomain fst snd].
        sepsimpl.
        (let xs := (match goal with
                      Hx : eval ?xs = old_out |- _ =>
                      xs end) in
         exists xs).
        sepsimpl;
          [ rewrite map_length, mulmod_length by assumption;
            congruence | ].
        cbn [Types.rep.equiv Types.base_rtype_of_ltype
                             Types.rep.Z Types.rep.listZ_mem].
        rewrite map_of_Z_unsigned.
        sepsimpl.
        eexists.
        sepsimpl;
          try match goal with
                | |- dexpr _ _ _ _ =>
                  apply get_put_same, word.of_Z_unsigned
                | _ => apply word.unsigned_range
              end; eauto using Forall_map_unsigned; [ ].
        rewrite word.of_Z_unsigned.
        assumption. } }

    repeat intro; cbv beta in *.
    cbn [Types.equivalent_flat_base
           Types.equivalent_listexcl_flat_base
           Types.equivalent_listonly_flat_base
           Types.rep.equiv Types.rep.listZ_mem Types.rep.Z
           type.final_codomain] in *.
    repeat match goal with
           | _ => progress subst
           | _ => progress sepsimpl_hyps
           | H : _ /\ _ |- _ => destruct H
           | |- _ /\ _ => split; [ reflexivity | ]
           end.
    sepsimpl.
    match goal with
    | H : dexpr _ _ (Syntax.expr.literal _) _ |- _ =>
      cbn [dexpr WeakestPrecondition.expr expr_body hd] in H;
        cbv [literal] in H; rewrite word.of_Z_unsigned in H;
          inversion H; clear H; subst
    end.
    cbv [Bignum].
    sepsimpl.
    eexists; sepsimpl; [ | | eassumption];
      [ | cbn [type.app_curried];
          rewrite map_length, mulmod_length; solve [eauto] ].
    cbn [type.app_curried fst snd].
    rewrite map_unsigned_of_Z.
    apply mulmod_correct; eauto.
  Qed.
  (* Print Assumptions mulmod_bedrock_correct. *)
End Proofs.
