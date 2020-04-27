Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.
Import Types Types.Notations.
Existing Instances rep.Z rep.listZ_mem.

(* TODO: this is copy-pasted from Stringification; put in a common location *)
Section with_parameters.
  Context {p : Types.parameters}.

  Fixpoint make_names (prefix : string) (nextn : nat) (t : base.type)
    : nat * base_ltype t :=
    match t as t0 return nat * base_ltype t0 with
    | base.type.prod a b =>
      let resa := make_names prefix nextn a in
      let resb := make_names prefix (fst resa) b in
      (fst resb, (snd resa, snd resb))
    | base_listZ =>
      let num := Decimal.Z.to_string (Z.of_nat nextn) in
      (S nextn, String.append prefix num)
    | _ =>
      let num := Decimal.Z.to_string (Z.of_nat nextn) in
      (S nextn, String.append prefix num)
    end.
  Fixpoint make_innames' (nextn : nat) (t : API.type)
    : nat * type.for_each_lhs_of_arrow ltype t :=
    match t as t0 return
          nat * type.for_each_lhs_of_arrow ltype t0 with
    | type.base _ => (nextn, tt)
    | type.arrow (type.base s) d =>
      let ress := make_names "in" nextn s in
      let resd := make_innames' (fst ress) d in
      (fst resd, (snd ress, snd resd))
    | type.arrow _ d =>
      let resd := make_innames' nextn d in
      (fst resd, (tt, snd resd))
    end.
  Definition make_innames t : type.for_each_lhs_of_arrow ltype t :=
    snd (make_innames' 0 t).
  Definition make_outnames t : base_ltype t :=
    snd (make_names "out" 0 t).

  Fixpoint list_lengths_repeat_base (n : nat) t : base_listonly nat t :=
    match t as t0 return base_listonly nat t0 with
    | base.type.prod a b =>
      (list_lengths_repeat_base n a, list_lengths_repeat_base n b)
    | base_listZ => n
    | _ => tt
    end.
  Fixpoint list_lengths_repeat_args (n : nat) t
    : type.for_each_lhs_of_arrow list_lengths t :=
    match t as t0 return type.for_each_lhs_of_arrow list_lengths t0 with
    | type.base b => tt
    | type.arrow (type.base s) d =>
      (list_lengths_repeat_base n s, list_lengths_repeat_args n d)
    | type.arrow s d => (tt, list_lengths_repeat_args n d)
    end.
End with_parameters.

Import Language.Compilers.
Import Language.Wf.Compilers.
Import Associational Positional.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Import QArith_base.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Section __.
  Context {p : Types.parameters}
          (n : nat) (s : Z) (c : list (Z * Z)).

  Definition make_bedrock_func {t} (res : API.Expr t) :=
    fst (translate_func res (make_innames _)
                        (list_lengths_repeat_args n _)
                        (make_outnames _)).

  Definition carry_mul
             (res : API.Expr (type.arrow type_listZ
                                         (type.arrow type_listZ
                                                     type_listZ)))
    : bedrock_func :=
    ("carry_mul", make_bedrock_func res).

  Definition max_bounds : list (option ZRange.zrange) :=
    repeat (Some {|ZRange.lower:=0; ZRange.upper:=2^Semantics.width-1|}) n.

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    Local Notation M := (s - Associational.eval c)%Z.
    Local Notation wt :=
      (ModOps.weight
         (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
         (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))).
    Local Notation eval := (eval wt n).
    Local Notation loose_bounds := (UnsaturatedSolinas.loose_bounds n s c).
    Local Notation tight_bounds := (UnsaturatedSolinas.tight_bounds n s c).

    Context
      (* loose_bounds_ok could be proven in parameterized form, but is a pain
      and is easily computable with parameters plugged in. So for now, leaving
      as a precondition. *)
      (loose_bounds_ok :
         ZRange.type.option.is_tighter_than
           (t:=type_listZ) (Some loose_bounds) (Some max_bounds) = true)
      (check_args_ok :
         check_args n s c Semantics.width (ErrorT.Success tt)
         = ErrorT.Success tt).

    Definition Bignum (addr : Semantics.word) (xs : list Z) :
      Semantics.mem -> Prop :=
      array scalar (word.of_Z word_size_in_bytes)
            addr (map word.of_Z xs).

    (* TODO: move to ListUtil or somewhere else common *)
    Fixpoint partition_equal_size' {T}
             (n : nat) (xs acc : list T) (i : nat)
      : list (list T) :=
      match xs with
      | [] => [acc]
      | x :: xs' =>
        match i with
        | O => acc :: partition_equal_size' n xs' [x] (n-1)
        | S i' => partition_equal_size' n xs' (acc ++ [x])%list i'
        end
      end.
    Definition partition_equal_size {T} (n : nat) (xs : list T) :=
      partition_equal_size' n xs [] n.

    Definition eval_bytes (bs : list Byte.byte) : list Z :=
      map (fun l => LittleEndian.combine _ (HList.tuple.of_list l))
          (partition_equal_size (Z.to_nat word_size_in_bytes) bs).

    Lemma scalar_of_bytes
          a l (H : length l = Z.to_nat word_size_in_bytes) :
      Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                     (scalar a (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list l)))).
    Admitted. (* TODO *)

    Lemma Bignum_of_bytes addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1 (array ptsto (word.of_Z 1) addr bs)
                     (Bignum addr (eval_bytes bs)).
    Admitted. (* TODO *)

    (* TODO: surely there is a general lemma somewhere about this; if not, make
       one using is_tighter_than *)
    Lemma relax_to_max_bounds x :
      list_Z_bounded_by loose_bounds x ->
      list_Z_bounded_by max_bounds x.
    Admitted.

    (* helper lemma to use list_Z_bounded_by to get the format
       needed by rep.listZ_mem *)
    Lemma list_Z_bounded_by_in_range x :
      list_Z_bounded_by max_bounds x ->
      Forall (fun z : Z => 0 <= z < 2 ^ Semantics.width) x.
    Proof.
      intro.
      pose proof length_list_Z_bounded_by max_bounds x ltac:(assumption).
      cbv [list_Z_bounded_by max_bounds] in *.
      rewrite repeat_length in *.
      generalize dependent n.
      induction n; intros;
        destruct x; intros; cbn [length] in *; subst.
      (* TODO *)
    Admitted.

    Lemma eval_bytes_in_range x :
      Forall (fun z : Z => 0 <= z < 2 ^ Semantics.width) (eval_bytes bs).
    (* TODO: should Bignums be just arrays of the correct number of bytes, and
    have the value computed? *)
    Instance spec_of_carry_mul : spec_of "carry_mul" :=
      fun functions =>
        forall x y px py pout old_out t m
               (Ra Rr : Semantics.mem -> Prop),
          list_Z_bounded_by loose_bounds x ->
          list_Z_bounded_by loose_bounds y ->
          sep (sep (Bignum px x) (Bignum py y)) Ra m ->
          sep (Bignum pout old_out) Rr m ->
          WeakestPrecondition.call
            (p:=semantics)
            functions "carry_mul" t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               Lift1Prop.ex1
                 (fun out =>
                    sep
                      (sep (emp (eval out mod M = (eval x * eval y) mod M
                                 /\ list_Z_bounded_by tight_bounds out))
                             (Bignum pout out)) Rr) m').

    Lemma carry_mul_correct :
      forall carry_mul_res :
               API.Expr (type_listZ -> type_listZ -> type_listZ),
        UnsaturatedSolinas.carry_mul n s c Semantics.width
        = ErrorT.Success carry_mul_res ->
        expr.Wf3 carry_mul_res ->
        valid_func (carry_mul_res (fun _ : API.type => unit)) ->
        forall functions,
          spec_of_carry_mul
            (("carry_mul", make_bedrock_func carry_mul_res) :: functions).
    Proof.
      cbv [spec_of_carry_mul]; intros.
      cbv [make_bedrock_func].

      match goal with H : _ = ErrorT.Success _ |- _ =>
                      apply UnsaturatedSolinas.carry_mul_correct in H;
                        [ | assumption ]
      end.

      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=(x, (y, tt))) (flat_args := [px; py]) ].
      { repeat intro.
        match goal with
          H : context [sep _ _ ?m] |- context [_ ?m] =>
          cbn in H
        end.
        sepsimpl_hyps.
        ssplit; [ congruence | congruence | ].

        eexists.
        sepsimpl;
          try match goal with
              | H : context [Solinas.carry_mul_correct] |- _ =>
               apply H; eauto
              end; [ ].
        cbv [Bignum expr.Interp].
        match goal with
        | H : literal (word.unsigned _) (eq (word.of_Z _)) |- _ =>
          let H' := fresh in
          cbv [literal] in H; inversion H as [H']; clear H;
            rewrite ?word.of_Z_unsigned in H';
            rewrite <-H'
        end.
        assumption. }

      (* now we prove translate_func preconditions *)
      all: try assumption.
      all: try reflexivity.

      { (* list_lengths_repeat_args correct *)
        (* use list_Z_bounded_by *)
        cbn.
        admit. }
      { (* varname_gen doesn't collide with make_innames
           (need to think about this one -- maybe find a way of constructing
           parameters that guarantees the same varname_gen? Or some varname_gen
           that is parameterized over the prefix, and a proof that the prefix is
           not in or out? *)
        admit. }
      { (* arg pointers are correct *)
        cbn; sepsimpl.
        exists 1%nat; sepsimpl;
          cbn [firstn skipn];
          [ solve [eauto using firstn_length_le] | ].
        exists (word.unsigned px); sepsimpl.
        { (* make a general lemma to get this from list_Z_bounded_by *)
          admit. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { reflexivity. }
        exists 1%nat; sepsimpl;
          cbn [firstn skipn];
          [ solve [eauto using firstn_length_le] | ].
        exists (word.unsigned py); sepsimpl.
        { (* make a general lemma to get this from list_Z_bounded_by *)
          admit. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { reflexivity. }
        { reflexivity. }
        cbv [Bignum] in *.
        rewrite !word.of_Z_unsigned.
        ecancel_assumption. }
      { (* no duplicates in argnames *)
        cbn; repeat constructor; cbn; try tauto.
        destruct 1; congruence. }
      { (* outnames and varname_gen don't collide *)
        admit. }
      { (* no duplicates in outnames *)
        cbn; repeat constructor; cbn. tauto. }
      { (* innames and outnames are disjoint --
           probably can make a separate lemma for this *)
        admit. }
      { cbn. sepsimpl.
        exists (old_out).
        sepsimpl.
        { (* todo: length of old_out, can get length of expr.interp from carry_mul_correct *)
          admit. }
        (* todo: tactic for this pattern, used in args above as well *)
        exists (word.unsigned pout); sepsimpl.
        { (* make a general lemma to get this from list_Z_bounded_by *)
          admit. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { rewrite word.of_Z_unsigned. eexists.
          rewrite ?map.get_put_diff, map.get_put_same by congruence.
          ssplit; reflexivity. }
        { rewrite !word.of_Z_unsigned.
          cbv [Bignum] in *.
          ecancel_assumption. }
    Qed.

  End Proofs.
End __.
