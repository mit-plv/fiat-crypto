Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.Util.ZUtil.

Local Arguments Z.mul !_ !_.
Local Opaque tuple_decoder.
Local Coercion Z.of_nat : nat >-> Z.
Local Open Scope Z_scope.

Fixpoint project_repeated_tuple {W base exp} : repeated_tuple W base exp -> match base, exp with
                                                                            | S _, _ => W
                                                                            | O, O => W
                                                                            | O, S _ => unit
                                                                            end
  := match exp, base
           return repeated_tuple W base exp -> match base, exp with
                                               | S _, _ => W
                                               | O, O => W
                                               | O, S _ => unit
                                               end
     with
     | O, O
     | O, S _
       => fun x => x
     | S exp', S O => @project_repeated_tuple W (S O) exp'
     | S exp', S (S base') => fun x => @project_repeated_tuple W (S (S base')) exp' (snd x)
     | S _, O => fun _ => tt
     end.

Lemma mul_1_l_decode {W} (P : forall n, decoder n W -> Prop)
      {n} (decode : decoder n W)
  : P n decode -> P (1 * n) {| Interface.decode := @Interface.decode n W decode |}.
Proof.
  pose proof (Z.mul_1_l n).
  set (n' := 1 * n) in *; clearbody n'.
  induction H.
  destruct decode.
  exact (fun x => x).
Qed.

Section decode.
  Context {n W}
          {decode : decoder n W}
          {isdecode : is_decode decode}
          {base : nat}.

  Fixpoint is_repeated_tuple_decode {exp : nat}
    : is_decode (@repeated_tuple_decoder n W decode base exp).
  Proof.
    refine match exp return is_decode (repeated_tuple_decoder (exp:=exp)) with
           | O => fun x => _
           | S exp' => fun x => _
           end.
    { clear is_repeated_tuple_decode.
      simpl; rewrite Z.mul_1_l; apply isdecode. }
    { specialize (is_repeated_tuple_decode exp').
      change (base^S exp') with (base^(1 + exp')%nat) at 3.
      rewrite (Nat2Z.inj_add 1 exp'), Z.pow_add_r, Z.pow_1_r by omega.
      simpl.
      destruct base as [|[| base' ]]; autorewrite with simpl_tuple_decoder.
      { simpl; omega. }
      { apply is_repeated_tuple_decode. }
      { assert (0 <= n) by exact (decode_exponent_nonnegative _ (project_repeated_tuple x)).
        assert (0 <= S (S base') ^ exp' * n) by zero_bounds.
        assert (0 <= (S base' * (S (S base') ^ exp' * n))) by zero_bounds.
        rewrite <- Z.mul_assoc.
        change (2 ^ (S (S base') * (S (S base') ^ exp' * n)))
        with (2 ^ (((1 + S base')%nat) * (S (S base') ^ exp' * n))).
        rewrite (Nat2Z.inj_add 1 (S base')), Z.mul_add_distr_r, Z.mul_1_l, Z.pow_add_r by omega.
        autorewrite with simpl_tuple_decoder Zshift_to_pow; generalize_decode; nia. } }
  Qed.
  Global Existing Instance is_repeated_tuple_decode.
End decode.

Ltac is_cls_fixpoint_t_gen decode n exp generalize_is_clsv IH :=
  let exp' := fresh exp in
  destruct exp as [|exp'];
  [ clear IH;
    destruct decode; generalize_is_clsv ();
    simpl;
    change (Z.of_nat 2 ^ Z.of_nat 0) with 1;
    generalize (Z.mul_1_l n); generalize (1 * n);
    intro; clear; induction 1;
    intros; repeat apply pair; try assumption
  | specialize (IH exp'); revert IH;
    repeat match goal with
           | [ |- (_ * _)%type -> _ ]
             => let x := fresh in
                let y := fresh in
                intros [x y]; revert x y
           | [ |- _ -> _ ]
             => intro
           end;
    simpl @repeated_tuple_decoder; simpl;
    change (Z.of_nat (S exp')) with (Z.of_nat (1 + exp'));
    rewrite (Nat2Z.inj_add 1 exp'), Z.pow_add_r, Z.pow_1_r, <- !Z.mul_assoc, <- decoder_eta by omega;
    repeat apply pair;
    try exact _ ].

Ltac is_cls_fixpoint_t decode n exp is_clsv IH :=
  is_cls_fixpoint_t_gen decode n exp ltac:(fun _ => generalize is_clsv) IH.

Ltac is_cls_fixpoint_t2 decode n exp is_clsv1 is_clsv2 IH :=
  is_cls_fixpoint_t_gen decode n exp ltac:(fun _ => generalize is_clsv1, is_clsv2) IH.

Ltac is_cls_fixpoint_t3 decode n exp is_clsv1 is_clsv2 is_clsv3 IH :=
  is_cls_fixpoint_t_gen decode n exp ltac:(fun _ => generalize is_clsv1, is_clsv2, is_clsv3) IH.

Ltac is_cls_fixpoint_t4 decode n exp is_clsv1 is_clsv2 is_clsv3 is_clsv4 IH :=
  is_cls_fixpoint_t_gen decode n exp ltac:(fun _ => generalize is_clsv1, is_clsv2, is_clsv3, is_clsv4) IH.
