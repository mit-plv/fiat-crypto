Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.

Section language.
  Context {base_type : Type}
          {interp_base_type : base_type -> Type}
          {op : flat_type base_type -> flat_type base_type -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.

  Lemma interp_apply' {n t}
        (x : @expr base_type interp_base_type op _ t)
        (args : binders_for' n t interp_base_type)
    : interp interp_op (Apply' n x args) = ApplyInterped' n (interp interp_op x) args.
  Proof.
    generalize dependent t; induction n as [|n IHn]; intros.
    { destruct x; reflexivity. }
    { destruct x as [|?? x]; simpl; [ reflexivity | ].
      apply IHn. }
  Qed.

  Lemma interp_apply {n t}
        (x : @expr base_type interp_base_type op _ t)
        (args : binders_for n t interp_base_type)
    : interp interp_op (Apply n x args) = ApplyInterped (interp interp_op x) args.
  Proof.
    destruct n; [ reflexivity | ].
    apply interp_apply'.
  Qed.

  Lemma interp_apply_all {t}
        (x : @expr base_type interp_base_type op _ t)
        (args : interp_all_binders_for t interp_base_type)
    : interp interp_op (ApplyAll x args) = ApplyInterpedAll (interp interp_op x) args.
  Proof.
    induction x as [|?? x IHx]; [ reflexivity | ].
    simpl; rewrite <- IHx; reflexivity.
  Qed.
End language.
