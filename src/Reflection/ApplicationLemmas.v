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

  Lemma fst_interp_all_binders_for_of' {A B}
        (args : interp_all_binders_for' (Arrow A B) interp_base_type)
    : fst_binder (interp_all_binders_for_of' args) = fst args.
  Proof.
    destruct B; reflexivity.
  Qed.

  Lemma snd_interp_all_binders_for_of' {A B}
        (args : interp_all_binders_for' (Arrow A B) interp_base_type)
    : snd_binder (interp_all_binders_for_of' args) = interp_all_binders_for_of' (snd args).
  Proof.
    destruct B.
    { edestruct interp_all_binders_for_of'; reflexivity. }
    { destruct args; reflexivity. }
  Qed.

  Lemma fst_interp_all_binders_for_to' {A B}
        (args : interp_all_binders_for (Arrow A B) interp_base_type)
    : fst (interp_all_binders_for_to' args) = fst_binder args.
  Proof.
    destruct B; reflexivity.
  Qed.

  Lemma snd_interp_all_binders_for_to' {A B}
        (args : interp_all_binders_for (Arrow A B) interp_base_type)
    : snd (interp_all_binders_for_to' args) = interp_all_binders_for_to' (snd_binder args).
  Proof.
    destruct B; reflexivity.
  Qed.

  Lemma interp_all_binders_for_to'_of' {t} (args : interp_all_binders_for' t interp_base_type)
    : interp_all_binders_for_to' (interp_all_binders_for_of' args) = args.
  Proof.
    induction t; destruct args; [ reflexivity | ].
    apply injective_projections;
      [ rewrite fst_interp_all_binders_for_to', fst_interp_all_binders_for_of'; reflexivity
      | rewrite snd_interp_all_binders_for_to', snd_interp_all_binders_for_of', IHt; reflexivity ].
  Qed.

  Lemma interp_all_binders_for_of'_to' {t} (args : interp_all_binders_for t interp_base_type)
    : interp_all_binders_for_of' (interp_all_binders_for_to' args) = args.
  Proof.
    induction t as [|A B IHt].
    { destruct args; reflexivity. }
    { destruct B; [ reflexivity | ].
      destruct args; simpl; rewrite IHt; reflexivity. }
  Qed.

  Lemma interp_apply_all' {t}
        (x : @expr base_type interp_base_type op _ t)
        (args : interp_all_binders_for' t interp_base_type)
    : interp interp_op (ApplyAll x (interp_all_binders_for_of' args)) = ApplyInterpedAll' (interp interp_op x) args.
  Proof.
    induction x as [|?? x IHx]; [ reflexivity | ].
    simpl; rewrite <- IHx; destruct args.
    rewrite snd_interp_all_binders_for_of', fst_interp_all_binders_for_of'; reflexivity.
  Qed.

  Lemma interp_apply_all {t}
        (x : @expr base_type interp_base_type op _ t)
        (args : interp_all_binders_for t interp_base_type)
    : interp interp_op (ApplyAll x args) = ApplyInterpedAll (interp interp_op x) args.
  Proof.
    unfold ApplyInterpedAll.
    rewrite <- interp_apply_all', interp_all_binders_for_of'_to'; reflexivity.
  Qed.

  Lemma interp_apply_all_to' {t}
         (x : @expr base_type interp_base_type op _ t)
         (args : interp_all_binders_for t interp_base_type)
    : interp interp_op (ApplyAll x args) = ApplyInterpedAll' (interp interp_op x) (interp_all_binders_for_to' args).
   Proof.
    rewrite <- interp_apply_all', interp_all_binders_for_of'_to'; reflexivity.
   Qed.
End language.
