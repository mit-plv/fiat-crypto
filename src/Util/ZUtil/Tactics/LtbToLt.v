Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Bool.
Local Open Scope Z_scope.

Module Z.
  Lemma eqb_cases x y : if x =? y then x = y else x <> y.
  Proof.
    pose proof (Z.eqb_spec x y) as H.
    inversion H; trivial.
  Qed.

  Lemma geb_spec0 : forall x y : Z, Bool.reflect (x >= y) (x >=? y).
  Proof.
    intros x y; pose proof (Zge_cases x y) as H; destruct (Z.geb x y); constructor; omega.
  Qed.
  Lemma gtb_spec0 : forall x y : Z, Bool.reflect (x > y) (x >? y).
  Proof.
    intros x y; pose proof (Zgt_cases x y) as H; destruct (Z.gtb x y); constructor; omega.
  Qed.

  Ltac ltb_to_lt_with_hyp H lem :=
    let H' := fresh in
    rename H into H';
    pose proof lem as H;
    rewrite H' in H;
    clear H'.

  Ltac ltb_to_lt_in_goal b' lem :=
    refine (proj1 (@reflect_iff_gen _ _ lem b') _);
    cbv beta iota.

  Ltac ltb_to_lt_hyps_step :=
    match goal with
    | [ H : (?x <? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zlt_cases x y)
    | [ H : (?x <=? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zle_cases x y)
    | [ H : (?x >? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zgt_cases x y)
    | [ H : (?x >=? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zge_cases x y)
    | [ H : (?x =? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (eqb_cases x y)
    end.
  Ltac ltb_to_lt_goal_step :=
    match goal with
    | [ |- (?x <? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.ltb_spec0 x y)
    | [ |- (?x <=? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.leb_spec0 x y)
    | [ |- (?x >? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.gtb_spec0 x y)
    | [ |- (?x >=? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.geb_spec0 x y)
    | [ |- (?x =? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.eqb_spec x y)
    end.
  Ltac ltb_to_lt_step :=
    first [ ltb_to_lt_hyps_step
          | ltb_to_lt_goal_step ].
  Ltac ltb_to_lt := repeat ltb_to_lt_step.

  Section R_Rb.
    Local Ltac t := intros ? ? []; split; intro; ltb_to_lt; omega.
    Local Notation R_Rb Rb R nR := (forall x y b, Rb x y = b <-> if b then R x y else nR x y).
    Lemma ltb_lt_iff : R_Rb Z.ltb Z.lt Z.ge. Proof. t. Qed.
    Lemma leb_le_iff : R_Rb Z.leb Z.le Z.gt. Proof. t. Qed.
    Lemma gtb_gt_iff : R_Rb Z.gtb Z.gt Z.le. Proof. t. Qed.
    Lemma geb_ge_iff : R_Rb Z.geb Z.ge Z.lt. Proof. t. Qed.
    Lemma eqb_eq_iff : R_Rb Z.eqb (@Logic.eq Z) (fun x y => x <> y). Proof. t. Qed.
  End R_Rb.
  Hint Rewrite ltb_lt_iff leb_le_iff gtb_gt_iff geb_ge_iff eqb_eq_iff : ltb_to_lt.
  Ltac ltb_to_lt_in_context :=
    repeat autorewrite with ltb_to_lt in *;
    cbv beta iota in *.
End Z.
