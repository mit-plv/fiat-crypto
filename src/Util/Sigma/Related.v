Import EqNotations.

Definition related_sigT_by_eq {A P1 P2} (R : forall x : A, P1 x -> P2 x -> Prop)
           (x : @sigT A P1) (y : @sigT A P2)
  : Prop
  := { pf : projT1 x = projT1 y
     | R _ (rew pf in projT2 x) (projT2 y) }.

Definition map_related_sigT_by_eq {A P1 P2} {R1 R2 : forall x : A, P1 x -> P2 x -> Prop}
           (HR : forall x v1 v2, R1 x v1 v2 -> R2 x v1 v2)
           (x : @sigT A P1) (y : @sigT A P2)
  : @related_sigT_by_eq A P1 P2 R1 x y -> @related_sigT_by_eq A P1 P2 R2 x y.
Proof using Type.
  destruct x, y; cbv [related_sigT_by_eq projT1 projT2].
  intro H; exists (proj1_sig H); apply HR, (proj2_sig H).
Qed.
