Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.ModularArithmetic. Local Open Scope F_scope.
Require Import Crypto.Curves.EdwardsMontgomery. Import M.
Require Import Crypto.Curves.Edwards.TwistIsomorphism.
Require Import Crypto.Spec.Curve25519.

Local Definition sqrtm1 : F p := F.pow (F.of_Z _ 2) ((N.pos p-1)/4).
Local Definition sqrt := PrimeFieldTheorems.F.sqrt_5mod8 sqrtm1.

Import MontgomeryCurve CompleteEdwardsCurve.

Local Definition a' := (M.a + (1 + 1)) / M.b.
Local Definition d' := (M.a - (1 + 1)) / M.b.
Local Definition r := sqrt (F.inv ((a' / M.b) / E.a)).

Local Lemma is_twist : E.a * d' = a' * E.d. Proof. vm_decide. Qed.
Local Lemma nonzero_a' : a' <> 0. Proof. vm_decide. Qed.
Local Lemma r_correct : E.a = r * r * a'. Proof. vm_decide. Qed.

Module E.
Definition of_Montgomery (P : Curve25519.M.point) : Curve25519.E.point :=
 @E.point1_of_point2 _ _ _ _ _ _ _ _ _ _ field _ E.a E.d a' d' is_twist E.nonzero_a nonzero_a' r r_correct
   (@to_Edwards _ _ _ _ _ _ _ _ _ _ field _ M.a M.b M.b_nonzero a' d' eq_refl eq_refl nonzero_a' P).
Lemma of_Montgomery_B : E.eq E.B (of_Montgomery M.B). Proof. vm_decide. Qed.
End E.

Module M.
Definition of_Edwards (P : Curve25519.E.point) : Curve25519.M.point :=
  @of_Edwards _ _ _ _ _  _ _ _ _ _ field _ char_ge_3 M.a M.b M.b_nonzero a' d' eq_refl eq_refl nonzero_a'
    (@E.point2_of_point1 _ _ _ _ _ _ _ _ _ _ field _ E.a E.d a' d' is_twist E.nonzero_a nonzero_a' r r_correct P).
Lemma of_Edwards_B : M.eq M.B (of_Edwards E.B). Proof.
Proof. simple notypeclasses refine (@dec_bool _ _ _). apply Affine.M.Decidable_eq. vm_decide. Qed.
End M.

Local Notation Eopp := ((@AffineProofs.E.opp _ _ _ _ _ _ _ _ _ _ field _ E.a E.d E.nonzero_a)).

Local Arguments Hierarchy.commutative_group _ {_} _ {_ _}.
Local Arguments CompleteEdwardsCurve.E.add {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ {_ _ _}.
Local Arguments Monoid.is_homomorphism {_ _ _ _ _ _}.
Local Arguments to_Edwards {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ { _ _ _ }.
Local Arguments of_Edwards {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ { _ _ _ }.

Lemma EdwardsMontgomery25519 : @Group.isomorphic_commutative_groups
       Curve25519.E.point E.eq Curve25519.E.add Curve25519.E.zero Eopp Curve25519.M.point
       M.eq Curve25519.M.add M.zero Curve25519.M.opp
       Montgomery_of_Edwards Edwards_of_Montgomery.
Proof.
  cbv [Montgomery_of_Edwards Edwards_of_Montgomery].
  epose proof E.twist_isomorphism(a1:=E.a)(a2:=a')(d1:=E.d)(d2:=d')(r:=r) as AB.
  epose proof EdwardsMontgomeryIsomorphism(a:=Curve25519.M.a)(b:=Curve25519.M.b)as BC.
  destruct AB as [A B ab ba], BC as [_ C bc cb].
  pose proof Group.compose_homomorphism(homom:=ab)(homom2:=bc) as ac.
  pose proof Group.compose_homomorphism(homom:=cb)(homom2:=ba)(groupH2:=ltac:(eapply A)) as ca.
  split; try exact ac; try exact ca; try exact A; try exact C.
  Unshelve.
  all : try (pose (@PrimeFieldTheorems.F.Decidable_square p prime_p eq_refl); vm_decide).
  all : try (eapply Hierarchy.char_ge_weaken; try apply ModularArithmeticTheorems.F.char_gt; vm_decide).
Qed.
