Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Logic.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.

Lemma symmetry_iff {T} {R} {Rsym:@Symmetric T R} x y: R x y <-> R y x.
  intuition eauto using symmetry.
Qed.

Lemma and_rewrite_l {A B} {RA RB} {Equivalence_RA:Equivalence RA} {Equivalence_RB:Equivalence RB}
      (f:A->B) ref P {Proper_P: Proper (RA==>RB==>iff) P} a
  : (RB (f a) ref /\ P a (f a)) <-> (RB (f a) ref /\ P a ref).
Proof.
  logic; match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
Qed.

Lemma and_rewriteleft_l {A B} {RA RB} {Equivalence_RA:Equivalence RA} {Equivalence_RB:Equivalence RB}
      (f:A->B) ref P {Proper_P: Proper (RA==>RB==>iff) P} a
  : (RB ref (f a) /\ P a (f a)) <-> (RB ref (f a) /\ P a ref).
Proof.
  logic; match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
Qed.

Lemma exists_and_equiv_r {A} {RA} {Equivalence_RA:Equivalence RA}
      P {Proper_P: Proper (RA==>iff) P} (ref:A)
  : (exists a, P a /\ RA a ref) <-> P ref.
Proof.
  logic; try match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
  repeat (assumption||reflexivity||econstructor); assumption. (* WHY the last [assumption]?*)
Qed.

Lemma iff_R_R_same_r {T R} {Req:@Equivalence T R} x y ref : R x y -> (R x ref <-> R y ref).
Proof.
  intro Hx; rewrite Hx; clear Hx. reflexivity.
Qed.