Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Logic.
From Coq Require Import Morphisms Setoid.

Lemma symmetry_iff {T} {R} {Rsym:@Symmetric T R} x y: R x y <-> R y x.
  epose symmetry; intuition eauto.
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

Global Instance Equivalence_and {A B RA RB}
       {Equivalence_RA:@Equivalence A RA}
       {Equivalence_RB:@Equivalence B RB}
       : Equivalence (fun ab AB => RA (fst ab) (fst AB) /\ RB (snd ab) (snd AB)).
Proof.
  do 2 match goal with H : Equivalence _ |- _ => destruct H end;
    cbv in *|-.
  repeat match goal with
           | _ => intro
           | _ => split
           | [p:prod _ _ |- _ ] => destruct p
           | [p:and _ _ |- _ ] => destruct p
           | _ => progress (cbv [fst snd] in * )
           | _ => solve[eauto]
         end.
Qed.

Global Instance eq_eta_Reflexive {T} : Reflexive (fun x y : T => x = y) | 1
  := eq_Reflexive.

Global Instance Symmetric_not {T:Type} (R:T->T->Prop)
       {SymmetricR:Symmetric R} : Symmetric (fun a b => not (R a b)).
Proof. cbv [Symmetric] in *; repeat intro; eauto. Qed.

Lemma not_exfalso (P:Prop) (H:P->False) : not P. auto with nocore. Qed.

Global Instance respectful_subrelation_pointwise {A B} {RA : relation A} {R R' : relation B}
  : subrelation eq RA -> subrelation R R' -> subrelation (RA ==> R)%signature (pointwise_relation A R') | 100.
Proof. cbv; eauto. Qed.

Global Instance pointwise_subrelation_respectful {A B} {RA : relation A} {R R' : relation B}
  : subrelation RA eq -> subrelation R' R -> subrelation (pointwise_relation A R') (RA ==> R)%signature | 100.
Proof. cbv; firstorder (subst; eauto). Qed.
