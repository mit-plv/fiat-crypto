Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop Coq.Relations.Relation_Definitions.
Require Export Crypto.Util.FixCoqMistakes.

Lemma PER_valid_l {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R x.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
Lemma PER_valid_r {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R y.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
Global Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_l _ R); [ | | solve [ auto with nocore ] ] : typeclass_instances.
Global Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_r _ R); [ | | solve [ auto with nocore ] ] : typeclass_instances.
