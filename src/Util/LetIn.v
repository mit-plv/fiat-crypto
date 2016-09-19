Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Notation "'dlet' x := y 'in' f" := (Let_In y (fun x => f)).

Global Instance Proper_Let_In_nd_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof. lazy; intros; subst; auto; congruence. Qed.

(* FIXME: it adding this as a typeclass instance makes typeclass
   resolution loop in ModularBaseystemOpt *)
Lemma Proper_Let_In_nd_changevalue {A B} RA {RB} (f:A->B) {Proper_f:Proper (RA==>RB) f}
  : Proper (RA ==> RB) (fun x => Let_In x f).
Proof. intuition. Qed.

Lemma app_Let_In_nd {A B C} (f:B -> C) : forall (e:A) (C:A -> B),
  f (Let_In e C) = Let_In e (fun v => f (C v)).
Proof. intros. cbv [Let_In]. reflexivity. Qed.

Class _call_let_in_to_Let_In {T} (e:T) := _let_in_to_Let_In_return : T.
(* : forall T, gallina T -> gallina T, structurally recursive in the argument *)
Ltac let_in_to_Let_In e :=
  lazymatch e with
  | let x := ?ex in @?eC x =>
    let ex := let_in_to_Let_In ex in
    let eC := let_in_to_Let_In eC in
    constr:(Let_In ex eC)
  | ?f ?x =>
    let f := let_in_to_Let_In f in
    let x := let_in_to_Let_In x in
    constr:(f x)
  | (fun x : ?T => ?C) =>
    lazymatch constr:(fun (x : T) => (_ : _call_let_in_to_Let_In C))
                       (* [C] here above is an open term that references "x" by name *)
    with fun x => @?C x => C end (* match drops the type cast *)
  | ?x => x
  end.
Hint Extern 0 (_call_let_in_to_Let_In ?e) => (
  let e := let_in_to_Let_In e in eexact e
) : typeclass_instances.
Ltac change_let_in_with_Let_In :=
  let g := get_goal in
  let g' := let_in_to_Let_In g in
  change g'.
