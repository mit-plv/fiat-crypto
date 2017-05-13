Require Import Crypto.Util.FixCoqMistakes.
Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.GetGoal.
Require Import Crypto.Util.Notations.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Definition Let_In_pf {A P} (x : A) (f : forall a : A, a = x -> P a) : P x := let y := x in f y eq_refl.
Notation "'dlet_nd' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )) (only parsing).
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Notation "'pflet' x , pf := y 'in' f" := (Let_In_pf y (fun x pf => f)).

Module Bug5107WorkAround.
  Notation "'dlet' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )).
End Bug5107WorkAround.

Global Instance Proper_Let_In_nd_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof. lazy; intros; subst; auto; congruence. Qed.

Global Instance Proper_Let_In_nd_changevalue {A B} (RA:relation A) {RB:relation B}
  : Proper (RA ==> (RA ==> RB) ==> RB) (Let_In (P:=fun _=>B)).
Proof. cbv; intuition. Qed.

Lemma Proper_Let_In_nd_changebody_eq {A P R} {Reflexive_R:@Reflexive P R} {x}
  : Proper ((fun f g => forall a, x = a -> R (f a) (g a)) ==> R) (@Let_In A (fun _ => P) x).
Proof. lazy; intros; subst; auto; congruence. Qed.

Definition app_Let_In_nd {A B T} (f:B->T) (e:A) (C:A->B)
  : f (Let_In e C) = Let_In e (fun v => f (C v)) := eq_refl.

Definition Let_app_In_nd {A B T} (f:A->B) (e:A) (C:B->T)
  : Let_In (f e) C = Let_In e (fun v => C (f v)) := eq_refl.

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
