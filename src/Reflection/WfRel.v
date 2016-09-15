Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Local Open Scope ctype_scope.
Local Open Scope expr_scope.

Section language.
  Context (base_type_code : Type).
  Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (R : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop).

  Section rel_pointwise.
    Fixpoint interp_flat_type_gen_rel_pointwise2 (t : flat_type base_type_code)
    : interp_flat_type_gen interp_base_type1 t -> interp_flat_type_gen interp_base_type2 t -> Prop :=
      match t with
      | Tbase t => R t
      | Prod _ _ => fun x y => interp_flat_type_gen_rel_pointwise2 _ (fst x) (fst y)
                               /\ interp_flat_type_gen_rel_pointwise2 _ (snd x) (snd y)
      end.
  End rel_pointwise.

  Section wf.
    Context {var1 var2 : base_type_code -> Type}.

    Local Notation eP := (fun t => var1 t * var2 t)%type (only parsing).
    Local Notation "x == y" := (existT eP _ (x, y)%core).

    Notation exprf1 := (@exprf base_type_code interp_base_type1 op var1).
    Notation exprf2 := (@exprf base_type_code interp_base_type2 op var2).
    Notation expr1 := (@expr base_type_code interp_base_type1 op var1).
    Notation expr2 := (@expr base_type_code interp_base_type2 op var2).

    Inductive rel_wff : list (sigT eP) -> forall {t}, exprf1 t -> exprf2 t -> Prop :=
    | RWfConst : forall t G n n', interp_flat_type_gen_rel_pointwise2 t n n' -> @rel_wff G t (Const n) (Const n')
    | RWfVar : forall G (t : base_type_code) x x', List.In (x == x') G -> @rel_wff G (Tbase t) (Var x) (Var x')
    | RWfOp : forall G {t} {tR} (e : exprf1 t) (e' : exprf2 t) op,
        rel_wff G e e'
        -> rel_wff G (Op (tR := tR) op e) (Op (tR := tR) op e')
    | RWfLet : forall G t1 t2 e1 e1' (e2 : interp_flat_type_gen var1 t1 -> exprf1 t2) e2',
        rel_wff G e1 e1'
        -> (forall x1 x2, rel_wff (flatten_binding_list base_type_code x1 x2 ++ G) (e2 x1) (e2' x2))
        -> rel_wff G (Let e1 e2) (Let e1' e2')
    | RWfPair : forall G {t1} {t2} (e1: exprf1 t1) (e2: exprf1 t2)
                       (e1': exprf2 t1) (e2': exprf2 t2),
        rel_wff G e1 e1'
        -> rel_wff G e2 e2'
        -> rel_wff G (Pair e1 e2) (Pair e1' e2').

    Inductive rel_wf : list (sigT eP) -> forall {t}, expr1 t -> expr2 t -> Prop :=
    | WfReturn : forall t G e e', @rel_wff G t e e' -> rel_wf G (Return e) (Return e')
    | WfAbs : forall A B G e e',
        (forall x x', @rel_wf ((x == x') :: G) B (e x) (e' x'))
        -> @rel_wf G (Arrow A B) (Abs e) (Abs e').
  End wf.

  Definition RelWf {t}
             (E1 : @Expr base_type_code interp_base_type1 op t)
             (E2 : @Expr base_type_code interp_base_type2 op t)
    := forall var1 var2, rel_wf nil (E1 var1) (E2 var2).
End language.

Global Arguments rel_wff {_ _ _ _ _ _ _} G {t} _ _.
Global Arguments rel_wf {_ _ _ _ _ _ _} G {t} _ _.
Global Arguments RelWf {_ _ _ _ _ t} _ _.
