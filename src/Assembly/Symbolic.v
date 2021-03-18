Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Module Import List.
  Definition option_all [A] : list (option A) -> option (list A). Admitted.
  Definition indexof [A] : (A -> bool) -> list A -> option nat. Admitted.
End List.

Require Import Crypto.Assembly.Syntax.
Print FLAG.
Definition idx := Z.
Local Set Boolean Equality Schemes.
Variant op := const (_ : Z) | add (* | ... *).

Definition node (arg : Set) : Set := op * list arg.
Definition node_eqb [arg : Set] (arg_eqb : arg -> arg -> bool) : node arg -> node arg -> bool. Admitted.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprNode (_ : node expr).
Local Set Elimination Schemes.
(* Note: need custom induction principle *)
Definition invert_ExprRef (e : expr) :=
  match e with ExprRef i => Some i | _ => None end.

Definition dag := list (node idx).

Definition memstate := list (Z * list (option idx)).
Definition regstate := REG -> option idx.
Definition flagstate := FLAG -> option idx.

Definition state : Set := dag * regstate * flagstate * memstate.

Section WithDag.
  Context (dag : dag).
  Definition reveal_idx_step reveal (i : idx) : expr :=
    match List.nth_error dag (Z.to_nat i) with
    | None => (* bad dag *) ExprRef i
    | Some (op, args) => ExprNode (op, List.map reveal args)
    end.
  Fixpoint reveal_idx_fuel (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_idx_step (reveal_idx_fuel n) i
    end.
  Definition reveal_idx i := reveal_idx_fuel (Z.to_nat i) i.

  Fixpoint reveal (e : expr) :=
    match e with
    | ExprRef i => reveal_idx i
    | ExprNode (op, args) => ExprNode (op, List.map reveal args)
    end.

  Fixpoint merge (e : expr) : expr :=
    match e with
    | ExprRef i => ExprRef i
    | ExprNode (op, args) =>
      let args : list expr := List.map merge args in
      match List.option_all (List.map invert_ExprRef args) with
      | None => ExprNode (op, args)
      | Some argidxs =>
          let n : node idx := (op, argidxs) in
          match List.indexof (node_eqb Z.eqb n) dag with
          | Some i => ExprRef (Z.of_nat i)
          | None => ExprNode (op, args)
          end
      end
    end.

  Lemma reveal_merge : forall e, reveal (merge e) = e.
  Admitted.
End WithDag.
