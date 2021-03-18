Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Module Import List.
  Definition option_all [A] : list (option A) -> option (list A) := OptionList.Option.List.lift.
  Lemma option_all_Some [A] ol l (H : @option_all A ol = Some l)
    : forall i a, nth_error l i = Some a -> nth_error ol i = (Some (Some a)).
  Admitted.
  Lemma option_all_None [A] ol (H : @option_all A ol = None)
    : exists j, nth_error ol j = None.
  Admitted.

  Section IndexOf.
    Context [A] (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_none l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Admitted.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a -> f a = true.
    Admitted.
    Lemma indexof_first l i (H : indexof l = Some i) :
      forall j a, j < i -> nth_error l j = Some a -> f a = false.
    Admitted.
  End IndexOf.
End List.

Require Import Crypto.Assembly.Syntax.
Definition idx := Z.
Local Set Boolean Equality Schemes.
Variant op := const (_ : Z) | add (width : Z) (* | ... *).

Definition node (arg : Set) : Set := op * list arg.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprNode (_ : node expr).
Local Set Elimination Schemes.
(* Note: need custom induction principle *)
Definition invert_ExprRef (e : expr) :=
  match e with ExprRef i => Some i | _ => None end.

Definition node_eqb [arg : Set] (arg_eqb : arg -> arg -> bool) : node arg -> node arg -> bool := 
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (Z * list (option idx)).

Record symbolic_state := { dag_state :> dag ; machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.

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
