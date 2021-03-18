Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Module Import List.
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


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let b_s := f a s in
          let bs_s := foldmap l (snd b_s) in
          (cons (fst b_s) (fst bs_s), snd bs_s)
      end.
  End FoldMap.
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
Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.

Section Reveal.
  Context (dag : dag).
  Definition reveal_step reveal (i : idx) : expr :=
    match List.nth_error dag (Z.to_nat i) with
    | None => (* bad dag *) ExprRef i
    | Some (op, args) => ExprNode (op, List.map reveal args)
    end.
  Fixpoint reveal_fuel (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal_fuel n) i
    end.
  Definition reveal i := reveal_fuel (Z.to_nat i) i.
End Reveal.

Fixpoint merge (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprNode (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let d : dag := snd idxs_d in
    let n : node idx := (op, fst idxs_d) in
    match List.indexof (node_eqb Z.eqb n) d with
    | Some i => (Z.of_nat i, d)
    | None => (Z.of_nat (length d), List.app d (cons n nil))
    end
  end.

Lemma reveal_merge : forall d e, reveal (snd (merge e d)) (fst (merge e d)) = e.
Proof.
Admitted.

Definition SymexConst (s : N) (a : CONST) (st : symbolic_state) : symbolic_state * idx :=
  let i_d := merge (ExprNode (const a, nil)) st in
  (update_dag_with st (fun _ => snd i_d), fst i_d).
