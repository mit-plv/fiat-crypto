Require Import Crypto.Reflection.Syntax.
Require Crypto.Reflection.InputSyntax.
Require Crypto.Reflection.ReifyDirect.
Require Crypto.Reflection.ReifyExact.
Require Crypto.Reflection.Linearize.

Module Direct.
  Export ReifyDirect.

  Import ReifyDebugNotations.

  Inductive base_type := Tnat.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | Tnat => nat
    end.
  Local Notation tnat := (Tbase Tnat).
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | Add : op (Prod tnat tnat) tnat
  | Mul : op (Prod tnat tnat) tnat.

  Global Instance: forall x y, reify_op op (x + y)%nat 2 Add := fun _ _ => I.
  Global Instance: forall x y, reify_op op (x * y)%nat 2 Mul := fun _ _ => I.
  Global Instance: reify type nat := Tnat.

  Ltac Reify e := ReifyDirect.Reify base_type interp_base_type op e.

  (*Ltac reify_debug_level ::= constr:(2).*)

  Goal (base_type -> Type) -> False.
    intro var.
    let x := reifyf base_type interp_base_type op var 1%nat in pose x.
    let x := Reify 1%nat in unify x (fun var => Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1).
    let x := reifyf base_type interp_base_type op var (1 + 1)%nat in pose x.
    let x := Reify (1 + 1)%nat in unify x (fun var => Op Add (Pair (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1))).
    let x := reify_abs base_type interp_base_type op var (fun x => x + 1)%nat in pose x.
    let x := Reify (fun x => x + 1)%nat in unify x (fun var => Abs (fun y => Op Add (Pair (Var y) (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)))).
    let x := reifyf base_type interp_base_type op var (let '(a, b) := (1, 1) in a + b)%nat in pose x.
    let x := reifyf base_type interp_base_type op var (let '(a, b, c) := (1, 1, 1) in a + b + c)%nat in pose x.
    let x := Reify (fun x => let '(a, b) := (1, 1) in a + x)%nat in
    unify x (fun var => Abs (fun x0 =>
                               let c1 := (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) in
                               Let (Pair c1 c1)
                                   (fun ab : var Tnat * var Tnat => Op Add (Pair (Var (fst ab)) (Var x0))))).
  Abort.
End Direct.

Module Exact.
  Export ReifyExact.
  Import InputSyntax.

  Import ReifyDebugNotations.

  Inductive base_type := Tnat.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | Tnat => nat
    end.
  Local Notation tnat := (Tbase Tnat).
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | Add : op (Prod tnat tnat) tnat
  | Mul : op (Prod tnat tnat) tnat.
  Definition interp_op src dst (f : op src dst) : interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst
    := match f with
       | Add => fun xy => fst xy + snd xy
       | Mul => fun xy => fst xy * snd xy
       end%nat.

  Global Instance: forall x y, reify_op op (x + y)%nat 2 Add := fun _ _ => I.
  Global Instance: forall x y, reify_op op (x * y)%nat 2 Mul := fun _ _ => I.
  Global Instance: reify type nat := Tnat.

  Ltac Reify' e := ReifyExact.Reify' base_type interp_base_type op e.
  Ltac Reify e := ReifyExact.Reify base_type interp_base_type op e.
  Ltac Reify_rhs := ReifyExact.Reify_rhs base_type interp_base_type op interp_op.

  (*Ltac reify_debug_level ::= constr:(2).*)

  Goal (flat_type base_type -> Type) -> False.
    intro var.
    let x := reifyf base_type interp_base_type op var 1%nat in pose x.
    let x := Reify' 1%nat in unify x (fun var => Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1).
    let x := reifyf base_type interp_base_type op var (1 + 1)%nat in pose x.
    let x := Reify' (1 + 1)%nat in unify x (fun var => Op Add (Pair (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1))).
    let x := reify_abs base_type interp_base_type op var (fun x => x + 1)%nat in pose x.
    let x := Reify' (fun x => x + 1)%nat in unify x (fun var => Abs (fun y => Op Add (Pair (Var y) (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)))).
    let x := reifyf base_type interp_base_type op var (let '(a, b) := (1, 1) in a + b)%nat in pose x.
    let x := reifyf base_type interp_base_type op var (let '(a, b, c) := (1, 1, 1) in a + b + c)%nat in pose x.
    let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in let x := (eval vm_compute in x) in pose x.
    let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in
    unify x (fun var => Abs (fun x' =>
                               let c1 := (Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) in
                               MatchPair (tC:=tnat) (Pair c1 c1)
                                         (fun x0 _ : var tnat => Op Add (Pair (Var x0) (Var x'))))).
    let x := reifyf base_type interp_base_type op var (let x := 5 in let y := 6 in (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in pose x.
    let x := Reify' (fun x y => (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in pose x.
  Abort.

  Goal (0 = let x := 1+2 in x*3)%nat.
    Reify_rhs.
  Abort.

  Goal (0 = let x := 1 in let y := 2 in x * y)%nat.
    Reify_rhs.
  Abort.

  Import Linearize.

  Goal True.
    let x := Reify (fun x y => (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in
    pose (InlineConst (Linearize x)) as e.
    vm_compute in e.
  Abort.
End Exact.
