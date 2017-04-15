Require Import Coq.omega.Omega Coq.micromega.Psatz.
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Compilers.Named.RegisterAssign.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Equality.
Require Export Crypto.Compilers.Reify.
Require Import Crypto.Compilers.InputSyntax.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Crypto.Compilers.Linearize Crypto.Compilers.Inline.
Require Import Crypto.Compilers.WfReflective.
Require Import Crypto.Compilers.Conversion.
Require Import Crypto.Util.NatUtil.

Import ReifyDebugNotations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive base_type := Tnat.
Definition interp_base_type (v : base_type) : Type :=
  match v with
  | Tnat => nat
  end.
Local Notation tnat := (Tbase Tnat).
Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| Const (v : nat) : op Unit tnat
| Add : op (Prod tnat tnat) tnat
| Mul : op (Prod tnat tnat) tnat
| Sub : op (Prod tnat tnat) tnat.
Definition is_const s d (v : op s d) : bool := match v with Const _ => true | _ => false end.
Definition interp_op src dst (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := match f with
     | Const v => fun _ => v
     | Add => fun xy => fst xy + snd xy
     | Mul => fun xy => fst xy * snd xy
     | Sub => fun xy => fst xy - snd xy
     end%nat.

Global Instance: reify_op op plus 2 Add := I.
Global Instance: reify_op op mult 2 Mul := I.
Global Instance: reify_op op minus 2 Sub := I.
Global Instance: reify type nat := Tnat.

Definition make_const (t : base_type) : interp_base_type t -> op Unit (Tbase t)
  := match t with
     | Tnat => fun v => Const v
     end.
Ltac Reify' e := Reify.Reify' base_type interp_base_type op e.
Ltac Reify e := Reify.Reify base_type interp_base_type op make_const e.
Ltac Reify_rhs := Reify.Reify_rhs base_type interp_base_type op make_const interp_op.
Ltac reify_context_variables :=
  Reify.reify_context_variables base_type interp_base_type op.

(*Ltac reify_debug_level ::= constr:(2).*)

Goal (flat_type base_type -> Type) -> False.
  intro var.
  let x := reifyf base_type interp_base_type op var 1%nat in pose x.
  let x := Reify' 1%nat in unify x (fun var => Return (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)).
  let x := reifyf base_type interp_base_type op var (1 + 1)%nat in pose x.
  let x := Reify' (1 + 1)%nat in unify x (fun var => Return (Op Add (Pair (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)))).
  let x := reify_abs base_type interp_base_type op var (fun x => x + 1)%nat in pose x.
  let x := Reify' (fun x => x + 1)%nat in unify x (fun var => Abs (fun y => Return (Op Add (Pair (Var y) (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1))))).
  let x := reifyf base_type interp_base_type op var (let '(a, b) := (1, 1) in a + b)%nat in pose x.
  let x := reifyf base_type interp_base_type op var (let '(a, b, c) := (1, 1, 1) in a + b + c)%nat in pose x.
  let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun x => let '(a, b, c, (d, e), f) := x in a + b + c + d + e + f)%nat in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun x => let '(a, b) := x in let '(a, c) := a in let '(a, d) := a in a + b + c + d)%nat in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun ab0 : nat * nat * nat * nat => let (f, g6) := fst ab0 in
                                                      let (f0, g7) := f in
                                                      let ab3 := (1, 1) in
                                                      let ab21 := (1, 1) in
                                                      let z := snd ab3 + snd ab21 in z + z)%nat in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun ab0 : nat * nat * nat => let (f, g7) := fst ab0 in 1 + 1) in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in
  unify x (fun var => Abs (fun x' =>
                          let c1 := (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) in
                          Return (MatchPair (tC:=tnat) (Pair c1 c1)
                                            (fun x0 y0 : var tnat => Op Add (Pair (Var x0) (Var x')))))).
  let x := reifyf base_type interp_base_type op var (let x := 5 in let y := 6 in (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in pose x.
  let x := Reify' (let x := 1 in let y := 1 in (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in pose x.
  let x := Reify' (fun xy => let '(x, y) := xy in (let a := 1 in let '(c, d) := (2, 3) in a + x + c + d) + y)%nat in pose x.
Abort.


Goal (0 = let x := 1+2 in x*3)%nat.
  Reify_rhs.
Abort.

Goal (0 = let x := 1 in let y := 2 in x * y)%nat.
  Reify_rhs.
Abort.

Import Linearize Inline.

Goal True.
  let x := Reify (fun xy => let '(x, y) := xy in (let a := 1 in let '(c, d) := (2, 3) in a + x - a + c + d) + y)%nat in
  pose (InlineConst is_const (ANormal x)) as e.
  vm_compute in e.
Abort.

Definition example_expr : Syntax.Expr base_type op (Syntax.Arrow (tnat * tnat) tnat).
Proof.
  let x := Reify (fun zw => let '(z, w) := zw in let unused := 1 + 1 in let x := 1 in let y := 1 in (let a := 1 in let cd := let cdef := (2, 3, 4, 5) in let '(c, d, e, f) := cdef in (c, d) in let '(c, d) := cd in a + x + (x + x) + (x + x) - (x + x) - a + c + d) + y + z + w)%nat in
  exact x.
Defined.

Definition example_expr_ctx : Syntax.Expr base_type op (Syntax.Arrow (tnat * tnat) tnat).
Proof.
  pose (((fun ab => let '(a, b) := ab in a + b)%nat)
        : Syntax.interp_type interp_base_type (Syntax.Arrow (tnat * tnat) tnat))
    as F.
  reify_context_variables.
  let x := Reify (fun zw => let '(z, w) := zw in F (z, w))%nat in
  exact x.
Defined.

Definition base_type_eq_semidec_transparent : forall t1 t2, option (t1 = t2)
  := fun t1 t2 => match t1, t2 with
               | Tnat, Tnat => Some eq_refl
               end.
Lemma base_type_eq_semidec_is_dec : forall t1 t2,
    base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2.
Proof.
  intros t1 t2; destruct t1, t2; simpl; intros; congruence.
Qed.
Definition op_beq t1 tR : op t1 tR -> op t1 tR -> reified_Prop
  := fun x y => match x, y return bool with
                | Const a, Const b => NatUtil.nat_beq a b
                | Const _, _ => false
                | Add, Add => true
                | Add, _ => false
                | Mul, Mul => true
                | Mul, _ => false
                | Sub, Sub => true
                | Sub, _ => false
                end.
Lemma op_beq_bl t1 tR (x y : op t1 tR)
  : to_prop (op_beq t1 tR x y) -> x = y.
Proof.
  destruct x; simpl;
    refine match y with Add => _ | _ => _ end;
    repeat match goal with
           | _ => progress simpl in *
           | _ => progress unfold op_beq in *
           | [ |- context[reified_Prop_of_bool ?b] ]
             => destruct b eqn:?; unfold reified_Prop_of_bool
           | _ => progress nat_beq_to_eq
           | _ => congruence
           | _ => tauto
           end.
Qed.

Ltac reflect_Wf := WfReflective.reflect_Wf base_type_eq_semidec_is_dec op_beq_bl.

Lemma example_expr_wf_slow : Wf example_expr.
Proof.
  Time (vm_compute; intros;
          repeat match goal with
                 | [ |- wf _ _ ] => constructor; intros
                 | [ |- wff _ _ _ ] => constructor; intros
                 | [ |- List.In _ _ ] => vm_compute
                 | [ |- ?x = ?x \/ _ ] => left; reflexivity
                 | [ |- ?x = ?y \/ _ ] => right
                 end). (* 0.036 s *)
Qed.

Definition example_expr_eta := Eval vm_compute in Eta.ExprEta example_expr.

Lemma example_expr_wf_eta : Wf example_expr_eta.
Proof. Time reflect_Wf. (* 0.008 s *) Qed.

Lemma example_expr_wf : Wf example_expr.
Proof. Time reflect_Wf. (* 0.008 s *) Qed.

Section cse.
  Let SConstT := nat.
  Inductive op_code : Set := SConst (v : nat) | SAdd | SMul | SSub.
  Definition symbolicify_op s d (v : op s d) : op_code
    := match v with
       | Const v => SConst v
       | Add => SAdd
       | Mul => SMul
       | Sub => SSub
       end.
  Definition CSE {t} e := @CSE base_type op_code base_type_beq op_code_beq internal_base_type_dec_bl op symbolicify_op (fun _ x => x) true t e (fun _ => nil).
End cse.

Definition example_expr_simplified := Eval vm_compute in InlineConst is_const (ANormal example_expr).
Compute CSE example_expr_simplified.

Definition example_expr_compiled
  := Eval vm_compute in
      match Named.Compile.compile (example_expr_simplified _) (List.map Pos.of_nat (seq 1 20)) as v return match v with Some _ => _ | _ => _ end with
      | Some v => v
      | None => True
      end.

Compute register_reassign (InContext:=PositiveContext_nd) (ReverseContext:=PositiveContext_nd) Pos.eqb empty empty example_expr_compiled (Some 1%positive :: Some 2%positive :: None :: List.map (@Some _) (List.map Pos.of_nat (seq 3 20))).

Module bounds.
  Record bounded := { lower : nat ; value : nat ; upper : nat }.
  Definition map_bounded_f2 (f : nat -> nat -> nat) (swap_on_arg2 : bool) (x y : bounded)
    := {| lower := f (lower x) (if swap_on_arg2 then upper y else lower y);
          value := f (value x) (value y);
          upper := f (upper x) (if swap_on_arg2 then lower y else upper y) |}.
  Definition bounded_pf :=  { b : bounded | lower b <= value b <= upper b }.
  Definition add_bounded_pf (x y : bounded_pf) : bounded_pf.
  Proof.
    exists (map_bounded_f2 plus false (proj1_sig x) (proj1_sig y)).
    simpl; abstract (destruct x, y; simpl; omega).
  Defined.
  Definition mul_bounded_pf (x y : bounded_pf) : bounded_pf.
  Proof.
    exists (map_bounded_f2 mult false (proj1_sig x) (proj1_sig y)).
    simpl; abstract (destruct x, y; simpl; nia).
  Defined.
  Definition sub_bounded_pf (x y : bounded_pf) : bounded_pf.
  Proof.
    exists (map_bounded_f2 minus true (proj1_sig x) (proj1_sig y)).
    simpl; abstract (destruct x, y; simpl; omega).
  Defined.
  Definition interp_base_type_bounds (v : base_type) : Type :=
    match v with
    | Tnat => { b : bounded | lower b <= value b <= upper b }
    end.
  Definition constant_bounded t (x : interp_base_type t) : interp_base_type_bounds t.
  Proof.
    destruct t.
    exists {| lower := x ; value := x ; upper := x |}.
    simpl; split; reflexivity.
  Defined.
  Definition interp_op_bounds src dst (f : op src dst) : interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst
    := match f with
       | Const v => fun _ => constant_bounded Tnat v
       | Add => fun xy => add_bounded_pf (fst xy) (snd xy)
       | Mul => fun xy => mul_bounded_pf (fst xy) (snd xy)
       | Sub => fun xy => sub_bounded_pf (fst xy) (snd xy)
       end%nat.
  Fixpoint constant_bounds t
    : interp_flat_type interp_base_type t -> interp_flat_type interp_base_type_bounds t
    := match t with
       | Tbase t => constant_bounded t
       | Unit => fun _ => tt
       | Prod _ _ => fun x => (constant_bounds _ (fst x), constant_bounds _ (snd x))
       end.

  Compute (fun x xpf y ypf => proj1_sig (Syntax.Interp interp_op_bounds example_expr
                                         (exist _ {| lower := 0 ; value := x ; upper := 10 |} xpf,
                                          exist _ {| lower := 100 ; value := y ; upper := 1000 |} ypf))).
End bounds.
