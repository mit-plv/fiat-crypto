Require Import Coq.omega.Omega Coq.micromega.Psatz.
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Named.RegisterAssign.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Equality.
Require Export Crypto.Reflection.Reify.
Require Import Crypto.Reflection.InputSyntax.
Require Import Crypto.Reflection.CommonSubexpressionElimination.
Require Crypto.Reflection.Linearize Crypto.Reflection.Inline.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Conversion.
Require Import Crypto.Reflection.DependentIdentitySigmaByEq.
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

(*Ltac reify_debug_level ::= constr:(2).*)

Goal (flat_type base_type -> Type) -> False.
  intro var.
  let x := reifyf base_type interp_base_type op var 1%nat in pose x.
  let x := Reify' 1%nat in unify x (fun var => Return (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)).
  let x := reifyf base_type interp_base_type op var (1 + 1)%nat in pose x.
  let x := Reify' (1 + 1)%nat in unify x (fun var => Return (Op Add (Pair (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)))).
  let x := reify_abs base_type interp_base_type op var (fun x => x + 1)%nat in pose x.
  let x := Reify' (fun x => x + 1)%nat in unify x (fun var => Abs (fun y => Op Add (Pair (Var y) (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1)))).
  let x := reifyf base_type interp_base_type op var (let '(a, b) := (1, 1) in a + b)%nat in pose x.
  let x := reifyf base_type interp_base_type op var (let '(a, b, c) := (1, 1, 1) in a + b + c)%nat in pose x.
  let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in let x := (eval vm_compute in x) in pose x.
  let x := Reify' (fun x => let '(a, b) := (1, 1) in a + x)%nat in
  unify x (fun var => Abs (fun x' =>
                          let c1 := (InputSyntax.Const (interp_base_type:=interp_base_type) (var:=var) (t:=Tbase Tnat) (op:=op) 1) in
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

Import Linearize Inline.

Goal True.
  let x := Reify (fun x y => (let a := 1 in let '(c, d) := (2, 3) in a + x - a + c + d) + y)%nat in
  pose (InlineConst is_const (Linearize x)) as e.
  vm_compute in e.
Abort.

Definition example_expr : Syntax.Expr base_type op (Arrow Tnat (Arrow Tnat (Tflat tnat))).
Proof.
  let x := Reify (fun z w => let unused := 1 + 1 in let x := 1 in let y := 1 in (let a := 1 in let '(c, d) := (2, 3) in a + x + (x + x) + (x + x) - (x + x) - a + c + d) + y + z + w)%nat in
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
                 | [ |- wf _ _ _ ] => constructor; intros
                 | [ |- wff _ _ _ ] => constructor; intros
                 | [ |- List.In _ _ ] => vm_compute
                 | [ |- ?x = ?x \/ _ ] => left; reflexivity
                 | [ |- ?x = ?y \/ _ ] => right
                 end). (* 0.036 s *)
Qed.

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
  Definition CSE {t} e := @CSE base_type op_code base_type_beq op_code_beq internal_base_type_dec_bl op symbolicify_op t e (fun _ => nil).
End cse.

Definition example_expr_simplified := Eval vm_compute in InlineConst is_const (Linearize example_expr).
Compute CSE example_expr_simplified.

Definition example_expr_compiled
  := Eval vm_compute in
      match Named.Compile.compile (example_expr_simplified _) (List.map Pos.of_nat (seq 1 20)) as v return match v with Some _ => _ | _ => _ end with
      | Some v => v
      | None => True
      end.

Compute register_reassign Pos.eqb empty empty example_expr_compiled (Some 1%positive :: Some 2%positive :: None :: List.map (@Some _) (List.map Pos.of_nat (seq 3 20))).

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
                                         (exist _ {| lower := 0 ; value := x ; upper := 10 |} xpf)
                                         (exist _ {| lower := 100 ; value := y ; upper := 1000 |} ypf))).
End bounds.

Section dependent_sigma_eq.
  Section gen.
    Import Reflection.Syntax.
    Context {var : base_type -> Type}.
    Fixpoint gen_let_sequence' (n : nat) (rv : @exprf base_type op var (Tbase Tnat))
      : @exprf base_type op var (Tbase Tnat)
      := match n with
         | 0 => rv
         | S n' => LetIn (Op Add (Pair rv rv))
                         (fun v => gen_let_sequence' n' (@Var base_type op var Tnat v))
         end.
    Definition gen_let_sequence n := gen_let_sequence' n (Op (Const 1) TT).
  End gen.

  Definition mexist_idf {var} {t} (e : @Syntax.exprf base_type op (fun t => @Syntax.exprf base_type op var (Tbase t)) t)
    := @mexist_id
         base_type op var base_type_beq
         internal_base_type_dec_bl
         (fun _ b => Syntax.Op (make_const _ match b return interp_base_type b with Tnat => 0 end) Syntax.TT)
         t e.
  Definition dexist_idf {var} {t} (e : @Syntax.exprf base_type op (fun t => @Syntax.exprf base_type op var (Tbase t)) t)
    := @dexist_id
         base_type op var base_type_beq
         internal_base_type_dec_bl
         (fun _ b => Syntax.Op (make_const _ match b return interp_base_type b with Tnat => 0 end) Syntax.TT)
         t e.
  Definition pexist_idf (let_in : forall A B, A -> (A -> B) -> B)
             {var} {t} (e : @Syntax.exprf base_type op (fun t => @Syntax.exprf base_type op var (Tbase t)) t)
    := @pexist_id
         base_type op var base_type_beq
         internal_base_type_dec_bl
         (fun _ b => Syntax.Op (make_const _ match b return interp_base_type b with Tnat => 0 end) Syntax.TT)
         let_in
         t e.
  Definition seq0 {var} := Eval vm_compute in @gen_let_sequence var 0.
  Definition seq1 {var} := Eval vm_compute in @gen_let_sequence var 1.
  Definition seq2 {var} := Eval vm_compute in @gen_let_sequence var 2.
  Definition seq3 {var} := Eval vm_compute in @gen_let_sequence var 2.
  Definition seq4 {var} := Eval vm_compute in @gen_let_sequence var 4.
  Definition seq5 {var} := Eval vm_compute in @gen_let_sequence var 5.
  Definition seq6 {var} := Eval vm_compute in @gen_let_sequence var 6.
  Definition seq7 {var} := Eval vm_compute in @gen_let_sequence var 7.
  Definition seq8 {var} := Eval vm_compute in @gen_let_sequence var 8.
  Definition seq9 {var} := Eval vm_compute in @gen_let_sequence var 9.
  Definition seq10 {var} := Eval vm_compute in @gen_let_sequence var 10.
  Definition seq11 {var} := Eval vm_compute in @gen_let_sequence var 11.
  Definition seq12 {var} := Eval vm_compute in @gen_let_sequence var 12.
  Definition seq13 {var} := Eval vm_compute in @gen_let_sequence var 13.
  Definition seq14 {var} := Eval vm_compute in @gen_let_sequence var 14.
  Definition seq15 {var} := Eval vm_compute in @gen_let_sequence var 15.
  Definition seq16 {var} := Eval vm_compute in @gen_let_sequence var 16.
  Definition seq17 {var} := Eval vm_compute in @gen_let_sequence var 17.
  Definition seq18 {var} := Eval vm_compute in @gen_let_sequence var 18.
  Definition seq19 {var} := Eval vm_compute in @gen_let_sequence var 19.
  Definition seq20 {var} := Eval vm_compute in @gen_let_sequence var 20.
  Definition seq21 {var} := Eval vm_compute in @gen_let_sequence var 21.
  Definition seq22 {var} := Eval vm_compute in @gen_let_sequence var 22.
  Definition seq23 {var} := Eval vm_compute in @gen_let_sequence var 23.
  Definition seq24 {var} := Eval vm_compute in @gen_let_sequence var 24.
  Definition seq25 {var} := Eval vm_compute in @gen_let_sequence var 25.
  Definition seq26 {var} := Eval vm_compute in @gen_let_sequence var 26.
  Definition seq27 {var} := Eval vm_compute in @gen_let_sequence var 27.
  Definition seq28 {var} := Eval vm_compute in @gen_let_sequence var 28.
  Definition seq29 {var} := Eval vm_compute in @gen_let_sequence var 29.
  Definition seq30 {var} := Eval vm_compute in @gen_let_sequence var 30.
  Definition seq31 {var} := Eval vm_compute in @gen_let_sequence var 31.
  Definition seq32 {var} := Eval vm_compute in @gen_let_sequence var 32.
  Definition seq33 {var} := Eval vm_compute in @gen_let_sequence var 33.
  Definition seq34 {var} := Eval vm_compute in @gen_let_sequence var 34.
  Definition seq35 {var} := Eval vm_compute in @gen_let_sequence var 35.
  Definition seq36 {var} := Eval vm_compute in @gen_let_sequence var 36.
  Definition seq37 {var} := Eval vm_compute in @gen_let_sequence var 37.
  Definition seq38 {var} := Eval vm_compute in @gen_let_sequence var 38.
  Definition seq39 {var} := Eval vm_compute in @gen_let_sequence var 39.
  Definition seq40 {var} := Eval vm_compute in @gen_let_sequence var 40.
  Definition seq41 {var} := Eval vm_compute in @gen_let_sequence var 41.
  Definition seq42 {var} := Eval vm_compute in @gen_let_sequence var 42.
  Definition seq43 {var} := Eval vm_compute in @gen_let_sequence var 43.
  Definition seq44 {var} := Eval vm_compute in @gen_let_sequence var 44.
  Definition seq45 {var} := Eval vm_compute in @gen_let_sequence var 45.
  Definition seq46 {var} := Eval vm_compute in @gen_let_sequence var 46.
  Definition seq47 {var} := Eval vm_compute in @gen_let_sequence var 47.
  Definition seq48 {var} := Eval vm_compute in @gen_let_sequence var 48.
  Definition seq49 {var} := Eval vm_compute in @gen_let_sequence var 49.
  (*Definition exist_idf {var t} e := LetInMonad.denote (@mexist_idf var t e).*)
  (*Definition exist_idf {var t} e := @dexist_idf var t e.*)
  Definition exist_idf {var t} e let_in := @pexist_idf let_in var t e.

  Section with_var.
    Context {var : base_type -> Type}.
    Opaque Let_In.
    Declare Reduction seqr := vm_compute.
    Time Definition seq0' := Eval seqr in @exist_idf var (Tbase Tnat) seq0.
    Time Definition seq1' := Eval seqr in @exist_idf var (Tbase Tnat) seq1.
    Time Definition seq2' := Eval seqr in @exist_idf var (Tbase Tnat) seq2.
    Time Definition seq3' := Eval seqr in @exist_idf var (Tbase Tnat) seq3.
    Time Definition seq4' := Eval seqr in @exist_idf var (Tbase Tnat) seq4.
    Time Definition seq5' := Eval seqr in @exist_idf var (Tbase Tnat) seq5.
    Time Definition seq6' := Eval seqr in @exist_idf var (Tbase Tnat) seq6.
    Time Definition seq7' := Eval seqr in @exist_idf var (Tbase Tnat) seq7.
    Time Definition seq8' := Eval seqr in @exist_idf var (Tbase Tnat) seq8.
    Time Definition seq9' := Eval seqr in @exist_idf var (Tbase Tnat) seq9.
    Time Definition seq10' := Eval seqr in @exist_idf var (Tbase Tnat) seq10.
    Time Definition seq11' := Eval seqr in @exist_idf var (Tbase Tnat) seq11.
    Time Definition seq12' := Eval seqr in @exist_idf var (Tbase Tnat) seq12.
    Time Definition seq13' := Eval seqr in @exist_idf var (Tbase Tnat) seq13.
    Time Definition seq14' := Eval seqr in @exist_idf var (Tbase Tnat) seq14.
    Time Definition seq15' := Eval seqr in @exist_idf var (Tbase Tnat) seq15.
    Time Definition seq16' := Eval seqr in @exist_idf var (Tbase Tnat) seq16.
    Time Definition seq17' := Eval seqr in @exist_idf var (Tbase Tnat) seq17.
    Time Definition seq18' := Eval seqr in @exist_idf var (Tbase Tnat) seq18.
    Time Definition seq19' := Eval seqr in @exist_idf var (Tbase Tnat) seq19.
    Time Definition seq20' := Eval seqr in @exist_idf var (Tbase Tnat) seq20.
    Time Definition seq21' := Eval seqr in @exist_idf var (Tbase Tnat) seq21.
    Time Definition seq22' := Eval seqr in @exist_idf var (Tbase Tnat) seq22.
    Time Definition seq23' := Eval seqr in @exist_idf var (Tbase Tnat) seq23.
    Time Definition seq24' := Eval seqr in @exist_idf var (Tbase Tnat) seq24.
    Time Definition seq25' := Eval seqr in @exist_idf var (Tbase Tnat) seq25.
    Time Definition seq26' := Eval seqr in @exist_idf var (Tbase Tnat) seq26.
    Time Definition seq27' := Eval seqr in @exist_idf var (Tbase Tnat) seq27.
    Time Definition seq28' := Eval seqr in @exist_idf var (Tbase Tnat) seq28.
    Time Definition seq29' := Eval seqr in @exist_idf var (Tbase Tnat) seq29.
    Time Definition seq30' := Eval seqr in @exist_idf var (Tbase Tnat) seq30.
    Time Definition seq31' := Eval seqr in @exist_idf var (Tbase Tnat) seq31.
    Time Definition seq32' := Eval seqr in @exist_idf var (Tbase Tnat) seq32.
    Time Definition seq33' := Eval seqr in @exist_idf var (Tbase Tnat) seq33.
    Time Definition seq34' := Eval seqr in @exist_idf var (Tbase Tnat) seq34.
    Time Definition seq35' := Eval seqr in @exist_idf var (Tbase Tnat) seq35.
    Time Definition seq36' := Eval seqr in @exist_idf var (Tbase Tnat) seq36.
    Time Definition seq37' := Eval seqr in @exist_idf var (Tbase Tnat) seq37.
    Time Definition seq38' := Eval seqr in @exist_idf var (Tbase Tnat) seq38.
    Time Definition seq39' := Eval seqr in @exist_idf var (Tbase Tnat) seq39.
    Time Definition seq40' := Eval seqr in @exist_idf var (Tbase Tnat) seq40.
    Time Definition seq41' := Eval seqr in @exist_idf var (Tbase Tnat) seq41.
    Time Definition seq42' := Eval seqr in @exist_idf var (Tbase Tnat) seq42.
    Time Definition seq43' := Eval seqr in @exist_idf var (Tbase Tnat) seq43.
    Time Definition seq44' := Eval seqr in @exist_idf var (Tbase Tnat) seq44.
    Time Definition seq45' := Eval seqr in @exist_idf var (Tbase Tnat) seq45.
    Time Definition seq46' := Eval seqr in @exist_idf var (Tbase Tnat) seq46.
    Time Definition seq47' := Eval seqr in @exist_idf var (Tbase Tnat) seq47.
    Time Definition seq48' := Eval seqr in @exist_idf var (Tbase Tnat) seq48.
    Time Definition seq49' := Eval seqr in @exist_idf var (Tbase Tnat) seq49.
  End with_var.
End dependent_sigma_eq.
