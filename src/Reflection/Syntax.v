(** * PHOAS Representation of Gallina *)
Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

(** We parameterize the language over a type of basic type codes (for
    things like [Z], [word], [bool]), as well as a type of n-ary
    operations returning one value, and n-ary operations returning two
    values. *)
Delimit Scope ctype_scope with ctype.
Local Open Scope ctype_scope.
Delimit Scope expr_scope with expr.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type).

  Inductive flat_type := Tbase (_ : base_type_code) | Prod (x y : flat_type).
  Bind Scope ctype_scope with flat_type.

  Inductive type := Tflat (_ : flat_type) | Arrow (x : base_type_code) (y : type).
  Bind Scope ctype_scope with type.

  Global Coercion Tflat : flat_type >-> type.
  Infix "*" := Prod : ctype_scope.
  Notation "A -> B" := (Arrow A B) : ctype_scope.
  Local Coercion Tbase : base_type_code >-> flat_type.

  Section interp.
    Section type.
      Context (interp_flat_type : flat_type -> Type).
      Fixpoint interp_type_gen (t : type) :=
        match t with
        | Tflat t => interp_flat_type t
        | Arrow x y => (interp_flat_type x -> interp_type_gen y)%type
        end.
      Section rel.
        Context (R : forall t, interp_flat_type t -> interp_flat_type t -> Prop).
        Fixpoint interp_type_gen_rel_pointwise (t : type)
          : interp_type_gen t -> interp_type_gen t -> Prop :=
          match t with
          | Tflat t => R t
          | Arrow _ y => fun f g => forall x, interp_type_gen_rel_pointwise y (f x) (g x)
          end.
        Global Instance interp_type_gen_rel_pointwise_Reflexive {H : forall t, Reflexive (R t)}
          : forall t, Reflexive (interp_type_gen_rel_pointwise t).
        Proof. induction t; repeat intro; reflexivity. Qed.
        Global Instance interp_type_gen_rel_pointwise_Symmetric {H : forall t, Symmetric (R t)}
          : forall t, Symmetric (interp_type_gen_rel_pointwise t).
        Proof. induction t; simpl; repeat intro; symmetry; eauto. Qed.
        Global Instance interp_type_gen_rel_pointwise_Transitive {H : forall t, Transitive (R t)}
          : forall t, Transitive (interp_type_gen_rel_pointwise t).
        Proof. induction t; simpl; repeat intro; etransitivity; eauto. Qed.
      End rel.
    End type.
    Section flat_type.
      Context (interp_base_type : base_type_code -> Type).
      Fixpoint interp_flat_type_gen (t : flat_type) :=
        match t with
        | Tbase t => interp_base_type t
        | Prod x y => prod (interp_flat_type_gen x) (interp_flat_type_gen y)
        end.
      Definition interp_type := interp_type_gen interp_flat_type_gen.
      Section rel.
        Context (R : forall t, interp_base_type t -> interp_base_type t -> Prop).
        Fixpoint interp_flat_type_gen_rel_pointwise (t : flat_type)
          : interp_flat_type_gen t -> interp_flat_type_gen t -> Prop :=
          match t with
          | Tbase t => R t
          | Prod _ _ => fun x y => interp_flat_type_gen_rel_pointwise _ (fst x) (fst y)
                               /\ interp_flat_type_gen_rel_pointwise _ (snd x) (snd y)
          end.
      End rel.
    End flat_type.
  End interp.

  Section expr_param.
    Context (interp_base_type : base_type_code -> Type).
    Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
    Section expr.
      Context {var : base_type_code -> Type}.

      (** N.B. [Let] binds the components of a pair to separate variables, and does so recursively *)
      Inductive exprf : flat_type -> Type :=
      | Const {t : flat_type} : interp_type t -> exprf t
      | Var {t} : var t -> exprf t
      | Op {t1 tR} : op t1 tR -> exprf t1 -> exprf tR
      | LetIn : forall {tx}, exprf tx -> forall {tC}, (interp_flat_type_gen var tx -> exprf tC) -> exprf tC
      | Pair : forall {t1}, exprf t1 -> forall {t2}, exprf t2 -> exprf (Prod t1 t2).
      Bind Scope expr_scope with exprf.
      Inductive expr : type -> Type :=
      | Return {t} : exprf t -> expr t
      | Abs {src dst} : (var src -> expr dst) -> expr (Arrow src dst).
      Bind Scope expr_scope with expr.
      Global Coercion Return : exprf >-> expr.
      (** Sometimes, we want to deal with partially-interpreted
          expressions, things like [prod (exprf A) (exprf B)] rather
          than [exprf (Prod A B)], or like [prod (var A) (var B)] when
          we start with the type [Prod A B].  These convenience
          functions let us recurse on the type in only one place, and
          replace one kind of pairing operator (be it [pair] or [Pair]
          or anything else) with another kind, and simultaneously
          mapping a function over the base values (e.g., [Var] (for
          turning [var] into [exprf]) or [Const] (for turning
          [interp_base_type] into [exprf])). *)
      Fixpoint smart_interp_flat_map {f g}
               (h : forall x, f x -> g (Tbase x))
               (pair : forall A B, g A -> g B -> g (Prod A B))
               {t}
        : interp_flat_type_gen f t -> g t
        := match t return interp_flat_type_gen f t -> g t with
           | Tbase _ => h _
           | Prod A B => fun v => pair _ _
                                       (@smart_interp_flat_map f g h pair A (fst v))
                                       (@smart_interp_flat_map f g h pair B (snd v))
           end.
      Fixpoint SmartVal {T} (val : forall t : base_type_code, T t) t : interp_flat_type_gen T t
        := match t return interp_flat_type_gen T t with
           | Tbase _ => val _
           | Prod A B => (@SmartVal T val A, @SmartVal T val B)
           end.

      (** [SmartVar] is like [Var], except that it inserts
          pair-projections and [Pair] as necessary to handle
          [flat_type], and not just [base_type_code] *)
      Definition SmartVar {t} : interp_flat_type_gen var t -> exprf t
        := @smart_interp_flat_map var exprf (fun t => Var) (fun A B x y => Pair x y) t.
      Definition SmartVarVar {t} : interp_flat_type_gen var t -> interp_flat_type_gen exprf t
        := @smart_interp_flat_map var (interp_flat_type_gen exprf) (fun t => Var) (fun A B x y => pair x y) t.
      Definition SmartConst {t} : interp_flat_type t -> interp_flat_type_gen exprf t
        := @smart_interp_flat_map _ (interp_flat_type_gen exprf) (fun t => Const) (fun A B x y => pair x y) t.
    End expr.

    Definition Expr (t : type) := forall var, @expr var t.

    Section interp.
      Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Fixpoint interpf {t} (e : @exprf interp_flat_type t) : interp_flat_type t
        := match e in exprf t return interp_flat_type t with
           | Const _ x => x
           | Var _ x => x
           | Op _ _ op args => @interp_op _ _ op (@interpf _ args)
           | LetIn _ ex _ eC => let x := @interpf _ ex in @interpf _ (eC x)
           | Pair _ ex _ ey => (@interpf _ ex, @interpf _ ey)
           end.
      Fixpoint interp {t} (e : @expr interp_type t) : interp_type t
        := match e in expr t return interp_type t with
           | Return _ x => interpf x
           | Abs _ _ f => fun x => @interp _ (f x)
           end.

      Definition Interp {t} (E : Expr t) : interp_type t := interp (E _).
    End interp.

    Section map.
      Context {var1 var2 : base_type_code -> Type}.
      Context (fvar12 : forall t, var1 t -> var2 t)
              (fvar21 : forall t, var2 t -> var1 t).

      Fixpoint mapf_interp_flat_type_gen {t} (e : interp_flat_type_gen var2 t) {struct t}
        : interp_flat_type_gen var1 t
        := match t return interp_flat_type_gen _ t -> interp_flat_type_gen _ t with
           | Tbase _ => fvar21 _
           | Prod x y => fun xy => (@mapf_interp_flat_type_gen _ (fst xy),
                                    @mapf_interp_flat_type_gen _ (snd xy))
           end e.

      Fixpoint mapf {t} (e : @exprf var1 t) : @exprf var2 t
        := match e in exprf t return exprf t with
           | Const _ x => Const x
           | Var _ x => Var (fvar12 _ x)
           | Op _ _ op args => Op op (@mapf _ args)
           | LetIn _ ex _ eC => LetIn (@mapf _ ex) (fun x => @mapf _ (eC (mapf_interp_flat_type_gen x)))
           | Pair _ ex _ ey => Pair (@mapf _ ex) (@mapf _ ey)
           end.
    End map.

    Section misc.
      Definition invert_Const {var t} (e : @exprf var t) : option (interp_type t)
        := match e with
           | Const _ v => Some v
           | _ => None
           end.
    End misc.

    Section wf.
      Context {var1 var2 : base_type_code -> Type}.

      Local Notation eP := (fun t => var1 t * var2 t)%type (only parsing).
      Local Notation "x == y" := (existT eP _ (x, y)).
      Fixpoint flatten_binding_list {t} (x : interp_flat_type_gen var1 t) (y : interp_flat_type_gen var2 t) : list (sigT eP)
        := (match t return interp_flat_type_gen var1 t -> interp_flat_type_gen var2 t -> list _ with
            | Tbase _ => fun x y => (x == y) :: nil
            | Prod t0 t1 => fun x y => @flatten_binding_list _ (snd x) (snd y) ++ @flatten_binding_list _ (fst x) (fst y)
            end x y)%list.

      Inductive wff : list (sigT eP) -> forall {t}, @exprf var1 t -> @exprf var2 t -> Prop :=
      | WfConst : forall t G n, @wff G t (Const n) (Const n)
      | WfVar : forall G (t : base_type_code) x x', List.In (x == x') G -> @wff G t (Var x) (Var x')
      | WfOp : forall G {t} {tR} (e : @exprf var1 t) (e' : @exprf var2 t) op,
          wff G e e'
          -> wff G (Op (tR := tR) op e) (Op (tR := tR) op e')
      | WfLetIn : forall G t1 t2 e1 e1' (e2 : interp_flat_type_gen var1 t1 -> @exprf var1 t2) e2',
          wff G e1 e1'
          -> (forall x1 x2, wff (flatten_binding_list x1 x2 ++ G) (e2 x1) (e2' x2))
          -> wff G (LetIn e1 e2) (LetIn e1' e2')
      | WfPair : forall G {t1} {t2} (e1: @exprf var1 t1) (e2: @exprf var1 t2)
                        (e1': @exprf var2 t1) (e2': @exprf var2 t2),
          wff G e1 e1'
          -> wff G e2 e2'
          -> wff G (Pair e1 e2) (Pair e1' e2').
      Inductive wf : list (sigT eP) -> forall {t}, @expr var1 t -> @expr var2 t -> Prop :=
      | WfReturn : forall t G e e', @wff G t e e' -> wf G (Return e) (Return e')
      | WfAbs : forall A B G e e',
          (forall x x', @wf ((x == x') :: G) B (e x) (e' x'))
          -> @wf G (Arrow A B) (Abs e) (Abs e').
    End wf.

    Definition Wf {t} (E : @Expr t) := forall var1 var2, wf nil (E var1) (E var2).

    Axiom Wf_admitted : forall {t} (E:Expr t), @Wf t E.
  End expr_param.
End language.
Global Arguments Prod {_} _ _.
Global Arguments Arrow {_} _ _.
Global Arguments Tbase {_} _.
Infix "*" := (@Prod _) : ctype_scope.
Notation "A -> B" := (@Arrow _ A B) : ctype_scope.

Ltac admit_Wf := apply Wf_admitted.

Global Arguments Const {_ _ _ _ _} _.
Global Arguments Var {_ _ _ _ _} _.
Global Arguments SmartVar {_ _ _ _ _} _.
Global Arguments SmartVal {_} T _ t.
Global Arguments SmartVarVar {_ _ _ _ _} _.
Global Arguments SmartConst {_ _ _ _ _} _.
Global Arguments Op {_ _ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _ _} _.
Global Arguments Abs {_ _ _ _ _ _} _.
Global Arguments interp_type_gen {_} _ _.
Global Arguments interp_flat_type_gen {_} _ _.
Global Arguments interp_type_gen_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_flat_type_gen_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_type {_} _ _.
Global Arguments wff {_ _ _ _ _} G {t} _ _.
Global Arguments wf {_ _ _ _ _} G {t} _ _.
Global Arguments Wf {_ _ _ t} _.
Global Arguments Interp {_ _ _} interp_op {t} _.
Global Arguments interp {_ _ _} interp_op {t} _.
Global Arguments interpf {_ _ _} interp_op {t} _.
Global Arguments invert_Const {_ _ _ _ _} _.

Notation "'slet' x := A 'in' b" := (LetIn A (fun x => b)) : expr_scope.
Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
