(** * PHOAS Representation of Gallina *)
Require Import Coq.Strings.String Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
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

  Fixpoint tuple' T n :=
    match n with
    | O => T
    | S n' => (tuple' T n' * T)%ctype
    end.
  Definition tuple T n :=
    match n with
    | O => T (* default value; no empty tuple *)
    | S n' => tuple' T n'
    end.

  Section interp.
    Section type.
      Section hetero.
        Context (interp_src_type : base_type_code -> Type).
        Context (interp_flat_type : flat_type -> Type).
        Fixpoint interp_type_gen_hetero (t : type) :=
          match t with
          | Tflat t => interp_flat_type t
          | Arrow x y => (interp_src_type x -> interp_type_gen_hetero y)%type
          end.
      End hetero.
      Section homogenous.
        Context (interp_flat_type : flat_type -> Type).
        Definition interp_type_gen := interp_type_gen_hetero interp_flat_type interp_flat_type.
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
      End homogenous.
    End type.
    Section flat_type.
      Context (interp_base_type : base_type_code -> Type).
      Fixpoint interp_flat_type (t : flat_type) :=
        match t with
        | Tbase t => interp_base_type t
        | Prod x y => prod (interp_flat_type x) (interp_flat_type y)
        end.
      Definition interp_type := interp_type_gen interp_flat_type.
      Fixpoint flat_interp_tuple' {T n} : interp_flat_type (tuple' T n) -> Tuple.tuple' (interp_flat_type T) n
        := match n return interp_flat_type (tuple' T n) -> Tuple.tuple' (interp_flat_type T) n with
           | O => fun x => x
           | S n' => fun xy => (@flat_interp_tuple' _ n' (fst xy), snd xy)
           end.
      Definition flat_interp_tuple {T n} : interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n
        := match n return interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n with
           | O => fun _ => tt
           | S n' => @flat_interp_tuple' T n'
           end.
      Fixpoint flat_interp_untuple' {T n} : Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n)
        := match n return Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n) with
           | O => fun x => x
           | S n' => fun xy => (@flat_interp_untuple' _ n' (fst xy), snd xy)
           end.
      Lemma flat_interp_untuple'_tuple' {T n v}
        : @flat_interp_untuple' T n (flat_interp_tuple' v) = v.
      Proof. induction n; [ reflexivity | simpl; rewrite IHn; destruct v; reflexivity ]. Qed.
      Lemma flat_interp_untuple'_tuple {T n v}
        : flat_interp_untuple' (@flat_interp_tuple T (S n) v) = v.
      Proof. apply flat_interp_untuple'_tuple'. Qed.
      Lemma flat_interp_tuple'_untuple' {T n v}
        : @flat_interp_tuple' T n (flat_interp_untuple' v) = v.
      Proof. induction n; [ reflexivity | simpl; rewrite IHn; destruct v; reflexivity ]. Qed.
      Lemma flat_interp_tuple_untuple' {T n v}
        : @flat_interp_tuple T (S n) (flat_interp_untuple' v) = v.
      Proof. apply flat_interp_tuple'_untuple'. Qed.
      Section rel.
        Context (R : forall t, interp_base_type t -> interp_base_type t -> Prop).
        Fixpoint interp_flat_type_rel_pointwise (t : flat_type)
          : interp_flat_type t -> interp_flat_type t -> Prop :=
          match t with
          | Tbase t => R t
          | Prod _ _ => fun x y => interp_flat_type_rel_pointwise _ (fst x) (fst y)
                                   /\ interp_flat_type_rel_pointwise _ (snd x) (snd y)
          end.
        Definition interp_type_rel_pointwise
          := interp_type_gen_rel_pointwise _ interp_flat_type_rel_pointwise.
      End rel.
    End flat_type.
    Section rel_pointwise2.
      Section type.
        Section hetero.
          Context (interp_src1 interp_src2 : base_type_code -> Type)
                  (interp_flat_type1 interp_flat_type2 : flat_type -> Type)
                  (Rsrc : forall t, interp_src1 t -> interp_src2 t -> Prop)
                  (R : forall t, interp_flat_type1 t -> interp_flat_type2 t -> Prop).

          Fixpoint interp_type_gen_rel_pointwise2_hetero (t : type)
            : interp_type_gen_hetero interp_src1 interp_flat_type1 t
              -> interp_type_gen_hetero interp_src2 interp_flat_type2 t
              -> Prop
            := match t with
               | Tflat t => R t
               | Arrow src dst => @respectful_hetero _ _ _ _ (Rsrc src) (fun _ _ => interp_type_gen_rel_pointwise2_hetero dst)
               end.
        End hetero.
        Section homogenous.
          Context (interp_flat_type1 interp_flat_type2 : flat_type -> Type)
                  (R : forall t, interp_flat_type1 t -> interp_flat_type2 t -> Prop).

          Definition interp_type_gen_rel_pointwise2
            := interp_type_gen_rel_pointwise2_hetero interp_flat_type1 interp_flat_type2
                                                     interp_flat_type1 interp_flat_type2
                                                     R R.
        End homogenous.
      End type.
      Section flat_type.
        Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
        Section gen_prop.
          Context (P : Type)
                  (and : P -> P -> P)
                  (R : forall t, interp_base_type1 t -> interp_base_type2 t -> P).

          Fixpoint interp_flat_type_rel_pointwise2_gen_Prop (t : flat_type)
            : interp_flat_type interp_base_type1 t -> interp_flat_type interp_base_type2 t -> P
            := match t with
               | Tbase t => R t
               | Prod x y => fun a b => and (interp_flat_type_rel_pointwise2_gen_Prop x (fst a) (fst b))
                                            (interp_flat_type_rel_pointwise2_gen_Prop y (snd a) (snd b))
               end.
        End gen_prop.

        Definition interp_flat_type_rel_pointwise2
          := @interp_flat_type_rel_pointwise2_gen_Prop Prop and.

        Definition interp_type_rel_pointwise2 R
          := interp_type_gen_rel_pointwise2 _ _ (interp_flat_type_rel_pointwise2 R).
      End flat_type.
    End rel_pointwise2.
  End interp.

  Section expr_param.
    Context (interp_base_type : base_type_code -> Type).
    Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).
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
      Definition UnReturn {t} (e : expr (Tflat t)) : exprf t
        := match e with
           | Return _ v => v
           | Abs _ _ _ => I
           end.
      Definition UnAbs {src dst} (e : expr (Arrow src dst)) : var src -> expr dst
        := match e with
           | Return _ _ => I
           | Abs _ _ f => f
           end.
      Definition UnReturn_eta {t} (e : expr (Tflat t)) : Return (UnReturn e) = e
        := match e in expr T return match T return expr T -> Prop with
                                    | Tflat _ => fun e => Return (UnReturn e) = e
                                    | _ => fun _ => I = I
                                    end e with
           | Return _ _ => eq_refl
           | Abs _ _ _ => eq_refl
           end.
      Definition UnAbs_eta {src dst} (e : expr (Arrow src dst)) : Abs (UnAbs e) = e
        := match e in expr T return match T return expr T -> Prop with
                                    | Arrow src dst => fun e => Abs (UnAbs e) = e
                                    | _ => fun _ => I = I
                                    end e with
           | Return _ _ => eq_refl
           | Abs _ _ _ => eq_refl
           end.
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
      Fixpoint smart_interp_map_hetero {f g g'}
               (h : forall x, f x -> g (Tflat (Tbase x)))
               (pair : forall A B, g (Tflat A) -> g (Tflat B) -> g (Prod A B))
               (abs : forall A B, (g' A -> g B) -> g (Arrow A B))
               {t}
        : interp_type_gen_hetero g' (interp_flat_type_gen f) t -> g t
        := match t return interp_type_gen_hetero g' (interp_flat_type_gen f) t -> g t with
           | Tflat _ => @smart_interp_flat_map f (fun x => g (Tflat x)) h pair _
           | Arrow A B => fun v => abs _ _
                                       (fun x => @smart_interp_map_hetero f g g' h pair abs B (v x))
           end.
      Fixpoint smart_interp_map {f g}
                 (h : forall x, f x -> g (Tflat (Tbase x)))
                 (h' : forall x, g (Tflat (Tbase x)) -> f x)
                 (pair : forall A B, g (Tflat A) -> g (Tflat B) -> g (Prod A B))
                 (abs : forall A B, (g (Tflat (Tbase A)) -> g B) -> g (Arrow A B))
                 {t}
        : interp_type_gen (interp_flat_type_gen f) t -> g t
        := match t return interp_type_gen (interp_flat_type_gen f) t -> g t with
           | Tflat _ => @smart_interp_flat_map f (fun x => g (Tflat x)) h pair _
           | Arrow A B => fun v => abs _ _
                                       (fun x => @smart_interp_map f g h h' pair abs B (v (h' _ x)))
           end.
      Fixpoint SmartValf {T} (val : forall t : base_type_code, T t) t : interp_flat_type_gen T t
        := match t return interp_flat_type_gen T t with
           | Tbase _ => val _
           | Prod A B => (@SmartValf T val A, @SmartValf T val B)
           end.
      Fixpoint SmartArrow (A : flat_type) (B : type) : type
        := match A with
           | Tbase A' => Arrow A' B
           | Prod A0 A1
             => SmartArrow A0 (SmartArrow A1 B)
           end.
      Fixpoint SmartAbs {A B} {struct A} : forall (f : exprf A -> expr B), expr (SmartArrow A B)
        := match A return (exprf A -> expr B) -> expr (SmartArrow A B) with
           | Tbase x => fun f => Abs (fun x => f (Var x))
           | Prod x y => fun f => @SmartAbs x _ (fun x' => @SmartAbs y _ (fun y' => f (Pair x' y')))
           end.

      (** [SmartVar] is like [Var], except that it inserts
          pair-projections and [Pair] as necessary to handle
          [flat_type], and not just [base_type_code] *)
      Definition SmartVarf {t} : interp_flat_type_gen var t -> exprf t
        := @smart_interp_flat_map var exprf (fun t => Var) (fun A B x y => Pair x y) t.
      Definition SmartVarfMap {var var'} (f : forall t, var t -> var' t) {t}
        : interp_flat_type_gen var t -> interp_flat_type_gen var' t
        := @smart_interp_flat_map var (interp_flat_type_gen var') f (fun A B x y => pair x y) t.
      Definition SmartFlatTypeMap {var'} (f : forall t, var' t -> base_type_code) {t}
        : interp_flat_type_gen var' t -> flat_type
        := @smart_interp_flat_map var' (fun _ => flat_type) f (fun _ _ => Prod) t.
      Fixpoint SmartFlatTypeMapInterp {var' var''} (f : forall t, var' t -> base_type_code)
                 (fv : forall t v, var'' (f t v)) {t} {struct t}
        : forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v)
        := match t return forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v) with
           | Tbase x => fv _
           | Prod A B => fun xy => (@SmartFlatTypeMapInterp _ _ f fv A (fst xy),
                                    @SmartFlatTypeMapInterp _ _ f fv B (snd xy))
           end.
      Definition SmartVarMap {var var'} (f : forall t, var t -> var' t) (f' : forall t, var' t -> var t) {t}
        : interp_type_gen (interp_flat_type_gen var) t -> interp_type_gen (interp_flat_type_gen var') t
        := @smart_interp_map var (interp_type_gen (interp_flat_type_gen var')) f f' (fun A B x y => pair x y) (fun A B f x => f x) t.
      Definition SmartVarMap_hetero {vars vars' var var'} (f : forall t, var t -> var' t) (f' : forall t, vars' t -> vars t) {t}
        : interp_type_gen_hetero vars (interp_flat_type_gen var) t -> interp_type_gen_hetero vars' (interp_flat_type_gen var') t
        := @smart_interp_map_hetero var (interp_type_gen_hetero vars' (interp_flat_type_gen var')) vars f (fun A B x y => pair x y) (fun A B f x => f (f' _ x)) t.
      Definition SmartVarVarf {t} : interp_flat_type_gen var t -> interp_flat_type_gen exprf t
        := SmartVarfMap (fun t => Var).
      Definition SmartConstf {t} : interp_flat_type t -> interp_flat_type_gen exprf t
        := SmartVarfMap (fun t => Const (t:=t)).
    End expr.

    Definition Expr (t : type) := forall var, @expr var t.

    Section interp.
      Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Definition interpf_step
                 (interpf : forall {t} (e : @exprf interp_flat_type t), interp_flat_type t)
                 {t} (e : @exprf interp_flat_type t) : interp_flat_type t
        := match e in exprf t return interp_flat_type t with
           | Const _ x => x
           | Var _ x => x
           | Op _ _ op args => @interp_op _ _ op (@interpf _ args)
           | LetIn _ ex _ eC => dlet x := @interpf _ ex in @interpf _ (eC x)
           | Pair _ ex _ ey => (@interpf _ ex, @interpf _ ey)
           end.

      Fixpoint interpf {t} e
        := @interpf_step (@interpf) t e.

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

      Fixpoint mapf_interp_flat_type {t} (e : interp_flat_type_gen var2 t) {struct t}
        : interp_flat_type_gen var1 t
        := match t return interp_flat_type_gen _ t -> interp_flat_type_gen _ t with
           | Tbase _ => fvar21 _
           | Prod x y => fun xy => (@mapf_interp_flat_type _ (fst xy),
                                    @mapf_interp_flat_type _ (snd xy))
           end e.

      Fixpoint mapf {t} (e : @exprf var1 t) : @exprf var2 t
        := match e in exprf t return exprf t with
           | Const _ x => Const x
           | Var _ x => Var (fvar12 _ x)
           | Op _ _ op args => Op op (@mapf _ args)
           | LetIn _ ex _ eC => LetIn (@mapf _ ex) (fun x => @mapf _ (eC (mapf_interp_flat_type x)))
           | Pair _ ex _ ey => Pair (@mapf _ ex) (@mapf _ ey)
           end.
    End map.

    Section misc.
      Definition invert_Const {var t} (e : @exprf var t) : option (interp_type t)
        := match e with
           | Const _ v => Some v
           | _ => None
           end.
      Definition invert_Pair {var A B} (e : @exprf var (Prod A B)) : option (exprf A * exprf B)
        := match e in @exprf _ t return option match t with
                                               | Prod _ _ => _
                                               | _ => unit
                                               end with
           | Pair _ x _ y => Some (x, y)%core
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
Global Arguments tuple' {_}%type_scope _%ctype_scope _%nat_scope.
Global Arguments tuple {_}%type_scope _%ctype_scope _%nat_scope.
Global Arguments Prod {_}%type_scope (_ _)%ctype_scope.
Global Arguments Arrow {_}%type_scope (_ _)%ctype_scope.
Global Arguments Tbase {_}%type_scope _%ctype_scope.

Ltac admit_Wf := apply Wf_admitted.

Scheme Equality for flat_type.
Scheme Equality for type.

Global Instance dec_eq_flat_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (flat_type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; auto.
Defined.
Global Instance dec_eq_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; typeclasses eauto.
Defined.

Global Arguments Const {_ _ _ _ _} _.
Global Arguments Var {_ _ _ _ _} _.
Global Arguments SmartVarf {_ _ _ _ _} _.
Global Arguments SmartValf {_} T _ t.
Global Arguments SmartVarVarf {_ _ _ _ _} _.
Global Arguments SmartVarfMap {_ _ _} _ {_} _.
Global Arguments SmartFlatTypeMap {_ _} _ {_} _.
Global Arguments SmartFlatTypeMapInterp {_ _ _ _} _ {_} _.
Global Arguments SmartVarMap_hetero {_ _ _ _ _} _ _ {_} _.
Global Arguments SmartVarMap {_ _ _} _ _ {_} _.
Global Arguments SmartConstf {_ _ _ _ _} _.
Global Arguments Op {_ _ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _ _} _.
Global Arguments Abs {_ _ _ _ _ _} _.
Global Arguments SmartAbs {_ _ _ _ _ _} _.
Global Arguments UnReturn {_ _ _ _ _} _.
Global Arguments UnAbs {_ _ _ _ _ _} _ _.
Global Arguments UnReturn_eta {_ _ _ _ _} _.
Global Arguments UnAbs_eta {_ _ _ _ _ _} _.
Global Arguments flat_interp_tuple' {_ _ _ _} _.
Global Arguments flat_interp_tuple {_ _ _ _} _.
Global Arguments flat_interp_untuple' {_ _ _ _} _.
Global Arguments interp_type_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments interp_type_gen_rel_pointwise2_hetero {_ _ _ _ _} Rsrc R {t} _ _.
Global Arguments interp_type_gen_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise2_gen_Prop {_ _ _ P} and R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments mapf_interp_flat_type {_ _ _} _ {t} _.
Global Arguments interp_type_gen_hetero {_} _ _ _.
Global Arguments interp_type_gen {_} _ _.
Global Arguments interp_flat_type {_} _ _.
Global Arguments interp_type_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_type_gen_rel_pointwise {_ _} _ {_} _ _.
Global Arguments interp_flat_type_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_type {_} _ _.
Global Arguments wff {_ _ _ _ _} G {t} _ _.
Global Arguments wf {_ _ _ _ _} G {t} _ _.
Global Arguments Wf {_ _ _ t} _.
Global Arguments Interp {_ _ _} interp_op {t} _.
Global Arguments interp {_ _ _} interp_op {t} _.
Global Arguments interpf {_ _ _} interp_op {t} _.
Global Arguments invert_Const {_ _ _ _ _} _.

Module Export Notations.
  Notation "A * B" := (@Prod _ A B) : ctype_scope.
  Notation "A -> B" := (@Arrow _ A B) : ctype_scope.
  Notation "'slet' x := A 'in' b" := (LetIn A (fun x => b)) : expr_scope.
  Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
  Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
  Bind Scope ctype_scope with flat_type.
  Bind Scope ctype_scope with type.
End Notations.
