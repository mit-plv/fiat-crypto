(** * PHOAS Representation of Gallina *)
Require Import Coq.Strings.String Coq.Classes.RelationClasses Coq.Classes.Morphisms.
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

  Inductive flat_type := Tbase (T : base_type_code) | Unit | Prod (A B : flat_type).
  Bind Scope ctype_scope with flat_type.

  Inductive type := Tflat (T : flat_type) | Arrow (A : base_type_code) (B : type).
  Bind Scope ctype_scope with type.

  Global Coercion Tflat : flat_type >-> type.
  Infix "*" := Prod : ctype_scope.
  Notation "A -> B" := (Arrow A B) : ctype_scope.
  Local Coercion Tbase : base_type_code >-> flat_type.

  Section tuple.
    Context (T : flat_type).
    Fixpoint tuple' n :=
      match n with
      | O => T
      | S n' => (tuple' n' * T)%ctype
      end.
    Definition tuple n :=
      match n with
      | O => Unit
      | S n' => tuple' n'
      end.
  End tuple.

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
      Definition interp_type_gen (interp_flat_type : flat_type -> Type)
        := interp_type_gen_hetero interp_flat_type interp_flat_type.
    End type.
    Section flat_type.
      Context (interp_base_type : base_type_code -> Type).
      Fixpoint interp_flat_type (t : flat_type) :=
        match t with
        | Tbase t => interp_base_type t
        | Unit => unit
        | Prod x y => prod (interp_flat_type x) (interp_flat_type y)
        end.
      Definition interp_type := interp_type_gen interp_flat_type.
    End flat_type.
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
      | TT : exprf Unit
      | Var {t} (v : var t) : exprf t
      | Op {t1 tR} (opc : op t1 tR) (args : exprf t1) : exprf tR
      | LetIn {tx} (ex : exprf tx) {tC} (eC : interp_flat_type_gen var tx -> exprf tC) : exprf tC
      | Pair {tx} (ex : exprf tx) {ty} (ey : exprf ty) : exprf (Prod tx ty).
      Bind Scope expr_scope with exprf.
      Inductive expr : type -> Type :=
      | Return {t} (ex : exprf t) : expr t
      | Abs {src dst} (f : var src -> expr dst) : expr (Arrow src dst).
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
               (tt : g Unit)
               (pair : forall A B, g A -> g B -> g (Prod A B))
               {t}
        : interp_flat_type_gen f t -> g t
        := match t return interp_flat_type_gen f t -> g t with
           | Tbase _ => h _
           | Unit => fun _ => tt
           | Prod A B => fun v => pair _ _
                                       (@smart_interp_flat_map f g h tt pair A (fst v))
                                       (@smart_interp_flat_map f g h tt pair B (snd v))
           end.
      Fixpoint smart_interp_flat_map2 {f1 f2 g}
               (h : forall x, f1 x -> f2 x -> g (Tbase x))
               (tt : g Unit)
               (pair : forall A B, g A -> g B -> g (Prod A B))
               {t}
        : interp_flat_type_gen f1 t -> interp_flat_type_gen f2 t -> g t
        := match t return interp_flat_type_gen f1 t -> interp_flat_type_gen f2 t -> g t with
           | Tbase _ => h _
           | Unit => fun _ _ => tt
           | Prod A B => fun v1 v2 => pair _ _
                                           (@smart_interp_flat_map2 f1 f2 g h tt pair A (fst v1) (fst v2))
                                           (@smart_interp_flat_map2 f1 f2 g h tt pair B (snd v1) (snd v2))
           end.
      Fixpoint smart_interp_map_hetero {f g g'}
               (h : forall x, f x -> g (Tflat (Tbase x)))
               (tt : g Unit)
               (pair : forall A B, g (Tflat A) -> g (Tflat B) -> g (Prod A B))
               (abs : forall A B, (g' A -> g B) -> g (Arrow A B))
               {t}
        : interp_type_gen_hetero g' (interp_flat_type_gen f) t -> g t
        := match t return interp_type_gen_hetero g' (interp_flat_type_gen f) t -> g t with
           | Tflat _ => @smart_interp_flat_map f (fun x => g (Tflat x)) h tt pair _
           | Arrow A B => fun v => abs _ _
                                       (fun x => @smart_interp_map_hetero f g g' h tt pair abs B (v x))
           end.
      Fixpoint smart_interp_map_gen {f g}
                 (h : forall x, f x -> g (Tflat (Tbase x)))
                 (h' : forall x, g (Tflat (Tbase x)) -> f x)
                 (flat_map : forall t, interp_flat_type_gen f t -> g t)
                 (abs : forall A B, (g (Tflat (Tbase A)) -> g B) -> g (Arrow A B))
                 {t}
        : interp_type_gen (interp_flat_type_gen f) t -> g t
        := match t return interp_type_gen (interp_flat_type_gen f) t -> g t with
           | Tflat T => flat_map T
           | Arrow A B => fun v => abs _ _
                                       (fun x => @smart_interp_map_gen f g h h' flat_map abs B (v (h' _ x)))
           end.
      Definition smart_interp_map {f g}
                 (h : forall x, f x -> g (Tflat (Tbase x)))
                 (h' : forall x, g (Tflat (Tbase x)) -> f x)
                 (tt : g Unit)
                 (pair : forall A B, g (Tflat A) -> g (Tflat B) -> g (Prod A B))
                 (abs : forall A B, (g (Tflat (Tbase A)) -> g B) -> g (Arrow A B))
                 {t}
        : interp_type_gen (interp_flat_type_gen f) t -> g t
        := @smart_interp_map_gen f g h h' (@smart_interp_flat_map f (fun x => g (Tflat x)) h tt pair) abs t.
      Fixpoint SmartValf {T} (val : forall t : base_type_code, T t) t : interp_flat_type_gen T t
        := match t return interp_flat_type_gen T t with
           | Tbase _ => val _
           | Unit => tt
           | Prod A B => (@SmartValf T val A, @SmartValf T val B)
           end.
      Fixpoint SmartArrow (A : flat_type) (B : type) : type
        := match A with
           | Tbase A' => Arrow A' B
           | Unit => B
           | Prod A0 A1
             => SmartArrow A0 (SmartArrow A1 B)
           end.
      Fixpoint SmartAbs {A B} {struct A} : forall (f : exprf A -> expr B), expr (SmartArrow A B)
        := match A return (exprf A -> expr B) -> expr (SmartArrow A B) with
           | Tbase x => fun f => Abs (fun x => f (Var x))
           | Unit => fun f => f TT
           | Prod x y => fun f => @SmartAbs x _ (fun x' => @SmartAbs y _ (fun y' => f (Pair x' y')))
           end.

      (** [SmartVar] is like [Var], except that it inserts
          pair-projections and [Pair] as necessary to handle
          [flat_type], and not just [base_type_code] *)
      Definition SmartPairf {t} : interp_flat_type_gen exprf t -> exprf t
        := @smart_interp_flat_map exprf exprf (fun t x => x) TT (fun A B x y => Pair x y) t.
      Definition SmartVarf {t} : interp_flat_type_gen var t -> exprf t
        := @smart_interp_flat_map var exprf (fun t => Var) TT (fun A B x y => Pair x y) t.
      Definition SmartVarfMap {var var'} (f : forall t, var t -> var' t) {t}
        : interp_flat_type_gen var t -> interp_flat_type_gen var' t
        := @smart_interp_flat_map var (interp_flat_type_gen var') f tt (fun A B x y => pair x y) t.
      Definition SmartVarfMap2 {var var' var''} (f : forall t, var t -> var' t -> var'' t) {t}
        : interp_flat_type_gen var t -> interp_flat_type_gen var' t -> interp_flat_type_gen var'' t
        := @smart_interp_flat_map2 var var' (interp_flat_type_gen var'') f tt (fun A B x y => pair x y) t.
      Definition SmartFlatTypeMap {var'} (f : forall t, var' t -> base_type_code) {t}
        : interp_flat_type_gen var' t -> flat_type
        := @smart_interp_flat_map var' (fun _ => flat_type) f Unit (fun _ _ => Prod) t.
      Fixpoint SmartFlatTypeMapInterp {var' var''} (f : forall t, var' t -> base_type_code)
                 (fv : forall t v, var'' (f t v)) t {struct t}
        : forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v)
        := match t return forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v) with
           | Tbase x => fv _
           | Unit => fun v => v
           | Prod A B => fun xy => (@SmartFlatTypeMapInterp _ _ f fv A (fst xy),
                                    @SmartFlatTypeMapInterp _ _ f fv B (snd xy))
           end.
      Fixpoint SmartFlatTypeMapUnInterp var' var'' var''' (f : forall t, var' t -> base_type_code)
               (fv : forall t (v : var' t), var'' (f t v) -> var''' t)
               {t} {struct t}
        : forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v)
                    -> interp_flat_type_gen var''' t
        := match t return forall v, interp_flat_type_gen var'' (SmartFlatTypeMap f (t:=t) v)
                                    -> interp_flat_type_gen var''' t with
           | Tbase x => fv _
           | Unit => fun _ v => v
           | Prod A B => fun v xy => (@SmartFlatTypeMapUnInterp _ _ _ f fv A _ (fst xy),
                                      @SmartFlatTypeMapUnInterp _ _ _ f fv B _ (snd xy))
           end.
      Definition SmartVarMap {var var'} (f : forall t, var t -> var' t) (f' : forall t, var' t -> var t) {t}
        : interp_type_gen (interp_flat_type_gen var) t -> interp_type_gen (interp_flat_type_gen var') t
        := @smart_interp_map var (interp_type_gen (interp_flat_type_gen var')) f f' tt (fun A B x y => pair x y) (fun A B f x => f x) t.
      Definition SmartVarMap_hetero {vars vars' var var'} (f : forall t, var t -> var' t) (f' : forall t, vars' t -> vars t) {t}
        : interp_type_gen_hetero vars (interp_flat_type_gen var) t -> interp_type_gen_hetero vars' (interp_flat_type_gen var') t
        := @smart_interp_map_hetero var (interp_type_gen_hetero vars' (interp_flat_type_gen var')) vars f tt (fun A B x y => pair x y) (fun A B f x => f (f' _ x)) t.
      Definition SmartVarVarf {t} : interp_flat_type_gen var t -> interp_flat_type_gen exprf t
        := SmartVarfMap (fun t => Var).
      (*Definition SmartConstf {t} : interp_flat_type t -> interp_flat_type_gen exprf t
        := SmartVarfMap (fun t => Const (t:=t)).*)
    End expr.

    Definition Expr (t : type) := forall var, @expr var t.

    Section interp.
      Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Definition interpf_step
                 (interpf : forall {t} (e : @exprf interp_flat_type t), interp_flat_type t)
                 {t} (e : @exprf interp_flat_type t) : interp_flat_type t
        := match e in exprf t return interp_flat_type t with
           | TT => tt
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
           | Unit => fun v : unit => v
           | Prod x y => fun xy => (@mapf_interp_flat_type _ (fst xy),
                                    @mapf_interp_flat_type _ (snd xy))
           end e.

      Fixpoint mapf {t} (e : @exprf var1 t) : @exprf var2 t
        := match e in exprf t return exprf t with
           | TT => TT
           | Var _ x => Var (fvar12 _ x)
           | Op _ _ op args => Op op (@mapf _ args)
           | LetIn _ ex _ eC => LetIn (@mapf _ ex) (fun x => @mapf _ (eC (mapf_interp_flat_type x)))
           | Pair _ ex _ ey => Pair (@mapf _ ex) (@mapf _ ey)
           end.
    End map.

    Section wf.
      Context {var1 var2 : base_type_code -> Type}.

      Local Notation eP := (fun t => var1 t * var2 t)%type (only parsing).
      Local Notation "x == y" := (existT eP _ (x, y)).
      Fixpoint flatten_binding_list {t} (x : interp_flat_type_gen var1 t) (y : interp_flat_type_gen var2 t) : list (sigT eP)
        := (match t return interp_flat_type_gen var1 t -> interp_flat_type_gen var2 t -> list _ with
            | Tbase _ => fun x y => (x == y) :: nil
            | Unit => fun x y => nil
            | Prod t0 t1 => fun x y => @flatten_binding_list _ (snd x) (snd y) ++ @flatten_binding_list _ (fst x) (fst y)
            end x y)%list.

      Inductive wff : list (sigT eP) -> forall {t}, @exprf var1 t -> @exprf var2 t -> Prop :=
      | WfTT : forall G, @wff G _ TT TT
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
Global Arguments Unit {_}%type_scope.
Global Arguments Prod {_}%type_scope (_ _)%ctype_scope.
Global Arguments Arrow {_}%type_scope (_ _)%ctype_scope.
Global Arguments Tbase {_}%type_scope _%ctype_scope.
Global Arguments Tflat {_}%type_scope _%ctype_scope.

Ltac admit_Wf := apply Wf_admitted.

Global Arguments Var {_ _ _ _} _.
Global Arguments SmartVarf {_ _ _ _} _.
Global Arguments SmartPairf {_ _ _ t} _.
Global Arguments SmartValf {_} T _ t.
Global Arguments SmartVarVarf {_ _ _ _} _.
Global Arguments SmartVarfMap {_ _ _} _ {_} _.
Global Arguments SmartVarfMap2 {_ _ _ _} _ {t} _ _.
Global Arguments SmartFlatTypeMap {_ _} _ {_} _.
Global Arguments SmartFlatTypeMapInterp {_ _ _ _} _ {_} _.
Global Arguments SmartFlatTypeMapUnInterp {_ _ _ _ _} fv {_ _} _.
Global Arguments SmartVarMap_hetero {_ _ _ _ _} _ _ {_} _.
Global Arguments SmartVarMap {_ _ _} _ _ {_} _.
(*Global Arguments SmartConstf {_ _ _ _ _} _.*)
Global Arguments TT {_ _ _}.
Global Arguments Op {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _} _.
Global Arguments Abs {_ _ _ _ _} _.
Global Arguments SmartAbs {_ _ _ _ _} _.
Global Arguments mapf_interp_flat_type {_ _ _} _ {t} _.
Global Arguments interp_type_gen_hetero {_} _ _ _.
Global Arguments interp_type_gen {_} _ _.
Global Arguments interp_flat_type {_} _ _.
Global Arguments interp_type {_} _ _.
Global Arguments wff {_ _ _ _} G {t} _ _.
Global Arguments wf {_ _ _ _} G {t} _ _.
Global Arguments Wf {_ _ t} _.
Global Arguments Interp {_ _ _} interp_op {t} _.
Global Arguments interp {_ _ _} interp_op {t} _.
Global Arguments interpf {_ _ _} interp_op {t} _.

Section hetero_type.
  Fixpoint flatten_flat_type {base_type_code} (t : flat_type (flat_type base_type_code)) : flat_type base_type_code
    := match t with
       | Tbase T => T
       | Unit => Unit
       | Prod A B => Prod (@flatten_flat_type _ A) (@flatten_flat_type _ B)
       end.

  Section smart_flat_type_map2.
    Context {base_type_code1 base_type_code2 : Type}.

    Definition SmartFlatTypeMap2 {var' : base_type_code1 -> Type} (f : forall t, var' t -> flat_type base_type_code2) {t}
      : interp_flat_type var' t -> flat_type base_type_code2
      := @smart_interp_flat_map base_type_code1 var' (fun _ => flat_type base_type_code2) f Unit (fun _ _ => Prod) t.
    Fixpoint SmartFlatTypeMapInterp2 {var' var''} (f : forall t, var' t -> flat_type base_type_code2)
             (fv : forall t v, interp_flat_type var'' (f t v)) t {struct t}
      : forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
      := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v) with
         | Tbase x => fv _
         | Unit => fun v => v
         | Prod A B => fun xy => (@SmartFlatTypeMapInterp2 _ _ f fv A (fst xy),
                                  @SmartFlatTypeMapInterp2 _ _ f fv B (snd xy))
         end.
    Fixpoint SmartFlatTypeMapUnInterp2 var' var'' var''' (f : forall t, var' t -> flat_type base_type_code2)
             (fv : forall t (v : var' t), interp_flat_type var'' (f t v) -> var''' t)
             {t} {struct t}
      : forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
                  -> interp_flat_type var''' t
      := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
                                  -> interp_flat_type var''' t with
         | Tbase x => fv _
         | Unit => fun _ v => v
         | Prod A B => fun v xy => (@SmartFlatTypeMapUnInterp2 _ _ _ f fv A _ (fst xy),
                                    @SmartFlatTypeMapUnInterp2 _ _ _ f fv B _ (snd xy))
         end.
  End smart_flat_type_map2.
End hetero_type.

Global Arguments SmartFlatTypeMap2 {_ _ _} _ {_} _.
Global Arguments SmartFlatTypeMapInterp2 {_ _ _ _ _} _ {_} _.
Global Arguments SmartFlatTypeMapUnInterp2 {_ _ _ _ _ _} fv {_ _} _.

Module Export Notations.
  Notation "()" := (@Unit _) : ctype_scope.
  Notation "A * B" := (@Prod _ A B) : ctype_scope.
  Notation "A -> B" := (@Arrow _ A B) : ctype_scope.
  Notation "'slet' x := A 'in' b" := (LetIn A (fun x => b)) : expr_scope.
  Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
  Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
  Notation "( )" := TT : expr_scope.
  Notation "()" := TT : expr_scope.
  Bind Scope ctype_scope with flat_type.
  Bind Scope ctype_scope with type.
End Notations.
