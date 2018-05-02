Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.

(** Notes:

1. pattern out identifiers and types.
   - type := arrow (_:type) (_:type) | type_base (_:base_type) -- the latter is a parameter
   - literal is an identifier
   - expr cases: var, abs, app, letin, ident -- ident is a parameter
2. add prenex polymorphism for identifiers (type variables)
   -
   - ident is indexed by typecodes, perhaps cases: arrow | base | typevar
*)

Module type.
  Inductive type (base_type : Type) := base (t : base_type) | arrow (s d : type base_type).
  Global Arguments base {_}.
  Global Arguments arrow {_} s d.

  Fixpoint for_each_lhs_of_arrow {base_type} (f : type base_type -> Type) (t : type base_type) : Type
    := match t with
       | base t => unit
       | arrow s d => f s * @for_each_lhs_of_arrow _ f d
       end.

  Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type
    := match t with
       | base t => base_interp t
       | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
       end.

  Fixpoint interpM {base_type} (M : Type -> Type) (base_interp : base_type -> Type) (t : type base_type) : Type
    := match t with
       | base t => base_interp t
       | arrow s d => @interpM _ M base_interp s -> M (@interpM _ M base_interp d)
       end.
End type.
Notation type := type.type.
Delimit Scope etype_scope with etype.
Bind Scope etype_scope with type.type.
Infix "->" := type.arrow : etype_scope.
Module base.
  Module type.
    Inductive type := nat | prod (A B : type) | list (A : type).
  End type.
  Notation type := type.type.
End base.
Bind Scope etype_scope with base.type.
Infix "*" := base.type.prod : etype_scope.

Module parametric.
  Local Notation einterp := type.interp.
  Module type.
    Section subst.
      Context {base_type_with_var base_type}
              (base_subst : base_type_with_var -> base_type)
              (base_interp : base_type_with_var -> Type)
              (base_subst_interp : base_type -> Type)
              (M : Type -> Type)
              (ret : forall T, T -> M T).

      Fixpoint subst (t : type base_type_with_var) : type base_type
        := match t with
           | type.base t => type.base (base_subst t)
           | type.arrow s d => type.arrow (subst s) (subst d)
           end.

      (* half_interp *)
      Fixpoint interp (t : type base_type_with_var) : Type
        := match t with
           | type.base t => base_interp t
           | type.arrow s d
             => match s with
                | type.arrow s' d' => type.interpM M base_subst_interp (subst s)
                | type.base t => base_interp t
                end -> interp d
           end.

      Fixpoint interpM_final (t : type base_type_with_var) : Type
        := match t with
           | type.base t => M (base_interp t)
           | type.arrow s d
             => match s with
                | type.arrow s' d' => type.interpM M base_subst_interp (subst s)
                | type.base t => base_interp t
                end -> interpM_final d
           end.

      Fixpoint interpM_final_of_interp {t} : interp t -> interpM_final t
        := match t with
           | type.base t => ret _
           | type.arrow s d
             => fun f x => @interpM_final_of_interp d (f x)
           end.
    End subst.
  End type.
  Local Notation btype := base.type.type.
  Local Notation bnat := base.type.nat.
  Local Notation bprod := base.type.prod.
  Local Notation blist := base.type.list.
  Module base.
    Module type.
      Inductive type := nat | prod (A B : type) | list (A : type) | var_with_subst (subst : btype).

      Fixpoint subst (t : type) : btype
        := match t with
           | nat => bnat
           | prod A B => bprod (subst A) (subst B)
           | list A => blist (subst A)
           | var_with_subst s => s
           end.

      Section interp.
        Context (base_interp : btype -> Type).

        Fixpoint interp (t : type) : Type
          := match t with
             | nat => Datatypes.nat
             | prod A B => interp A * interp B
             | list A => Datatypes.list (interp A)
             | var_with_subst s => base_interp s
             end%type.
      End interp.
    End type.
    Notation type := type.type.
  End base.

  Definition subst (t : type base.type) : type btype
    := type.subst base.type.subst t.

  Definition half_interp (M : Type -> Type) (half_interp : base.type.type -> Type) (interp : btype -> Type) (t : type base.type) : Type
    := type.interp base.type.subst half_interp interp M t.
  Definition half_interp2 (M : Type -> Type) (half_interp : base.type.type -> Type) (interp : btype -> Type) (t : type base.type) : Type
    := type.interpM_final base.type.subst half_interp interp M t.
  Definition half_interp2_of_interp {M half_interpf interp t} ret
    : half_interp M half_interpf interp t -> half_interp2 M half_interpf interp t
    := type.interpM_final_of_interp _ _ _ _ ret.
End parametric.
Notation ptype := (type.type parametric.base.type).
Delimit Scope ptype_scope with ptype.
Notation "s -> d" := (type.arrow s%ptype d%ptype) : ptype_scope.
Bind Scope ptype_scope with parametric.base.type.
Infix "*" := parametric.base.type.prod : ptype_scope.
Notation "# x" := (parametric.base.type.var_with_subst x) (at level 9, x at level 10, format "# x") : ptype_scope.

Fixpoint upperboundT (t : base.type) : Type
  := match t with
     | base.type.nat => option nat
     | base.type.prod A B => upperboundT A * upperboundT B
     | base.type.list A => option (list (upperboundT A))
     end.

Module expr.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Context {ident : type -> Type}
            {var : type -> Type}.

    Inductive expr : type -> Type :=
    | Ident {t} (idc : ident t) : expr t
    | Var {t} (v : var t) : expr t
    | Abs {s d} (f : var s -> expr d) : expr (s -> d)
    | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
    | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
    .
  End with_var.

  Module Export Notations.
    Delimit Scope expr_scope with expr.
    Bind Scope expr_scope with expr.
    Infix "@" := App : expr_scope.
    Reserved Notation "\ x .. y , t" (at level 200, x binder, y binder, right associativity, format "\  x .. y , '//' t").
    Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'λ' x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
    Notation "'$' x" := (Var x) (at level 9, format "'$' x") : expr_scope.
    Notation "### x" := (Ident x) (at level 9, x at level 10, format "### x") : expr_scope.
  End Notations.
End expr.
Import expr.Notations.
Notation expr := expr.expr.

Module ident.
  Local Notation type := (type base.type).
  Section with_base.
    Let type_base (x : base.type) : type := type.base x.
    Local Coercion type_base : base.type >-> type.
    Let ptype_base (x : parametric.base.type) : ptype := type.base x.
    Local Coercion ptype_base : parametric.base.type >-> ptype.

    Inductive pident : ptype -> Type :=
    | Literal (v : nat) : pident parametric.base.type.nat
    | Plus : pident (parametric.base.type.nat -> parametric.base.type.nat -> parametric.base.type.nat)
    | Pair {A B : base.type} : pident (#A -> #B -> #A * #B)%ptype
    | Fst {A B} : pident (#A * #B -> #A)%ptype
    | Snd {A B} : pident (#A * #B -> #B)%ptype
    | Nil {A} : pident (parametric.base.type.list #A)%ptype
    | Cons {A} : pident (#A -> parametric.base.type.list #A -> parametric.base.type.list #A)%ptype
    | List_map {A B} : pident ((#A -> #B) -> parametric.base.type.list #A -> parametric.base.type.list #B)%ptype
    | List_app {A} : pident (parametric.base.type.list #A -> parametric.base.type.list #A -> parametric.base.type.list #A)%ptype
    | List_flat_map {A B} : pident ((#A -> parametric.base.type.list #B) -> parametric.base.type.list #A -> #(base.type.list B))%ptype
    | List_rect {A P} : pident (#P -> (#A -> parametric.base.type.list #A -> #P -> #P) -> parametric.base.type.list #A -> #P)%ptype
    | Cast {T} (upper_bound : upperboundT T) : pident (#T -> #T)%ptype
    .

    Inductive wident (pident : ptype -> Type) : type -> Type :=
    | wrap {T} (idc : pident T) : wident pident (parametric.subst T).
    Definition ident := wident pident.
    Definition pwrap {T} (idc : pident T) : ident _ := @wrap pident T idc.
  End with_base.
  Global Arguments wrap {pident T} idc.
  Global Coercion pwrap : pident >-> ident.

  Module Export Notations.
    Delimit Scope ident_scope with ident.
    Bind Scope ident_scope with ident.
    Bind Scope ident_scope with pident.
    Global Arguments expr.Ident {base_type%type ident%function var%function t%etype} idc%ident.
    Notation "## x" := (Literal x) (at level 9, x at level 10, format "## x") : ident_scope.
    Notation "## x" := (expr.Ident (wrap (Literal x))) (at level 9, x at level 10, format "## x") : expr_scope.
    Notation "# x" := (expr.Ident (wrap x)) (at level 9, x at level 10, format "# x") : expr_scope.
    Notation "( x , y , .. , z )" := (expr.App (expr.App (#Pair) .. (expr.App (expr.App (#Pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
    Notation "x + y" := (#Plus @ x @ y)%expr : expr_scope.
    (*Notation "x :: y" := (#Cons @ x @ y)%expr : expr_scope.*)
    (* Unification fails if we don't fill in [wident pident] explicitly *)
    Notation "x :: y" := (@expr.App base.type.type (wident pident) _ _ _ (#Cons @ x) y)%expr : expr_scope.
    Notation "[ ]" := (#Nil)%expr : expr_scope.
    Notation "[ x ]" := (#Cons @ x @ (#Nil))%expr : expr_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (@expr.App base.type.type (wident pident) _ _ _ (#Cons @ x) (#Cons @ y @ .. (#Cons @ z @ #Nil) ..))%expr : expr_scope.
  End Notations.
End ident.
Import ident.Notations.
Notation ident := ident.ident.
Notation pident := ident.pident.
Notation wident := ident.wident.

Module UnderLets.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Context {ident : type -> Type}
            {var : type -> Type}.
    Local Notation expr := (@expr base_type ident var).

    Inductive UnderLets {T : Type} :=
    | Base (v : T)
    | UnderLet {A} (x : expr A) (f : var A -> UnderLets).

    Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
      := match x with
         | Base v => e v
         | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
         end.

    Fixpoint splice_list {A B} (ls : list (@UnderLets A)) (e : list A -> @UnderLets B) : @UnderLets B
      := match ls with
         | nil => e nil
         | cons x xs
           => splice x (fun x => @splice_list A B xs (fun xs => e (cons x xs)))
         end.

    Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
      := match x with
         | Base v => v
         | UnderLet A x f
           => expr.LetIn x (fun v => @to_expr _ (f v))
         end.
  End with_var.
  Global Arguments UnderLets : clear implicits.
End UnderLets.
Delimit Scope under_lets_scope with under_lets.
Bind Scope under_lets_scope with UnderLets.UnderLets.
Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.
(** FIXME: MOVE ME *)
Reserved Notation "A <--- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <---  X ; '/' B ']'").
Notation "x <--- y ; f" := (UnderLets.splice_list y (fun x => f%under_lets)) : under_lets_scope.

Module partial.
  Import UnderLets.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Let type_base (x : base_type) : type := type.base x.
    Local Coercion type_base : base_type >-> type.
    Context {ident : type -> Type}
            {var : type -> Type}.
    Local Notation expr := (@expr base_type ident).
    Local Notation UnderLets := (@UnderLets base_type ident var).
    Context (base_value : base_type -> Type)
            (abstract_domain' : base_type -> Type)
            (annotate : forall t, abstract_domain' t -> option (ident (t -> t)))
            (intersect_state : forall A, abstract_domain' A -> abstract_domain' A -> abstract_domain' A)
            (bottom' : forall A, abstract_domain' A)
            (abstraction_function : forall t, base_value t -> abstract_domain' t)
            (base_reify : forall t, base_value t -> @expr var t).

    Definition value (t : type)
      := type.interpM
           UnderLets
           (fun t => abstract_domain' t * @expr var t + base_value t)%type
           t.
    Definition value_with_lets (t : type)
      := UnderLets (value t).

    Context (interp_ident : forall t, ident t -> value_with_lets t).

    Definition abstract_domain (t : type)
      := type.interp abstract_domain' t.

    Fixpoint bottom {t} : abstract_domain t
      := match t with
         | type.base t => bottom' t
         | type.arrow s d => fun _ => @bottom d
         end.

    Fixpoint bottom_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow abstract_domain t
      := match t return type.for_each_lhs_of_arrow abstract_domain t with
         | type.base t => tt
         | type.arrow s d => (bottom, @bottom_for_each_lhs_of_arrow d)
         end.

    Fixpoint state_of_value {t} : value t -> abstract_domain t
      := match t return value t -> abstract_domain t with
         | type.base t
           => fun v
              => match v with
                 | inl (st, _) => st
                 | inr n => abstraction_function _ n
                 end
         | type.arrow s d => fun _ => bottom
         end.

    Fixpoint reify {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> @expr var t
      := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> @expr var t with
         | type.base t
           => fun v 'tt
              => match v with
                 | inl (st, e)
                   => match annotate _ st with
                      | None => e
                      | Some cst => ###cst @ e
                      end%expr
                 | inr v => base_reify _ v
                 end
         | type.arrow s d
           => fun f '(sv, dv)
              => λ x , (UnderLets.to_expr
                          (fx <-- f (@reflect _ (expr.Var x) sv);
                             Base (@reify _ fx dv)))
         end%core%expr
    with reflect {t} : @expr var t -> abstract_domain t -> value t
         := match t return @expr var t -> abstract_domain t -> value t with
            | type.base t
              => fun e st => inl (st, e)
            | type.arrow s d
              => fun e absf v
                 => let stv := state_of_value v in
                    Base (@reflect d (e @ (@reify s v bottom_for_each_lhs_of_arrow)) (absf stv))%expr
            end.

    Fixpoint interp {t} (e : @expr value_with_lets t) : value_with_lets t
      := match e in expr.expr t return value_with_lets t with
         | expr.Ident t idc => interp_ident t idc
         | expr.Var t v => v
         | expr.Abs s d f => Base (fun x => @interp d (f (Base x)))
         | expr.App s d f x
           => (x' <-- @interp s x;
                 f' <-- @interp (s -> d)%etype f;
                 f' x')
         | expr.LetIn (type.arrow _ _) B x f
           => (x' <-- @interp _ x;
                 @interp _ (f (Base x')))
         | expr.LetIn (type.base A) B x f
           => (x' <-- @interp _ x;
                 UnderLet
                   (reify x' tt)
                   (fun x'v
                    => @interp _ (f (Base (reflect (expr.Var x'v) (state_of_value x'))))))
         end%under_lets.

    Definition eval_with_bound {t} (e : @expr value_with_lets t)
               (st : type.for_each_lhs_of_arrow abstract_domain t)
      : expr t
      := UnderLets.to_expr (e' <-- interp e; Base (reify e' st)).

    Definition eval {t} (e : @expr value_with_lets t) : expr t
      := eval_with_bound e bottom_for_each_lhs_of_arrow.
  End with_var.

  Module wident.
    Section with_var.
      Local Notation type := (type base.type).
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Let type_pbase (x : parametric.base.type) : ptype := type.base x.
      Local Coercion type_pbase : parametric.base.type >-> type.
      Context {var : type -> Type}
              (pident : ptype -> Type).
      Local Notation ident := (wident pident).
      Local Notation expr := (@expr base.type ident).
      Local Notation UnderLets := (@UnderLets base.type ident var).
      Context (abstract_domain' : base.type -> Type).
      Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
      Context (annotate : forall t, abstract_domain' t -> option (ident (t -> t)))
              (abstract_interp_ident : forall t, pident t -> type.interp abstract_domain' (parametric.subst t))
              (intersect_state : forall A, abstract_domain' A -> abstract_domain' A -> abstract_domain' A)
              (update_literal_with_state : abstract_domain' base.type.nat -> nat -> nat)
              (state_of_upperbound : forall T, upperboundT T -> abstract_domain' T)
              (bottom' : forall A, abstract_domain' A)
              (** we need constructors for reify and destructors for
              intersect_state, which is needed to talk about how to do
              cast on values; there's a leaky abstraction barrier
              here: we assume that we can take apart the abstract
              state via type structure and then put it back together
              again, in order to cast values.  But we don't require
              that the abstract state is actually a pair on product
              types, so we pay the cost of crossing that abstraction
              barrier in both directions a decent amount *)
              (ident_Literal : nat -> pident parametric.base.type.nat)
              (ident_Pair : forall A B, pident (#A -> #B -> #A * #B)%ptype)
              (ident_Nil : forall A, pident (parametric.base.type.list #A)%ptype)
              (ident_Cons : forall A, pident (#A -> parametric.base.type.list #A -> parametric.base.type.list #A)%ptype)
              (ident_List_app : forall A, pident (parametric.base.type.list #A -> parametric.base.type.list #A -> parametric.base.type.list #A)%ptype)
              (ident_Fst : forall A B, pident (#A * #B -> #A)%ptype)
              (ident_Snd : forall A B, pident (#A * #B -> #B)%ptype)
              (hd_tl_list_state : forall A, abstract_domain' (base.type.list A) -> abstract_domain' A * abstract_domain' (base.type.list A)).

      Local Notation expr_with_abs A
        := (prod (abstract_domain' A) (@expr var A)).
      Local Notation expr_or base_value A
        := (sum (expr_with_abs A) (base_value A%etype)).
      Fixpoint base_value (t : base.type)
        := match t return Type with
           | base.type.nat as t
             => nat
           | base.type.prod A B as t
             => (expr_or base_value A) * (expr_or base_value B)
           | base.type.list A as t
             => list (expr_or base_value A) (* cons cells *)
           end%type.
      Local Notation value := (@value base.type ident var base_value abstract_domain').
      Local Notation value_with_lets := (@value_with_lets base.type ident var base_value abstract_domain').
      Fixpoint pbase_value (t : parametric.base.type)
        := match t return Type with
           | parametric.base.type.nat as t
             => nat
           | parametric.base.type.prod A B as t
             => pbase_value A * pbase_value B
           | parametric.base.type.list A as t
             => list (pbase_value A)
           | parametric.base.type.var_with_subst A as t
             => value A
           end%type.

      Fixpoint abstraction_function {t} : base_value t -> abstract_domain' t
        := match t return base_value t -> abstract_domain' t with
           | base.type.nat
             => fun v => abstract_interp_ident _ (ident_Literal v)
           | base.type.prod A B
             => fun '(a, b)
                => let sta := match a with
                              | inl (st, _) => st
                              | inr a' => @abstraction_function A a'
                              end in
                   let stb := match b with
                              | inl (st, _) => st
                              | inr b' => @abstraction_function B b'
                              end in
                   abstract_interp_ident
                     _ (ident_Pair A B) sta stb
           | base.type.list A
             => fun cells
                => let st_cells
                       := List.map
                            (fun a => match a with
                                      | inl (st, _) => st
                                      | inr a' => @abstraction_function A a'
                                      end)
                            cells in
                   List.fold_right
                     (abstract_interp_ident _ (ident_Cons A))
                     (abstract_interp_ident _ (ident_Nil A))
                     st_cells
           end.

      Fixpoint base_reify {t} : base_value t -> @expr var t
        := match t return base_value t -> expr t with
           | base.type.nat
             => fun v => expr.Ident (ident.wrap (ident_Literal v))
           | base.type.prod A B
             => fun '(a, b)
                => let ea := match a with
                             | inl (st, e)
                               => match annotate _ st with
                                  | None => e
                                  | Some cst => ###cst @ e
                                  end%expr
                             | inr v => @base_reify _ v
                             end in
                   let eb := match b with
                             | inl (st, e)
                               => match annotate _ st with
                                  | None => e
                                  | Some cst => ###cst @ e
                                  end%expr
                             | inr v => @base_reify _ v
                             end in
                   (#(ident_Pair A B) @ ea @ eb)%expr
           | base.type.list A
             => fun cells
                => let cells'
                       := List.map
                            (fun a
                             => match a with
                                | inl (st, e) (* list chunk *)
                                  => match annotate _ st with
                                     | None => e
                                     | Some cst => ###cst @ e
                                     end%expr
                                | inr v
                                  => @base_reify _ v
                                end)
                            cells in
                   List.fold_right
                     (fun x xs => (#(ident_Cons A) @ x @ xs)%expr)
                     (#(ident_Nil A))%expr
                     cells'
           end.

      Context (half_interp : forall {t} (idc : pident t),
                  parametric.half_interp UnderLets pbase_value value t
                  + parametric.half_interp2 UnderLets pbase_value value t).

      Fixpoint intersect_state_base_value {t} : abstract_domain' t -> base_value t -> base_value t
        := match t return abstract_domain' t -> base_value t -> base_value t with
           | base.type.nat => update_literal_with_state
           | base.type.prod _ _
             => fun st '(a, b)
                => let sta := abstract_interp_ident _ (ident_Fst _ _) st in
                   let stb := abstract_interp_ident _ (ident_Snd _ _) st in
                   let a' := match a with
                             | inl (sta', e) => inl (intersect_state _ sta sta', e)
                             | inr v => inr (@intersect_state_base_value _ sta v)
                             end in
                   let b' := match b with
                             | inl (stb', e) => inl (intersect_state _ stb stb', e)
                             | inr v => inr (@intersect_state_base_value _ stb v)
                             end in
                   (a', b')
           | base.type.list _
             => fun st cells
                => let '(cells', st)
                       := List.fold_left
                            (fun '(rest_cells, st) cell
                             => let '(st0, st') := hd_tl_list_state _ st in
                                (match cell with
                                 | inl (st0', e) => inl (intersect_state _ st0 st0', e)
                                 | inr v => inr (@intersect_state_base_value _ st0 v)
                                 end :: rest_cells,
                                 st'))
                            cells
                            (nil, st) in
                   cells'
           end.


      Definition intersect_state_value {t} : abstract_domain t -> value t -> value t
        := match t with
           | type.base t
             => fun st e
                => match e with
                   | inl (st', e) => inl (intersect_state _ st st', e)
                   | inr v => inr (intersect_state_base_value st v)
                   end
           | type.arrow s d => fun _ e => e
           end.

      Local Notation reify := (@reify base.type ident var base_value abstract_domain' annotate bottom' (@abstraction_function) (@base_reify)).
      Local Notation reflect := (@reflect base.type ident var base_value abstract_domain' annotate bottom' (@abstraction_function) (@base_reify)).

      Fixpoint pinterp_base {t : parametric.base.type} : parametric.half_interp UnderLets pbase_value value (type.base t) -> value (parametric.subst (type.base t))
        := match t return parametric.half_interp UnderLets pbase_value value (type.base t) -> value (parametric.subst (type.base t)) with
           | parametric.base.type.nat
             => fun v => inr v
           | parametric.base.type.prod A B
             => fun '(a, b) => inr (@pinterp_base A a, @pinterp_base B b)
           | parametric.base.type.list A
             => fun ls => inr (List.map (@pinterp_base A) ls)
           | parametric.base.type.var_with_subst subst
             => fun v => v
           end.

      Fixpoint puninterp_base {t : parametric.base.type} : value (parametric.subst (type.base t)) -> option (parametric.half_interp UnderLets pbase_value value (type.base t))
        := match t return value (parametric.subst (type.base t)) -> option (parametric.half_interp UnderLets pbase_value value (type.base t)) with
           | parametric.base.type.nat
             => fun v
                => match v with
                   | inl _ => None
                   | inr v' => Some v'
                   end
           | parametric.base.type.prod A B
             => fun ab
                => match ab with
                   | inl _ => None
                   | inr (a, b)
                     => (a' <- @puninterp_base A a;
                           b' <- @puninterp_base B b;
                           Some (a', b'))
                   end
           | parametric.base.type.list A
             => fun ls
                => match ls with
                   | inl rest => None
                   | inr ls
                     => List.fold_right
                          (fun x xs
                           => (x' <- x; xs' <- xs; Some (x' :: xs'))%option)
                          (Some nil)
                          (List.map (@puninterp_base A) ls)
                   end
           | parametric.base.type.var_with_subst subst
             => @Some _
           end%option.

      Fixpoint pinterp {t} : UnderLets (value (parametric.subst t)) -> parametric.half_interp2 UnderLets pbase_value value t -> value_with_lets (parametric.subst t)
        := match t return UnderLets (value (parametric.subst t)) -> parametric.half_interp2 UnderLets pbase_value value t -> value_with_lets (parametric.subst t) with
           | type.base t
             => fun default partial => (partial' <-- partial;
                                          Base (pinterp_base partial'))
           | type.arrow (type.base s) d
             => fun fdefault fpartial
                => Base
                     (fun (v : value (parametric.subst (type.base s)))
                      => let default := (fdefault' <-- fdefault; fdefault' v) in
                         match puninterp_base v return UnderLets (value (parametric.subst d)) with
                         | Some v' => @pinterp d default (fpartial v')
                         | None => default
                         end)
           | type.arrow s d
             => fun fdefault fpartial
                => Base
                     (fun (v : value (parametric.subst s))
                      => @pinterp
                           d (fdefault' <-- fdefault; fdefault' v)
                           (fpartial v))
           end%under_lets.

      Local Notation bottom := (@bottom base.type abstract_domain' bottom').

      Definition interp {t} (idc : ident t) : value_with_lets t
        := match idc in ident.wident _ t return value_with_lets t with
           | ident.wrap T idc' as idc
             => pinterp
                  (Base (reflect (###idc) (abstract_interp_ident _ idc')))%expr
                  match half_interp _ idc' with
                  | inl interp_idc => parametric.half_interp2_of_interp (fun T => @Base _ ident var T) interp_idc
                  | inr interp2_idc => interp2_idc
                  end
           end.

      Definition eval_with_bound {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := @eval_with_bound base.type ident var base_value abstract_domain' annotate bottom' (@abstraction_function) (@base_reify) (@interp) t e st.

      Definition eval {t} (e : @expr value_with_lets t) : @expr var t
        := @eval base.type ident var base_value abstract_domain' annotate bottom' (@abstraction_function) (@base_reify) (@interp) t e.
    End with_var.
  End wident.

  Module ident.
    Section with_var.
      Local Notation type := (type base.type).
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Context {var : type -> Type}.
      Local Notation expr := (@expr base.type ident).
      Local Notation UnderLets := (@UnderLets base.type ident var).
      Context (abstract_domain' : base.type -> Type).
      Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
      Context (annotate : forall t, abstract_domain' t -> option (ident (t -> t)))
              (abstract_interp_ident : forall t, pident t -> type.interp abstract_domain' (parametric.subst t))
              (intersect_state : forall A, abstract_domain' A -> abstract_domain' A -> abstract_domain' A)
              (update_literal_with_state : abstract_domain' base.type.nat -> nat -> nat)
              (state_of_upperbound : forall T, upperboundT T -> abstract_domain' T)
              (bottom' : forall A, abstract_domain' A)
              (hd_tl_list_state : forall A, abstract_domain' (base.type.list A) -> abstract_domain' A * abstract_domain' (base.type.list A)).

      Local Notation base_value := (@wident.base_value var pident abstract_domain').
      Local Notation pbase_value := (@wident.pbase_value var pident abstract_domain').
      Local Notation value := (@value base.type ident var base_value abstract_domain').
      Local Notation intersect_state_value := (@wident.intersect_state_value var pident abstract_domain' abstract_interp_ident intersect_state update_literal_with_state (@ident.Fst) (@ident.Snd) (@hd_tl_list_state)).
      Local Notation abstraction_function := (@wident.abstraction_function var pident abstract_domain' abstract_interp_ident (@ident.Literal) (@ident.Pair) (@ident.Nil) (@ident.Cons)).
      Local Notation base_reify := (@wident.base_reify var pident abstract_domain' annotate (@ident.Literal) (@ident.Pair) (@ident.Nil) (@ident.Cons)).
      Local Notation reify := (@reify base.type ident var base_value abstract_domain' annotate bottom' (@abstraction_function) (@base_reify)).
      Local Notation state_of_value := (@state_of_value base.type ident var base_value abstract_domain' bottom' (@abstraction_function)).

      Definition half_interp {t} (idc : pident t)
        : parametric.half_interp UnderLets pbase_value value t
          + parametric.half_interp2 UnderLets pbase_value value t
        := match idc in ident.pident t return parametric.half_interp UnderLets pbase_value value t + parametric.half_interp2 UnderLets pbase_value value t with
           | ident.Literal v => inl v
           | ident.Plus => inl Nat.add
           | ident.Pair A B => inl (@pair _ _)
           | ident.Fst A B => inl (@fst _ _)
           | ident.Snd A B => inl (@snd _ _)
           | ident.Nil _ => inl (@nil _)
           | ident.Cons _ => inl (@cons _)
           | ident.List_app _ => inl (@List.app _)
           | ident.List_map _ _
             => inr (fun f ls => fls <--- List.map f ls; Base fls)
           | ident.List_flat_map A B
             => inr (fun f ls
                     => fls <--- List.map f ls;
                          Base
                            (List.fold_right
                               (fun ls1 ls2 : value (base.type.list B)
                                => match ls1, ls2 with
                                   | inr ls1, inr ls2 => inr (ls1 ++ ls2)
                                   | _, _
                                     => let rls1 := reify ls1 tt in
                                        let rls2 := reify ls2 tt in
                                        let st1 := state_of_value ls1 in
                                        let st2 := state_of_value ls2 in
                                        inl (abstract_interp_ident _ (ident.List_app) st1 st2,
                                             (#ident.List_app @ rls1 @ rls2)%expr)
                                   end)
                               (inr nil)
                               fls))
           | ident.List_rect A P
             => inr
                  (fun N_case C_case ls
                   => list_rect
                        _
                        (Base N_case)
                        (fun x xs rest
                         => (rest' <-- rest;
                               C_case <-- C_case x;
                               C_case <-- C_case (inr xs);
                               C_case rest'))
                        ls)
           | ident.Cast T upper_bound as idc
             => inl (intersect_state_value (t:=T) (state_of_upperbound _ upper_bound))
           end%under_lets.

      Local Notation value_with_lets := (@value_with_lets base.type ident var base_value abstract_domain').

      Definition eval_with_bound {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := @wident.eval_with_bound var pident abstract_domain' annotate abstract_interp_ident bottom' (@ident.Literal) (@ident.Pair) (@ident.Nil) (@ident.Cons) (@half_interp) t e st.

      Definition eval {t} (e : @expr value_with_lets t) : @expr var t
        := @wident.eval var pident abstract_domain' annotate abstract_interp_ident bottom' (@ident.Literal) (@ident.Pair) (@ident.Nil) (@ident.Cons) (@half_interp) t e.
    End with_var.
  End ident.
End partial.

Section specialized.
  Local Notation abstract_domain' := upperboundT.
  Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
  Notation expr := (@expr base.type ident).
  Local Notation type := (type base.type).
  Let type_base (x : base.type) : type := type.base x.
  Local Coercion type_base : base.type >-> type.
  Definition annotate t (st : abstract_domain' t) : option (ident (t -> t))
    := Some (ident.wrap (ident.Cast st)).
  Fixpoint bottom' T : abstract_domain' T
    := match T return abstract_domain' T with
       | base.type.nat => None
       | base.type.prod A B => (bottom' _, bottom' _)
       | base.type.list _ => None
       end.
  Fixpoint intersect_state A : abstract_domain' A -> abstract_domain' A -> abstract_domain' A
    := match A return abstract_domain' A -> abstract_domain' A -> abstract_domain' A with
       | base.type.nat
         => fun x y
            => match x, y with
               | Some x', Some y' => Some (Nat.min x' y')
               | Some x', None | None, Some x' => Some x'
               | None, None => None
               end
       | base.type.prod A B
         => fun '(x, y) '(x', y') => (@intersect_state _ x x', @intersect_state _ y y')
       | base.type.list A
         => fun ls1 ls2
            => match ls1, ls2 with
               | None, v => v
               | v, None => v
               | Some ls1, Some ls2
                 => Some (List.map (fun '(x, x') => @intersect_state A x x')
                                   (List.combine ls1 ls2))
               end
       end.
  Axiom evil : nat -> nat.
  Definition update_literal_with_state : abstract_domain' base.type.nat -> nat -> nat
    := fun upperbound n
       => match upperbound with
        | Some upperbound'
          => if Nat.leb n upperbound' then n else evil n
        | None => n
        end.
  Definition state_of_upperbound : forall T, upperboundT T -> abstract_domain' T
    := fun _ x => x.
  Definition abstract_interp_ident t (idc : pident t) : type.interp abstract_domain' (parametric.subst t)
    := match idc in ident.pident t return type.interp abstract_domain' (parametric.subst t) with
       | ident.Literal v => Some v
       | ident.Plus
         => fun x y
            => match x, y with
               | Some x', Some y' => Some (x' + y')
               | _, _ => None
               end
       | ident.Pair A B => @pair _ _
       | ident.Fst A B => @fst _ _
       | ident.Snd A B => @snd _ _
       | ident.Nil A => Some nil
       | ident.Cons A
         => fun x xs => (xs' <- xs; Some (cons x xs'))
       | ident.List_map A B
         => fun f ls => option_map (List.map f) ls
       | ident.List_app A
         => fun ls1 ls2 => (ls1' <- ls1; ls2' <- ls2; Some (ls1' ++ ls2'))
       | ident.List_flat_map A B
         => fun f ls
            => (ls' <- ls;
                  List.fold_right
                    (fun ls1 ls2 => (ls1' <- ls1; ls2' <- ls2; Some (ls1' ++ ls2')))
                    (Some nil)
                    (List.map f ls'))
       | ident.List_rect A P
         => fun N C ls
            => match ls with
               | Some ls'
                 => list_rect
                      _
                      N
                      (fun x xs rec => C x (Some xs) rec)
                      ls'
               | None => bottom' _
               end
       | ident.Cast T upper_bound
         => intersect_state _ (state_of_upperbound _ upper_bound)
       end%option.

  Definition hd_tl_list_state A (st : abstract_domain' (base.type.list A))
    : abstract_domain' A * abstract_domain' (base.type.list A)
    := match st with
       | None => (bottom' _, None)
       | Some nil => (bottom' _, Some nil)
       | Some (cons x xs) => (x, Some xs)
       end.

  Definition eval {var} {t} (e : @expr _ t) : expr t
    := (@partial.ident.eval)
         var abstract_domain' annotate abstract_interp_ident intersect_state update_literal_with_state state_of_upperbound bottom' hd_tl_list_state t e.
  Definition eval_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
    := (@partial.ident.eval_with_bound)
         var abstract_domain annotate abstract_interp_ident intersect_state update_literal_with_state state_of_upperbound bottom' hd_tl_list_state t e bound.

  Import expr.
  Import ident.

  Compute eval (#Fst @ (expr_let x := ##10 in ($x, $x)))%expr.

  Compute eval ((\ x , expr_let y := ##5 in #Fst @ $x + (#Fst @ $x + ($y + $y)))
                  @ (##1, ##1))%expr.

  Compute eval ((\ x , expr_let y := ##5 in $y + ($y + (#Fst @ $x + #Snd @ $x)))
                  @ (##1, ##7))%expr.


  Eval cbv in eval_with_bound
                (\z , ((\ x , expr_let y := ##5 in $y + ($z + (#Fst @ $x + #Snd @ $x)))
                         @ (##1, ##7)))%expr
                (Some 100, tt).
End specialized.
