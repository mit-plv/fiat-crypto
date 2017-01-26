(** * PHOAS Representation of Gallina *)
Require Import Crypto.Util.LetIn.
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
  End expr_param.
End language.
Global Arguments tuple' {_}%type_scope _%ctype_scope _%nat_scope.
Global Arguments tuple {_}%type_scope _%ctype_scope _%nat_scope.
Global Arguments Unit {_}%type_scope.
Global Arguments Prod {_}%type_scope (_ _)%ctype_scope.
Global Arguments Arrow {_}%type_scope (_ _)%ctype_scope.
Global Arguments Tbase {_}%type_scope _%ctype_scope.
Global Arguments Tflat {_}%type_scope _%ctype_scope.

Global Arguments Var {_ _ _ _} _.
Global Arguments TT {_ _ _}.
Global Arguments Op {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _} _.
Global Arguments Abs {_ _ _ _ _} _.
Global Arguments interp_type_gen_hetero {_} _ _ _.
Global Arguments interp_type_gen {_} _ _.
Global Arguments interp_flat_type {_} _ _.
Global Arguments interp_type {_} _ _.
Global Arguments Interp {_ _ _} interp_op {t} _.
Global Arguments interp {_ _ _} interp_op {t} _.
Global Arguments interpf {_ _ _} interp_op {t} _.

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
