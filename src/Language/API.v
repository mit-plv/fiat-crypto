Require Import Crypto.Language.APINotations.

Export Language.Pre.
Export Language.Language.
Export Language.IdentifiersBasicGENERATED.

Module Compilers.
  Import IdentifiersBasicGENERATED.Compilers.
  Import Language.Wf.Compilers.
  Include Language.APINotations.Compilers.

  (** This is the module that defines the top-level constants which
      are used by clients of the language once it has been specialized
      to the identifiers and types we are using.  To see what things
      are under the hood, you can write things like

<<
Unset Printing Notations.
Compute API.Expr. (* to figure out what goes into an expression *)
Compute API.type. (* to figure out what goes into a type *)
>>

      You can then print out the things resulting from [Compute] to
      see the constructors of the various inductive types.
   *)
  Module Import API.
    Export Coercions.

    (** [type] is the type of reified type-codes for expressions *)
    Notation type := (type base.type).
    (** [Expr : type -> Type] is the type family of specialized PHOAS expressions *)
    Notation Expr := (@expr.Expr base.type ident).
    (** [expr : forall {var : type -> Type}, type -> Type] is the [var]-specific PHOAS expression type *)
    Notation expr := (@expr base.type ident).

    (** [interp_type : type -> Type] is the type code denotation function *)
    Notation interp_type := (@type.interp base.type base.interp).
    (** [Interp : forall {t}, Expr t -> interp_type t] is the [Expr] denotation function *)
    Notation Interp := (@expr.Interp base.type ident base.interp (@ident_interp)).
    (** [interp : forall {t}, @expr interp_type t -> interp_type t] is the [expr] denotation function *)
    Notation interp := (@expr.interp base.type ident base.interp (@ident_interp)).

    Ltac reify_type ty := type.reify ltac:(reify_base_type) constr:(base.type) ty.
    Notation reify_type t := (ltac:(let rt := reify_type t in exact rt)) (only parsing).
    Notation reify_type_of e := (reify_type ((fun t (_ : t) => t) _ e)) (only parsing).

    Ltac reify var term := Compilers.reify var term.
    Ltac Reify term := Compilers.Reify term.
    Ltac Reify_rhs _ := Compilers.Reify_rhs ().

    Notation wf := (@expr.wf base.type ident).
    Notation Wf := (@expr.Wf base.type ident).
  End API.

  Module GallinaReify.
    Export Language.Compilers.GallinaReify.
    Module base.
      Export Language.Compilers.GallinaReify.base.
      (** [Reify] does Ltac type inference to get the type *)
      Notation Reify v
        := (@Reify_as Compilers.base base_interp ident buildIdent (base.reify_type_of v) (fun _ => v)) (only parsing).
    End base.

    (** [Reify] does Ltac type inference to get the type *)
    Notation Reify v
      := (@Reify_as Compilers.base base_interp ident buildIdent (reify_type_of v) (fun _ => v)) (only parsing).
  End GallinaReify.
End Compilers.
