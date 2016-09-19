(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.FilterLive.
Require Import Crypto.Reflection.Syntax.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code interp_base_type op (fun _ => Name)).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation lexprf := (@Syntax.exprf base_type_code interp_base_type op (fun _ => list (option Name))).
  Local Notation lexpr := (@Syntax.expr base_type_code interp_base_type op (fun _ => list (option Name))).
  Local Notation nexprf := (@Named.exprf base_type_code interp_base_type op Name).
  Local Notation nexpr := (@Named.expr base_type_code interp_base_type op Name).

  Definition get_live_namesf (names : list Name) {t} (e : lexprf t) : list (option Name)
    := filter_live_namesf
         base_type_code interp_base_type op
         (option Name) None
         (fun x y => match x, y with
                     | Some x, _ => Some x
                     | _, Some y => Some y
                     | None, None => None
                     end)
         nil (List.map (@Some _) names) e.
  Definition get_live_names (names : list Name) {t} (e : lexpr t) : list (option Name)
    := filter_live_names
         base_type_code interp_base_type op
         (option Name) None
         (fun x y => match x, y with
                     | Some x, _ => Some x
                     | _, Some y => Some y
                     | None, None => None
                     end)
         nil (List.map (@Some _) names) e.

  Definition compile_and_eliminate_dead_codef
             {t} (e : exprf t) (e' : lexprf t) (ls : list Name)
    : option (nexprf t)
    := ocompilef e (get_live_namesf ls e').

  Definition compile_and_eliminate_dead_code
             {t} (e : expr t) (e' : lexpr t) (ls : list Name)
    : option (nexpr t)
    := ocompile e (get_live_names ls e').

  Definition CompileAndEliminateDeadCode
             {t} (e : Expr t) (ls : list Name)
    : option (nexpr t)
    := compile_and_eliminate_dead_code (e _) (e _) ls.
End language.

Global Arguments compile_and_eliminate_dead_codef {_ _ _ _ t} _ _ ls.
Global Arguments compile_and_eliminate_dead_code {_ _ _ _ t} _ _ ls.
Global Arguments CompileAndEliminateDeadCode {_ _ _ _ t} _ ls.
