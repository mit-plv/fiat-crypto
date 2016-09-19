(** * PHOAS → Named Representation of Gallina *)
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Named.RegisterAssign.
Require Import Crypto.Reflection.Named.EstablishLiveness.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type)
          {Context : Context Name (fun _ : base_type_code => positive)}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code interp_base_type op (fun _ => Name)).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  (*Local Notation lexprf := (@Syntax.exprf base_type_code interp_base_type op (fun _ => list (option Name))).
  Local Notation lexpr := (@Syntax.expr base_type_code interp_base_type op (fun _ => list (option Name))).*)
  Local Notation nexprf := (@Named.exprf base_type_code interp_base_type op Name).
  Local Notation nexpr := (@Named.expr base_type_code interp_base_type op Name).

  (*Definition get_live_namesf (names : list (option Name)) {t} (e : lexprf t) : list (option Name)
    := filter_live_namesf
         base_type_code interp_base_type op
         (option Name) None
         (fun x y => match x, y with
                     | Some x, _ => Some x
                     | _, Some y => Some y
                     | None, None => None
                     end)
         nil names e.
  Definition get_live_names (names : list (option Name)) {t} (e : lexpr t) : list (option Name)
    := filter_live_names
         base_type_code interp_base_type op
         (option Name) None
         (fun x y => match x, y with
                     | Some x, _ => Some x
                     | _, Some y => Some y
                     | None, None => None
                     end)
         nil names e.*)

  Definition CompileAndEliminateDeadCode
             {t} (e : Expr t) (ls : list Name)
    : option (nexpr t)
    := let e := compile (Name:=positive) (e _) (List.map Pos.of_nat (seq 1 (CountBinders e))) in
       match e with
       | Some e => Let_In (insert_dead_names None e ls) (* help vm_compute by factoring this out *)
                          (fun names => register_reassign Pos.eqb empty empty e names)
       | None => None
       end.
End language.

Global Arguments CompileAndEliminateDeadCode {_ _ _ _ _ t} e ls.
