(** * PHOAS → Named Representation of Gallina *)
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Compilers.Named.RegisterAssign.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.EstablishLiveness.
Require Import Crypto.Compilers.CountLets.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type)
          {Context : Context Name (fun _ : base_type_code => positive)}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).

  Definition CompileAndEliminateDeadCode
             {t} (e : Expr t) (ls : list Name)
    : option (nexpr t)
    := let e := compile (Name:=positive) (e _) (List.map Pos.of_nat (seq 1 (CountBinders e))) in
       match e with
       | Some e => Let_In (insert_dead_names (Context:=PositiveContext_nd) None e ls) (* help vm_compute by factoring this out *)
                          (fun names => register_reassign (InContext:=PositiveContext_nd) (ReverseContext:=Context) Pos.eqb empty empty e names)
       | None => None
       end.
End language.

Global Arguments CompileAndEliminateDeadCode {_ _ _ _ t} e ls.
