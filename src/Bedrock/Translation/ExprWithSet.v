Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* TODO : prune imports *)

Import API.Compilers.
Import Types.Notations Types.Types.

(* A few expressions bound by a single let-in in the fiat-crypto code need to
   translate to multiple [set] commands in the bedrock2 code (adds with carries,
   for instance, since bedrock2 doesn't have carries). Since these need to
   output [cmd.cmd], they can't be handled in translate_expr, so they get
   special cases here. *)
(* TODO: add mul_split *)
Section ExprWithSet.
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  Local Notation AddGetCarry r1 r2 s x y :=
    (expr.App
       (s:=type_ZZ) (d:=type_ZZ)
       (* cast *)
       (expr.App
          (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
          (expr.Ident ident.Z_cast2)
          (expr.App
             (s:=type_range) (d:=type_range2)
             (expr.App
                (s:=type_range) (d:=type.arrow type_range type_range2)
                (expr.Ident ident.pair)
                (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
             (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
       (* add-get-carry expression *)
       (expr.App (s:=type_Z)
                 (expr.App (s:=type_Z)
                           (expr.App
                              (expr.Ident ident.Z_add_get_carry)
                              (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                           x) y)).
  Local Notation AddWithGetCarry r1 r2 s c x y :=
    (expr.App
       (s:=type_ZZ) (d:=type_ZZ)
       (* cast *)
       (expr.App
          (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
          (expr.Ident ident.Z_cast2)
          (expr.App
             (s:=type_range) (d:=type_range2)
             (expr.App
                (s:=type_range) (d:=type.arrow type_range type_range2)
                (expr.Ident ident.pair)
                (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
             (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
       (* add-with-get-carry expression *)
       (expr.App (s:=type_Z)
                 (expr.App (s:=type_Z)
                           (expr.App (s:=type_Z)
                                     (expr.App
                                        (expr.Ident ident.Z_add_with_get_carry)
                                        (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                     c) x) y)).

  Definition translate_add_get_carry (sum carry : String.string)
             r1 r2 s (x y : API.expr type_Z) : Syntax.cmd.cmd :=
    if (range_good r1 && range_good r2)%bool
    then if Z.eqb s maxint
         then
           let sum_expr := Syntax.expr.op Syntax.bopname.add
                                          (translate_expr true x) (translate_expr true y) in
           (* Given (0 <= x < w) and (0 <= y < w), carry bit = (x + y) mod w
                <? x: if (x + y) mod w < x, then clearly the sum must have
                overflowed (since 0 <= y) if the sum overflowed, then (x + y)
                mod w = x + y - w < x *)
           let carry_expr := Syntax.expr.op Syntax.bopname.ltu
                                            (Syntax.expr.var sum) (translate_expr true x) in
           Syntax.cmd.seq (Syntax.cmd.set sum sum_expr) (Syntax.cmd.set carry carry_expr)
         else Syntax.cmd.skip
    else Syntax.cmd.skip.

  Definition translate_add_with_get_carry (sum carry : String.string)
             r1 r2 s (c x y : API.expr type_Z) : Syntax.cmd.cmd :=
    if (range_good r1 && range_good r2)%bool
    then if Z.eqb s maxint
         then
           let sum_cx := Syntax.expr.op Syntax.bopname.add
                                        (translate_expr true c) (translate_expr true x) in
           let sum_cxy := Syntax.expr.op Syntax.bopname.add
                                         (Syntax.expr.var sum) (translate_expr true y) in
           (* compute the carry by adding together the carries of both
                additions, using the same strategy as in Z_add_get_carry *)
           let carry_cx := Syntax.expr.op Syntax.bopname.ltu
                                          (Syntax.expr.var sum) (translate_expr true x) in
           let carry_cxy := Syntax.expr.op Syntax.bopname.ltu
                                           (Syntax.expr.var sum) (translate_expr true y) in
           let carry_expr := Syntax.expr.op Syntax.bopname.add (Syntax.expr.var carry) carry_cxy in
           (* sum := c + x
                carry := (sum <? x)
                sum +=y
                carry += (sum <? y) *)
           (Syntax.cmd.seq
              (Syntax.cmd.seq
                 (Syntax.cmd.seq
                    (Syntax.cmd.set sum sum_cx)
                    (Syntax.cmd.set carry carry_cx))
                 (Syntax.cmd.set sum sum_cxy))
              (Syntax.cmd.set carry carry_expr))
         else Syntax.cmd.skip
    else Syntax.cmd.skip.


  Definition translate_expr_with_set {t} (e : @API.expr ltype t) (nextn : nat)
    : option (nat * ltype t * Syntax.cmd.cmd) :=
    let sum := varname_gen nextn in
    let carry := varname_gen (S nextn) in
    match e with
    | AddGetCarry r1 r2 s x y =>
      Some (2%nat, (sum,carry), translate_add_get_carry sum carry r1 r2 s x y)
    | AddWithGetCarry r1 r2 s c x y =>
      Some (2%nat, (sum,carry), translate_add_with_get_carry sum carry r1 r2 s c x y)
    | _ => None
    end.
End ExprWithSet.
