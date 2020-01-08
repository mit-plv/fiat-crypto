Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Varnames.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* TODO : prune imports *)

Import API.Compilers.
Import Wf.Compilers.expr.
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

  Definition translate_add_get_carry (sum carry : Syntax.varname)
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

  Definition translate_add_with_get_carry (sum carry : Syntax.varname)
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

  Section Proofs.
    Context {p_ok : @ok p}.
    Context (call : Syntax.funname ->
                    Semantics.trace ->
                    Interface.map.rep (map:=Semantics.mem) ->
                    list Interface.word.rep ->
                    (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                     list Interface.word.rep -> Prop) ->
                    Prop).
    Context (Proper_call :
               Morphisms.pointwise_relation
                 Syntax.funname
                 (Morphisms.pointwise_relation
                    Semantics.trace
                    (Morphisms.pointwise_relation
                       Interface.map.rep
                       (Morphisms.pointwise_relation
                          (list Interface.word.rep)
                          (Morphisms.respectful
                             (Morphisms.pointwise_relation
                                Semantics.trace
                                (Morphisms.pointwise_relation
                                   Interface.map.rep
                                   (Morphisms.pointwise_relation
                                      (list Interface.word.rep) Basics.impl)))
                             Basics.impl)))) call call).

    (* TODO: are these all needed? *)
    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    (* TODO : fill this in *)
    Axiom valid_expr_wset :
      forall {t}, @API.expr (fun _ => unit) t -> Prop.

    Lemma translate_expr_with_set_Some {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_expr_wset x1 ->
      exists cmdx,
        translate_expr_with_set (t:=type.base t) x3 nextn = Some cmdx.
    Admitted.

    (* valid exprs can't possibly be valid expr-with-set commands *)
    Lemma translate_expr_with_set_None {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_expr true x1 ->
      translate_expr_with_set (t:=type.base t) x3 nextn = None.
    Admitted.

    Lemma translate_expr_with_set_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t)) :
      (* e1 is a valid input to translate_expr_with_set_correct *)
      valid_expr_wset e1 ->
      forall G nextn
             (trx : nat * base_ltype t * Syntax.cmd.cmd),
        wf3 G e1 e2 e3 ->
        translate_expr_with_set e3 nextn = Some trx ->
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          context_equiv G locals ->
          WeakestPrecondition.cmd
            call (snd trx) tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               (* translate_expr_with_set never stores anything -- mem unchanged *)
               /\ mem = mem'
               (* return values match the number of variables used *)
               /\ PropSet.sameset (varname_set (snd (fst trx)))
                                  (used_varnames nextn (fst (fst trx)))
               (* new locals only differ in the values of LHS variables *)
               /\ Interface.map.only_differ locals (varname_set (snd (fst trx))) locals'
               (* information stored in LHS variables is equivalent to interp *)
               /\ sep
                    (emp (locally_equivalent
                            (API.interp e2) (rtype_of_ltype (snd (fst trx))) locals'))
                    R mem').
    Admitted.
  End Proofs.
End ExprWithSet.