Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Varnames.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Bedrock.Translation.ExprWithSet.
Require Import Crypto.Bedrock.Proofs.Expr.
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

Section ExprWithSet.
  Context {p : Types.parameters} {p_ok : @ok p}.
  Context (call : string ->
                  Semantics.trace ->
                  Interface.map.rep (map:=Semantics.mem) ->
                  list Interface.word.rep ->
                  (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                   list Interface.word.rep -> Prop) ->
                  Prop).
  Context (Proper_call :
             Morphisms.pointwise_relation
               string
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
  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local. (* local list representation *)
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : Interface.map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

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
End ExprWithSet.
