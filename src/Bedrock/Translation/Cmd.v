Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Types.Notations Types.Types.

Section Cmd.
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  Fixpoint assign_list (nextn : nat) (xs : base_rtype base_listZ)
    : nat * base_ltype base_listZ * Syntax.cmd.cmd :=
    match xs with
      | [] => (0%nat, [], Syntax.cmd.skip)
      | x :: xs' =>
        let rec := assign_list (S nextn) xs' in
        (S (fst (fst rec)), varname_gen nextn :: snd (fst rec),
         Syntax.cmd.seq (Syntax.cmd.set (varname_gen nextn) x) (snd rec))
    end.

  Fixpoint assign {t : base.type} (nextn : nat)
    : base_rtype t -> (nat * base_ltype t * Syntax.cmd.cmd) :=
    match t with
    | base.type.prod a b =>
      fun rhs =>
        let assign1 := assign nextn (fst rhs) in
        let assign2 := assign (nextn + fst (fst assign1)) (snd rhs) in
        ((fst (fst assign1) + fst (fst assign2))%nat,
         (snd (fst assign1), snd (fst assign2)),
         Syntax.cmd.seq (snd assign1) (snd assign2))
    | base.type.list (base.type.type_base base.type.Z) =>
      assign_list nextn
    | base.type.list _ | base.type.option _ | base.type.unit
    | base.type.type_base _ =>
      fun rhs =>
        let v := varname_gen nextn in
        (1%nat, v, Syntax.cmd.set v rhs)
    end.

  Fixpoint assign' {t} (nextn : nat)
    : rtype t -> (nat * ltype t * Syntax.cmd.cmd) :=
    match t as t0 return
          rtype t0 -> nat * ltype t0 * _ with
    | type.base b => assign (t:=b) nextn
    | _ =>
      fun _ =>
        (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.

  Fixpoint translate_cmd
           {t} (e : @API.expr ltype t) (nextn : nat)
    : nat (* number of variable names used *)
      * ltype t (* variables in which return values are stored *)
      * Syntax.cmd.cmd (* actual program *) :=
    match e in expr.expr t0
          return (nat * ltype t0 * Syntax.cmd.cmd) with
    | expr.LetIn (type.base t1) (type.base t2) x f =>
      let trx := assign nextn (translate_expr true x) in
      let trf := translate_cmd (f (snd (fst trx))) (nextn + fst (fst trx)) in
      ((fst (fst trx) + fst (fst trf))%nat,
       snd (fst trf),
       Syntax.cmd.seq (snd trx) (snd trf))
    | expr.App
        type_listZ type_listZ
        (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
      let trx := assign nextn (translate_expr true x) in
      let trl := translate_cmd l (S nextn) in
      ((fst (fst trx) + fst (fst trl))%nat,
       snd (fst trx) :: snd (fst trl),
       Syntax.cmd.seq (snd trx) (snd trl))
    | expr.Ident type_listZ (ident.nil _) =>
      (0%nat, [], Syntax.cmd.skip)
    | expr.App _ _ f x =>
      let v := translate_expr true (expr.App f x) in
      assign' nextn v
    | expr.Ident _ i =>
      let v := translate_expr true (expr.Ident i) in
      assign' nextn v
    | expr.Var _ v =>
      let v := translate_expr true (expr.Var v) in
      assign' nextn v
    | _ => (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.
End Cmd.
