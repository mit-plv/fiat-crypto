Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Types.Notations.

Section Cmd.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
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

  Fixpoint assign_base {t : base.type} (nextn : nat)
    : base_rtype t -> (nat * base_ltype t * Syntax.cmd.cmd) :=
    match t with
    | base.type.prod a b =>
      fun rhs =>
        let assign1 := assign_base nextn (fst rhs) in
        let assign2 := assign_base (nextn + fst (fst assign1)) (snd rhs) in
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

  Definition assign {t} (nextn : nat)
    : rtype t -> (nat * ltype t * Syntax.cmd.cmd) :=
    match t as t0 return
          rtype t0 -> nat * ltype t0 * _ with
    | type.base b => assign_base (t:=b) nextn
    | _ =>
      fun _ =>
        (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.

  Definition translate_ident2_for_cmd {a b c} (i : ident (a -> b -> c))
    : ltype a -> ltype b -> option (ltype c)
    := match i in ident t return ltype (type.domain t) -> ltype (type.domain (type.codomain t)) -> option (ltype (type.codomain (type.codomain t))) with
       | ident.cons base_Z => fun x xs => Some (x :: xs)
       | ident.pair _ _ => fun x y => Some (x, y)
       | _ => fun _ _ => None
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
    | expr.App _ _ _ _ as e
      => let result_if_ident2
             := (ixy <- invert_expr.invert_AppIdent2_cps e (@translate_cmd) (@translate_cmd);
                let '(existT _ (i, translate_cmd_x, translate_cmd_y)) := ixy in
                let trx := translate_cmd_x nextn in
                let try := translate_cmd_y (fst (fst trx) + nextn)%nat in
                vars <- translate_ident2_for_cmd i (snd (fst trx)) (snd (fst try));
                Some ((fst (fst trx) + fst (fst try))%nat,
                      vars,
                      Syntax.cmd.seq (snd trx) (snd try)))%option in
         match result_if_ident2 with
         | Some res => res
         | None =>
           let v := translate_expr true e in
           assign nextn v
         end
    | expr.Ident type_listZ (ident.nil _) =>
      (0%nat, [], Syntax.cmd.skip)
    | expr.Ident _ i =>
      let v := translate_expr true (expr.Ident i) in
      assign nextn v
    | expr.Var _ v =>
      let v := translate_expr true (expr.Var v) in
      assign nextn v
    | _ => (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.
End Cmd.
