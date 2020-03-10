Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Proofs.Varnames.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Expr.
  Context {p : Types.parameters} {p_ok : @ok p}.

  (* TODO: are these all needed? *)
  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local. (* local list representation *)
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : Interface.map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

  Inductive valid_expr
    : forall {t},
      bool (* require_casts *) ->
      @API.expr (fun _ => unit) (type.base t) -> Prop :=
  | valid_cast1 :
      forall rc r x,
        valid_expr false x ->
        range_good r = true ->
        valid_expr rc
                   (expr.App
                      (expr.App (expr.Ident ident.Z_cast)
                                (expr.Ident (ident.Literal (t:=base.type.zrange) r))) x)
  | valid_cast2 :
      forall (rc : bool) r1 r2 x,
        valid_expr false x ->
        range_good r1 = true ->
        range_good r2 = true ->
        valid_expr rc
                   (expr.App
                      (expr.App (expr.Ident ident.Z_cast2)
                                (expr.App
                                   (expr.App
                                      (expr.Ident ident.pair)
                                      (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                                   (expr.Ident (ident.Literal (t:=base.type.zrange) r2)))) x)
  | valid_fst :
      forall rc (x y : API.expr type_Z),
        valid_expr true x ->
        valid_expr rc
                   (expr.App (expr.Ident ident.fst)
                             (expr.App (expr.App (expr.Ident ident.pair) x) y))
  | valid_snd :
      forall rc (x y : API.expr type_Z),
        valid_expr true y ->
        valid_expr rc
                   (expr.App (expr.Ident ident.snd)
                             (expr.App (expr.App (expr.Ident ident.pair) x) y))
  | valid_literalz :
      forall rc z,
        (* either bounded or casts not required *)
        (is_bounded_by_bool z max_range || negb rc = true)%bool ->
        valid_expr rc (expr.Ident (ident.Literal (t:=base.type.Z) z))
  | valid_nth_default :
      forall rc d l i,
        valid_expr true d ->
        valid_expr
          rc (* casts not required, since a list of vars must be already cast *)
          (expr.App (expr.App (expr.App (expr.Ident ident.List_nth_default) d)
                              (expr.Var (t:=type_listZ) l))
                    (expr.Ident (ident.Literal i)))
  | valid_var :
      forall rc t v, valid_expr (t:= t) rc (expr.Var v)
  | valid_basic_binop :
      forall rc i (x y : API.expr type_Z),
        translate_binop i <> None ->
        valid_expr true x ->
        valid_expr true y ->
        valid_expr (t:=base_Z) rc (expr.App (expr.App (expr.Ident i) x) y)
  | valid_truncating_binop :
      forall rc i (s : Z) (x y : API.expr type_Z),
        translate_truncating_binop i <> None ->
        s = Semantics.width ->
        valid_expr true x ->
        valid_expr true y ->
        valid_expr (t:=base_Z) rc
                   (expr.App (expr.App
                                (expr.App (expr.Ident i)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                x) y)
  .

  Lemma translate_expr_correct {t}
        (* three exprs, representing the same Expr with different vars *)
        (e1 : @API.expr (fun _ => unit) (type.base t))
        (e2 : @API.expr API.interp_type (type.base t))
        (e3 : @API.expr ltype (type.base t))
        (require_cast : bool) :
    (* e1 is a valid input to translate_carries_correct *)
    valid_expr require_cast e1 ->
    forall G locals,
      wf3 G e1 e2 e3 ->
      let out := translate_expr require_cast e3 in
      context_equiv G locals ->
      locally_equivalent (API.interp e2) out locals.
  Admitted.
End Expr.
