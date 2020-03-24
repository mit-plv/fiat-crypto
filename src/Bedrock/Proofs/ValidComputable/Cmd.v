Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Expr.
Require Import Crypto.Bedrock.Proofs.Cmd.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Cmd.
  Context {p : Types.parameters} {p_ok : @ok p}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Definition is_nil_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.nil base_Z => true
    | _ => false
    end.

  Definition is_cons_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.cons base_Z => true
    | _ => false
    end.
  Definition valid_cons_App2_bool {t} (f : @API.expr (fun _ => unit) t) : bool :=
    match f with
    | expr.Ident
        (type.arrow type_Z (type.arrow type_listZ type_listZ)) i =>
      is_cons_ident i
    | _ => false
    end.
  Definition valid_cons_App1_bool {t} (f : @API.expr (fun _ => unit) t) : bool :=
    match f with
    | expr.App type_Z (type.arrow type_listZ type_listZ) f x =>
      valid_cons_App2_bool f && valid_expr_bool true x
    | _ => false
    end.

  Definition valid_expr_bool_if_base
           {t} : @API.expr (fun _ => unit) t -> bool :=
    match t as t0 return API.expr t0 -> bool with
    | type.base _ => valid_expr_bool true
    | _ => fun _ => false
    end.

  Fixpoint valid_cmd_bool
           {t} (e : @API.expr (fun _ => unit) t) : bool :=
    if valid_expr_bool_if_base e
    then true
    else
      match e return bool with
      | expr.LetIn
          (type.base (base.type.prod
                        (base.type.type_base a)
                        (base.type.type_base b)))
          (type.base c) x f =>
        valid_cmd_bool (f tt) && valid_expr_bool true x
      | expr.LetIn
          (type.base (base.type.type_base a))
          (type.base b) x f =>
        valid_cmd_bool (f tt) && valid_expr_bool true x
      | expr.App (type.base s) _ f x =>
        (valid_cons_App1_bool f && valid_cmd_bool x)
      | expr.Ident _ i => is_nil_ident i
      | _ => false
      end.

  Lemma valid_cmd_valid_expr {t} e :
    valid_expr_bool_if_base e = true ->
    valid_cmd (t:=t) e.
  Proof.
    cbv [valid_expr_bool_if_base].
    break_match; try congruence; [ ].
    intros;
      match goal with
        H : valid_expr_bool _ _ = true |- _ =>
        apply valid_expr_bool_iff in H
      end.
    constructor; eauto.
  Qed.

  Lemma is_nil_ident_valid {t} i :
    @is_nil_ident t i = true ->
    valid_cmd (expr.Ident i).
  Proof.
    destruct i; cbn [is_nil_ident]; try congruence; [ ].
    break_match; try congruence; [ ].
    intros; constructor.
  Qed.

  Lemma is_cons_ident_eq {t} i :
    @is_cons_ident t i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_listZ type_listZ) =>
       fun i => i = ident.cons (t:=base_Z)
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_cons_ident]; break_match; congruence.
  Qed.

  Lemma valid_cons_App2_bool_impl1 {t} (f : API.expr t) :
    valid_cons_App2_bool f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow _ (type.arrow _ _) =>
       fun f =>
         forall x l,
           valid_expr true x ->
           valid_cmd l ->
           valid_cmd (expr.App (expr.App f x) l)
     | _ => fun _ => False
     end) f.
  Proof.
    remember t.
    cbv [valid_cons_App2_bool];
      break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : is_cons_ident _ = true |- _ =>
               apply is_cons_ident_eq in H; subst
             end.
    constructor; eauto.
  Qed.

  Lemma valid_cons_App1_bool_impl1 {t} (f : API.expr t) :
    valid_cons_App1_bool f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow _ _ =>
       fun f =>
         forall l,
           valid_cmd l ->
           valid_cmd (expr.App f l)
     | _ => fun _ => False
     end) f.
  Proof.
    remember t.
    cbv [valid_cons_App1_bool];
      break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply Bool.andb_true_iff in H; destruct H
             | H : valid_expr_bool _ _ = true |- _ =>
               apply valid_expr_bool_iff in H
             | H : valid_cons_App2_bool _ = true |- _ =>
               apply valid_cons_App2_bool_impl1 in H; apply H;
                 solve [eauto]
             end.
  Qed.

  Lemma valid_cmd_impl1 {t} e :
    @valid_cmd_bool t e = true -> valid_cmd e.
  Proof.
    induction e; cbn [valid_cmd_bool]; break_match; intros;
      repeat match goal with
          | H : valid_expr_bool_if_base _ = true |- _ =>
            apply valid_cmd_valid_expr in H; apply H
          | H : valid_expr_bool _ _ = true |- _ =>
            apply valid_expr_bool_iff in H
          | H : is_nil_ident _ = true |- _ =>
            apply is_nil_ident_valid in H; apply H
          | H : _ && _ = true |- _ =>
            apply Bool.andb_true_iff in H; destruct H
          | H : false = true |- _ =>
            congruence
          | H : valid_cons_App1_bool _ = true |- _ =>
            apply valid_cons_App1_bool_impl1 in H; apply H;
              solve [eauto]
          | _ => constructor; solve [eauto]
          end.
  Qed.
End Cmd.
