Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import (*hints*) Coq.btauto.Algebra.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Translation.Cmd.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Expr.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Cmd.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Import API.Compilers.
Import Types.Notations.

Section Cmd.
  Context 
    {width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}.
  Context {ok : ok}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.

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

  Definition is_add_get_carry_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Z_add_get_carry => true
    | _ => false
    end.

  Definition is_add_with_get_carry_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Z_add_with_get_carry => true
    | _ => false
    end.

  Definition valid_ident_special3 {a b c d} (i : ident (a -> b -> c -> d))
    : @API.expr (fun _ => unit) a
      -> @API.expr (fun _ => unit) b
      -> @API.expr (fun _ => unit) c
      -> bool :=
    if is_add_get_carry_ident i
    then (fun s x y => is_literalz s (2 ^ width))
    else (fun _ _ _ => false).

  Definition valid_carry_bool {t} : @API.expr (fun _ => unit) t -> bool :=
    match t with
    | type_Z =>
      fun c =>
        match invert_expr.invert_App_Z_cast c with
          | Some rc =>
            if ((ZRange.lower (fst rc) =? 0) && (ZRange.upper (fst rc) =? 1))%bool
            then valid_expr_bool false (snd rc)
            else false
          | None => false
        end
    | _ => fun _ => false
    end.

  Definition valid_ident_special4 {a b c d e} (i : ident (a -> b -> c -> d -> e))
    : @API.expr (fun _ => unit) a
      -> @API.expr (fun _ => unit) b
      -> @API.expr (fun _ => unit) c
      -> @API.expr (fun _ => unit) d
      -> bool :=
    if is_add_with_get_carry_ident i
    then (fun s c x y => is_literalz s (2 ^ width) && valid_carry_bool c)
    else (fun _ _ _ _ => false).

  Definition valid_special3_bool {t} (e : @API.expr (fun _ => unit) t) : bool :=
    match invert_AppIdent3 e with
    | Some (existT _ (i, x, y, z)) => valid_ident_special3 i x y z
    | None => false
    end.

  Definition valid_special4_bool {t} (e : @API.expr (fun _ => unit) t) : bool :=
    match invert_AppIdent4 e with
    | Some (existT _ (i, w, x, y, z)) => valid_ident_special4 i w x y z
    | None => false
    end.

  Definition valid_special_bool {t} (e : @API.expr (fun _ => unit) t) : bool :=
    match invert_expr.invert_App_cast e with
    | Some rx =>
      if range_type_good (width:=width) (fst rx)
      then valid_special3_bool (snd rx) || valid_special4_bool (snd rx)
      else false
    | None => false
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
        valid_cmd_bool (f tt) && (valid_expr_bool true x || valid_special_bool x)
      | expr.LetIn
          (type.base (base.type.type_base a))
          (type.base b) x f =>
        valid_cmd_bool (f tt) && (valid_expr_bool true x || valid_special_bool x)
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

  Lemma is_add_get_carry_ident_eq {t} i :
    @is_add_get_carry_ident t i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_ZZ)) =>
       fun i => i = ident.Z_add_get_carry
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_add_get_carry_ident]; break_match; congruence.
  Qed.

  Lemma is_literalz_eq t (e : API.expr t) (x : Z) :
    is_literalz e x = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type_Z => fun e => e = expr.Ident (ident.Literal (t:=Compilers.Z) x)
     | _ => fun _ => False
     end) e.
  Proof.
    cbv [is_literalz]. break_match; try congruence; [ ].
    rewrite Z.eqb_eq; intros; subst; reflexivity.
  Qed.

  (*
  Lemma valid_ident_special3_valid_cmd a b c d t i x y z (f : unit -> API.expr t) :
    @valid_ident_special3 a b c d i x y z = true ->
    valid_cmd (t:=t) (f tt) ->
    valid_cmd (expr_let x := (expr.App (#i @ x @ y @ z) in
                     f x).
  Proof.
    cbv [valid_ident_special3].
    break_match; intros; [ | congruence ].
    repeat lazymatch goal with
           | H : is_add_get_carry_ident _ = true |- _ =>
             apply is_add_get_carry_ident_eq in H;
               break_match_hyps; try contradiction; [ ];
                 subst
           | H : is_literalz _ _ = true |- _ =>
             apply is_literalz_eq in H; subst
           end.
    apply is_literalz_eq in H.
  Qed. *)

  (*
  Lemma valid_special3_valid_cmd {s d} f x :
    valid_special3_bool (t:=s) x = true ->
    valid_cmd (t:=d) (f tt) ->
    valid_cmd (t:=d) (expr.LetIn x f).
  Proof.
    cbv [valid_special3_bool].
    break_match; [ | congruence ].
    lazymatch goal with
    | H : invert_AppIdent3 _ = Some _ |- _ =>
      apply invert_AppIdent3_Some in H
    end.
    subst; cbn [fst snd projT2].
    cbv [valid_ident_special3].
    break_match; intros; [ | congruence ].
    repeat lazymatch goal with
           | H : is_add_get_carry_ident _ = true |- _ =>
             apply is_add_get_carry_ident_eq in H;
               break_match_hyps; try contradiction; [ ];
                 subst
           | H : is_literalz _ _ = true |- _ =>
             apply is_literalz_eq in H; subst
           end.
    destruct i.
    break_match.
  Qed. *)

  Lemma valid_special_valid_cmd {s d} f x :
    valid_special_bool (t:=s) x = true ->
    valid_cmd (t:=d) (f tt) ->
    valid_cmd (t:=d) (expr.LetIn x f).
  Proof.
    cbv [valid_special_bool].
    break_match; try congruence; [ ].
    repeat lazymatch goal with p : _ * _ |- _ => destruct p end; cbn [fst snd] in *.
    lazymatch goal with
    | |- (_ || _) = true -> _ =>
      let H := fresh in intro H; rewrite orb_true_iff in H; destruct H
    end.
    { (* valid 3-argument function *)
      cbv [valid_special3_bool] in *.
      break_match_hyps; try congruence; [ ].
      lazymatch goal with
      | H : invert_AppIdent3 _ = Some _ |- _ =>
        apply invert_AppIdent3_Some in H
      end.
      subst; cbn [fst snd projT2] in *.
      cbv [valid_ident_special3] in *.
      break_match_hyps; intros; [ | congruence ].
      repeat lazymatch goal with
             | p : _ * _ |- _ => destruct p; cbn [fst snd] in *
             | H : is_add_get_carry_ident _ = true |- _ =>
               apply is_add_get_carry_ident_eq in H;
                 break_match_hyps; try contradiction; [ ];
                   subst
             | H : is_literalz _ _ = true |- _ =>
               apply is_literalz_eq in H; subst
             end.
    destruct i.
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

  Lemma valid_cmd_bool_impl1 {t} e :
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

  Lemma valid_cmd_bool_valid_expr {t} e :
    valid_expr_bool_if_base (t:=t) e = true ->
    valid_cmd_bool e = true.
  Proof.
    destruct e; cbn [valid_cmd_bool]; cbv [valid_expr_bool_if_base];
    break_match; congruence.
  Qed.

  Lemma valid_cmd_bool_impl2 {t} e :
    valid_cmd e -> @valid_cmd_bool t e = true.
  Proof.
    induction 1; intros; subst; cbn;
      repeat match goal with
             | H : valid_expr true _ |- _ =>
               apply valid_expr_bool_iff in H
             end;
      auto using Bool.andb_true_iff; [ ].
    { apply valid_cmd_bool_valid_expr.
      assumption. }
  Qed.

  Lemma valid_cmd_bool_iff {t} e :
    @valid_cmd_bool t e = true <-> valid_cmd e.
  Proof.
    split;
      auto using valid_cmd_bool_impl1, valid_cmd_bool_impl2.
  Qed.
End Cmd.
