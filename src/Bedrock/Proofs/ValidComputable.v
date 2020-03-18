Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Bedrock.Proofs.Expr.
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

Section Expr.
  Context {p : Types.parameters} {p_ok : @ok p}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Definition is_fst_snd_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.fst base_Z base_Z => true
    | ident.snd base_Z base_Z => true
    | _ => false
    end.

  Definition valid_expr_App1_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App type_range (type.arrow type_Z type_Z) f r =>
      is_cast_ident_expr f && is_cast_literal r
    | expr.App type_range2 (type.arrow type_ZZ type_ZZ) f r =>
      is_cast_ident_expr f && is_cast2_literal r
    | expr.Ident (type.arrow type_ZZ type_Z) i =>
      negb require_casts && is_fst_snd_ident i
    | _ => false
    end.

  Definition is_mul_high_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Z_mul_high => true
    | _ => false
    end.
  Definition is_mul_high_ident_expr {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident (type.arrow type_Z
                             (type.arrow type_Z
                                         (type.arrow type_Z type_Z)))
                 i => is_mul_high_ident i
    | _ => false
    end.
  
  Definition valid_expr_App2_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z s)) =>
      (is_mul_high_ident_expr f)
        && (negb require_casts)
        && (Z.eqb s (2 ^ Semantics.width))
    | expr.Ident (type.arrow type_Z (type.arrow type_Z type_Z)) i =>
      match translate_binop i with
      | None => false
      | Some _ => negb require_casts
      end
    | _ => false
    end.

  Definition is_shiftl_ident {t} (i : ident.ident t) :=
    match i with
    | ident.Z_truncating_shiftl => true
    | _ => false
    end.
  Definition is_shiftl_ident_expr 
             {t} (e : @API.expr (fun _ => unit) t) :=
    match e with
    | expr.Ident
        (type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)))
        i => is_shiftl_ident i
    | _ => false
    end.
  Definition valid_expr_shift_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z s)) =>
      (is_shiftl_ident_expr f)
        && (negb require_casts)
        && Z.eqb s Semantics.width
    | expr.Ident _ ident.Z_shiftr =>
      negb require_casts
    | _ => false
    end.

  Definition valid_shifter {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z n) =>
      is_bounded_by_bool n width_range
    | _ => false
    end.

  Definition valid_expr_nth_default_App3_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.List_nth_default base_Z) =>
      true
    | _ => false
    end.
  Definition valid_expr_nth_default_App2_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow
                  type_listZ
                  (type.arrow type_nat type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z d)) =>
      valid_expr_nth_default_App3_bool f && is_bounded_by_bool d max_range
    | _ => false
    end.
  Definition valid_expr_nth_default_App1_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App type_listZ (type.arrow type_nat type_Z)
               f (expr.Var _ l) =>
      valid_expr_nth_default_App2_bool f
    | _ => false
    end.
  Definition valid_expr_nth_default_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_nat type_Z
        f (expr.Ident _ (ident.Literal base.type.nat i)) =>
      valid_expr_nth_default_App1_bool f
    | _ => false
    end.

  Fixpoint valid_expr_bool {t} (require_casts : bool)
             (e : @API.expr (fun _ => unit) t) {struct e} : bool :=
    match e with
    | expr.App type_nat _ f x =>
      (* only thing accepting nat is nth_default *)
      if require_casts
      then false
      else valid_expr_nth_default_bool (expr.App f x)
    | expr.App type_Z type_Z
               (expr.App type_Z _ f x) y =>
      if valid_expr_App2_bool require_casts f
      then valid_expr_bool true x && valid_expr_bool true y
      else if valid_expr_shift_bool require_casts f
           then valid_expr_bool true x && valid_shifter y
           else false
    | expr.App type_Z type_Z f x =>
      valid_expr_App1_bool require_casts f && valid_expr_bool true x
    | expr.App type_ZZ type_Z f x =>
      valid_expr_App1_bool require_casts f && valid_expr_bool true x
    | expr.App type_ZZ type_ZZ f x =>
      valid_expr_App1_bool require_casts f && valid_expr_bool true x
    | expr.Ident _ (ident.Literal base.type.Z z) =>
      negb require_casts || is_bounded_by_bool z max_range
    | expr.Ident _ (ident.Literal base.type.nat n) =>
      negb require_casts
    | expr.Var type_Z v => negb require_casts
    | expr.Var type_listZ v => true
    | _ => false
    end.
 
  Lemma valid_expr_App1_bool_type {t} rc (e : API.expr t) :
    valid_expr_App1_bool rc e = true ->
    (exists d,
        t = type.arrow type_Z d
        \/ t = type.arrow type_ZZ d).
  Proof.
    cbv [valid_expr_App1_bool].
    destruct e;
      match goal with
      | idc : ident.ident _ |- _ =>
        destruct idc; try congruence;
          break_match; try congruence; intros;
            eexists; right; reflexivity
      | v: unit, t : API.type |- _ =>
        destruct t; congruence
      | f : API.expr (?s -> ?d) |- _ =>
        destruct d;
          break_match; try congruence;
        try (eexists; right; reflexivity);
        eexists; left; reflexivity
      | |- forall (_: false = true), _ => congruence
      | |- context [@expr.LetIn _ _ _ _ ?B] =>
        destruct B; congruence
      | _ => idtac
      end.
  Qed.

  Lemma is_mul_high_ident_expr_type {t} (f : API.expr t) :
    is_mul_high_ident_expr f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z
                               (type.arrow type_Z type_Z)).
  Proof.
    cbv [is_mul_high_ident_expr].
    break_match; congruence.
  Qed.

  Lemma valid_expr_shift_bool_type {t} rc (f : API.expr t) :
    valid_expr_shift_bool rc f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z type_Z).
  Proof.
    cbv [valid_expr_shift_bool].
    break_match; congruence.
  Qed.

  Lemma valid_expr_App2_bool_type {t} rc (f : API.expr t) :
    valid_expr_App2_bool rc f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z type_Z).
  Proof.
    cbv [valid_expr_App2_bool translate_binop].
    destruct f;
      match goal with
      | idc : ident.ident _ |- _ =>
        destruct idc; try congruence;
          break_match; congruence
      | |- forall (_: false = true), _ => congruence
      | _ => idtac
      end; [ ].
    break_match; congruence.
  Qed.

  Lemma valid_expr_nth_default_App2_bool_type {t}
        (f : API.expr t) :
    valid_expr_nth_default_App2_bool f = true ->
    match t with
    | type.arrow type_listZ
                 (type.arrow type_nat type_Z) =>
      True
    | _ => False
    end.
  Proof.
    cbv [valid_expr_nth_default_App2_bool].
    break_match; try congruence; [ ].
    tauto.
  Qed.

  Lemma valid_expr_nth_default_App1_bool_type {t}
        (f : API.expr t) :
    valid_expr_nth_default_App1_bool f = true ->
    match t with
    | type.arrow type_nat type_Z =>
      True
    | _ => False
    end.
  Proof.
    cbv [valid_expr_nth_default_App1_bool].
    break_match; try congruence; [ ].
    tauto.
  Qed.

  Lemma valid_expr_nth_default_App3_bool_impl1 {t}
        (f : API.expr t) n l d :
    valid_expr_nth_default_App3_bool f = true ->
    is_bounded_by_bool d max_range = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z
                  (type.arrow type_listZ (type.arrow type_nat type_Z)) =>
       fun f =>
         valid_expr
           false (expr.App
                    (expr.App
                       (expr.App
                          f
                          (expr.Ident
                             (ident.Literal (t:=base.type.Z) d)))
                       (expr.Var l))
                 (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App3_bool].
    break_match; try congruence; [ ].
    intros. constructor.
    cbv [is_bounded_by_bool upper lower max_range] in *.
    repeat match goal with
           | H : _ && _ = true |- _ =>
             apply andb_true_iff in H; destruct H
           end.
    Z.ltb_to_lt; lia.
  Qed.

  Lemma valid_expr_nth_default_App2_bool_impl1 {t}
        (f : API.expr t) n l :
    valid_expr_nth_default_App2_bool f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_listZ (type.arrow type_nat type_Z) =>
       fun f =>
         valid_expr
           false
           (expr.App
              (expr.App f (expr.Var l))
              (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App2_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : valid_expr_nth_default_App3_bool _ = true |- _ =>
               eapply valid_expr_nth_default_App3_bool_impl1 in H;
                 eassumption
             end.
  Qed.

  Lemma valid_expr_nth_default_App1_bool_impl1 {t}
        (f : API.expr t) n :
    valid_expr_nth_default_App1_bool f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_nat type_Z =>
       fun f =>
         valid_expr
           false (expr.App f
                        (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App1_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             end;
      match goal with
      | H : valid_expr_nth_default_App2_bool _ = true |- _ =>
        eapply valid_expr_nth_default_App2_bool_impl1 in H
      end.
    break_match_hyps; try tauto; [ ].
    eassumption.
  Qed.

  Lemma is_fst_snd_ident_impl1 {t} (i : ident.ident t) :
    is_fst_snd_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_ZZ type_Z =>
       fun i =>
         forall x : API.expr type_ZZ,
           valid_expr true x ->
           valid_expr false (expr.App (expr.Ident i) x)
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_fst_snd_ident].
    break_match; try congruence; [ | ];
      intros; constructor; eauto.
  Qed.

  Lemma is_cast_literal_ident_eq {t} (i : ident.ident t) :
    is_cast_literal_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type_range =>
       fun i => i = ident.Literal (t:=base.type.zrange) max_range
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_cast_literal_ident].
    break_match; try congruence; [ ].
    cbv [range_good].
    intros; progress reflect_beq_to_eq zrange_beq; subst.
    reflexivity.
  Qed.

  Lemma is_cast_literal_eq {t} (r : API.expr t) :
    is_cast_literal r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range =>
       fun r =>
         r = expr.Ident (ident.Literal (t:=base.type.zrange) max_range)
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast_literal].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_cast_literal_ident _ = true |- _ =>
        apply is_cast_literal_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma is_pair_range_eq {t} (i : ident.ident t) :
    is_pair_range i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_range (type.arrow type_range type_range2) =>
       fun i => i = ident.pair
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_pair_range].
    break_match; congruence.
  Qed.

  Lemma is_cast2_literal_App2_eq {t} (r : API.expr t) :
    is_cast2_literal_App2 r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type.arrow type_range (type.arrow type_range type_range2) =>
       fun r => r = expr.Ident ident.pair
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal_App2].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_pair_range _ = true |- _ =>
        apply is_pair_range_eq in H
      end.
    congruence.
  Qed.

  Lemma is_cast2_literal_App1_eq {t} (r : API.expr t) :
    is_cast2_literal_App1 r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type.arrow type_range type_range2 =>
       fun r =>
         r = expr.App
               (expr.Ident ident.pair)
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) max_range))
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal_App1].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : is_cast_literal _ = true |- _ =>
               apply is_cast_literal_eq in H; subst
             | H : is_cast2_literal_App2 _ = true |- _ =>
               apply is_cast2_literal_App2_eq in H; subst
             end.
    congruence.
  Qed.

  Lemma is_cast2_literal_eq {t} (r : API.expr t) :
    is_cast2_literal r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range2 =>
       fun r =>
         r = expr.App
               (expr.App
                  (expr.Ident ident.pair)
                  (expr.Ident
                     (ident.Literal (t:=base.type.zrange) max_range)))
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) max_range))
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : is_cast_literal _ = true |- _ =>
               apply is_cast_literal_eq in H; subst
             | H : is_cast2_literal_App1 _ = true |- _ =>
               apply is_cast2_literal_App1_eq in H; subst
             end.
    congruence.
  Qed.

  Lemma is_cast_ident_expr_impl1 {t} rc (f : API.expr t) :
    is_cast_ident_expr f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_range (type.arrow type_Z type_Z) =>
       fun f =>
         forall
           (r : API.expr type_range)
           (x : API.expr type_Z),
           is_cast_literal r = true ->
           valid_expr false x ->
           valid_expr rc (expr.App (expr.App f r) x)
     | type.arrow type_range2 (type.arrow type_ZZ type_ZZ) =>
       fun f =>
         forall
           (r : API.expr type_range2)
           (x : API.expr type_ZZ),
           is_cast2_literal r = true ->
           valid_expr false x ->
           valid_expr rc (expr.App (expr.App f r) x)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_cast_ident_expr is_cast_ident].
    break_match; try congruence; [ | ];
      intros;
      match goal with
      | H : is_cast_literal _ = true |- _ =>
        apply is_cast_literal_eq in H; subst
      | H : is_cast2_literal _ = true |- _ =>
        apply is_cast2_literal_eq in H; subst
      end.
    { constructor;
        cbv [range_good]; auto using zrange_lb. }
    { constructor;
        cbv [range_good]; auto using zrange_lb. }
  Qed.

  Lemma valid_expr_App1_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_App1_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z _ =>
       fun f =>
         forall x : API.expr type_Z,
           valid_expr false x ->
           valid_expr rc (expr.App f x)
     | type.arrow type_ZZ type_Z =>
       fun f =>
         forall x : API.expr type_ZZ,
           valid_expr true x ->
           valid_expr rc (expr.App f x)
     | type.arrow type_ZZ type_ZZ =>
       fun f =>
         forall x : API.expr type_ZZ,
           valid_expr false x ->
           valid_expr rc (expr.App f x)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_App1_bool].
    remember t.
    destruct t; try congruence.
    { intros; exfalso.
      break_match_hyps; congruence. }
    { break_match; try congruence; [ | | ]; intros;
        repeat match goal with
               | H : _ && _ = true |- _ =>
                 apply andb_true_iff in H; destruct H
               | H : negb ?rc = true |- _ =>
                 destruct rc; cbn [negb] in *; try congruence; [ ]
               | H : is_fst_snd_ident _ = true |- _ =>
                 apply is_fst_snd_ident_impl1 in H; solve [eauto]
               | H : is_cast_ident_expr _ = true |- _ =>
                 eapply is_cast_ident_expr_impl1 in H;
                   apply H; solve [eauto]
               end. }
  Qed.

  Lemma valid_expr_nth_default_bool_impl1 {t}
        (e : API.expr t) :
    (exists b, t = type.base b) ->
    valid_expr_nth_default_bool e = true ->
    valid_expr false e.
  Proof.
    cbv [valid_expr_nth_default_bool].
    intro; destruct e; try congruence; [ ].
    match goal with
      | _ : API.expr (type.arrow _ ?d) |- _ =>
        destruct d
    end;
      break_match; try congruence; intros; [ ].
    match goal with
    | H : valid_expr_nth_default_App1_bool _ = true |- _ =>
      eapply valid_expr_nth_default_App1_bool_impl1 in H
    end.
    eassumption.
  Qed.

  Lemma is_mul_high_ident_eq {t} (i : ident.ident t) :
    is_mul_high_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun i => i = ident.Z_mul_high
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_mul_high_ident].
    break_match; congruence.
  Qed.

  Lemma is_mul_high_ident_expr_eq {t} (f : API.expr t) :
    is_mul_high_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f => f = expr.Ident ident.Z_mul_high
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_mul_high_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_mul_high_ident _ = true |- _ =>
        apply is_mul_high_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_expr_App2_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_App2_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_expr true y ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_App2_bool].
    break_match; try congruence; [ | ];
      intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : is_mul_high_ident_expr _ = true |- _ =>
               apply is_mul_high_ident_expr_eq in H; subst
             end; [ | ].
    { constructor; eauto; congruence. }
    { constructor; eauto; Z.ltb_to_lt; congruence. }
  Qed.

  Lemma is_shiftl_ident_eq {t} (i : ident.ident t) :
    is_shiftl_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun i => i = ident.Z_truncating_shiftl
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_shiftl_ident].
    break_match; congruence.
  Qed.

  Lemma is_shiftl_ident_expr_eq {t} (f : API.expr t) :
    is_shiftl_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f => f = expr.Ident ident.Z_truncating_shiftl
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_shiftl_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_shiftl_ident _ = true |- _ =>
        apply is_shiftl_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_shifter_eq {t} (x : API.expr t) :
    valid_shifter x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun x =>
         exists n,
           is_bounded_by_bool n width_range = true /\
           x = expr.Ident (ident.Literal (t:=base.type.Z) n)
     | _ => fun _ => False
     end) x.
  Proof.
    cbv [valid_shifter].
    break_match; try congruence; [ ].
    intros; eexists; eauto.
  Qed.

  Lemma valid_expr_shift_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_shift_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_shifter y = true ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_shift_bool].
    break_match; try congruence; [ | ];
      intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : is_bounded_by_bool _ width_range = true |- _ =>
               cbv [is_bounded_by_bool upper lower width_range] in H
             | H : is_shiftl_ident_expr _ = true |- _ =>
               apply is_shiftl_ident_expr_eq in H; subst
             | H : valid_shifter _ = true |- _ =>
               apply valid_shifter_eq in H;
                 destruct H as [? [? ?] ]; subst
             end.
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
  Qed.

  Lemma valid_expr_App_bool_impl1 {t} rc
        (f : API.expr t) (y : API.expr type_Z) :
    match f with
    | expr.App type_Z _ f x =>
      if valid_expr_App2_bool rc f
      then valid_expr_bool true x && valid_expr_bool true y
      else if valid_expr_shift_bool rc f
           then valid_expr_bool true x && valid_shifter y
           else false
    | _ => false
    end = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z type_Z =>
       fun f =>
           valid_expr true y ->
           valid_expr rc (expr.App f y)
     | type.arrow type_ZZ _ =>
       fun f =>
         forall y,
           valid_expr true y ->
           valid_expr rc (expr.App f y)
     | _ => fun _ => False
     end) f.
  Proof.
    intro. remember t.
    break_match;
      try match goal with
          | |- forall (_:false = true), _ => congruence
          | H : valid_expr_App2_bool _ _ = true |- _ =>
            apply valid_expr_App2_bool_type in H;
              congruence
          | H : valid_expr_shift_bool _ _ = true |- _ =>
            apply valid_expr_shift_bool_type in H;
              congruence
          end; [ | ].
    { intros;
        repeat match goal with
               | H : _ && _ = true |- _ =>
                 apply andb_true_iff in H; destruct H
               | H : valid_expr_App2_bool _ _ = true |- _ =>
                 apply valid_expr_App2_bool_impl1 in H
               end.
      eauto. }
    { intros; 
        repeat match goal with
               | H : _ && _ = true |- _ =>
                 apply andb_true_iff in H; destruct H
               | H : valid_expr_shift_bool _ _ = true |- _ =>
                 apply valid_expr_shift_bool_impl1 in H
               end.
      eauto. }
  Qed.

  Lemma valid_expr_bool_impl1 {t} (e : API.expr t) :
    (exists b, t = type.base b) ->
    forall rc,
      valid_expr_bool rc e = true -> valid_expr rc e.
  Proof.
    induction e; intros;
      cbn [valid_expr_bool] in *.
    { break_match_hyps; try congruence.
      { constructor.
        repeat match goal with
               | _ => progress cbn [orb]
               | H : _ || _ = true |- _ =>
                 apply orb_true_iff in H; destruct H
               | H : _ = true |- _ => rewrite H
               | _ => rewrite Bool.orb_true_r
               | _ => reflexivity
               end. }
      { destruct rc; cbn [negb] in *; try congruence.
        constructor. } }
    { break_match_hyps; try congruence.
      { destruct rc; cbn [negb] in *; try congruence.
        constructor. }
      { constructor. } }
    { break_match_hyps; congruence. }
    { remember s.
      break_match_hyps; try congruence;
          repeat match goal with
                 | H : _ && _ = true |- _ =>
                   apply andb_true_iff in H; destruct H
                 | H: valid_expr_App1_bool _ _ = true |- _ =>
                   apply valid_expr_App1_bool_type in H;
                     destruct H; destruct H; congruence
                 end; [ | | | ].
      { apply (@valid_expr_App_bool_impl1 (type.arrow type_Z type_Z)).
        { 
        break_match; try congruence;
          repeat match goal with
                 | H : _ && _ = true |- _ =>
                   apply andb_true_iff in H; destruct H
                 | _ => assumption
                 end. }
      { eauto using valid_expr_nth_default_bool_impl1. }
      { pose proof H0.
        apply valid_expr_App1_bool_type in H0.
        destruct H0. destruct H0; try congruence.
        inversion H0; subst.
        (* need valid_expr_App1_bool_impl1 like nth_default model *)
        (* probably get rid of current valid_expr_App_bool_impl1? *)

  Fixpoint valid_expr_bool {t} (require_casts : bool)
             (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        (expr.Ident _ (ident.Literal base.type.zrange r))) x =>
      range_good r && valid_expr_bool false x
    | expr.App
        _ _
        (expr.App
           _ _ (expr.Ident _ ident.Z_cast2)
           (expr.App
              _ _
              (expr.App
                 _ _
                 (expr.Ident _ (ident.pair _ _))
                 (expr.Ident _ (ident.Literal base.type.zrange r1)))
              (expr.Ident _ (ident.Literal base.type.zrange r2)))) x =>
      range_good r1 && range_good r2 && valid_expr_bool false x
    | expr.App _ _ (expr.Ident _ (ident.fst _ _)) x =>
      negb require_casts && valid_expr_bool true x
    | expr.App _ _ (expr.Ident _ (ident.snd _ _)) x =>
      negb require_casts && valid_expr_bool true x
    | expr.Ident _ (ident.Literal base.type.Z z) =>
      negb require_casts || is_bounded_by_bool z max_range
    | expr.Ident _ (ident.Literal base.type.nat n) =>
      negb require_casts
    | expr.Var type_Z v => negb require_casts
    | expr.Var type_listZ v => true
    | expr.App
        _ _ (expr.App
               _ _ (expr.App
                      _ _ (expr.Ident _ (ident.List_nth_default _)) d)
               (expr.Var type_listZ l))
        (expr.Ident _ (ident.Literal base.type.nat i)) =>
      negb require_casts && valid_expr_bool true d
    | expr.App
        _ _ (expr.App
               _ _ (expr.Ident _ ident.Z_shiftr) x)
        (expr.Ident _ (ident.Literal base.type.Z n)) =>
      negb require_casts && is_bounded_by_bool n width_range
           && valid_expr_bool true x
    | expr.App
        _ _ (expr.App
               _ _ (expr.App
                      _ _ (expr.Ident _ ident.Z_mul_high)
                      (expr.Ident _ (ident.Literal base.type.Z s)))
               x) y =>
      negb require_casts && Z.eqb s (2 ^ Semantics.width)
           && valid_expr_bool true x && valid_expr_bool true y
    | expr.App
        _ _ (expr.App
               _ _ (expr.App
                      _ _ (expr.Ident _ ident.Z_truncating_shiftl)
                      (expr.Ident _ (ident.Literal base.type.Z s)))
               x)
        (expr.Ident _ (ident.Literal base.type.Z n)) =>
      negb require_casts && is_bounded_by_bool n width_range
           && Z.eqb s Semantics.width && valid_expr_bool true x
    | expr.App
        _ _ (expr.App _ _ (expr.Ident _ i) x) y =>
      match translate_binop i with
      | None => false
      | Some _ =>
        negb require_casts && valid_expr_bool true x
             && valid_expr_bool true y
      end
    | _ => false
    end.
  (* TODO: remove nat case *)


  Lemma valid_expr_bool_impl1 {t} (e : API.expr t) :
    forall rc,
      valid_expr_bool rc e = true -> valid_expr rc e.
  Proof.
    induction e; intros;
      cbn [valid_expr_bool] in *.
    { break_match_hyps; try congruence.
      { constructor.
        repeat match goal with
               | _ => progress cbn [orb]
               | H : _ || _ = true |- _ =>
                 apply orb_true_iff in H; destruct H
               | H : _ = true |- _ => rewrite H
               | _ => rewrite Bool.orb_true_r
               | _ => reflexivity
               end. }
      { destruct rc; cbn [negb] in *; try congruence.
        constructor. } }
    { break_match_hyps; try congruence.
      { destruct rc; cbn [negb] in *; try congruence.
        constructor. }
      { constructor. } }
    { break_match_hyps; try congruence. }
    { break_match_hyps; try congruence.
        repeat match goal with
               | _ => progress cbn [orb]
               | H : _ || _ = true |- _ =>
                 apply orb_true_iff in H; destruct H
               | H : _ = true |- _ => rewrite H
               | _ => rewrite Bool.orb_true_r
               | _ => reflexivity
               end.
        
        
        
      cbn [valid_expr_bool cast_exempt negb andb] in *;
      break_match_hyps;
      cbn [valid_ident_bool valid_cast_exempt_bool
                            valid_cast_bool
                            translate_binop] in *;
      repeat match goal with
             | H : false = true |- _ => congruence
             | H : true = false |- _ => congruence
             | H : exists _, type.arrow _ _ = type.base _ |- _ =>
               destruct H; congruence
             | _ => progress subst
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : _ && _ = false |- _ =>
               apply andb_false_iff in H; destruct H
             end.

  Definition valid_ident_bool {t} (i : ident.ident t)
    : type.for_each_lhs_of_arrow API.expr t -> (* argument expressions *)
      bool :=
    match i in ident.ident t0 return
          type.for_each_lhs_of_arrow (@API.expr (fun _ => unit))
                                     t0 -> bool with
    | ident.fst _ _ => fun _ => true
    | ident.snd _ _ => fun _ => true
    | ident.Z_cast => fun _ => true
    | ident.Z_cast2 => fun _ => true
    | ident.List_nth_default base_Z =>
      fun args =>
        let '(d, (l, (i, _))) := args in
        match i with
        | expr.Ident _ (ident.Literal base.type.nat i) =>
          true
        | _ => false
        end
    | ident.Z_shiftr =>
      fun args =>
        let '(x, (n, _)) := args in
        match n with
        | expr.Ident _ (ident.Literal base.type.Z n) =>
          is_bounded_by_bool n width_range
        | _ => false
        end
    | ident.Z_truncating_shiftl =>
      fun args =>
        let '(s, (x, (n, _))) := args in
        match s with
        | expr.Ident _ (ident.Literal base.type.Z s) =>
          match n with
          | expr.Ident _ (ident.Literal base.type.Z n) =>
            (Z.eqb s Semantics.width) && is_bounded_by_bool n width_range 
          | _ => false
          end
        | _ => false
        end
    | ident.Z_mul_high =>
      fun args =>
        let '(s, (x, (y, _))) := args in
        match s with
        | expr.Ident _ (ident.Literal base.type.Z s) =>
          Z.eqb s (2 ^ Semantics.width)
        | _ => false
        end
    | i =>
      fun _ =>
        match translate_binop i with
        | Some x => true
        | None => false
        end
    end.

  Definition valid_cast_exempt_bool {t}
             (require_in_bounds : bool)
             (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | (expr.Ident type_Z (ident.Literal base.type.Z z)) =>
      if require_in_bounds
      then is_bounded_by_bool z max_range
      else true 
    | (expr.Ident type_nat (ident.Literal base.type.nat n)) =>
      (* nats are only valid if not required to be in bounds
         (in practice, this means only if they are an argument to
         nth_default) *)
      negb (require_in_bounds)
    | expr.Var type_listZ x => true
    | _ => false
    end.

  Definition valid_cast_bool
             {t} (f : @API.expr (fun _ => unit) t) : bool :=
    match f with
    | expr.App
        _ _ (expr.Ident _ ident.Z_cast)
        (expr.Ident type_range (ident.Literal base.type.zrange r)) =>
      range_good r
    | expr.App
        _ _ (expr.Ident _ ident.Z_cast2)
        (expr.App
           _ _
           (expr.App
              _ _ (expr.Ident _ (ident.pair _ _))
              (expr.Ident type_range (ident.Literal base.type.zrange r1)))
           (expr.Ident type_range (ident.Literal base.type.zrange r2))) =>
      range_good r1 && range_good r2
    | _ => false
    end.

  Fixpoint valid_expr_bool {t} (require_cast : bool)
           (e : @API.expr (fun _ => unit) t) :
    type.for_each_lhs_of_arrow API.expr t -> bool :=
    if cast_exempt e
    then fun _ => valid_cast_exempt_bool require_cast e
    else if require_cast
         then match e in expr.expr t0 return
                    type.for_each_lhs_of_arrow _ t0 -> bool with
              | expr.App (type.base _) _ f x =>
                fun y =>
                  if valid_cast_bool f
                  then (valid_expr_bool false f (x, y))
                         && (valid_expr_bool false x tt)
                  else false
              | _ => fun _ => false
              end
         else
           match e in expr.expr t0 return
                 type.for_each_lhs_of_arrow _ t0 -> bool with
           | expr.App (type.base _) _ f x =>
             fun y =>
               let rc := require_cast_for_arg f in
               (valid_expr_bool false f (x, y))
                 && (valid_expr_bool rc x tt)
           | expr.Ident _ i => valid_ident_bool i
           | expr.Var type_Z x => fun _ => true
           | expr.Var type_listZ x => fun _ => true
           | _ => fun _ => false
           end.


  Lemma valid_expr_bool_impl1 {t} (e : API.expr t) :
    (exists b, t = type.base b) ->
    forall rc args,
      valid_expr_bool rc e args = true -> valid_expr rc e.
  Proof.
    induction e; intros;
      cbn [valid_expr_bool cast_exempt negb andb] in *;
      break_match_hyps;
      cbn [valid_ident_bool valid_cast_exempt_bool
                            valid_cast_bool
                            translate_binop] in *;
      repeat match goal with
             | H : false = true |- _ => congruence
             | H : true = false |- _ => congruence
             | H : exists _, type.arrow _ _ = type.base _ |- _ =>
               destruct H; congruence
             | _ => progress subst
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : _ && _ = false |- _ =>
               apply andb_false_iff in H; destruct H
             end.
    { destruct rc;
        constructor;
        repeat match goal with
               | H : is_bounded_by_bool _ _ = true |- _ =>
                 rewrite H
               | |- (_ || _)%bool = true => apply Bool.orb_true_iff
               | _ => tauto
               end. }
    { destruct rc;
        try constructor;
        repeat match goal with
               | H : false = true |- _ => congruence
               | _ => progress cbn [negb] in *
               | H : is_bounded_by_bool _ _ = true |- _ =>
                 rewrite H
               | |- (_ || _)%bool = true => apply Bool.orb_true_iff
               | _ => tauto
               end. }
    { constructor. }
    { break_match_hyps;
        try constructor;
        repeat match goal with
               | H : false = true |- _ => congruence
               end. }
    2:{
      


      cbv [is_cast] in *.
      break_match_hyps.
      constructor. 
  Qed.

  Lemma is_cast_literal_type {var t} (r : @API.expr var t) :

    is_cast_literal r = true ->
    t = type_range.
  Proof.
    cbv [is_cast_literal].
    break_match; congruence.
  Qed.

  Lemma valid_cast_ident {var t} (r : @API.expr var t) :
    is_cast_literal r = true ->
    (match t as t0 return
           expr.expr t0 -> Prop with
     | type_range =>
       fun r =>
         r = expr.Ident (ident.Literal (t:=base.type.zrange) max_range)
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast_literal].
    break_match; try congruence.
    destruct idc.

  Lemma valid_cast_ident {t} (f : API.expr t) :
    is_cast_ident f = true ->
    (match t as t0 return
           expr.expr t0 -> Prop with
     | type.arrow s1 (type.arrow s2 d) =>
       fun f =>
         forall
           (r : API.expr s1)
           (x : API.expr s2)
           (args : type.for_each_lhs_of_arrow API.expr d),
           is_cast_literal r = true ->
           valid_expr_bool false (expr.App f r) (x, args) = true ->
           valid_expr true x ->
           valid_expr true (expr.App (expr.App f r) x)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_cast_ident].
    break_match; try congruence;
      intros;
      try match goal with
          | H: @is_cast_literal _ _ type_range2 _ = true |- _ =>
            apply is_cast_literal_type in H; congruence
          end.
    break_match_hyps; try congruence.
    apply valid_cast_literal in H0
    

    2:{
      intros.
      apply valid_cast_literal in H0.
      congruence.
      exfalso.
      clear H1.
      remember type_ZZ.
      cbv [is_cast_literal] in *.
      break_match_hyps; try congruence.
      destruct r; try congruence.
      destruct idc; try congruence.
      destruct t; try congruence.
      { destruct idc0; try congruence.
        destruct t0; try congruence.

  Lemma valid_cast_impl1 {t} (f : API.expr t):
    is_cast f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.base _ => fun _ => False
     | type.arrow s d =>
       fun f =>
         forall
           (x : API.expr s)
           (args : type.for_each_lhs_of_arrow API.expr d),
           valid_expr_bool false f (x, args) = true ->
           (* valid_expr_bool false x tt = true -> *)
           valid_expr true (expr.App f x)
     end) f.
  Proof.
    cbv [is_cast].
    break_match; try congruence.
    remember t.
    repeat match goal with
           | |- forall (_: match ?x with | _ => _ end = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ _ = true), _ =>
             destruct x; try congruence
           end.
    { break_match.
      Set Printing Implicit.
      cbv [is_cast_ident].
      destruct f1.
    destruct f; try congruence.
    destruct s; try congruence.
    destruct t; try congruence.
    { destruct t; try congruence. 
    destruct f1.
  Lemma is_cast_ident_base
             {var s d} (e : @API.expr var (s -> d)) :
    (exists b, d = type.base b) ->
    is_cast_ident e = false.
  Proof.
    cbv [is_cast_ident].
    destruct e; try reflexivity.
    destruct idc; try reflexivity.
    break_match; try congruence. 
    destruct e; cbn.
    



  Definition valid_cast_postcondition {t}
    : API.expr t -> Prop :=
    match t as t0 return expr.expr t0 -> Prop with
     | type.base _ => fun _ => False
     | type.arrow s d =>
       fun f =>
         forall
           (x : API.expr s)
           (args : type.for_each_lhs_of_arrow API.expr d),
           valid_expr_bool false f (x, args) = true ->
           (* valid_expr_bool false x tt = true -> *)
           valid_expr true (expr.App f x)
     end. 

  Lemma valid_cast_apprange {t1 t2}
        (f : API.expr t1)
        (r : API.expr t2) :
    match f with
    | expr.Ident _ ident.Z_cast =>
      match r with
      | expr.Ident _ (ident.Literal base.type.zrange r) =>
        range_good r
      | _ => false
      end
    | _ => false
    end = true ->
    (match t1 as t3 return
           expr.expr t3 -> expr.expr t2 -> Prop with
     | type.arrow type_range d =>
       fun f =>
         match t2 as t4 return expr.expr t4 -> Prop with
         | type_range =>
           fun r =>
             valid_cast_postcondition (expr.App f r)
         | _ => fun _ => False
         end
     | _ => fun _ _ => False
     end) f r.
  Proof.
    destruct f; try congruence.
    destruct idc; try congruence.
    destruct r; try congruence.
    destruct idc; try congruence.
    destruct t; try congruence.
    cbn [valid_cast_postcondition]; intros.
    cbn [valid_expr_bool cast_exempt require_cast_for_arg] in *.
    rewrite Bool.andb_false_r in *. congruence.
  Qed.

  (*
  Lemma valid_cast2_apppair {t1 t2}
        (f : API.expr t1)
        (r : API.expr t2) :
    match f with
    | expr.App
        _ _ (expr.Ident type_range2 (ident.pair _ _))
        (expr.Ident _ (ident.Literal base.type.zrange r1)))
        (expr.Ident _ (ident.Literal base.type.zrange r2)) =>
      range_good r1 && range_good r2
    | _ => false
    end
    | _ => false
    end = true ->
    (match t1 as t3 return
           expr.expr t3 -> expr.expr t2 -> Prop with
     | type.arrow type_range2 d =>
       fun f =>
         match t2 as t4 return expr.expr t4 -> Prop with
         | type_range2 =>
           fun r =>
             valid_cast_postcondition (expr.App f r)
         | _ => fun _ => False
         end
     | _ => fun _ _ => False
     end) f r.
  Proof.
*)

  Lemma of_apprange {var d}
        (P : forall d,
            API.expr (var:=var) (type_range -> d) ->
            API.expr (var:=var) type_range -> Prop)
        (f : API.expr (type_range -> d))
        (x : API.expr type_range):
    (forall t1 t2
            (f' : API.expr t1)
            (x' : API.expr t2),
        (match t1 as t3
               return expr.expr t3 ->
                      expr.expr t2 -> Prop with
         | type.arrow type_range d0 =>
           fun f'' : API.expr (type_range -> d0) =>
             match t2 as t4
                   return expr.expr t4 -> Prop with
             | type_range =>
               fun x'' => P d0 f'' x''
             | _ => fun _ => False
             end
         | _ => fun _ _ => False
         end) f' x') ->
    P _ f x.
  Proof.
    let H := fresh in
    intro H; specialize (H _ _ f x).
    assumption.
  Qed.

  (*
    match f with
    | Ident (s -> d) _ => 
      match x with
      | _ =>
      end
    end = true ->
    P (f @ x)
    


    match f with
    | Ident (s -> d) _ => 
      match x with
      | _ =>
      end
    end = true ->
    P e

  *)
  Lemma of_apprange' {var d}
        (pre : forall t2 t1, (* important to take t2 first *)
            API.expr (var:=var) t1 ->
            API.expr (var:=var) t2 -> bool)
        (P : forall t,
            API.expr (var:=var) t -> Prop)
        (f : API.expr (type_range -> d))
        (x : API.expr type_range):
    (forall t1 t2 f' x',
        pre t2 t1 f' x' = true ->
        (match t1 as t3 return
               expr.expr t3 -> expr.expr t2 -> Prop with
         | type.arrow type_range d =>
           fun f'' =>
             match t2 as t4 return expr.expr t4 -> Prop with
             | type_range =>
               fun x'' =>
                 P _ (expr.App f'' x'')
             | _ => fun _ => False
             end
         | _ => fun _ _ => False
         end) f' x') ->
    (pre _ _ f x = true) ->
    P d (expr.App f x).
  Proof.
    let H := fresh in
    intro H; specialize (H _ _ f x).
    assumption.
  Qed.
  Lemma of_apprange2 {var d}
        (pre : forall t2 t1, (* important to take t2 first *)
            API.expr (var:=var) t1 ->
            API.expr (var:=var) t2 -> bool)
        (P : forall t,
            API.expr (var:=var) t -> Prop)
        (f : API.expr (type_range2 -> d))
        (x : API.expr type_range2):
    (forall t1 t2 f' x',
        pre t2 t1 f' x' = true ->
        (match t1 as t3 return
               expr.expr t3 -> expr.expr t2 -> Prop with
         | type.arrow type_range2 d =>
           fun f'' =>
             match t2 as t4 return expr.expr t4 -> Prop with
             | type_range2 =>
               fun x'' =>
                 P _ (expr.App f'' x'')
             | _ => fun _ => False
             end
         | _ => fun _ _ => False
         end) f' x') ->
    (pre _ _ f x = true) ->
    P d (expr.App f x).
  Proof.
    let H := fresh in
    intro H; specialize (H _ _ f x).
    assumption.
  Qed.
  
  (*
  Lemma valid_cast2_apprange {t1 t2}
        (f : API.expr t1)
        (r : API.expr t2) :
    match f with
    | expr.Ident _ ident.Z_cast2 =>
      match r with
      | expr.App
          _ _ (expr.App
                 _ _ (expr.Ident type_range2 (ident.pair _ _))
                 (expr.Ident _ (ident.Literal base.type.zrange r1)))
          (expr.Ident _ (ident.Literal base.type.zrange r2)) =>
        range_good r1 && range_good r2
      | _ => false
      end
    | _ => false
    end = true ->
    (match t1 as t3 return
           expr.expr t3 -> expr.expr t2 -> Prop with
     | type.arrow type_range2 d =>
       fun f =>
         match t2 as t4 return expr.expr t4 -> Prop with
         | type_range2 =>
           fun r =>
             valid_cast_postcondition (expr.App f r)
         | _ => fun _ => False
         end
     | _ => fun _ _ => False
     end) f r.
  Proof.
    repeat match goal with
           | |- forall (_: match ?x with | _ => _ end = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ _ = true), _ =>
             destruct x; try congruence
           end.
    eapply of_apprange.
    destruct r1.
    destruct f; try congruence.
    destruct idc; try congruence.
    destruct r; try congruence.
    destruct idc; try congruence.
    destruct t; try congruence.
    cbn [valid_cast_postcondition]; intros.
    cbn [valid_expr_bool cast_exempt require_cast_for_arg] in *.
    rewrite Bool.andb_false_r in *. congruence.
  Qed.
*)

  Lemma valid_cast_impl1 {t}
        (f : API.expr t) :
    is_cast f = true ->
    valid_cast_postcondition f.
  Proof.
    cbv [is_cast].
    repeat match goal with
           | |- forall (_: match ?x with | _ => _ end = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ = true), _ =>
             destruct x; try congruence
           | |- forall (_: (match ?x with | _ => _ end) _ _ = true), _ =>
             destruct x; try congruence
           end.
    { match goal with
      | e1 : API.expr (type.arrow ?s ?d), e2 : API.expr ?t2
        |- ?pre = true -> ?Q =>
        let pre :=
            lazymatch (eval pattern e2 in pre) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern e1 in pre) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern (type.arrow s d) in pre) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern t2 in pre) with ?f _ => f end in
        change (pre _ _ e1 e2 = true -> Q);
          intro;
          apply (of_apprange' pre); [ | assumption ]
      end.
      clear. intros *.
      repeat match goal with
             | |- forall (_: match ?x with | _ => _ end = true), _ =>
               destruct x; try congruence
             | |- forall (_: (match ?x with | _ => _ end) _ = true), _ =>
               destruct x; try congruence
             | |- forall (_: (match ?x with | _ => _ end) _ _ = true), _ =>
               destruct x; try congruence
             end.
      cbn [valid_cast_postcondition]; intros.
      cbn [valid_expr_bool cast_exempt require_cast_for_arg
                           valid_ident_bool andb] in *.
      congruence. }
    { match goal with
      | e1 : API.expr (type.arrow ?s ?d), e2 : API.expr ?t2
        |- ?pre = true -> ?Q =>
        let pre :=
            lazymatch (eval pattern e2 in pre) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern e1 in pre) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern (type.arrow s d) in pre) with ?f _ => f end in
        remember pre end.

      match type of Heqb with _ =
                              (fun t e (e0 : API.expr type_range2) =>
                                 ?f) =>
                              let pre :=
                                  constr:(fun t t' e (e0 : API.expr t') =>
                                     f) in
                              idtac pre
      end.
      
                              idtac f end.
                              let f := lazymatch (eval pattern type_range2 in x) with ?f _ => f end in idtac f end.
          idtac t2 pre end.
        let pre :=
            lazymatch (eval pattern t2 in pre) with ?f _ => f end in
          idtac pre end.
        change (pre _ _ e1 e2 = true -> Q);
          intro;
          apply (of_apprange' pre); [ | assumption ]
      end.
      clear. intros *.
      repeat match goal with
             | |- forall (_: match ?x with | _ => _ end = true), _ =>
               destruct x; try congruence
             | |- forall (_: (match ?x with | _ => _ end) _ = true), _ =>
               destruct x; try congruence
             | |- forall (_: (match ?x with | _ => _ end) _ _ = true), _ =>
               destruct x; try congruence
             end.
      cbn [valid_cast_postcondition]; intros.
      cbn [valid_expr_bool cast_exempt require_cast_for_arg
                           valid_ident_bool andb] in *.
      congruence. }
        
        intros. subst b.
      pose proof (fun d => @of_apprange' _ d b) as HAPP.
      intro H.
      apply HAPP.
      apply HAPP in H.
      apply (of_apprange' b).
      apply H.
      match goal with
      | |- ?P -> ?Q =>
        let pre :=
            lazymatch (eval pattern f1 in P) with ?f _ => f end in
        let pre :=
            lazymatch (eval pattern (type.arrow type_range (type.arrow type_Z type_Z)) in pre) with ?f _ => f end in
        idtac pre
      end.
      
    (pre _ _ f x = true) ->
    P d (expr.App f x).
      eapply of_apprange'; eauto; intros.
      break_match.
    { let H := fresh in
      intro H; apply valid_cast_apprange in H.
      assumption. }
    { 
    destruct f; try congruence.
    destruct s; try congruence.
    destruct t; try congruence.
    { destruct t; try congruence.
      destruct d; try congruence.
      destruct d1; try congruence.
      destruct t; try congruence.
      destruct t; try congruence.
      destruct d2; try congruence.
      destruct t; try congruence.
      destruct t; try congruence.
      intros.
      apply valid_cast_apprange in H.
      apply H. }
    { destruct t1; try congruence.
      destruct t; try congruence.
      destruct d; try congruence.
      destruct d1; try congruence.
      destruct t; try congruence.
      destruct t; try congruence.
      destruct d2; try congruence.
      destruct t; try congruence.
      destruct t; try congruence.
      intros.
      apply valid_cast_apprange in H.
      apply H. }

