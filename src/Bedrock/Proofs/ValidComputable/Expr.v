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

  Definition valid_expr_binop_bool {t} (require_casts : bool)
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
    | expr.Ident _ ident.Z_shiftl =>
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

  (* add an extra flag to translate binops because otherwise the inductive
     hypothesis won't be strong enough to give information about *both*
     arguments to a binop *)
  Fixpoint valid_expr_bool' {t}
           (binop_only shift_only require_casts : bool)
           (e : @API.expr (fun _ => unit) t) {struct e} : bool :=
    if binop_only
    then match e with
         | expr.App type_Z (type.arrow type_Z type_Z) f x =>
           (valid_expr_binop_bool require_casts f)
             && valid_expr_bool' false false true x
         | _ => false
         end
    else
      if shift_only
      then match e with
           | expr.App type_Z (type.arrow type_Z type_Z) f x =>
             (valid_expr_shift_bool require_casts f)
               && valid_expr_bool' false false true x
           | _ => false
           end
      else
        match e with
        | expr.App type_nat _ f x =>
          (* only thing accepting nat is nth_default *)
          if require_casts
          then false
          else valid_expr_nth_default_bool (expr.App f x)
        | expr.App type_Z type_Z f x =>
          if valid_expr_bool' true false require_casts f
          then (* f is a binop applied to one valid argument;
                check that x (second argument) is also valid *)
            valid_expr_bool' false false true x
          else if valid_expr_bool' false true require_casts f
               then (* f is a shift applied to one valid
                       argument; check that x (shifting index) is a
                       valid shifter *)
                 valid_shifter x
               else (* must be a cast *)
                 (valid_expr_App1_bool require_casts f)
                   && valid_expr_bool' false false false x
        | expr.App type_ZZ type_Z f x =>
          (* fst or snd *)
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' false false true x
        | expr.App type_ZZ type_ZZ f x =>
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' false false false x
        | expr.Ident _ (ident.Literal base.type.Z z) =>
          is_bounded_by_bool z max_range || negb require_casts
        | expr.Ident _ (ident.Literal base.type.nat n) =>
          negb require_casts
        | expr.Var type_Z v => true
        | expr.Var type_listZ v => true
        | _ => false
        end.

  Definition valid_expr_bool {t} := @valid_expr_bool' t false false.

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

  Lemma valid_expr_binop_bool_type {t} rc (f : API.expr t) :
    valid_expr_binop_bool rc f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z type_Z).
  Proof.
    cbv [valid_expr_binop_bool translate_binop].
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

  Lemma valid_expr_binop_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_binop_bool rc f = true ->
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
    cbv [valid_expr_binop_bool].
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
    break_match; try congruence; [ | | ];
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
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
  Qed.

  Lemma valid_expr_bool'_impl1 {t} (e : API.expr t) :
    forall binop_only shift_only rc,
      valid_expr_bool' binop_only shift_only rc e = true ->
      if binop_only
      then (match t as t0 return expr.expr t0 -> Prop with
            | type.arrow type_Z type_Z =>
              fun f =>
                forall x,
                  valid_expr true x ->
                  valid_expr rc (expr.App f x)
            | _ => fun _ => False
            end) e
      else if shift_only
           then (match t as t0 return expr.expr t0 -> Prop with
                 | type.arrow type_Z type_Z =>
                   fun f =>
                     forall x,
                       valid_shifter x = true ->
                       valid_expr rc (expr.App f x)
                 | _ => fun _ => False
                 end) e
           else
             (exists b, t = type.base b) -> valid_expr rc e.
  Proof.
    induction e; intros;
      cbn [valid_expr_bool'] in *;
      [ | | | | ].
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
      { constructor. }
      { constructor. } }
    { break_match_hyps; congruence. }
    { remember s.
      remember d.
      (** Work around COQBUG(https://github.com/coq/coq/issues/11959); suppress warning *)
      Local Set Warnings Append "-variable-collision".
      break_match_hyps; try congruence;
          repeat match goal with
                 | H : _ && _ = true |- _ =>
                   apply andb_true_iff in H; destruct H
                 | H: valid_expr_App1_bool _ _ = true |- _ =>
                   apply valid_expr_App1_bool_type in H;
                     destruct H; destruct H; congruence
                 | IH : forall binop_only shift_only _ _,
                     if binop_only
                     then False
                     else if shift_only
                          then False
                          else _ |- _ =>
                   specialize (IH false false); cbn in IH
                 end.
      { (* only_binop case *)
        intros.
        apply (valid_expr_binop_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* only_shift case *)
        intros.
        apply (valid_expr_shift_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* fully-applied binop case *)
        intros.
        apply (IHe1 true false); eauto. }
      { (* fully-applied shift case *)
        intros.
        apply (IHe1 false true); eauto. }
      { (* cast Z case *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_Z -> type_Z)); eauto. }
      { (* nth_default case *)
        eauto using valid_expr_nth_default_bool_impl1. }
      { (* fst/snd *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_ZZ -> type_Z)); eauto. }
      { (* cast ZZ *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_ZZ -> type_ZZ)); eauto. } }
    { break_match; try congruence. }
  Qed.

  Lemma valid_expr_bool_impl1 {t} (e : API.expr t) :
    (exists b, t = type.base b) ->
    forall rc,
      valid_expr_bool rc e = true -> valid_expr rc e.
  Proof.
    cbv [valid_expr_bool]; intros.
    match goal with H : _ = true |- _ =>
                    apply valid_expr_bool'_impl1 in H end.
    eauto.
  Qed.

  Lemma valid_expr_bool_impl2 {t} (e : API.expr t) :
    forall rc,
      valid_expr rc e ->
      valid_expr_bool rc e = true.
  Proof.
    cbv [valid_expr_bool].
    induction 1; intros; subst; cbn;
      repeat match goal with
             | _ => progress cbn [andb]
             | H : valid_expr_bool' _ _ _ _ = true |- _ =>
               rewrite H
             | _ => rewrite Z.eqb_refl
             end;
      auto using
           Bool.andb_true_iff, Bool.orb_true_iff,
      is_bounded_by_bool_max_range,
      is_bounded_by_bool_width_range; [ ].
    (* remaining case : binop *)
    match goal with
    | H : translate_binop ?i <> None
      |- context [match translate_binop ?i with _ => _ end] =>
      destruct (translate_binop i)
    end; cbn [andb]; congruence.
  Qed.

  Lemma valid_expr_bool_iff {t} (e : API.expr (type.base t)) :
    forall rc,
      valid_expr_bool rc e = true <-> valid_expr rc e.
  Proof.
    split; eauto using valid_expr_bool_impl1, valid_expr_bool_impl2.
  Qed.
End Expr.
