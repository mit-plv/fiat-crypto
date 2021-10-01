Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Expr.
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

Section Expr.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.

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
      is_cast_ident_expr f && is_cast_literal(width:=width) r
    | expr.App type_range2 (type.arrow type_ZZ type_ZZ) f r =>
      is_cast_ident_expr f && is_cast2_literal(width:=width) r
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
        && (Z.eqb s (2 ^ width))
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
        && Z.eqb s width
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
      is_bounded_by_bool n (@width_range width)
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
      valid_expr_nth_default_App3_bool f && is_bounded_by_bool d (@max_range width)
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

  Definition is_literalz {t}
             (e : @API.expr (fun _ => unit) t) (z : Z) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z x) => Z.eqb x z
    | _ => false
    end.
  Definition valid_expr_select_bool {t}
             rc (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ ident.Z_zselect => negb rc
    | _ => false
    end.

  Definition valid_expr_lnot_modulo_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ ident.Z_lnot_modulo =>
      negb require_casts
    | _ => false
    end.
  Definition valid_lnot_modulus {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z n) =>
      (is_bounded_by_bool (n-1) (@max_range width)) && (n =? 2 ^ Z.log2 n)
    | _ => false
    end.

  (* opp is the only unary operation we accept *)
  Definition is_opp_ident {t} (i : ident t) : bool :=
    match i with
    | ident.Z_opp => true
    | _ => false
    end.
  Definition is_opp_ident_expr
             {t} (e : @API.expr (fun _ => unit) t) :=
    match e with
    | expr.Ident (type.arrow type_Z type_Z) i => is_opp_ident i
    | _ => false
    end.

  (* Because some operations are only valid if the arguments obey certain
     constraints, and to make the inductive logic work out, it helps to be able
     to call valid_expr_bool' recursively but have it return false for anything
     other than a specific kind of operation. This lets us, on encountering the
     very last application in a multi-argument function, take a sneak peek ahead
     to see if the rest of the applications match a certain kind of operation,
     and then enforce any constraints on the last argument. *)
  Inductive PartialMode := NotPartial | Binop | Shift | Select | Lnot.

  Fixpoint valid_expr_bool' {t}
           (mode : PartialMode) (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) {struct e} : bool :=
    match mode with
    | Binop =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_binop_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Shift =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_shift_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Select =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_bool' Select require_casts f)
          && is_literalz x 0
      | expr.App type_Z
                 (type.arrow type_Z
                             (type.arrow type_Z type_Z)) f x =>
        (valid_expr_select_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Lnot =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_lnot_modulo_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | NotPartial =>
        match e with
        | expr.App type_nat _ f x =>
          (* only thing accepting nat is nth_default *)
          if require_casts
          then false
          else valid_expr_nth_default_bool (expr.App f x)
        | expr.App type_Z type_Z f x =>
          if valid_expr_bool' Binop require_casts f
          then (* f is a binop applied to one valid argument;
                check that x (second argument) is also valid *)
            valid_expr_bool' NotPartial true x
          else if valid_expr_bool' Shift require_casts f
               then (* f is a shift applied to one valid
                       argument; check that x (shifting index) is a
                       valid shifter *)
                 valid_shifter x
               else if valid_expr_bool' Select require_casts f
                    then (* f is a select; make sure x = 2^w-1 *)
                      is_literalz x (2^width-1)
                    else
                      if valid_expr_bool' Lnot require_casts f
                      then (* f is lnot_modulo; make sure argument is a valid
                              modulus *)
                        (negb require_casts)
                          && valid_lnot_modulus x
                      else
                        if is_opp_ident_expr f
                        then (* f is opp *)
                          (negb require_casts)
                            && valid_expr_bool' NotPartial true x
                        else (* must be a cast *)
                          (valid_expr_App1_bool require_casts f)
                            && valid_expr_bool' NotPartial false x
        | expr.App type_ZZ type_Z f x =>
          (* fst or snd *)
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' NotPartial true x
        | expr.App type_ZZ type_ZZ f x =>
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' NotPartial false x
        | expr.Ident _ (ident.Literal base.type.Z z) =>
          is_bounded_by_bool z (@max_range width)|| negb require_casts
        | expr.Ident _ (ident.Literal base.type.nat n) =>
          negb require_casts
        | expr.Var type_Z v => true
        | expr.Var type_listZ v => true
        | _ => false
        end
    end.

  Definition valid_expr_bool {t} := @valid_expr_bool' t NotPartial.

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
    is_bounded_by_bool d (@max_range width) = true ->
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
    is_cast_literal_ident (width:=width) i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type_range =>
       fun i => i = ident.Literal (t:=base.type.zrange) (@max_range width)
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
    is_cast_literal (width:=width) r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range =>
       fun r =>
         r = expr.Ident (ident.Literal (t:=base.type.zrange) (@max_range width))
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
    is_cast2_literal_App1 (width:=width) r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type.arrow type_range type_range2 =>
       fun r =>
         r = expr.App
               (expr.Ident ident.pair)
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) (@max_range width)))
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
    is_cast2_literal (width:=width) r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range2 =>
       fun r =>
         r = expr.App
               (expr.App
                  (expr.Ident ident.pair)
                  (expr.Ident
                     (ident.Literal (t:=base.type.zrange) (@max_range width))))
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) (@max_range width)))
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
           is_cast_literal (width:=width) r = true ->
           valid_expr false x ->
           valid_expr rc (expr.App (expr.App f r) x)
     | type.arrow type_range2 (type.arrow type_ZZ type_ZZ) =>
       fun f =>
         forall
           (r : API.expr type_range2)
           (x : API.expr type_ZZ),
           is_cast2_literal (width:=width) r = true ->
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
           is_bounded_by_bool n (@width_range width) = true /\
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

  Lemma is_literalz_impl1 {t} (e : API.expr t) (x : Z) :
    is_literalz e x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun e => e = expr.Ident (ident.Literal (t:=base.type.Z) x)
     | _ => fun _ => False
     end) e.
  Proof.
    cbv [is_literalz].
    break_match; try congruence; intros.
    Z.ltb_to_lt; subst; congruence.
  Qed.

  Lemma is_opp_ident_eq {t} (i : ident.ident t) :
    is_opp_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z type_Z => fun i => i = ident.Z_opp
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_opp_ident]. break_match; congruence.
  Qed.

  Lemma is_opp_ident_expr_eq {t} (f : API.expr t) :
    is_opp_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z type_Z =>
       fun f => f = expr.Ident ident.Z_opp
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_opp_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_opp_ident _ = true |- _ =>
        apply is_opp_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_expr_select_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_select_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f =>
         forall c x y : API.expr type_Z,
           valid_expr true c ->
           is_literalz x 0 = true ->
           is_literalz y (2^width-1) = true ->
           valid_expr rc
                      (expr.App
                         (expr.App
                            (expr.App f c) x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_select_bool].
    break_match; try congruence; [ ]; intros.
    repeat match goal with
           | H : negb ?rc = true |- _ =>
             destruct rc; cbn [negb] in *; try congruence; [ ]
           | H : is_literalz _ _ = true |- _ =>
             apply is_literalz_impl1 in H
           end.
    subst; constructor; eauto.
  Qed.

  Lemma valid_lnot_modulus_eq {t} (x : API.expr t) :
    valid_lnot_modulus x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun x =>
         exists n,
           is_bounded_by_bool (n-1) (@max_range width) = true
           /\ n = 2 ^ Z.log2 n
           /\ x = expr.Ident (ident.Literal (t:=base.type.Z) n)
     | _ => fun _ => False
     end) x.
  Proof.
    cbv [valid_lnot_modulus].
    break_match; try congruence; [ ].
    intros; eexists; repeat split; eauto.
  Qed.

  Lemma valid_expr_lnot_modulo_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_lnot_modulo_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_lnot_modulus y = true ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_lnot_modulo_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : valid_lnot_modulus _ = true |- _ =>
               apply valid_lnot_modulus_eq in H;
                 destruct H as [? [? [? ?] ] ]; subst
             end.
    constructor; eauto.
  Qed.

  Lemma valid_expr_bool'_impl1 {t} (e : API.expr t) :
    forall mode rc,
      valid_expr_bool' mode rc e = true ->
      match mode with
      | Binop =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_expr true x ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | Shift =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_shifter x = true ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | Select =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               is_literalz x (2^width-1) = true ->
               valid_expr rc (expr.App f x)
         | type.arrow type_Z (type.arrow type_Z type_Z) =>
           fun f =>
             forall x y,
               is_literalz x 0 = true ->
               is_literalz y (2^width-1) = true ->
               valid_expr rc (expr.App (expr.App f x) y)
         | type.arrow
             type_Z
             (type.arrow type_Z (type.arrow type_Z type_Z)) =>
           fun f =>
             forall c x y,
               valid_expr true c ->
               valid_expr_select_bool rc f = true ->
               is_literalz x 0 = true ->
               is_literalz y (2^width-1) = true ->
               valid_expr rc (expr.App (expr.App (expr.App f c) x) y)
         | _ => fun _ => False
         end) e
      | Lnot =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_lnot_modulus x = true ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | NotPartial => (exists b, t = type.base b) -> valid_expr rc e
      end.
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
      break_match_hyps; try congruence;
          repeat match goal with
                 | H : _ && _ = true |- _ =>
                   apply andb_true_iff in H; destruct H
                 | H: valid_expr_App1_bool _ _ = true |- _ =>
                   apply valid_expr_App1_bool_type in H;
                     destruct H; destruct H; congruence
                 | IH : forall mode _ _,
                     match mode with
                     | NotPartial => _
                     | Binop => False
                     | Shift => False
                     | Select => False
                     | Lnot => False
                     end |- _ =>
                   specialize (IH NotPartial); (cbn match in IH)
                 end.
      { (* fully-applied binop case *)
        intros. apply (IHe1 Binop); eauto. }
      { (* fully-applied shift case *)
        intros. apply (IHe1 Shift); eauto. }
      { (* fully-applied select case *)
        intros.  apply (IHe1 Select); eauto. }
      { (* fully-applied lnot_modulo case *)
        intros.  apply (IHe1 Lnot); eauto. }
      { (* opp case *)
        intros.
        repeat match goal with
               | H : is_opp_ident_expr _ = true |- _ =>
                 apply is_opp_ident_expr_eq in H; subst
               | H : negb ?rc = true |- _ =>
                 destruct rc; cbn [negb] in *; try congruence; [ ]
               end.
        econstructor.
        eauto. }
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
                 (t := type_ZZ -> type_ZZ)); eauto. }
      { (* partially-applied binop case *)
        intros.
        apply (valid_expr_binop_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied shift case *)
        intros.
        apply (valid_expr_shift_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied select case (last 2 arguments) *)
        intros. apply (IHe1 Select); eauto. }
      { (* partially-applied select case (all 3 arguments) *)
        intros.
        apply (valid_expr_select_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied lnot_modulo case *)
        intros.
        apply (valid_expr_lnot_modulo_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. } }
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
             | H : valid_expr_bool' _ _ _ = true |- _ =>
               rewrite H
             | _ => rewrite Z.eqb_refl
             end;
      auto using
           Bool.andb_true_iff, Bool.orb_true_iff,
      is_bounded_by_bool_max_range,
      is_bounded_by_bool_width_range; [ | | ].
    { (* lnot_modulo *)
      apply Bool.andb_true_iff; split;
        Z.ltb_to_lt; auto. }
    { (* select *)
      break_match;
        repeat match goal with
               | H : (_ && _)%bool = true  |- _ =>
                 apply Bool.andb_true_iff in H; destruct H
               end; congruence. }
    { (* binop *)
      match goal with
      | H : translate_binop ?i <> None
        |- context [match translate_binop ?i with _ => _ end] =>
        destruct (translate_binop i)
      end; cbn [andb]; congruence. }
  Qed.

  Lemma valid_expr_bool_iff {t} (e : API.expr (type.base t)) :
    forall rc,
      valid_expr_bool rc e = true <-> valid_expr rc e.
  Proof.
    split; eauto using valid_expr_bool_impl1, valid_expr_bool_impl2.
  Qed.
End Expr.
