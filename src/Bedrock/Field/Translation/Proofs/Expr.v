Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.CastLemmas.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Translation.Proofs.EquivalenceProperties.
Require Import Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.LnotModulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations.

Section Expr.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.

  Inductive valid_expr
    : forall {t},
      bool (* require_casts *) ->
      @API.expr (fun _ => unit) t -> Prop :=
  | valid_cast1 :
      forall rc r x,
        valid_expr false x ->
        range_good (width:=width) r = true ->
        valid_expr rc
                   (expr.App
                      (expr.App (expr.Ident ident.Z_cast)
                                (expr.Ident (ident.Literal (t:=base.type.zrange) r))) x)
  | valid_cast2 :
      forall (rc : bool) r1 r2 x,
        valid_expr false x ->
        range_good (width:=width) r1 = true ->
        range_good (width:=width) r2 = true ->
        valid_expr rc
                   (expr.App
                      (expr.App (expr.Ident ident.Z_cast2)
                                (expr.App
                                   (expr.App
                                      (expr.Ident ident.pair)
                                      (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                                   (expr.Ident (ident.Literal (t:=base.type.zrange) r2)))) x)
  | valid_fst :
      forall (x : API.expr type_ZZ),
        valid_expr true x ->
        valid_expr false (expr.App (expr.Ident ident.fst) x)
  | valid_snd :
      forall (x : API.expr type_ZZ),
        valid_expr true x ->
        valid_expr false (expr.App (expr.Ident ident.snd) x)
  | valid_literalz :
      forall rc z,
        (is_bounded_by_bool z (max_range(width:=width)) || negb rc)%bool = true ->
        valid_expr rc (expr.Ident (ident.Literal (t:=base.type.Z) z))
  | valid_literalnat :
      forall n,
        valid_expr false (expr.Ident (ident.Literal (t:=base.type.nat) n))
  | valid_var_z :
      forall rc v, valid_expr (t:=type_Z) rc (expr.Var v)
  | valid_var_listz :
      forall rc v, valid_expr (t:=type_listZ) rc (expr.Var v)
  | valid_nth_default :
      forall d l i,
        (* only accepting literal d, because it makes things easier for
           computable condition *)
        0 <= d < 2 ^ width ->
        valid_expr
          false
          (expr.App
             (expr.App
                (expr.App
                   (expr.Ident
                      (ident.List_nth_default (t:=base_Z)))
                   (expr.Ident (ident.Literal (t:=base.type.Z) d)))
                (expr.Var l))
             (expr.Ident (ident.Literal (t:=base.type.nat) i)))
  | valid_shiftr :
      forall (x : API.expr type_Z) n,
        valid_expr true x ->
        0 <= n < width ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App (expr.Ident ident.Z_shiftr) x)
                   (expr.Ident (ident.Literal (t:=base.type.Z) n)))
  | valid_shiftl :
      forall (x : API.expr type_Z) n,
        valid_expr true x ->
        0 <= n < width ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App (expr.Ident ident.Z_shiftl) x)
                   (expr.Ident (ident.Literal (t:=base.type.Z) n)))
  | valid_mul_high :
      forall (s : Z) (x y : API.expr type_Z),
        s = 2 ^ width ->
        valid_expr true x ->
        valid_expr true y ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App
                                (expr.App (expr.Ident ident.Z_mul_high)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                x) y)
  | valid_truncating_shiftl :
      forall (s n : Z) (x : API.expr type_Z),
        s = width ->
        0 <= n < width ->
        valid_expr true x ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App
                                (expr.App (expr.Ident ident.Z_truncating_shiftl)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                x) (expr.Ident (ident.Literal (t:=base.type.Z) n)))
  | valid_lnot_modulo :
      forall (x : API.expr type_Z) (m : Z),
        is_bounded_by_bool (m-1) (max_range(width:=width)) = true ->
        2 ^ Z.log2 m = m ->
        valid_expr true x ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App (expr.Ident ident.Z_lnot_modulo)
                                       x)
                             (expr.Ident (ident.Literal (t:=base.type.Z) m)))
  | valid_zselect :
      forall (c : API.expr type_Z) (x y : Z),
        x = 0 ->
        y = 2^width-1 ->
        valid_expr true c ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.App
                                (expr.App (expr.Ident ident.Z_zselect) c)
                                (expr.Ident (ident.Literal (t:=base.type.Z) x)))
                                (expr.Ident (ident.Literal (t:=base.type.Z) y)))
  | valid_opp :
      forall (x : API.expr type_Z),
        valid_expr true x ->
        valid_expr (t:=type_Z) false
                   (expr.App (expr.Ident ident.Z_opp) x)
  | valid_binop :
      forall i (x y : API.expr type_Z),
        translate_binop i <> None ->
        valid_expr (t:=type_Z) true x ->
        valid_expr (t:=type_Z) true y ->
        valid_expr (t:=type_Z) false (expr.App (expr.App (expr.Ident i) x) y)
  .

  (* version generalized to any t, necessary to destruct i *)
  Lemma translate_binop_correct' {t} :
    forall (i : ident.ident t)
           (xargs : type.for_each_lhs_of_arrow API.interp_type t)
           (yargs : type.for_each_lhs_of_arrow rtype t)
           op locals,
      translate_binop i = Some op ->
      locally_equivalent_args xargs yargs locals ->
      (match t as t0
            return
            rtype t0 ->
            API.interp_type t0 ->
            type.for_each_lhs_of_arrow API.interp_type t0 ->
            type.for_each_lhs_of_arrow rtype t0 ->
            Prop with
      | (type_Z -> type_Z -> type_Z)%etype =>
        fun op (f : Z -> Z -> Z) (x : Z * (Z * unit))
            (y : (Syntax.expr * (Syntax.expr * unit))) =>
          let x1 := fst x in
          let x2 := fst (snd x) in
          let y1 := fst y in
          let y2 := fst (snd y) in
          WeakestPrecondition.dexpr
            map.empty locals (op y1 y2)
            (word.of_Z (f x1 x2))
      | _ => fun _ _ _ _ => False
       end) op (Compilers.ident_interp i) xargs yargs.
  Proof.
    cbv [translate_binop]; intros *.
    break_match; try congruence; intros.
    all:repeat match goal with
               | _ => progress sepsimpl
               | _ => progress
                        cbn [fst snd
                                 Compilers.ident_interp
                                 type.app_curried
                                 type.final_codomain
                                 equivalent_base
                                 rep.equiv rep.Z
                                 equivalent_args
                                 locally_equivalent_args
                                 Semantics.interp_binop] in *
               | _ => progress
                        cbn [Language.Compilers.base.interp
                               Compilers.type.interp
                               Compilers.base_interp] in *
               | _ => progress
                        (cbv [WeakestPrecondition.dexpr] in *;
                         cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body])
               | H : Some _ = Some _ |- _ => inversion H; subst; clear H
               | H : word.unsigned _ = _ |- _ => rewrite <-H
               | _ => break_match; [ ]; cbn [fst snd]
               end.
    all: (do 2 (eapply Proper_expr; [ | eassumption]; repeat intro; subst)).
    (* solves ring operations *)
    all:autorewrite with rew_word_morphism.
    all:rewrite ?word.of_Z_unsigned; try reflexivity.

    (* solves and/or/xor *)
    all:apply word.unsigned_inj; rewrite ?word.unsigned_of_Z.
    all:first [ rewrite word.unsigned_and
              | rewrite word.unsigned_ltu
              | rewrite word.unsigned_xor
              | rewrite word.unsigned_or ].
    all: try reflexivity.

    (* last goal: ltu *)
    { cbv [Definitions.Z.ltz].
      rewrite Bool.pull_bool_if, word.unsigned_of_Z.
      reflexivity. }
  Qed.

  Lemma translate_binop_correct
        (i : ident.ident (type_Z -> type_Z -> type_Z))
        (x1 x2 : base.interp base_Z)
        (y1 y2 : Syntax.expr)
        op l :
    translate_binop i = Some op ->
    locally_equivalent (t:=type_Z) x1 y1 l ->
    locally_equivalent (t:=type_Z) x2 y2 l ->
    WeakestPrecondition.dexpr
      map.empty l
      (op y1 y2) (word.of_Z (Compilers.ident_interp i x1 x2)).
  Proof.
    intros.
    apply (translate_binop_correct'
             i (x1, (x2, tt)) (y1, (y2, tt)));
      eauto; [ ].
    cbv [locally_equivalent] in *.
    cbn [locally_equivalent_args equivalent_args fst snd].
    repeat lazymatch goal with
           | |- exists _, _ => exists (Separation.emp True)
           | |- _ /\ _ => split
           | |- True => tauto
           | _ => solve [sepsimpl; eauto]
           end.
  Qed.

  Fixpoint locally_equivalent_nobounds_base {t}
    : base.interp t -> base_rtype t -> locals -> Prop :=
    match t as t0 return
          base.interp t0 ->
          base_rtype t0 ->
          locals -> Prop with
    | base.type.prod a b =>
      fun x y locals =>
        locally_equivalent_nobounds_base (fst x) (fst y) locals /\
        locally_equivalent_nobounds_base (snd x) (snd y) locals
    | base_Z =>
      fun x y locals =>
        WeakestPrecondition.dexpr map.empty locals y (word.of_Z x)
    | base_nat =>
      fun x y locals =>
        WeakestPrecondition.dexpr map.empty locals y (word.of_Z (Z.of_nat x))
    | base_listZ =>
      (* we never assign to lists, so they get a pass *)
      fun _ _ _ => True
    | _ => fun _ _ _ => False
    end.
  Definition locally_equivalent_nobounds {t}
    : API.interp_type t -> rtype t -> locals -> Prop :=
    match t with
    | type.base b => locally_equivalent_nobounds_base
    | type.arrow _ _ => fun _ _ _ => False
    end.

  Lemma locally_equivalent_nobounds_impl {t} :
    forall x y locals,
      locally_equivalent (t:=type.base t) x y locals ->
      locally_equivalent_nobounds x y locals.
  Proof.
    cbv [locally_equivalent equivalent locally_equivalent_nobounds].
    induction t;
      cbn [equivalent_base
             locally_equivalent
             locally_equivalent_nobounds_base
             rep.equiv rep.Z rep.listZ_local];
      break_match; intros; sepsimpl; subst;
        rewrite ?word.of_Z_unsigned; eauto.
  Qed.

  Lemma require_cast_for_arg_binop {var t} :
    forall i : ident.ident t,
      translate_binop i <> None ->
      require_cast_for_arg (width:=width) (var:=var) (expr.Ident i) = true.
  Proof.
    destruct i;
      cbn [translate_binop require_cast_for_arg];
      congruence.
  Qed.

  Lemma require_cast_for_arg_binop2 {var s d} :
    forall (i : ident.ident (s -> d)) x,
      translate_binop i <> None ->
      require_cast_for_arg (width:=width) (var:=var) (expr.App (expr.Ident i) x) = true.
  Proof.
    (* destruct is too weak *)
    intro i.
    refine match i with
           | ident.Literal _ _ => _
           | _ => _
           end; try exact idProp; try reflexivity;
      cbn [translate_binop]; congruence.
  Qed.

  Lemma translate_ident_binop {t} :
    forall i : ident.ident t,
      translate_binop i <> None ->
      translate_binop i = Some (translate_ident i).
  Proof.
    destruct i;
      cbn [translate_binop]; try congruence.
    all:cbn [translate_ident translate_binop].
    all:reflexivity.
  Qed.

  Lemma translate_binop_cast_exempt {var t} :
    forall i : ident.ident t,
      translate_binop i <> None ->
      cast_exempt (var:=var) (expr.Ident i) = false.
  Proof.
    destruct i;
      cbn [translate_binop cast_exempt];
      congruence.
  Qed.

  Lemma is_bounded_by_bool_max_range n :
    0 <= n < 2 ^ width ->
    is_bounded_by_bool n (max_range(width:=width)) = true.
  Proof.
    intros; cbv [is_bounded_by_bool upper lower max_range].
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
  Qed.

  Lemma is_bounded_by_bool_width_range n :
    0 <= n < width ->
    is_bounded_by_bool n (@width_range width) = true.
  Proof.
    intros; cbv [is_bounded_by_bool upper lower width_range].
    apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
  Qed.

  (* useful fact to say anything in width_range is also in max_range *)
  Lemma width_lt_pow2width : width < 2 ^ width.
  Proof. pose proof word.width_pos. apply Z.pow_gt_lin_r; lia. Qed.

  Lemma pow2width_pos : 0 < 2 ^ width.
  Proof.
    pose proof word.width_pos.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  (** TODO: Find a better place for this *)
  Hint Rewrite word.testbit_wrap : Ztestbit_full.
  Lemma translate_expr_correct' {t}
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
      if require_cast
      then locally_equivalent (API.interp e2) out locals
      else locally_equivalent_nobounds (API.interp e2) out locals.
  Proof.
    cbv zeta.
    pose proof width_lt_pow2width.
    pose proof pow2width_pos.

    induction 1; inversion 1; cleanup_wf; intros.

    all:repeat match goal with
               | _ => progress cleanup_wf
               | H : wf3 _ ?x ?y _ |- _ =>
                 (* for specific cases, repeatedly do inversion *)
                 progress match y with
                          | expr.App _ _ => idtac (* don't invert original, already-inverted hypothesis *)
                          | _ => match x with
                                 | context [expr.Ident] =>
                                   inversion H; clear H
                                 | context [expr.Var] =>
                                   inversion H; clear H
                                 end
                          end
               end.

    all:cbv [locally_equivalent equivalent].
    all:cbn [locally_equivalent_nobounds] in *.
    all:cbn [expr.interp Compilers.ident_interp].
    all:cbn [translate_expr is_cast is_cast_literal_ident
                            is_cast_literal is_cast2_literal
                            is_cast2_literal_App1
                            is_cast2_literal_App2
                            is_cast_ident is_cast_ident_expr
                            is_pair_range negb andb].
    all:rewrite ?require_cast_for_arg_binop by auto.
    all:rewrite ?require_cast_for_arg_binop2 by auto.
    all:rewrite ?translate_binop_cast_exempt by auto.
    all:cbn [require_cast_for_arg cast_exempt
                                  translate_cast_exempt].
    all:repeat match goal with
               | H : range_good _ = _ |- _ =>
                 rewrite H
               | H : is_bounded_by_bool _ _ = true |- _ =>
                 rewrite H
               | _ => rewrite is_bounded_by_bool_width_range by lia
               | _ => rewrite is_bounded_by_bool_max_range by lia
               end.
    all:cbn [negb andb];
      rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.if_const.

    (* solve the binop goal first (nasty when translate_ident unfolded) *)
    all: try match goal with
             | H : translate_binop _ <> None |- _ =>
               apply translate_binop_correct;
                 eauto using translate_ident_binop end.

    all:cbn [translate_ident translate_binop].

    { (* cast1 *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent equivalent_base rep.equiv rep.Z
                              locally_equivalent_nobounds_base] in *.
      cbv [range_good max_range ident.literal] in *.
      intros; progress reflect_beq_to_eq zrange_beq; subst.
      rewrite ident.cast_out_of_bounds_simple_0_mod by lia.
      cleanup.
      rewrite Z.sub_simpl_r.
      erewrite word.of_Z_inj_mod
        by (rewrite Z.mod_mod by lia; reflexivity).
      destruct rc; try eexists; sepsimpl;
        try apply Z.mod_pos_bound; try lia;
          eauto; [ ].
      rewrite word.unsigned_of_Z. reflexivity. }
    { (* cast2 *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbv [range_good max_range ident.literal ident.cast2] in *.
      cbn [locally_equivalent equivalent_base rep.equiv rep.Z fst snd
                              locally_equivalent_nobounds_base] in *.
      cbn [Compilers.base_interp] in *.
      intros; progress reflect_beq_to_eq zrange_beq; subst.
      rewrite !ident.cast_out_of_bounds_simple_0_mod by lia.
      rewrite Z.sub_simpl_r.
      destruct rc; repeat match goal with
                          | _ => progress sepsimpl
                          | _ => rewrite word.unsigned_of_Z
                          | _ => eassumption
                          | _ => eexists
                          | _ =>
                            erewrite word.of_Z_inj_mod
                              by (rewrite Z.mod_mod by lia; reflexivity);
                              solve [eauto]
                          end. }
    { (* fst *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent equivalent] in *.
      cbn [locally_equivalent_nobounds_base
             locally_equivalent_nobounds
             equivalent_base rep.equiv rep.Z] in *.
      sepsimpl; eauto.
      match goal with
      | H : word.unsigned _ = _ |- _ => rewrite <-H
      end.
      rewrite word.of_Z_unsigned. auto. }
    { (* snd *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent equivalent] in *.
      cbn [locally_equivalent_nobounds_base
             locally_equivalent_nobounds
             equivalent_base rep.equiv rep.Z] in *.
      sepsimpl; eauto.
      match goal with
      | H : word.unsigned _ = _ |- _ => rewrite <-H
      end.
      rewrite word.of_Z_unsigned. auto. }
    { (* literal Z *)
      cbn [locally_equivalent_nobounds_base
             locally_equivalent equivalent_base rep.equiv rep.Z].
      cbv [ident.literal] in *.
      repeat match goal with
             | H : (_ || _)%bool = true |- _ =>
               apply Bool.orb_true_iff in H; destruct H
             | H : is_bounded_by_bool _ _ = true |- _ =>
               rewrite H
             | H : is_bounded_by_bool _ _ = true |- _ =>
               cbv [is_bounded_by_bool upper lower max_range] in H;
                 apply Bool.andb_true_iff in H; cleanup
             end; Z.ltb_to_lt.
      all:destruct rc; cbn [negb] in *; try congruence.
      all:eexists; sepsimpl; try reflexivity.
      all:rewrite ?word.unsigned_of_Z; cbv [word.wrap].
      all:Z.rewrite_mod_small; try reflexivity. }
    { (* literal nat *)
      reflexivity. }
    { (* var (Z) *)
      match goal with
      | H : context_equiv _ _ |- _ =>
        cbv [context_equiv] in H;
          rewrite Forall_forall in H;
          specialize (H _ ltac:(eassumption))
      end.
      cbv [equiv3 locally_equivalent] in *.
      destruct rc;
      try apply locally_equivalent_nobounds_impl;
      eauto. }
    { (* var (list Z) *)
      match goal with
      | H : context_equiv _ _ |- _ =>
        cbv [context_equiv] in H;
          rewrite Forall_forall in H;
          specialize (H _ ltac:(eassumption))
      end.
      cbv [equiv3 locally_equivalent] in *.
      destruct rc;
      try apply locally_equivalent_nobounds_impl;
      eauto. }
    { (* nth_default *)
      cbv [ident.literal rnth_default]. rewrite Nat2Z.id.
      apply locally_equivalent_nobounds_impl.
      match goal with
        |- locally_equivalent
             (nth_default ?d1 ?l1 ?i) (nth_default ?d2 ?l2 ?i) ?locals =>
        let R := constr:(fun x y =>
                           locally_equivalent (t:=type_Z) x y locals) in
        assert (length l1 = length l2 /\
                (forall i,
                    R (nth_default d1 l1 i) (nth_default d2 l2 i)));
          [ apply (@Forall.Forall2_forall_iff'' _ _ R)
          | cleanup; solve [eauto] ]
      end.
      split.
      { match goal with
        | H : context_equiv _ _ |- _ =>
          cbv [context_equiv] in H;
            rewrite Forall_forall in H;
            specialize (H _ ltac:(eassumption))
        end.
        eauto. }
      { cbn [locally_equivalent_nobounds
               locally_equivalent_nobounds_base
               locally_equivalent equivalent_base
               equivalent rep.equiv rep.Z ident.literal] in *.
        eexists; sepsimpl; try reflexivity; [ ].
        rewrite word.unsigned_of_Z. cbv [word.wrap].
        Z.rewrite_mod_small; reflexivity. } }
    { (* shiftr *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbv [rshiftr literal_ltwidth invert_literal].
      rewrite is_bounded_by_bool_width_range by lia.
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl_hyps.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      cbv [WeakestPrecondition.literal dlet.dlet ident.literal].
      apply word.unsigned_inj.
      rewrite word.unsigned_sru, !word.unsigned_of_Z
         by (rewrite word.unsigned_of_Z; cbv [word.wrap];
             Z.rewrite_mod_small; lia).
      cbv [word.wrap]; Z.rewrite_mod_small.
      congruence. }
    { (* shiftl *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbv [rshiftl literal_ltwidth invert_literal].
      rewrite is_bounded_by_bool_width_range by lia.
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl; [ lia .. | ].
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      cbv [WeakestPrecondition.literal dlet.dlet ident.literal].
      apply word.unsigned_inj.
      rewrite word.unsigned_slu, !word.unsigned_of_Z
        by (rewrite word.unsigned_of_Z; cbv [word.wrap];
            Z.rewrite_mod_small; lia).
      cbv [word.wrap]. Z.rewrite_mod_small.
      congruence. }
    { (* mul_high *)
      cbv [ident.literal rmul_high literal_eqb invert_literal].
      rewrite Z.eqb_refl.
      match goal with
        |- context [_ (translate_expr _ ?a) (translate_expr _ ?b)] =>
        specialize (IHvalid_expr1 _ a _ _
                                  ltac:(eassumption) ltac:(eassumption));
        specialize (IHvalid_expr2 _ b _ _
                                  ltac:(eassumption) ltac:(eassumption))
      end.
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl_hyps.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      rewrite MulSplit.Z.mul_high_div.
      apply word.unsigned_inj.
      rewrite word.unsigned_mulhuu, !word.unsigned_of_Z.
      cbv [word.wrap]. Z.rewrite_mod_small.
      congruence. }
    { (* truncating_shiftl *)
      cbv [rtruncating_shiftl literal_eqb literal_ltwidth invert_literal].
      rewrite Z.eqb_refl, is_bounded_by_bool_width_range by lia.
      specialize (IHvalid_expr _ _ _ _
                                ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl_hyps.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      cbv [WeakestPrecondition.literal dlet.dlet].
      rewrite TruncatingShiftl.Z.truncating_shiftl_correct.
      apply word.unsigned_inj.
      rewrite word.unsigned_slu, !word.unsigned_of_Z
        by (rewrite word.unsigned_of_Z; cbv [word.wrap];
            Z.rewrite_mod_small; lia).
      cbv [word.wrap]. Z.rewrite_mod_small.
      congruence. }
    { (* lnot_modulo *)
      cbv [rlnot_modulo invert_literal].
      rewrite (proj2 (Z.eqb_eq _ _)) by lia.
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      break_innermost_match; Z.ltb_to_lt.
      all: cbn [locally_equivalent_nobounds
                  locally_equivalent_nobounds_base
                  locally_equivalent equivalent
                  equivalent_base rep.equiv rep.Z ident.literal] in *.
      all: cbv [WeakestPrecondition.dexpr ident.literal] in *.
      all: cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                         Semantics.interp_binop].
      all: sepsimpl_hyps.
      all: eapply Proper_expr; [ | eassumption ].
      all: repeat intro; subst.
      all: cbv [WeakestPrecondition.literal dlet.dlet].
      all: apply word.unsigned_inj.
      all: let H := match goal with H : 2^Z.log2 _ = ?m |- context[Definitions.Z.lnot_modulo _ ?m] => H end in
           rewrite <- H, Z.lnot_modulo_correct, <- Z.land_ones, -> ?H by auto using Z.log2_nonneg.
      all: rewrite word.unsigned_xor, ?word.unsigned_and_nowrap, !word.unsigned_of_Z.
      all: apply Z.bits_inj'; intros; autorewrite with Ztestbit Ztestbit_full.
      all: cbv [xorb negb andb orb]; break_innermost_match; Z.ltb_to_lt; try congruence; try lia. }

    { (* select *)
      cbv [ident.literal rselect literal_eqb invert_literal].
      rewrite !Z.eqb_refl.
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl_hyps.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      rewrite Zselect.Z.zselect_correct.
      apply word.unsigned_inj.
      rewrite word.unsigned_add, word.unsigned_eqb.
      rewrite <-Bool.pull_bool_if, !word.unsigned_of_Z.
      cbv [word.wrap]. Z.rewrite_mod_small.
      pose proof word.width_pos.
      break_match; subst; Z.rewrite_mod_small;
        Z.ltb_to_lt; try lia.
      all:pull_Zmod.
      all:autorewrite with zsimplify_fast.
      all:try reflexivity.
      rewrite Z.mod_opp_l_nz
        by (rewrite ?Z.mod_1_l; auto with zarith).
      Z.rewrite_mod_small.
      reflexivity. }
    { (* opp *)
      specialize (IHvalid_expr _ _ _ _
                               ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent_nobounds
             locally_equivalent_nobounds_base
             locally_equivalent equivalent
             equivalent_base rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr ident.literal] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl_hyps.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      apply word.unsigned_inj.
      rewrite word.unsigned_sub, word.unsigned_of_Z_0.
      rewrite !word.unsigned_of_Z.
      f_equal. lia. }
  Qed.

  Lemma translate_expr_correct {t}
        (* three exprs, representing the same Expr with different vars *)
        (e1 : @API.expr (fun _ => unit) (type.base t))
        (e2 : @API.expr API.interp_type (type.base t))
        (e3 : @API.expr ltype (type.base t)) :
    (* e1 is a valid input to translate_expr *)
    valid_expr true e1 ->
    forall G locals,
      wf3 G e1 e2 e3 ->
      let out := translate_expr true e3 in
      context_equiv G locals ->
      locally_equivalent (API.interp e2) out locals.
  Proof.
    apply (translate_expr_correct' _ _ _ true).
  Qed.
End Expr.
