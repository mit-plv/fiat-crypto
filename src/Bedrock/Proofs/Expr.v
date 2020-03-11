Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.CastLemmas.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Proofs.Varnames.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
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
      forall (x : API.expr type_ZZ),
        valid_expr true x ->
        valid_expr false (expr.App (expr.Ident ident.fst) x)
  | valid_snd :
      forall (x : API.expr type_ZZ),
        valid_expr true x ->
        valid_expr false (expr.App (expr.Ident ident.fst) x)
  | valid_literalz :
      forall rc z,
        is_bounded_by_bool z max_range = true ->
        valid_expr rc (expr.Ident (ident.Literal (t:=base.type.Z) z))
  | valid_var :
      forall v, valid_expr (t:=base_Z) false (expr.Var v)
  | valid_nth_default :
      forall d l i,
        valid_expr true d ->
        valid_expr
          false
          (expr.App (expr.App (expr.App (expr.Ident ident.List_nth_default) d)
                              (expr.Var (t:=type_listZ) l))
                    (expr.Ident (ident.Literal i)))
  | valid_shiftr :
      forall (x : API.expr type_Z) n,
        valid_expr true x ->
        0 <= n < Semantics.width ->
        valid_expr (t:=base_Z) false
                   (expr.App (expr.App (expr.Ident ident.Z_shiftr) x)
                   (expr.Ident (ident.Literal (t:=base.type.Z) n)))
  | valid_basic_binop :
      forall i (x y : API.expr type_Z),
        translate_binop i <> None ->
        valid_expr (t:=base_Z) true x ->
        valid_expr (t:=base_Z) true y ->
        valid_expr (t:=base_Z) false (expr.App (expr.App (expr.Ident i) x) y)
  | valid_truncating_binop :
      forall i (s : Z) (x y : API.expr type_Z),
        translate_truncating_binop i s <> None ->
        valid_expr true x ->
        valid_expr true y ->
        valid_expr (t:=base_Z) false
                   (expr.App (expr.App
                                (expr.App (expr.Ident i)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                x) y)
  .

  Lemma equivalent_cast1 r x y locals:
    range_good r = true ->
    locally_equivalent (t:=base_Z) x y locals ->
    locally_equivalent (t:=base_Z) (ident.cast (ident.literal r) x) y locals.
  Proof.
    cbv [range_good max_range]. cbn [locally_equivalent equivalent rep.equiv rep.Z].
    let X := fresh in
    assert (0 <= Semantics.width) as X by (pose proof word.width_pos; lia);
      pose proof (Z.pow_pos_nonneg 2 Semantics.width ltac:(lia) X).
    intros; progress reflect_beq_to_eq zrange_beq; subst r.
    cbv [ident.literal].
    rewrite ident.cast_out_of_bounds_simple_0_mod, Z.sub_simpl_r by lia.
    sepsimpl; try apply Z.mod_pos_bound; eauto; [ ].
    cbv [ident.literal WeakestPrecondition.dexpr] in *.
    rewrite Z.mod_small by lia.
    eapply Proper_expr; [ | eassumption ].
    repeat intro; subst. apply word.of_Z_inj_mod.
    reflexivity.
  Qed.

  Lemma equivalent_cast2 r1 r2 x y locals :
    range_good r1 = true ->
    range_good r2 = true ->
    locally_equivalent (t:=base_ZZ) x y locals ->
    locally_equivalent (t:=base_ZZ)
                       (ident.cast2 (ident.literal r1, ident.literal r2) x) y locals.
  Proof.
    cbv [range_good max_range]. cbn [locally_equivalent equivalent rep.equiv rep.Z ].
    let X := fresh in
    assert (0 <= Semantics.width) as X by (pose proof word.width_pos; lia);
      pose proof (Z.pow_pos_nonneg 2 Semantics.width ltac:(lia) X).
    intros; progress reflect_beq_to_eq zrange_beq; subst r1 r2.
    cbv [fst snd ident.cast2 ident.literal
             WeakestPrecondition.dexpr] in *.
    break_match; [ ].
    rewrite !ident.cast_out_of_bounds_simple_0_mod, Z.sub_simpl_r by lia.
    sepsimpl; try apply Z.mod_pos_bound; eauto; [ | ].
    all:eapply Proper_expr; [ | eassumption ].
    all:repeat intro; subst; apply word.of_Z_inj_mod.
    all:rewrite Z.mod_mod by lia.
    all:reflexivity.
  Qed.

  (*
  (* version generalized to any t, necessary to destruct i *)
  Lemma translate_binop_correct' {t} :
    forall (i : ident.ident t)
           (xargs : type.for_each_lhs_of_arrow API.interp_type t)
           (yargs : type.for_each_lhs_of_arrow rtype t)
           op locals,
      translate_binop i = Some op ->
      locally_equivalent_args xargs yargs locals ->
      let rhs : type.for_each_lhs_of_arrow rtype t -> base_rtype (type.final_codomain t)
          := match t as t0 return
                   type.for_each_lhs_of_arrow rtype t0 ->
                   base_rtype (type.final_codomain t0) with
             | (type_Z -> type_Z -> type_Z)%etype =>
               fun (y : (Syntax.expr * (Syntax.expr * unit))) =>
                 let y1 := fst y in
                 let y2 := fst (snd y) in
                 expr.op op y1 y2
             | _ => fun _ => base_rtype_of_ltype (dummy_base_ltype _)
             end in
      locally_equivalent (type.app_curried (Compilers.ident_interp i) xargs) 
                         (rhs yargs) locals.
  Proof.
    cbv [translate_binop]; intros *.
    break_match; try congruence; intros.
    all:repeat match goal with
               | _ => progress sepsimpl
               | _ => progress
                        cbn [fst snd
                                 Compilers.ident_interp
                                 type.map_for_each_lhs_of_arrow
                                 type.app_curried
                                 type.final_codomain
                                 locally_equivalent
                                 equivalent rep.Z rep.equiv
                                 equivalent_args
                                 Semantics.interp_binop
                                 locally_equivalent_args] in *
               | _ => progress
                        (cbv [WeakestPrecondition.dexpr] in *;
                         cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body])
               | H : Some _ = Some _ |- _ => inversion H; subst; clear H
               | _ => break_match; [ ]; cbn [fst snd]
               end.
    all: (do 2 (eapply Proper_expr; [ | eassumption]; repeat intro; subst)).
    all:autorewrite with rew_word_morphism; try reflexivity.

    { apply word.unsigned_inj.
      rewrite word.unsigned_and.
      rewrite !word.unsigned_of_Z.

  Lemma translate_binop_correct
        (i : ident.ident (type_Z -> type_Z -> type_Z))
        (x1 x2 : base.interp base_Z)
        (y1 y2 : Syntax.expr)
        op locals :
    translate_binop i = Some op ->
    locally_equivalent (t:=base_Z) x1 y1 locals ->
    locally_equivalent (t:=base_Z) x2 y2 locals ->
    locally_equivalent (Compilers.ident_interp i x1 x2) 
                       (expr.op op y1 y2) locals.
  Proof.
    intros.
    let H := fresh in
    pose proof (translate_binop_correct'
                  i (x1, (x2, tt)) (y1, (y2, tt))) as H;
      apply H; clear H; eauto; [ ].
    cbn [locally_equivalent_args equivalent_args fst snd].
    cbv [locally_equivalent] in *.
    eapply sep_empty_iff.
    sepsimpl; eauto.
  Qed.

  Qed.*)
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
  Proof.
    cbv zeta.
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
    { (* cast1 *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      match goal with H : range_good _ = true |- _ =>
                      rewrite H end.
      cbn [negb]; rewrite Bool.andb_false_r.
      eauto using equivalent_cast1. }
    { (* cast2 *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      repeat match goal with H : range_good _ = true |- _ =>
                             rewrite H end.
      cbn [negb andb]; rewrite Bool.andb_false_r.
      eauto using equivalent_cast2. }
    { (* fst *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      specialize (IHvalid_expr _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent equivalent rep.equiv rep.Z] in *.
      sepsimpl; eauto. }
    { (* snd *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      specialize (IHvalid_expr _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      cbn [locally_equivalent equivalent rep.equiv rep.Z] in *.
      sepsimpl; eauto. }
    { (* literal *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      repeat match goal with H : is_bounded_by_bool _ _ = true |- _ =>
                             rewrite H end.
      cbn [negb]. rewrite !Bool.andb_false_r.
      cbn [locally_equivalent equivalent rep.equiv rep.Z].
      cbv [is_bounded_by_bool] in *. cbn [upper lower max_range] in *.
      match goal with
        H : (_ && _)%bool = true |- _ =>
        apply Bool.andb_true_iff in H; cleanup
      end; Z.ltb_to_lt.
      cbv [ident.literal].
      sepsimpl; eauto with lia; reflexivity. }
    { (* var *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      match goal with
      | H : context_equiv _ _ |- _ =>
        cbv [context_equiv] in H;
          rewrite Forall_forall in H;
          specialize (H _ ltac:(eassumption))
      end.
      eauto. }
    { (* nth_default *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      cbv [ident.literal].
      match goal with
        |- locally_equivalent (nth_default ?d1 ?l1 ?i) (nth_default ?d2 ?l2 ?i) ?locals =>
        let R := constr:(fun x y => locally_equivalent (t:=base_Z) x y locals) in
        assert (length l1 = length l2 /\
                (forall i,
                    R (nth_default d1 l1 i) (nth_default d2 l2 i)));
          [ apply (@Forall.Forall2_forall_iff'' _ _ R) | cleanup; solve [eauto] ]
      end.
      split; [ | solve [eauto] ].
      match goal with
      | H : context_equiv _ _ |- _ =>
        cbv [context_equiv] in H;
          rewrite Forall_forall in H;
          specialize (H _ ltac:(eassumption))
      end.
      eauto. }
    { (* shiftr *) 
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      specialize (IHvalid_expr _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
      cbn [translate_binop translate_shiftr].
      rewrite !Bool.andb_true_l, Bool.if_negb.
      cbv [is_bounded_by_bool]. cbn [upper lower max_range].
      assert (Semantics.width < 2 ^ Semantics.width) by
          (apply Z.pow_gt_lin_r; lia).
      break_match;
        repeat match goal with
               | H : (_ && _)%bool = true |- _ =>
                 apply Bool.andb_true_iff in H; cleanup
               | H : (_ && _)%bool = false |- _ =>
                 apply Bool.andb_false_iff in H; destruct H
               end; Z.ltb_to_lt; try lia; [ ].
      cbn [locally_equivalent equivalent rep.equiv rep.Z ident.literal] in *.
      cbv [WeakestPrecondition.dexpr] in *.
      cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body
                                    Semantics.interp_binop].
      sepsimpl.
      1-2:admit.
      eapply Proper_expr; [ | eassumption ].
      repeat intro; subst.
      cbv [WeakestPrecondition.literal dlet.dlet ident.literal].
      apply word.unsigned_inj.
      rewrite word.unsigned_sru, !word.unsigned_of_Z.
  Admitted.
  (*
      (* need a proof that says if valid_expr true, then bounded. Or maybe if in
         context, then bounded *)
      all:admit. }
    { (* basic binop *)
      (* GROSS -- shiftr special case vomits all over this *)
      cbn [translate_expr has_casts expr.interp Compilers.ident_interp].
      cbn [negb]. rewrite !Bool.andb_true_r.
      break_match.
      break_match; try congruence; [ ].
      apply translate_binop_correct; eauto. }

  Qed. *)
End Expr.
