Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Z.PushPullMod.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Expr.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Translation.Proofs.EquivalenceProperties.
Require Import Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Translation.Cmd.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations.

Section Cmd.
  Context
    {width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}.
  Context {ok : ok}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.

  Inductive valid_cmd :
    forall {t}, @API.expr (fun _ => unit) t -> Prop :=
  (* N.B. LetIn is split into cases so that only pairs of type_base and type_base are
      allowed; this is primarily because we don't want lists on the LHS *)
  | valid_LetIn_prod :
      forall {a b c} x f,
        valid_expr true x ->
        valid_cmd (f tt) ->
        valid_cmd (expr.LetIn
                     (A:=type.base (base.type.prod
                                      (base.type.type_base a) (base.type.type_base b)))
                     (B:=type.base c) x f)
  | valid_LetIn_base :
      forall {a b} x f,
        valid_expr true x -> valid_cmd (f tt) ->
        valid_cmd (expr.LetIn (A:=type.base (base.type.type_base a)) (B:=type.base b) x f)
  | valid_cons :
      forall x l,
        valid_expr true x ->
        valid_cmd l ->
        valid_cmd
          (expr.App
             (expr.App
                (expr.Ident
                   (ident.cons (t:=base.type.type_base base.type.Z))) x) l)
  | valid_nil :
      valid_cmd (expr.Ident (ident.nil (t:=base.type.type_base base.type.Z)))
  | valid_inner :
      forall {t} e,
        valid_expr (t:=type.base t) true e ->
        valid_cmd e
  | valid_add_get_carry :
      forall t r1 r2 (s : Z) x y f,
        range_good (width:=width) r1 = true ->
        range_good (width:=width) r2 = true ->
        s = 2 ^ width ->
        valid_expr true x ->
        valid_expr true y ->
        valid_cmd (f tt) ->
        valid_cmd
          (expr.LetIn
             (B:=type.base t)
             (expr.App
                (expr.App (expr.Ident ident.Z_cast2)
                          (expr.App
                             (expr.App
                                (expr.Ident ident.pair)
                                (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                             (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
                (expr.App
                   (expr.App
                      (expr.App (expr.Ident ident.Z_add_get_carry)
                                (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                      x) y)) f)
  | valid_add_with_get_carry :
      forall t rc r1 r2 (s : Z) c x y f,
        range_good (width:=width) r1 = true ->
        range_good (width:=width) r2 = true ->
        ZRange.lower rc = 0 ->
        ZRange.upper rc = 1 ->
        s = 2 ^ width ->
        valid_expr false c ->
        valid_expr true x ->
        valid_expr true y ->
        valid_cmd (f tt) ->
        valid_cmd
          (expr.LetIn
             (B:=type.base t)
             (expr.App
                (expr.App (expr.Ident ident.Z_cast2)
                          (expr.App
                             (expr.App
                                (expr.Ident ident.pair)
                                (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                             (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
                (expr.App
                   (expr.App
                      (expr.App
                         (expr.App (expr.Ident ident.Z_add_with_get_carry)
                                   (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                         (expr.App (expr.App (expr.Ident ident.Z_cast)
                                             (expr.Ident (ident.Literal (t:=base.type.zrange) rc)))
                                   c))
                      x) y)) f)
  .

  Local Instance spec_of_add_carryx : spec_of add_carryx :=
    fnspec! add_carryx x y carry ~> sum carry_out,
    { (* The required upper bound on `carry` isn't necessary for the
         current `add_with_carry` to support the `ensures` clause, but
         it does formalize an expected condition that future
         implementations should be free to leverage. *)
      requires t m := word.unsigned carry < 2;
      ensures T M :=
        M = m /\ T = t /\
        word.unsigned sum + 2^width * word.unsigned carry_out =
        word.unsigned x + word.unsigned carry + word.unsigned y
    }.

  Lemma assign_list_correct :
    forall (rhs : base_rtype base_listZ)
           (xs : base.interp base_listZ)
           (nextn : nat)
           tr
           (mem : mem)
           (locals : locals)
           functions,
      (* rhs == x *)
      locally_equivalent_base xs rhs locals ->
      (* locals don't contain any variables we can overwrite *)
      (forall n nvars,
          (nextn <= n)%nat ->
          map.undef_on locals (used_varnames (varname_gen:=varname_gen) n nvars)) ->
      let out := assign_list nextn rhs in
      let nvars := fst (fst out) in
      let lhs := snd (fst out) in
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (snd out)
        tr mem locals
        (fun tr' mem' locals' =>
           tr = tr'
           /\ mem = mem'
           /\ PropSet.sameset (varname_set_base lhs)
                              (used_varnames (varname_gen:=varname_gen) nextn nvars)
           /\ map.only_differ locals (varname_set_base lhs) locals'
           /\ locally_equivalent_base xs (base_rtype_of_ltype lhs) locals').
  Proof.
    cbn [locally_equivalent_base equivalent_base rep.equiv rep.listZ_local].
    induction rhs; intros; cbn [assign_list fst snd].
    { repeat straightline.
      repeat match goal with
             | |- _ /\ _ => split
             | _ => eassumption
             | _ => apply only_differ_empty
             | _ => reflexivity
             end. }
    { match goal with
        H : Forall2 _ ?x (_ :: _) |- _ =>
        destruct x; inversion H; subst; clear H; [ ]
      end.
      cbn [rep.equiv rep.Z] in *. sepsimpl.
      repeat straightline.
      eexists; split; [ eapply expr_empty; eassumption | ].
      eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
      2:{
        eapply IHrhs; eauto.
        { eapply Forall2_impl_strong; eauto.
          intros; sepsimpl; [ lia .. | ].
          eexists; sepsimpl; [ eassumption | ].
          eapply expr_only_differ_undef; eauto.
          rewrite used_varnames_1.
          eauto using @only_differ_sym, @only_differ_put with typeclass_instances. }
        { intros. apply put_undef_on; eauto with lia.
          rewrite used_varnames_iff; intro; cleanup.
          match goal with H : varname_gen _ = varname_gen _ |- _ =>
                          apply varname_gen_unique in H end.
          lia. } }
      cbv beta in *. cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        try reflexivity.
      { cbn [varname_set_base
               rep.varname_set rep.listZ_local rep.Z fold_right] in *.
        rewrite used_varnames_succ_low, add_union_singleton.
        match goal with H : PropSet.sameset _ _ |- _ =>
                        rewrite H end.
        reflexivity. }
      { cbn [varname_set_base
               rep.varname_set rep.listZ_local rep.Z fold_right] in *.
        eauto 10 using @only_differ_sym, @only_differ_put, @only_differ_trans with typeclass_instances. }
      { constructor; eauto; [ ].
        sepsimpl; [ lia .. | ].
        cbn [rep.rtype_of_ltype rep.Z].
        eexists; sepsimpl; [ reflexivity | ].
        eapply expr_untouched with (mem2:=map.empty); eauto;
          [ | solve [apply dexpr_put_same] ].
        match goal with H : PropSet.sameset _ _ |- _ =>
                        rewrite sameset_iff in H;
                          rewrite H
        end.
        rewrite used_varnames_iff; intro; cleanup.
        match goal with H : varname_gen _ = varname_gen _ |- _ =>
                        apply varname_gen_unique in H end.
        lia. } }
  Qed.

  Lemma assign_base_correct {t} :
    forall (x : base.interp t)
           (rhs : base_rtype t)
           (nextn : nat)
           tr
           (mem : mem)
           (locals : locals)
           functions,
      (* rhs == x *)
      locally_equivalent_base x rhs locals ->
      (* locals don't contain any variables we can overwrite *)
      (forall n nvars,
          (nextn <= n)%nat ->
          map.undef_on locals (used_varnames (varname_gen:=varname_gen) n nvars)) ->
      let out := assign_base nextn rhs in
      let nvars := fst (fst out) in
      let lhs := snd (fst out) in
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (snd out) tr mem locals
        (fun tr' mem' locals' =>
           tr = tr'
           (* assign never stores anything -- mem unchanged *)
           /\ mem = mem'
           (* return values match the number of variables used *)
           /\ PropSet.sameset (varname_set_base lhs)
                              (used_varnames (varname_gen:=varname_gen) nextn nvars)
           (* new locals only differ in the values of LHS variables *)
           /\ map.only_differ locals (varname_set_base lhs) locals'
           (* evaluating lhs == x *)
           /\ locally_equivalent_base x (base_rtype_of_ltype lhs) locals').
  Proof.
    cbv zeta. cbv [locally_equivalent_base].
    induction t; cbn [assign_base equivalent_base fst snd];
      break_match; intros; sepsimpl; [ | | ].
    { (* base_Z *)
      cbn [rep.Z rep.equiv rep.varname_set
                 rep.rtype_of_ltype
                 varname_set_base
                 base_rtype_of_ltype] in *.
      sepsimpl. repeat straightline.
      eexists; split;
        [ apply expr_empty; eassumption | ].
      repeat (split; [reflexivity | ]).
      repeat match goal with |- _ /\ _ => split end;
        try eexists; sepsimpl;
        eauto using @dexpr_put_same, @only_differ_sym, @only_differ_put with typeclass_instances.
      all:cbv [PropSet.singleton_set]; apply sameset_iff; intros.
      all:rewrite used_varnames_iff; split; intros; cleanup; subst; eauto;
        first [ eexists; eauto with lia
              | f_equal; lia ]. }
    { (* prod *)
      repeat straightline.
      eapply Proper_cmd; [ solve [apply Proper_call]
                         | repeat intro | eapply IHt1; solve [eauto] ].
      cbv beta in *; cleanup; subst.
      eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
      2:{
        eapply IHt2; eauto; [ | ].
         { eapply equivalent_only_differ_undef; eauto;
             try exact equiv_listZ_only_differ_undef_local.
           match goal with H : PropSet.sameset _ _ |- _ =>
                           rewrite H end.
           eauto. }
         { intros.
           eapply only_differ_disjoint_undef_on;
             try eapply undef_on_subset;
             eauto using used_varnames_subset with lia.
           match goal with H : PropSet.sameset _ _ |- _ =>
                           rewrite H end.
           apply used_varnames_disjoint; lia. } }
      cbv beta in *; cleanup; subst.
      cbn [varname_set_base base_rtype_of_ltype fst snd].
      repeat match goal with |- _ /\ _ => split end;
        eauto 10 using @only_differ_sym, @only_differ_trans with typeclass_instances; [ | ].
      { rewrite used_varnames_union.
        repeat match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite H end.
        reflexivity. }
      { apply sep_empty_iff; split; eauto; [ ].
        eapply equivalent_only_differ; eauto with equiv.
        repeat match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite H end.
        symmetry.
        apply used_varnames_disjoint; lia. } }
    { (* base_listZ *)
      eapply assign_list_correct; eauto. }
  Qed.

  Lemma assign_correct {t} :
    forall (x : API.interp_type t)
           (rhs : rtype t)
           (nextn : nat)
           tr
           (mem : mem)
           (locals : locals)
           functions,
      (* rhs == x *)
      locally_equivalent x rhs locals ->
      (* locals don't contain any variables we can overwrite *)
      (forall n nvars,
          (nextn <= n)%nat ->
          map.undef_on locals (used_varnames (varname_gen:=varname_gen) n nvars)) ->
      let out := assign nextn rhs in
      let nvars := fst (fst out) in
      let lhs := snd (fst out) in
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (snd out) tr mem locals
        (fun tr' mem' locals' =>
           tr = tr'
           (* assign never stores anything -- mem unchanged *)
           /\ mem = mem'
           (* return values match the number of variables used *)
           /\ PropSet.sameset (varname_set lhs)
                              (used_varnames (varname_gen:=varname_gen) nextn nvars)
           (* new locals only differ in the values of LHS variables *)
           /\ map.only_differ locals (varname_set lhs) locals'
           (* evaluating lhs == x *)
           /\ locally_equivalent x (rtype_of_ltype _ lhs) locals').
  Proof.
    destruct t;
      cbn [locally_equivalent equivalent varname_set];
      [ apply assign_base_correct | tauto ].
  Qed.

  (* if e is a valid_expr, it will hit the cases that call translate_expr *)
  Lemma translate_cmd_valid_expr {t}
        (e1 : @API.expr (fun _ => unit) t)
        (e2 : @API.expr API.interp_type t)
        (e3 : @API.expr ltype t)
        G nextn :
    valid_expr true e1 ->
    wf3 G e1 e2 e3 ->
    translate_cmd e3 nextn = assign nextn (translate_expr true e3).
  Proof.
    inversion 1; cleanup_wf; try reflexivity; intros.
    all: repeat first [ reflexivity
                      | match goal with
                        | [ H : wf3 _ ?x _ _ |- _ ]
                          => assert_fails is_var x; inversion H; clear H; cleanup_wf
                        end ].
  Qed.

  Lemma max_range_good : range_good (width:=width) (max_range (width:=width)) = true.
  Proof.
    cbv [range_good].
    destruct (ZRange.reflect_zrange_eq (max_range (width:=width))
                                       (max_range (width:=width))); congruence.
  Qed.

  Ltac invert_wf3_until_exposed :=
    repeat match goal with
           | _ => progress cleanup_wf
           | H : wf3 _ ?x ?y _ |- _ =>
             progress match x with
                      | expr.App _ _ =>
                        progress match y with
                                 | expr.App _ _ => idtac (* already inverted *)
                                 | _ => inversion H; clear H
                                 end
                        | expr.Ident _ =>
                          progress match y with
                                   | expr.Ident _ _ => idtac (* already inverted *)
                                   | _ => inversion H; clear H
                                   end
                        | expr.Var _ =>
                          progress match y with
                                   | expr.Var _ _ => idtac (* already inverted *)
                                   | _ => inversion H; clear H
                                   end
                      end
           end.

  Lemma valid_expr_not_special3 {t}
        (e1 : @API.expr (fun _ => unit) t)
        (e2 : @API.expr API.interp_type t)
        (e3 : @API.expr ltype t) G :
    valid_expr false e1 ->
    wf3 G e1 e2 e3 ->
    translate_if_special3 e3 = None.
  Proof.
    induction 1; intros; invert_wf3_until_exposed; reflexivity.
  Qed.

  Lemma valid_expr_not_special4 {t}
        (e1 : @API.expr (fun _ => unit) t)
        (e2 : @API.expr API.interp_type t)
        (e3 : @API.expr ltype t) G :
    valid_expr false e1 ->
    wf3 G e1 e2 e3 ->
    translate_if_special4 e3 = None.
  Proof.
    induction 1; intros; invert_wf3_until_exposed; reflexivity.
  Qed.

  Lemma invert_App_Z_cast_Some {var} (x : @API.expr var type_Z) r :
    invert_expr.invert_App_Z_cast
      (expr.App (expr.App (expr.Ident ident.Z_cast)
                          (expr.Ident (ident.Literal r)))
                x) = Some (r, x).
  Proof. reflexivity. Qed.

  Lemma invert_App_Z_cast2_Some {var} (x : @API.expr var type_ZZ) r1 r2 :
    invert_expr.invert_App_Z_cast2
      (expr.App (expr.App (expr.Ident ident.Z_cast2)
                          (expr.App (expr.App (expr.Ident ident.pair)
                                              (expr.Ident (ident.Literal r1)))
                                              (expr.Ident (ident.Literal r2))))
                x) = Some (r1, r2, x).
  Proof. reflexivity. Qed.

  Lemma valid_expr_not_special_function {t}
        (e1 : @API.expr (fun _ => unit) t)
        (e2 : @API.expr API.interp_type t)
        (e3 : @API.expr ltype t) G :
    valid_expr true e1 ->
    wf3 G e1 e2 e3 ->
    translate_if_special_function e3 = None.
  Proof.
    induction 1; intros; invert_wf3_until_exposed;
      try reflexivity; cbv [translate_if_special_function invert_expr.invert_App_cast].
    { rewrite invert_App_Z_cast_Some.
      cbn. erewrite valid_expr_not_special3, valid_expr_not_special4 by eauto.
      break_innermost_match; reflexivity. }
    { rewrite invert_App_Z_cast2_Some.
      cbn. erewrite valid_expr_not_special3, valid_expr_not_special4 by eauto.
      break_innermost_match; reflexivity. }
  Qed.

  (* Convenience lemma for add_with_get_carry case. *)
  Lemma add_get_carry_full_equiv (x y sum carry_out : @word.rep width word) r1 r2:
    word.unsigned sum + 2^width * word.unsigned carry_out
    = word.unsigned x + word.unsigned y ->
    range_good (width:=width) r1 = true -> range_good (width:=width) r2 = true ->
    PreExtra.ident.cast2
      (r1, r2)
      (Definitions.Z.add_get_carry_full
         (2 ^ width) (word.unsigned x) (word.unsigned y))
    = (word.unsigned sum, word.unsigned carry_out).
  Proof.
    pose proof word.width_pos. intro Heq. intros.
    pose proof (Properties.word.unsigned_range x).
    pose proof (Properties.word.unsigned_range y).
    pose proof (Properties.word.unsigned_range sum).
    pose proof (Properties.word.unsigned_range carry_out).
    repeat lazymatch goal with
           | H : range_good _ = true |- _ => apply range_good_eq in H; subst
           end.
    cbv [Definitions.Z.add_get_carry_full
           Definitions.Z.add_with_get_carry
           Definitions.Z.add_with_carry
           Definitions.Z.add_get_carry
           Definitions.Z.get_carry
           PreExtra.ident.cast2
           Rewriter.Util.LetIn.Let_In
        ].
    cbn [fst snd]. rewrite Z.log2_pow2, Z.eqb_refl by lia.
    cbn [fst snd]. rewrite Z.add_0_l.
    rewrite !CastLemmas.ident.cast_in_bounds by (apply is_bounded_by_bool_max_range; Z.div_mod_to_equations; nia).
    rewrite <-Heq. apply f_equal2.
    { Z.push_mod. rewrite Z.mod_same by lia. Z.push_pull_mod.
      rewrite Z.mod_small; lia. }
    { Z.div_mod_to_equations; nia. }
  Qed.

  (* Convenience lemma for add_with_get_carry case. *)
  Lemma add_with_get_carry_full_equiv (x y sum carry_in carry_out : @word.rep width word) r1 r2:
    word.unsigned sum + 2^width * word.unsigned carry_out
    = word.unsigned carry_in + word.unsigned x + word.unsigned y ->
    range_good (width:=width) r1 = true -> range_good (width:=width) r2 = true ->
    PreExtra.ident.cast2
      (r1, r2)
      (Definitions.Z.add_with_get_carry_full
         (2 ^ width) (word.unsigned carry_in) (word.unsigned x) (word.unsigned y))
    = (word.unsigned sum, word.unsigned carry_out).
  Proof.
    pose proof word.width_pos. intro Heq. intros.
    pose proof (Properties.word.unsigned_range x).
    pose proof (Properties.word.unsigned_range y).
    pose proof (Properties.word.unsigned_range carry_in).
    pose proof (Properties.word.unsigned_range sum).
    pose proof (Properties.word.unsigned_range carry_out).
    repeat lazymatch goal with
           | H : range_good _ = true |- _ => apply range_good_eq in H; subst
           end.
    cbv [Definitions.Z.add_with_get_carry_full
           Definitions.Z.add_with_get_carry
           Definitions.Z.add_with_carry
           Definitions.Z.get_carry
           PreExtra.ident.cast2
           Rewriter.Util.LetIn.Let_In
        ].
    cbn [fst snd]. rewrite Z.log2_pow2, Z.eqb_refl by lia.
    cbn [fst snd].
    rewrite !CastLemmas.ident.cast_in_bounds by (apply is_bounded_by_bool_max_range; Z.div_mod_to_equations; nia).
    rewrite <-Heq. apply f_equal2.
    { Z.push_mod. rewrite Z.mod_same by lia. Z.push_pull_mod.
      rewrite Z.mod_small; lia. }
    { Z.div_mod_to_equations; nia. }
  Qed.

  (* TODO: move to equivalence *)
  Lemma locally_equiv_pair l w1 w2 n1 n2 z1 z2 :
    n1 <> n2 ->
    word.unsigned w1 = z1 ->
    word.unsigned w2 = z2 ->
    locally_equivalent (t:=type_ZZ) (z1, z2)
                       (Syntax.expr.var n1, Syntax.expr.var n2)
                       (map.put (map.put l n1 w1) n2 w2).
  Proof.
    intros; repeat eexists; cbn [fst snd];
      repeat lazymatch goal with
               | |- context [map.putmany map.empty _] =>
                 rewrite Properties.map.putmany_empty_l
               | |- context [map.disjoint map.empty _] =>
                 apply Properties.map.disjoint_empty_l
               | H : word.unsigned _ = ?z |- word.unsigned _ = ?z => exact H
               | |- context [map.get (map.put _ ?k _) ?k] =>
                 rewrite map.get_put_same
               | |- context [map.get (map.put _ _ _) _] =>
                 rewrite map.get_put_diff by congruence
               | _ => reflexivity
             end.
  Qed.

  Lemma interp_and_carry x :
    word.unsigned (word:=word)
                  (Semantics.interp_binop Syntax.bopname.and x (word.of_Z 1)) = (word.unsigned x) mod 2.
  Proof.
    cbn [Semantics.interp_binop].
    rewrite word.unsigned_and, !word.unsigned_of_Z.
    pose proof word.width_pos.
    assert (2 <= 2 ^ width) by (apply Pow.Z.pow_pos_le; lia).
    cbv [word.wrap]. rewrite (Z.mod_small 1) by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    rewrite Z.pow_1_r.
    lazymatch goal with
    | |- (?x mod 2) mod _ = _ =>
      pose proof (Z.mod_pos_bound x 2);
        rewrite (Z.mod_small (x mod 2)) by lia
    end.
    reflexivity.
  Qed.

  Lemma interp_cast_carry r x :
    ZRange.lower r = 0 -> ZRange.upper r = 1 -> PreExtra.ident.cast r x = word.wrap x mod 2.
  Proof.
    destruct r; cbn [ZRange.lower ZRange.upper]; intros; subst.
    rewrite CastLemmas.ident.cast_out_of_bounds_simple_0_mod by lia.
    pose proof word.width_pos. cbv [word.wrap].
    rewrite Modulo.Z.mod_pow_same_base_smaller with (m:=1); try lia.
    reflexivity.
  Qed.

  Lemma invert_Literal_Some {var t} (x : Compilers.base_interp t) :
    invert_expr.invert_Literal (var:=var) (expr.Ident (ident.Literal x)) = Some x.
  Proof. reflexivity. Qed.

  Lemma invert_AppIdent3_Some {Q R S a b c d var} (i : ident (a -> b -> c -> d))
        (x : expr a) (y : expr b) (z : expr c)
        (f1 : forall t x, Q t)
        (f2 : forall t x, R t)
        (f3 : forall t x, S t) :
    invert_AppIdent3_cps (var:=var) (expr.App (expr.App (expr.App (expr.Ident i) x) y) z) f1 f2 f3
    = Some (existT _ (a, b, c) (i, f1 _ x, f2 _ y, f3 _ z)).
  Proof. reflexivity. Qed.

  Lemma invert_AppIdent4_Some {P Q R S a b c d e var} (i : ident (a -> b -> c -> d -> e))
        (w : expr a) (x : expr b) (y : expr c) (z : expr d)
        (f1 : forall t x, P t)
        (f2 : forall t x, Q t)
        (f3 : forall t x, R t)
        (f4 : forall t x, S t) :
    invert_AppIdent4_cps (var:=var)
                         (expr.App (expr.App (expr.App (expr.App (expr.Ident i) w) x) y) z)
                         f1 f2 f3 f4
    = Some (existT _ (a, b, c, d) (i, f1 _ w, f2 _ x, f3 _ y, f4 _ z)).
  Proof. reflexivity. Qed.

  Lemma translate_add_get_carry nextn (x y : API.expr type_Z) r1 r2 :
    range_good (width:=width) r1 = true ->
    range_good (width:=width) r2 = true ->
    let sum := varname_gen nextn in
    let carry := varname_gen (S nextn) in
    translate_if_special_function
      (expr.App
         (expr.App (expr.Ident ident.Z_cast2)
                   (expr.App
                      (expr.App
                         (expr.Ident ident.pair)
                         (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                      (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (expr.App
            (expr.App
               (expr.App (expr.Ident ident.Z_add_get_carry)
                         (expr.Ident (ident.Literal (t:=base.type.Z) (2 ^ width))))
               x) y)) nextn
    = Some (2%nat, (sum,carry), Syntax.cmd.call [sum;carry] add_carryx [(translate_expr true x); (translate_expr true y); Syntax.expr.literal 0]).
  Proof.
    cbv [translate_if_special_function]; intros.
    repeat lazymatch goal with H : range_good ?r = true |- _ => apply range_good_eq in H; subst end.
    cbn [invert_expr.invert_App_cast].
    rewrite invert_App_Z_cast2_Some.
    cbn [Crypto.Util.Option.bind fst snd range_type_good range_base_good].
    rewrite !max_range_good. cbn [andb].
    cbv [translate_if_special3]. rewrite invert_AppIdent3_Some.
    cbn [Crypto.Util.Option.bind fst snd].
    cbv [translate_ident_special3].
    cbn [type.domain]. rewrite invert_Literal_Some.
    cbn [Crypto.Util.Option.bind fst snd].
    rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma translate_add_with_get_carry nextn (c x y : API.expr type_Z) rc r1 r2 :
    range_good (width:=width) r1 = true ->
    range_good (width:=width) r2 = true ->
    ZRange.lower rc = 0 ->
    ZRange.upper rc = 1 ->
    let sum := varname_gen nextn in
    let carry := varname_gen (S nextn) in
    translate_if_special_function
      (expr.App
         (expr.App (expr.Ident ident.Z_cast2)
                   (expr.App
                      (expr.App
                         (expr.Ident ident.pair)
                         (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
                      (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (expr.App
            (expr.App
               (expr.App
                  (expr.App (expr.Ident ident.Z_add_with_get_carry)
                            (expr.Ident (ident.Literal (t:=base.type.Z) (2 ^ width))))
                  (expr.App (expr.App (expr.Ident ident.Z_cast)
                                      (expr.Ident (ident.Literal (t:=base.type.zrange) rc)))
                            c))
                  x) y)) nextn
    = Some (2%nat, (sum,carry), Syntax.cmd.call [sum;carry] add_carryx
                                              [translate_expr true x
                                               ; translate_expr true y
                                               ; Syntax.expr.op
                                                   Syntax.bopname.and
                                                   (translate_expr false c)
                                                   (Syntax.expr.literal 1)]).
  Proof.
    cbv [translate_if_special_function]; intros.
    repeat lazymatch goal with H : range_good ?r = true |- _ => apply range_good_eq in H; subst end.
    cbn [invert_expr.invert_App_cast].
    rewrite invert_App_Z_cast2_Some.
    cbn [Crypto.Util.Option.bind fst snd range_type_good range_base_good].
    rewrite !max_range_good. cbn [andb].
    lazymatch goal with
    | |- context [translate_if_special3 ?x ?n] =>
      lazymatch type of x with
      | API.expr ?t =>
        change (translate_if_special3 x n) with (@None (nat * ltype t * Syntax.cmd.cmd))
      end
    end.
    cbn iota. cbv [translate_if_special4].
    rewrite invert_AppIdent4_Some.
    cbn [Crypto.Util.Option.bind fst snd].
    cbv [translate_ident_special4].
    rewrite invert_App_Z_cast_Some.
    cbn [Crypto.Util.Option.bind fst snd].
    cbn [type.domain]. rewrite invert_Literal_Some.
    cbn [Crypto.Util.Option.bind fst snd].
    repeat lazymatch goal with
           | H : ZRange.upper ?r = _ |- context [ZRange.upper ?r] => rewrite H
           | H : ZRange.lower ?r = _ |- context [ZRange.lower ?r] => rewrite H
           end.
    rewrite !Z.eqb_refl. cbn [andb].
    reflexivity.
  Qed.

  Local Ltac simplify :=
    repeat
      first [ progress (intros; cleanup)
            | progress
                cbn [fst snd assign assign_base context_varname_set
                         varname_set varname_set_base
                         ltype rtype base_ltype base_rtype rtype_of_ltype
                         base_rtype_of_ltype rep.rtype_of_ltype
                         rep.equiv rep.listZ_local rep.Z
                         locally_equivalent equivalent
                         locally_equivalent_base equivalent_base
                         map Datatypes.length Compilers.ident_interp] in *
            | match goal with |- _ /\ _ => split end ].

  Local Ltac setsimplify :=
    repeat match goal with
           | _ => progress cbv [PropSet.union PropSet.of_list
                                              PropSet.singleton_set PropSet.elem_of] in *
           | H : PropSet.sameset _ _ |- _ => rewrite sameset_iff in H; rewrite H
           end.

  (* prove that context doesn't include overwritable variables *)
  Local Ltac context_not_overwritable :=
    repeat match goal with
           | _ => progress (intros; cleanup)
           | _ => progress
                    cbn [ltype base_ltype assign_base context_varname_set
                               varname_set_base varname_set fst snd] in *
           | _ => progress setsimplify
           | _ => apply Forall_cons; [ | solve [eauto with lia] ]
           | _ => rewrite used_varnames_iff
           | H : varname_gen _ = varname_gen _ |- _ =>
             apply varname_gen_unique in H; subst
           | |- ~ (_ \/ _) =>
             let X := fresh in intro X; destruct X; cleanup
           | H : context [context_varname_set] |- _ =>
             eapply H; try eassumption; lia
           | _ => lia
           end.

  (* prove that paired variable values in the context are equivalent *)
  Local Ltac context_equiv_ok :=
    repeat match goal with
           | _ => progress (intros; cleanup)
           | |- context_equiv (_ :: _) _ =>
             apply Forall_cons; [ solve [eauto] | ]
           | _ =>
             eapply equivalent_not_in_context_forall;
               eauto using disjoint_sameset, disjoint_used_varnames_lt
           | _ => solve [subst; eauto]
           end.

  Local Ltac new_context_ok :=
    match goal with
    | |- context_equiv _ _ => context_equiv_ok
    | _ => context_not_overwritable
    end.

  Local Ltac only_differ_ok :=
       repeat match goal with
              | _ => eapply only_differ_step; try eassumption; [ ]
              | _ => eapply Proper_only_differ; eauto;
                     solve[symmetry; eauto]
              end.

  Lemma translate_cmd_correct {t}
        (* three exprs, representing the same Expr with different vars *)
        (e1 : @API.expr (fun _ => unit) t)
        (e2 : @API.expr API.interp_type t)
        (e3 : @API.expr ltype t)
        (* e1 is valid input to translate_cmd *)
        (e1_valid : valid_cmd e1)
        (* context list *)
        (G : list _) :
    (* exprs are all related *)
    wf3 G e1 e2 e3 ->
    forall functions
           (locals : locals)
           (nextn : nat),
      (* specifications of bedrock2 functions we might call *)
      spec_of_add_carryx functions ->
      (* ret := fiat-crypto interpretation of e2 *)
      let ret1 : API.interp_type t := API.interp e2 in
      (* out := translation output for e3 *)
      let out := translate_cmd e3 nextn in
      let nvars := fst (fst out) in
      let ret2 := rtype_of_ltype _ (snd (fst out)) in
      let body := snd out in
      (* G doesn't contain variables we could accidentally overwrite *)
      (forall n,
          (nextn <= n)%nat ->
          ~ context_varname_set G (varname_gen n)) ->
      (* locals don't contain any variables we can overwrite *)
      (forall n nvars,
          (nextn <= n)%nat ->
          map.undef_on locals (used_varnames(varname_gen:=varname_gen) n nvars)) ->
      forall tr (mem : mem),
        (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
        context_equiv G locals ->
        (* executing translation output is equivalent to interpreting e *)
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          body tr mem locals
          (fun tr' mem' locals' =>
             tr = tr' /\
             mem = mem' /\
             PropSet.subset
               (varname_set (snd (fst out)))
               (used_varnames(varname_gen:=varname_gen) nextn nvars) /\
             map.only_differ
               locals (used_varnames(varname_gen:=varname_gen) nextn nvars) locals' /\
             locally_equivalent ret1 ret2 locals').
  Proof.
    revert e2 e3 G. cbv zeta.
    induction e1_valid; try (inversion 1; [ ]).

    (* inversion on wf3 leaves a mess; clean up hypotheses *)
    Ltac invert_until_exposed H y :=
      progress match y with
               | expr.App _ _ => idtac (* don't invert original, already-inverted one *)
               | _ => inversion H; clear H
               end.
    all:repeat match goal with
               | _ => progress cleanup_wf
               | _ => progress cbn [varname_set]
               | H : wf3 _ ?x ?y _ |- _ =>
                 (* for cons and special functions, repeatedly do inversion until they are exposed *)
                 progress match x with
                          | expr.App _ _ =>invert_until_exposed H y
                          | expr.Ident _ =>invert_until_exposed H y
                          end
               end.

    (* simplify goals *)
    all:repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => progress cbv [Rewriter.Util.LetIn.Let_In] in *
               | _ => erewrite translate_cmd_valid_expr by eauto
               | _ => erewrite valid_expr_not_special_function by eauto
               | _ => progress cbn [translate_cmd expr.interp type.app_curried
                                                  WeakestPrecondition.cmd
                                                  WeakestPrecondition.cmd_body] in *
               | _ => eapply Proper_cmd;
                        [ eapply Proper_call | repeat intro
                          | eapply assign_correct; eauto;
                            eapply translate_expr_correct; solve [eauto] ]
               | _ => progress cbn [translate_if_special_function (*translate_if_special3*) invert_AppIdent3_cps invert_AppIdent4_cps invert_expr.invert_pair_cps invert_expr.invert_AppIdent2_cps Option.bind invert_expr.invert_App2_cps invert_expr.invert_App_cps invert_expr.invert_Ident invert_expr.is_pair Compilers.invertIdent Option.bind translate_ident2_for_cmd Crypto.Util.Option.bind]
               end.

    { (* let-in (product of base types) *)
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2: {
        eapply IHe1_valid; clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => solve [new_context_ok]
               | H : _ |- _ => solve [apply H]
               | _ => congruence
               end; [ ].
        eapply only_differ_disjoint_undef_on; eauto with lia; [ ].
        match goal with H : PropSet.sameset _ _ |- _ =>
                        rewrite H end.
        apply used_varnames_disjoint; lia. }
      { simplify; subst; eauto; only_differ_ok.
        etransitivity; [ eassumption | ].
        apply used_varnames_shift. } }
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2: {
        eapply IHe1_valid; clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => solve [new_context_ok]
               | H : _ |- _ => solve [apply H]
               | _ => congruence
               end; [ ].
        eapply only_differ_disjoint_undef_on; eauto with lia; [ ].
        match goal with H : PropSet.sameset _ _ |- _ =>
                        rewrite H end.
        apply used_varnames_disjoint; lia. }
      { simplify; subst; eauto; only_differ_ok.
        etransitivity; [ eassumption | ].
        apply used_varnames_shift. }
    { (* cons *)
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2: {
        eapply IHe1_valid with (G:=G); clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | H : _ |- _ => solve [apply H]
               | _ => solve [new_context_ok]
               | _ => congruence
               end; [ ].
        eapply only_differ_disjoint_undef_on; eauto with lia; [ ].
        match goal with H : PropSet.sameset _ _ |- _ => rewrite H end.
        apply used_varnames_disjoint. lia. }
      simplify; subst; eauto; [ | | ].
      { (* varnames subset *)
        rewrite varname_set_local.
        rewrite PropSet.of_list_cons.
        rewrite add_union_singleton.
        apply subset_union_l;
          [ apply used_varnames_subset_singleton; lia| ].
        rewrite <-varname_set_local.
        etransitivity; [eassumption|].
        apply used_varnames_shift. }
      { (* only_differ *)
        only_differ_ok. }
      { (* equivalence of output holds *)
        simplify. cbv [WeakestPrecondition.dexpr] in *.
        apply Forall2_cons; [intros | eassumption].
        sepsimpl.
        eexists; sepsimpl; [ eassumption | ].
        eapply (expr_untouched ltac:(eassumption)
                                      ltac:(eassumption)); eauto; [ ].
        cbv [used_varnames]. setsimplify.
        rewrite in_map_iff. intro; cleanup.
        match goal with H : varname_gen ?x = varname_gen _ |- _ =>
                        apply varname_gen_unique in H; subst x end.
        match goal with H : In _ (seq _ _) |- _ =>
                        apply in_seq in H end.
        lia. } }
    { (* nil *)
      cbv [locally_equivalent equivalent]; simplify; eauto;
        try reflexivity.
      right; reflexivity. }
    { (* valid expr *)
      simplify; subst; eauto; only_differ_ok.
      match goal with H : PropSet.sameset _ _ |- _ =>
                      rewrite H end; reflexivity. }
    { (* add_get_carry *)
      rewrite translate_add_get_carry by auto. cbn [fst snd].
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      repeat lazymatch goal with
             | H : valid_expr _ ?e |- _ =>
               lazymatch goal with
               | Hwf : wf3 ?G e ?e2 ?e3 |- _ =>
                 let Htr := fresh in
                 pose proof translate_expr_correct e e2 e3 ltac:(eassumption) G _ Hwf ltac:(eassumption) as Htr;
                   destruct Htr; sepsimpl
               end;
                 clear H
             end.
      eexists; split; [ | ].
      { (* Argument expressions. *)
        repeat lazymatch goal with
               | |- dexprs _ _ (_ :: _) _ => apply dexprs_cons_iff; split
               | H : dexpr map.empty ?l ?x _ |- WeakestPrecondition.expr ?m ?l ?x _ =>
                 apply expr_empty; apply H
               | _ => reflexivity
               end. }
      straightline_call; [ rewrite Properties.word.unsigned_of_Z_0; lia | ].
      sepsimpl; subst; cleanup.
      eexists; split; [ reflexivity | ].
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2:{
        eapply IHe1_valid; clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | H : forall v1 v2 v3, wf3 _ (?f v1) _ _ |- wf3 _ (?f tt) _ _ => solve [apply (H tt)]
               | H : ?P |- ?P => exact H
               end; [ | | ].
        { (* context varname_set *)
          new_context_ok.
          lazymatch goal with
          | H : rep.varname_set _ _ \/ rep.varname_set _ _ |- _ =>
            cbn  in H; destruct H as [H | H]; apply varname_gen_unique in H; lia
          end. }
        { (* undef on *)
          repeat lazymatch goal with
                 | |- map.undef_on (map.put _ _ _) _ => apply put_undef_on
                 | H : forall n nvars, _ -> map.undef_on ?l (used_varnames n nvars)
                                  |- map.undef_on ?l (used_varnames _ _) =>
                   apply H; lia
                 | |- ~ used_varnames _ _ _ => rewrite used_varnames_iff; intro; simplify
                 | H : varname_gen _ = varname_gen _ |- _ => apply varname_gen_unique in H; lia
                 end. }
        { (* context equivalent *)
          apply Forall_cons;
            [ apply locally_equiv_pair; eauto; rewrite varname_gen_unique; lia | ].
          eapply equivalent_not_in_context_forall; eauto;
            repeat lazymatch goal with
                   | |- map.only_differ (map.put _ _ _) _ _ =>
                     eapply only_differ_trans; [ | solve [apply only_differ_put] ]
                   | |- map.only_differ ?m _ ?m => solve [apply only_differ_empty]
                   | |- map.only_differ _ _ (map.put _ _ _) =>
                     apply only_differ_sym
                   | |- disjoint (union _ _) _ =>
                     apply disjoint_union_l_iff; split
                   | |- disjoint empty_set _ =>
                     solve [apply disjoint_empty_l]
                   | |- disjoint (singleton_set _) _ =>
                     symmetry; apply disjoint_singleton_r_iff
                   | _ => solve [eauto with lia]
                   end. } }
      clear IHe1_valid.
      simplify; subst; eauto; [ | | ].
      { (* varnames subset *)
        rewrite <-used_varnames_shift; eauto. }
      { (* only_differ *)
        only_differ_ok.
        eauto using only_differ_succ, only_differ_zero. }
      { (* equivalence of output holds *)
        lazymatch goal with
        | H : equivalent_base ?x1 ?y ?a ?l ?m |- equivalent_base ?x2 ?y ?a ?l ?m =>
          replace x2 with x1; [ exact H | ]
        end.
        lazymatch goal with
          | H : context [word.unsigned (word.of_Z 0)] |- _ =>
            rewrite Properties.word.unsigned_of_Z_0 in H
        end.
        repeat lazymatch goal with
               | H : word.unsigned _ = expr.interp ?iinterp ?x |- context [expr.interp ?iinterp ?x] =>
                 rewrite <-H
               end.
        erewrite add_get_carry_full_equiv; eauto with lia. } }
    { (* add_with_get_carry *)
      rewrite translate_add_with_get_carry by auto. cbn [fst snd].
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      repeat lazymatch goal with
             | H : valid_expr ?require_cast ?e |- _ =>
               lazymatch goal with
               | Hwf : wf3 ?G e ?e2 ?e3 |- _ =>
                 let Htr := fresh in
                 pose proof translate_expr_correct' e e2 e3 require_cast ltac:(eassumption) G _ Hwf ltac:(eassumption) as Htr; cbn iota in Htr; simplify
               end;
                 clear H
             | H : Lift1Prop.ex1 _ _ |- _ => destruct H
             | H : emp _ _ |- _ => destruct H; cleanup
             end.
      cbn [locally_equivalent_nobounds locally_equivalent_nobounds_base] in *.
      eexists; split; [ | ].
      { (* Argument expressions. *)
        repeat lazymatch goal with
               | |- dexprs _ _ (_ :: _) _ => apply dexprs_cons_iff; split
               | H : dexpr map.empty ?l ?x _ |- WeakestPrecondition.expr ?m ?l ?x _ =>
                 apply expr_empty; apply H
               | _ => reflexivity
               end; [ ].
        (* Carry argument is left over. *)
        cbn [WeakestPrecondition.expr WeakestPrecondition.expr_body].
        eapply Proper_expr; [ | solve [apply expr_empty; eauto] ].
        repeat intro; subst. reflexivity. }
      straightline_call;
        [ (* carry is < 2 *)
          rewrite interp_and_carry; apply Z.mod_pos_bound; lia | ].
      sepsimpl; subst; cleanup.
      eexists; split; [ reflexivity | ].
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2:{
        eapply IHe1_valid; clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | H : forall v1 v2 v3, wf3 _ (?f v1) _ _ |- wf3 _ (?f ?v1) _ (_ ?v3) =>
                 solve [eapply (H v1 _ v3)]
               | H : ?P |- ?P => exact H
               end; [ | | ].
        { (* context varname_set *)
          new_context_ok.
          lazymatch goal with
          | H : rep.varname_set _ _ \/ rep.varname_set _ _ |- _ =>
            cbn  in H; destruct H as [H | H]; apply varname_gen_unique in H; lia
          end. }
        { (* undef on *)
          repeat lazymatch goal with
                 | |- map.undef_on (map.put _ _ _) _ => apply put_undef_on
                 | H : forall n nvars, _ -> map.undef_on ?l (used_varnames n nvars)
                                  |- map.undef_on ?l (used_varnames _ _) =>
                   apply H; lia
                 | |- ~ used_varnames _ _ _ => rewrite used_varnames_iff; intro; simplify
                 | H : varname_gen _ = varname_gen _ |- _ => apply varname_gen_unique in H; lia
                 end. }
        { (* context equivalent *)
          apply Forall_cons;
            [ apply locally_equiv_pair; eauto; rewrite varname_gen_unique; lia | ].
          eapply equivalent_not_in_context_forall; eauto;
            repeat lazymatch goal with
                   | |- map.only_differ (map.put _ _ _) _ _ =>
                     eapply only_differ_trans; [ | solve [apply only_differ_put] ]
                   | |- map.only_differ ?m _ ?m => solve [apply only_differ_empty]
                   | |- map.only_differ _ _ (map.put _ _ _) =>
                     apply only_differ_sym
                   | |- disjoint (union _ _) _ =>
                     apply disjoint_union_l_iff; split
                   | |- disjoint empty_set _ =>
                     solve [apply disjoint_empty_l]
                   | |- disjoint (singleton_set _) _ =>
                     symmetry; apply disjoint_singleton_r_iff
                   | _ => solve [eauto with lia]
                   end. } }
      clear IHe1_valid.
      simplify; subst; eauto; [ | | ].
      { (* varnames subset *)
        rewrite <-used_varnames_shift; eauto. }
      { (* only_differ *)
        only_differ_ok.
        eauto using only_differ_succ, only_differ_zero. }
      { (* equivalence of output holds *)
        lazymatch goal with
        | H : equivalent_base ?x1 ?y ?a ?l ?m |- equivalent_base ?x2 ?y ?a ?l ?m =>
          replace x2 with x1; [ exact H | ]
        end.
        repeat lazymatch goal with
               | H : word.unsigned _ = expr.interp ?iinterp ?x |- context [expr.interp ?iinterp ?x] =>
                 rewrite <-H
               end.
        lazymatch goal with
        | H : context [word.unsigned
                         (Semantics.interp_binop Syntax.bopname.and (word.of_Z ?x) (word.of_Z 1))]
          |- context [Definitions.Z.add_with_get_carry_full _ (PreExtra.ident.cast ?r ?c) _ _] =>
          (* more complex rewrite for the carry *)
          replace (PreExtra.ident.cast r c)
            with (word.unsigned (word:=word)
                                (Semantics.interp_binop Syntax.bopname.and (word.of_Z x) (word.of_Z 1)))
        end; [ erewrite add_with_get_carry_full_equiv; solve [eauto with lia] | ].
        rewrite interp_and_carry, interp_cast_carry by auto.
        rewrite word.unsigned_of_Z. reflexivity. } }
  Qed.
End Cmd.
