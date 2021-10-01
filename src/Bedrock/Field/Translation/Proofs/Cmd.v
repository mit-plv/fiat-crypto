Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.PropSet.
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
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.

  Inductive valid_cmd :
    forall {t}, @API.expr (fun _ => unit) t -> Prop :=
  (* N.B. LetIn is split into cases so that only pairs of type_base and type_base are
      allowed; this is primarily because we don't want lists on the LHS *)
  | valid_LetIn_prod :
      forall {a b c} x f,
        valid_expr true x -> valid_cmd (f tt) ->
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
  .

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
      forall tr
             (mem : mem),
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
    all:repeat match goal with
               | _ => progress cleanup_wf
               | _ => progress cbn [varname_set]
               | H : wf3 _ ?x ?y _ |- _ =>
                 (* for the cons case, repeatedly do inversion until the cons is exposed *)
                 progress match x with
                            context [Compilers.ident.cons] =>
                            progress match y with
                                     | expr.App _ _ => idtac (* don't invert original, already-inverted one *)
                                     | _ => inversion H; clear H
                                     end
                          end
               end.

    (* simplify goals *)
    all:repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => progress cbv [Rewriter.Util.LetIn.Let_In] in *
               | _ => erewrite translate_cmd_valid_expr by eauto
               | _ => progress cbn [translate_cmd expr.interp type.app_curried
                                                  WeakestPrecondition.cmd
                                                  WeakestPrecondition.cmd_body] in *
               | _ => eapply Proper_cmd;
                        [ eapply Proper_call | repeat intro
                          | eapply assign_correct; eauto;
                            eapply translate_expr_correct; solve [eauto] ]
               | _ => progress cbn [invert_expr.invert_pair_cps invert_expr.invert_AppIdent2_cps Option.bind invert_expr.invert_App2_cps invert_expr.invert_App_cps invert_expr.invert_Ident invert_expr.is_pair Compilers.invertIdent Option.bind translate_ident2_for_cmd Crypto.Util.Option.bind]
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
    { (* let-in (base type) *)
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
        match goal with H : PropSet.sameset _ _ |- _ =>
                        rewrite H end.
        apply used_varnames_disjoint; lia. }
      { simplify; subst; eauto; [ | | ].
        { (* varnames subset *)
          rewrite varname_set_local.
          rewrite PropSet.of_list_cons.
          rewrite add_union_singleton.
          apply subset_union_l;
            [ apply used_varnames_subset_singleton; lia| ].
          rewrite <-varname_set_local.
          etransitivity; [eassumption|].
          rewrite <-Nat.add_1_r.
          apply used_varnames_shift. }
        { (* only_differ *)
          rewrite <-(Nat.add_comm nextn 1) in *.
          only_differ_ok. }
        { (* equivalence of output holds *)
          clear IHe1_valid.
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
          lia. } } }
    { (* nil *)
      cbv [locally_equivalent equivalent]; simplify; eauto;
        try reflexivity.
      right; reflexivity. }
    { (* valid expr *)
      simplify; subst; eauto; only_differ_ok.
      match goal with H : PropSet.sameset _ _ |- _ =>
                      rewrite H end; reflexivity. }
  Qed.
End Cmd.
