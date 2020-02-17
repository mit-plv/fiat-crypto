Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Expr.
Require Import Crypto.Bedrock.Proofs.Varnames.
Require Import Crypto.Bedrock.Translation.Cmd.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Cmd.
  Context {p : Types.parameters} {p_ok : @ok p}.
  Context (call : string ->
                  Semantics.trace ->
                  Interface.map.rep (map:=Semantics.mem) ->
                  list Interface.word.rep ->
                  (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                   list Interface.word.rep -> Prop) ->
                  Prop).
  Context (Proper_call :
             Morphisms.pointwise_relation
               string
               (Morphisms.pointwise_relation
                  Semantics.trace
                  (Morphisms.pointwise_relation
                     Interface.map.rep
                     (Morphisms.pointwise_relation
                        (list Interface.word.rep)
                        (Morphisms.respectful
                           (Morphisms.pointwise_relation
                              Semantics.trace
                              (Morphisms.pointwise_relation
                                 Interface.map.rep
                                 (Morphisms.pointwise_relation
                                    (list Interface.word.rep) Basics.impl)))
                           Basics.impl)))) call call).

  (* TODO: are these all needed? *)
  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local. (* local list representation *)
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : Interface.map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

  Inductive valid_cmd : forall {t}, @API.expr (fun _ => unit) (type.base t) -> Prop :=
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
  | valid_inner : forall {t} e,
      valid_expr true e -> valid_cmd (t:=t) e
  .

  (* TODO: it's always the case that
         varname_set (snd (fst a)) = { nextn,  ..., nextn + fst (fst a) - 1}
       consider which representation is easier to work with *)
  Lemma assign_correct {t} :
    forall (x : base.interp t)
           (rhs : base_rtype t)
           (nextn : nat)
           (tr : Semantics.trace)
           (mem locals : Interface.map.rep),
      (* rhs == x *)
      locally_equivalent x rhs locals ->
      let a := assign nextn rhs in
      WeakestPrecondition.cmd
        call (snd a)
        tr mem locals
        (fun tr' mem' locals' =>
           tr = tr'
           (* assign never stores anything -- mem unchanged *)
           /\ mem = mem'
           (* return values match the number of variables used *)
           /\ PropSet.sameset (varname_set (snd (fst a)))
                              (used_varnames nextn (fst (fst a)))
           (* new locals only differ in the values of LHS variables *)
           /\ Interface.map.only_differ locals (varname_set (snd (fst a))) locals'
           (* evaluating lhs == x *)
           /\ locally_equivalent x (rtype_of_ltype (snd (fst a))) locals').
  Admitted.

  (* if e is a valid_expr, it will hit the cases that call translate_expr *)
  Lemma translate_cmd_valid_expr {t}
        (e1 : @API.expr (fun _ => unit) (type.base t))
        (e2 : @API.expr API.interp_type (type.base t))
        (e3 : @API.expr ltype (type.base t))
        G nextn :
    valid_expr true e1 ->
    wf3 G e1 e2 e3 ->
    translate_cmd e3 nextn = assign nextn (translate_expr true e3).
  Proof.
    inversion 1; cleanup_wf; try reflexivity;
      inversion 1; cleanup_wf; reflexivity.
  Qed.

  Ltac setsimplify :=
    repeat match goal with
           | _ => progress cbv [PropSet.union PropSet.singleton_set PropSet.elem_of] in *
           | H : PropSet.sameset _ _ |- _ => rewrite sameset_iff in H; rewrite H
           end.

  (* prove that context doesn't include overwritable variables *)
  Ltac context_not_overwritable :=
    repeat match goal with
           | _ => progress (intros; cleanup)
           | _ => progress cbn [ltype base_ltype assign varname_not_in_context
                                      varname_set fst snd] in *
           | _ => progress setsimplify
           | _ => apply Forall_cons; [ | solve [eauto with lia] ]
           | _ => setoid_rewrite varname_gen_unique
           | _ => solve [eauto using used_varnames_le with lia]
           end.

  (* prove that paired variable values in the context are equivalent *)
  Ltac context_equiv_ok :=
    repeat match goal with
           | _ => progress (intros; cleanup)
           | |- context_equiv (_ :: _) _ =>
             apply Forall_cons; [ solve [eauto] | ]
           | _ =>
             eapply equivalent_not_in_context_forall; eauto;
             intro; setsimplify; rewrite used_varnames_iff
           | _ => solve [subst; eauto]
           end.

  Ltac new_context_ok :=
    match goal with
    | |- context_equiv _ _ => context_equiv_ok
    | _ => context_not_overwritable
    end.

  Lemma translate_cmd_correct {t'} (t:=type.base t')
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
    forall (locals : Interface.map.rep)
           (nextn : nat),
      (* ret := fiat-crypto interpretation of e2 *)
      let ret1 : base.interp t' := API.interp e2 in
      (* out := translation output for e3 *)
      let out := translate_cmd e3 nextn in
      let nvars := fst (fst out) in
      let ret2 := rtype_of_ltype (snd (fst out)) in
      let body := snd out in
      (* G doesn't contain variables we could accidentally overwrite *)
      (forall n,
          (nextn <= n)%nat ->
          Forall (varname_not_in_context (varname_gen n)) G) ->
      forall (tr : Semantics.trace)
             (mem : Interface.map.rep),
        (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
        context_equiv G locals ->
        (* executing translation output is equivalent to interpreting e *)
        WeakestPrecondition.cmd
          call body tr mem locals
          (fun tr' mem' locals' =>
             tr = tr' /\
             mem = mem' /\
             Interface.map.only_differ
               locals (used_varnames nextn nvars) locals' /\
             locally_equivalent ret1 ret2 locals').
  Proof.
    revert e2 e3 G. subst t. cbv zeta.
    induction e1_valid; try (inversion 1; [ ]).

    (* inversion on wf3 leaves a mess; clean up hypotheses *)
    all:repeat match goal with
               | _ => progress cleanup_wf
               | H : wf3 _ ?x _ _ |- _ =>
                 (* for the cons case, repeatedly do inversion until the cons is exposed *)
                 progress match x with context [Compilers.ident.cons] =>
                                       inversion H; clear H
                          end
               end.

    (* simplify goals *)
    all:repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => progress cbv [Rewriter.Util.LetIn.Let_In] in *
               | _ => progress cbn [translate_cmd expr.interp type.app_curried
                                                  WeakestPrecondition.cmd
                                                  WeakestPrecondition.cmd_body] in *
               | _ => erewrite translate_cmd_valid_expr by eauto
               | _ => eapply Proper_cmd;
                        [ eapply Proper_call | repeat intro
                          | eapply assign_correct, translate_expr_correct; solve [eauto] ]
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
               end. }
      { intros; cleanup; subst; repeat split; try tauto; [ ].
        (* remaining case : only_differ *)
        eapply only_differ_step; try eassumption; [ ].
        eapply only_differ_sameset; eauto. } }
    { (* let-in (base type) *)
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2: {
        eapply IHe1_valid; clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | _ => solve [new_context_ok]
               | H : _ |- _ => solve [apply H]
               | _ => congruence
               end. }
      { intros; cleanup; subst; repeat split; try tauto; [ ].
        (* remaining case : only_differ *)
        eapply only_differ_step; try eassumption; [ ].
        eapply only_differ_sameset; eauto. } }
    { (* cons *)
      eapply Proper_cmd; [ eapply Proper_call | repeat intro | ].
      2: {
        eapply IHe1_valid with (G:=G); clear IHe1_valid;
        repeat match goal with
               | _ => progress (intros; cleanup)
               | H : _ |- _ => solve [apply H]
               | _ => solve [new_context_ok]
               | _ => congruence
               end. }
      { intros; cleanup; subst;
          repeat match goal with |- _ /\ _ => split end;
          try tauto; [ | ].
        all:cbn [assign fst snd varname_set] in *.
        { (* only_differ *)
          rewrite <-(Nat.add_1_r nextn) in *.
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. }
        { (* equivalence of output holds *)
          clear IHe1_valid. intro.
          repeat match goal with H : locally_equivalent _ _ _ |- _ =>
                          (* plug in just anything for locally_equivalent mem *)
                          specialize (H ltac:(auto))
          end.
          cbn [fst snd rtype_of_ltype rep.rtype_of_ltype rep.equiv rep.listZ_local
                   rep.Z rep.equiv base_ltype equivalent] in *.
          cleanup. cbn [map Compilers.ident_interp].
          split; cbn [Datatypes.length]; [ congruence | ].
          apply Forall2_cons; [intros|eassumption].
          eapply (expr_untouched ltac:(eassumption) ltac:(eassumption)); eauto; [ ].
          cbv [used_varnames PropSet.of_list PropSet.elem_of].
          rewrite in_map_iff. intro; cleanup.
          match goal with H : varname_gen ?x = varname_gen _ |- _ =>
                          apply varname_gen_unique in H; subst x end.
          match goal with H : In _ (seq _ _) |- _ =>
                          apply in_seq in H end.
          lia. } } }
    { (* nil *)
      repeat split; eauto; [ | ].
      { cbv [Interface.map.only_differ]. right; reflexivity. }
      { cbn [map locally_equivalent equivalent rep.equiv
                 rep.Z rep.listZ_local rep.rtype_of_ltype rtype_of_ltype
                 Compilers.ident_interp].
        eauto. } }
    { (* valid expr *)
      cleanup. repeat split; eauto.
      eapply only_differ_sameset; eauto. }
  Qed.
End Cmd.
