Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Varnames.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Bedrock.Translation.ExprWithSet.
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
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  Fixpoint assign {t : base.type} (nextn : nat)
    : base_rtype t -> (nat * base_ltype t * Syntax.cmd.cmd) :=
    match t with
    | base.type.prod a b =>
      fun rhs =>
        let assign1 := assign nextn (fst rhs) in
        let assign2 := assign (nextn + fst (fst assign1)) (snd rhs) in
        ((fst (fst assign1) + fst (fst assign2))%nat,
         (snd (fst assign1), snd (fst assign2)),
         Syntax.cmd.seq (snd assign1) (snd assign2))
    | base.type.list (base.type.type_base base.type.Z) =>
      fun _ =>
        (* not allowed to assign to a list; return garbage *)
        (0%nat, dummy_base_ltype _, Syntax.cmd.skip)
    | base.type.list _ | base.type.option _ | base.type.unit
    | base.type.type_base _ =>
      fun rhs =>
        let v := varname_gen nextn in
        (1%nat, v, Syntax.cmd.set v rhs)
    end.

  Fixpoint translate_cmd {t} (e : @API.expr ltype (type.base t)) (nextn : nat)
    : nat (* number of variable names used *)
      * base_ltype t (* variables in which return values are stored *)
      * Syntax.cmd.cmd (* actual program *) :=
    match e in expr.expr t0 return (nat * ltype t0 * Syntax.cmd.cmd) with
    | expr.LetIn (type.base t1) (type.base t2) x f =>
      let trx :=
          match translate_expr_with_set x nextn with
          | Some trx => trx
          | None => assign nextn (translate_expr true x)
          end in
      let trf := translate_cmd (f (snd (fst trx))) (nextn + fst (fst trx)) in
      ((fst (fst trx) + fst (fst trf))%nat,
       snd (fst trf),
       Syntax.cmd.seq (snd trx) (snd trf))
    | expr.App
        type_listZ type_listZ
        (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
      let trx := assign nextn (translate_expr true x) in
      let trl := translate_cmd l (S nextn) in
      ((fst (fst trx) + fst (fst trl))%nat,
       snd (fst trx) :: snd (fst trl),
       Syntax.cmd.seq (snd trx) (snd trl))
    | expr.App _ (type.base t) f x =>
      let v := translate_expr true (expr.App f x) in
      assign nextn v
    | expr.Ident type_listZ (ident.nil _) =>
      (0%nat, [], Syntax.cmd.skip)
    | expr.Ident (type.base _) x =>
      let v := translate_expr true (expr.Ident x) in
      assign nextn v
    | expr.Var (type.base _) x =>
      let v := translate_expr true (expr.Var x) in
      assign nextn v
    | _ => (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.

  Section Proofs.
    Context {p_ok : @ok p}.
    Context (call : Syntax.funname ->
                    Semantics.trace ->
                    Interface.map.rep (map:=Semantics.mem) ->
                    list Interface.word.rep ->
                    (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                     list Interface.word.rep -> Prop) ->
                    Prop).
    Context (Proper_call :
               Morphisms.pointwise_relation
                 Syntax.funname
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
    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    Inductive valid_cmd : forall {t}, @API.expr (fun _ => unit) (type.base t) -> Prop :=
    | valid_LetIn_with_set :
        forall {b} x f,
          valid_expr_wset x -> valid_cmd (f tt) ->
          valid_cmd (expr.LetIn (A:=type_ZZ) (B:=type.base b) x f)
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
             (mem locals : Interface.map.rep)
             (R : Interface.map.rep -> Prop),
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
             /\ sep (emp (locally_equivalent x (rtype_of_ltype (snd (fst a))) locals')) R mem').
    Admitted.

    (* N.B. technically, x2 and f2 are not needed in the following
       lemmas, it just makes things easier *)
    Lemma translate_cmd_expr_with_set {t1 t2 : base.type}
          G x1 x2 x3 f1 f2 f3 nextn
          (trx : nat * base_ltype t1 * Syntax.cmd.cmd) :
      wf3 G x1 x2 x3 ->
      (forall v1 v2 v3,
          wf3
            (existT (fun t => (unit * API.interp_type t * ltype t)%type)
                    (type.base t1) (v1, v2, v3) :: G)
              (f1 v1) (f2 v2) (f3 v3)) ->
      valid_cmd (f1 tt) ->
      translate_expr_with_set (t:=type.base t1) x3 nextn = Some trx ->
      let trf := translate_cmd (f3 (snd (fst trx))) (nextn + fst (fst trx)) in
      let nvars := (fst (fst trx) + fst (fst trf))%nat in
      translate_cmd (expr.LetIn (A:=type.base t1) (B:=type.base t2) x3 f3) nextn =
      (nvars, snd (fst trf), Syntax.cmd.seq (snd trx) (snd trf)).
    Proof.
      intros. subst nvars trf. cbn [translate_cmd].
      match goal with H : _ = Some _ |- _ => rewrite H end.
      reflexivity.
    Qed.


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
      inversion 1; hammer_wf; try reflexivity;
        inversion 1; hammer_wf; reflexivity.
    Qed.

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
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
          context_equiv G locals ->
          (* TODO: does this need to be a separation-logic condition? *)
          R mem ->
          (* executing translation output is equivalent to interpreting e *)
          WeakestPrecondition.cmd
            call body tr mem locals
            (fun tr' mem' locals' =>
               tr = tr' /\
               mem = mem' /\
               Interface.map.only_differ
                 locals (used_varnames nextn nvars) locals' /\
          sep (emp (locally_equivalent ret1 ret2 locals')) R mem').
    Proof.
      revert e2 e3 G.
      subst t.
      induction e1_valid; try (inversion 1; [ ]); cbv zeta in *; intros.
      all:hammer_wf. (* get rid of the wf nonsense *)

      { (* let-in with an expr-with-set *)
        (* posit the existence of a return value from translate_expr_with_set and use
           it to rewrite translate_expr *)
        match goal with H : valid_expr_wset _ |- _ =>
                        pose proof H;
                        eapply translate_expr_with_set_Some in H;
                        [ destruct H | eassumption .. ]
        end.
        erewrite @translate_cmd_expr_with_set by eassumption.
        cleanup.

        (* simplify fiat-crypto step *)
        intros; cbn [expr.interp type.app_curried] in *.
        cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

        (* simplify bedrock2 step *)
        cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
        2 : eapply translate_expr_with_set_correct with (R0:=R); try eassumption.

        (* use inductive hypothesis *)
        cleanup.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].

        2: { eapply IHe1_valid with (R:=R);
             clear IHe1_valid;
             try match goal with H : _ |- _ => solve [apply H] end;
             repeat match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
             cleanup; eauto with lia.

             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context].
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               eauto using used_varnames_le. }
             { (* proof that context_list_equiv continues to hold *)
               cbv [context_equiv] in *; apply Forall_cons; [ eassumption | ].
               eapply equivalent_not_in_context_forall; eauto. intro.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               rewrite used_varnames_iff. intros; cleanup.
               subst. eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* let-in (product of base types) *)
      (* simplify one translation step *)
      cbn [translate_cmd].
      erewrite translate_expr_with_set_None by eassumption.
      cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.
             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context ltype base_ltype] in *.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               eauto using used_varnames_le. }
             { (* proof that context_list_equiv continues to hold *)
               cbv [context_equiv] in *; apply Forall_cons; eauto; [ ].
               eapply equivalent_not_in_context_forall; eauto. intro.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               rewrite used_varnames_iff. intros; cleanup.
               subst. eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* let-in (base type) *)
      (* simplify one translation step *)
      cbn [translate_cmd].
      erewrite translate_expr_with_set_None by eassumption.
      cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.

           { (* proof that new context doesn't contain variables that could be
                overwritten in the future *)
             intros; apply Forall_cons; eauto with lia; [ ].
             cbn [assign fst] in *.
             cbn [varname_not_in_context varname_set fst snd].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             setoid_rewrite varname_gen_unique.
             lia. }
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_equiv] in *; apply Forall_cons; eauto; [ ].
             eapply equivalent_not_in_context_forall; eauto.
             cbn [assign snd fst varname_set].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             intros; subst; eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* cons *)

      (* repeatedly do inversion until the cons is exposed *)
      repeat match goal with
             | H : wf3 _ _ _ _ |- _ =>
               match type of H with context [Compilers.ident.cons] =>
                                    inversion H; hammer_wf
               end
             end.

      (* simplify one translation step *)
      cbn [translate_cmd]. cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried Compilers.ident_interp] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R); clear IHe1_valid.
           all:try match goal with H : _ |- _ => solve [apply H] end.
           all: match goal with
                  H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
           all:cleanup.
           all: try solve [eauto with lia].
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_equiv] in *.
             eapply equivalent_not_in_context_forall; eauto.
             cbn [assign snd fst varname_set].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             intros; subst; eauto. } }
      { intros; cleanup; subst; repeat split; try tauto; [ | ].
        all:cbn [assign fst snd varname_set] in *.
        { (* only_differ *)
          rewrite <-(Nat.add_1_r nextn) in *.
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. }
        { (* equivalence of output holds *)
          clear IHe1_valid.
          apply sep_emp_l.
          repeat match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
          destruct_head'_and.
          match goal with H : locally_equivalent _ _ _ |- _ =>
                          cbv [locally_equivalent] in *;
                            (* plug in just anything for locally_equivalent mem *)
                            specialize (H ltac:(auto))
          end.
          cbn [fst snd rtype_of_ltype rep.rtype_of_ltype rep.equiv rep.listZ_local
                   locally_equivalent equivalent] in *.
          cleanup.
          rewrite ?map_length in *.
          repeat split; cbn [length]; [ congruence | | assumption ].
          apply Forall2_cons; [|eassumption].

          cbn [rep.equiv rep.Z] in *.
          let mem := fresh "mem" in
          intros ? mem; eapply (expr_untouched mem mem); eauto; [ ].
          cbv [used_varnames PropSet.of_list PropSet.elem_of].
          rewrite in_map_iff. intro; cleanup.
          match goal with H : varname_gen ?x = varname_gen _ |- _ =>
                          apply varname_gen_unique in H; subst x end.
          match goal with H : In _ (seq _ _) |- _ =>
                          apply in_seq in H end.
          lia. } } }
    { (* nil *)
      (* simplify one translation step *)
      cbn [translate_cmd assign fst snd]. cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried Compilers.ident_interp] in *.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

      repeat split; eauto; [ | ].
      { cbv [Interface.map.only_differ]. right; reflexivity. }
      { apply sep_emp_l. cbv [locally_equivalent].
        cbn [equivalent rep.Z rep.listZ_local rep.equiv
                        rep.rtype_of_ltype rtype_of_ltype map].
        eauto. } }
    { (* valid expr *)
      erewrite translate_cmd_valid_expr by eauto.

      (* simplify bedrock2 cmd *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      cleanup. repeat split; eauto.
      eapply only_differ_sameset; eauto. }
    Qed.
  End Proofs.
End Cmd.