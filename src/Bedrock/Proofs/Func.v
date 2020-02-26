Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Cmd.
Require Import Crypto.Bedrock.Proofs.Flatten.
Require Import Crypto.Bedrock.Proofs.Varnames.
Require Import Crypto.Bedrock.Proofs.LoadStoreList.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Bedrock.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Func.
  Context {p : parameters} {p_ok : @ok p}.
  Local Notation bedrock_func := (string * (list string * list string * cmd))%type.

  (* TODO: are these all needed? *)
  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

  Inductive valid_func : forall {t}, @API.expr (fun _ => unit) t -> Prop :=
  | validf_Abs :
      forall {s d} f, valid_func (f tt) ->
                      valid_func (expr.Abs (s:=type.base s) (d:=d) f)
  | validf_base :
      forall {b} e, valid_cmd e -> valid_func (t:=type.base b) e
  .

  Lemma translate_func'_correct {t}
        (* three exprs, representing the same Expr with different vars *)
        (e0 : @API.expr (fun _ => unit) t)
        (e1 : @API.expr API.interp_type t)
        (e2 : @API.expr ltype t)
        (* expressions are valid input to translate_func' *)
        (e0_valid : valid_func e0)
        (* context list (consists only of arguments) *)
        (G : list _) :
    (* exprs are all related *)
    wf3 G e0 e1 e2 ->
    forall (argnames : type.for_each_lhs_of_arrow ltype t)
           (args : type.for_each_lhs_of_arrow API.interp_type t)
           (nextn : nat),
      (* ret1 := fiat-crypto interpretation of e1 applied to args1 *)
      let ret1 : base.interp (type.final_codomain t) :=
          type.app_curried (API.interp e1) args in
      (* out := translation output for e2; triple of
         (# varnames used, return values, cmd) *)
      let out := translate_func' e2 nextn argnames in
      let nvars := fst (fst out) in
      let ret2 := base_rtype_of_ltype (snd (fst out)) in
      let body := snd out in
      (* look up variables in argnames *)
      let argvalues :=
          type.map_for_each_lhs_of_arrow rtype_of_ltype argnames in
      (* argnames don't contain variables we could later overwrite *)
      (forall n,
        (nextn <= n)%nat ->
        ~ varname_set_args argnames (varname_gen n)) ->
      (* G doesn't contain variables we could later overwrite *)
      (forall n,
        (nextn <= n)%nat ->
        Forall (varname_not_in_context (varname_gen n)) G) ->
      forall (tr : Semantics.trace)
             (locals : Semantics.locals)
             (mem : Semantics.mem)
             (functions : list bedrock_func),
        (* argument values are equivalent *)
        locally_equivalent_args args argvalues locals ->
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
             Interface.map.only_differ
               locals (used_varnames nextn nvars) locals' /\
             locally_equivalent (listZ:=rep.listZ_local) ret1 ret2 locals').
  Proof.
    revert G. cbv zeta.
    induction e0_valid; intros *.
    { (* Abs *)
      inversion 1; cleanup_wf.
      cbn [translate_func']; intros.
      match goal with
      | H : context [varname_set_args] |- _ =>
        cbn [varname_set_args] in H;
          setoid_rewrite not_union_iff in H;
          match type of H with
            forall x y, ?P /\ ?Q =>
            assert (forall x y, P) by (apply H);
            assert (forall x y, Q) by (apply H);
            clear H
          end
      end.
      destruct argnames.
      cbv [locally_equivalent_args] in *.
      cbn [fst snd equivalent_args
               type.map_for_each_lhs_of_arrow] in *.
      match goal with H : sep _ _ map.empty |- _ =>
                      apply sep_empty_iff in H; cleanup
      end.
      eapply IHe0_valid; cbv [varname_not_in_context]; eauto;
        eapply Forall_cons; eauto. }
    { (* base case *)
      inversion 1; cleanup_wf;
      cbv [translate_func']; intros.
      all:eapply Proper_cmd;
        [solve [apply Proper_call]
        | repeat intro
        | eapply translate_cmd_correct;
          solve [eauto using Proper_call] ];
        cbv beta in *; cleanup; subst;
          tauto. }
  Qed.

  (* This lemma handles looking up the return values *)
  (* TODO : rename *)
  Lemma look_up_return_values {t} :
    forall (ret : base.interp t)
           (retnames : base_ltype (listZ:=rep.listZ_mem) t)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (R : Semantics.mem -> Prop),
    sep (equivalent ret (base_rtype_of_ltype retnames) locals) R mem ->
    let retvalues := base_rtype_of_ltype retnames in
    WeakestPrecondition.list_map
      (WeakestPrecondition.get locals) (flatten_retnames retnames)
      (fun flat_rets =>
         WeakestPrecondition.dexprs
           mem map.empty (flatten_rets retvalues) flat_rets /\
         sep (equivalent ret retvalues map.empty) R mem).
  Proof.
    cbv [flatten_retnames].
    induction t; cbn [flatten_base_ltype equivalent]; break_match;
      repeat match goal with
             | _ => progress (intros; cleanup)
             | _ => progress subst
             | _ => progress cbn [rep.equiv rep.listZ_mem rep.Z] in *
             | _ => progress cbn [WeakestPrecondition.list_map WeakestPrecondition.list_map_body]
             | H : sep (emp _) _ _ |- _ => apply sep_emp_l in H
             | H : WeakestPrecondition.dexpr _ _ _ _ |- _ => destruct H
             | |- WeakestPrecondition.get _ _ _ => eexists; split; [ eassumption | ]
             end.
    (* TODO *)
  Admitted.

  Lemma translate_func_correct {t}
        (e : API.Expr t)
        (* expressions are valid input to translate_func *)
        (e_valid : valid_func (e _)) :
    Wf3 e ->
    forall (fname : string)
           (retnames : base_ltype (type.final_codomain t))
           (argnames : type.for_each_lhs_of_arrow ltype t)
           (args : type.for_each_lhs_of_arrow API.interp_type t),
      (* rets1 := fiat-crypto interpretation of e1 applied to args *)
      let rets1 : base.interp (type.final_codomain t) :=
          type.app_curried (API.interp (e _)) args in
      (* extract list lengths from fiat-crypto arguments/return values *)
      let arglengths := list_lengths_from_args args in
      let retlengths := list_lengths_from_value rets1 in
      (* look up variables in argnames *)
      let argvalues :=
          type.map_for_each_lhs_of_arrow rtype_of_ltype argnames in
      (* out := translation output for e2; triple of
         (function arguments, function return variable names, body) *)
      let out := translate_func e argnames arglengths retnames in
      let f : bedrock_func := (fname, out) in
      let rets2 := base_rtype_of_ltype retnames in
      forall (tr : Semantics.trace)
             (mem : Semantics.mem)
             (flat_args : list Semantics.word)
             (functions : list bedrock_func)
             (P Ra Rr : Semantics.mem -> Prop),
        let init_locals :=
            match
              map.of_list_zip (flatten_argnames argnames) flat_args with
            | Some x => x
            | None => map.empty
            end in
        (* argnames don't contain variables we could later overwrite *)
        (forall n, ~ varname_set_args argnames (varname_gen n)) ->
        (* argument values (in their 3 forms) are equivalent *)
        sep (equivalent_args args argvalues init_locals) Ra mem ->
        (forall locals,
            WeakestPrecondition.dexprs
              mem locals (flatten_args argvalues) flat_args) ->
        (* seplogic frame for return values *)
        sep (lists_reserved retlengths) Rr mem ->
        (* translated function produces equivalent results *)
        WeakestPrecondition.call
          ((fname, out) :: functions) fname tr mem flat_args
          (fun tr' mem' flat_rets =>
             tr = tr' /\
             (* rets2 is a valid representation of flat_rets with no local
                variables in context *)
             WeakestPrecondition.dexprs
               mem' map.empty (flatten_rets rets2) flat_rets /\
             (* return values are equivalent *)
             sep (equivalent (listZ:=rep.listZ_mem) rets1 rets2 map.empty) Rr mem').
  Proof.
    cbv [translate_func Wf3]; intros.
    cbn [WeakestPrecondition.call WeakestPrecondition.call_body WeakestPrecondition.func].
    rewrite eqb_refl.
    match goal with H : _ |- _ =>
                    pose proof H; eapply of_list_zip_flatten_argnames in H;
                      destruct H as [? H]; rewrite H in * |-
    end.
    eexists; split; [ eassumption | ].
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
    2 : { eapply load_arguments_correct; try eassumption; eauto. }
    cbv beta in *. cleanup; subst.
    eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
    2 : { eapply translate_func'_correct with (args0:=args);
          cbv [context_equiv]; eauto. }
    cbv beta in *. cleanup; subst.
    eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
    2 : { eapply store_return_values_correct; eauto. }
    cbv beta in *. cleanup; subst.

    eapply Proper_list_map; [ solve [apply Proper_get]
                            | | eapply look_up_return_values;
                                solve [eauto] ].
    repeat intro; cleanup; eauto.
  Qed.

  (*
    TODO : prove assumptions shown by:
    Print Assumptions translate_func_correct.

    used_varnames_le (easy)
    used_varnames_iff (easy)
    only_differ_trans (easy)
    only_differ_sym (easy)
    only_differ_sameset (easy)
    only_differ_put (easy)
    equiv_Z_only_differ_iff1 (medium)
    get_untouched (medium)
    look_up_return_values (medium)
    assign_correct (medium/hard)
    translate_expr_correct (hard)
    store_return_values_correct (hard)

  *)
End Func.
