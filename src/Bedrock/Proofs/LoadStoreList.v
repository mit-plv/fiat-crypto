Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Dexprs.
Require Import Crypto.Bedrock.Proofs.Flatten.
Require Import Crypto.Bedrock.Proofs.Varnames.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Bedrock.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Import ListNotations.

Import API.Compilers.
Import Types.Notations Types.Types.

Section LoadStoreList.
  Context {p : parameters} {p_ok : @ok p}.

  (* TODO: are these all needed? *)
  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

  (* separation-logic relation that says space exists in memory for lists
     (other values are ignored) *)
  Fixpoint lists_reserved {t}
    : base_list_lengths t ->
      Semantics.mem -> (* memory *)
      Prop :=
    match t with
    | base.type.prod a b =>
      fun x => sep (lists_reserved (fst x)) (lists_reserved (snd x))
    | base_listZ =>
      fun n =>
        Lift1Prop.ex1
          (fun start : Semantics.word =>
             Lift1Prop.ex1
               (fun oldvalues : list Semantics.word =>
                  let size := Interface.word.of_Z (Z.of_nat n) in
                  array scalar size start oldvalues))
    | base_Z => fun _ _ => True
    |  _ => fun _ _ => False
    end.

  Fixpoint list_lengths_from_value {t}
    : base.interp t -> base_list_lengths t :=
    match t as t0 return base.interp t0 -> base_list_lengths t0 with
    | base.type.prod a b =>
      fun x : base.interp a * base.interp b =>
        (list_lengths_from_value (fst x),
         list_lengths_from_value (snd x))
    | base_listZ => fun x : list Z => length x
    | _ => fun _ => tt
    end.

  Fixpoint list_lengths_from_args {t}
    : type.for_each_lhs_of_arrow API.interp_type t ->
      type.for_each_lhs_of_arrow list_lengths t :=
    match t with
    | type.base b => fun _ => tt
    | type.arrow (type.base a) b =>
      fun x =>
        (list_lengths_from_value (fst x), list_lengths_from_args (snd x))
    | type.arrow a b =>
      fun x => (tt, list_lengths_from_args (snd x))
    end.

  Lemma load_list_item_correct
        (name : base_ltype (listZ:=rep.listZ_mem) base_listZ)
        i l :
    forall mem locals R,
      (i < length l)%nat ->
      sep (rep.equiv (t:=base_listZ)
                     l (base_rtype_of_ltype name) locals) R mem ->
      WeakestPrecondition.dexpr mem locals
                                (load_list_item (expr.var name) i)
                                (word.of_Z (hd 0%Z (skipn i l))).
  Proof.
    cbv [load_list_item];
      cbn [rep.equiv rep.listZ_mem rep.Z base_rtype_of_ltype
                     rep.rtype_of_ltype rep.listZ_mem ]; intros.
    cbn [WeakestPrecondition.dexpr
           WeakestPrecondition.expr WeakestPrecondition.expr_body] in *.
    repeat match goal with
           | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
             apply sep_ex1_l in H; destruct H; cbv zeta in *
           | H : context [emp] |- _ =>
             apply sep_assoc, sep_emp_l in H; cleanup
           end.
    match goal with
    | H : context[array] |- _ =>
      eapply Proper_sep_iff1 in H;
        [ | symmetry; apply array_index_nat_inbounds
                        with (n:=i) (default:=word.of_Z 0);
            rewrite map_length; eauto
          | reflexivity]
    end.
    match goal with
    | H : context[array] |- _ =>
      rewrite !word.ring_morph_mul, !word.of_Z_unsigned in H;
      rewrite <-!word.ring_morph_mul in H
    end.
    straightline.
    eapply Proper_get; [ repeat intro |  eassumption ].
    subst.
    eexists; split.
    { eapply load_word_of_sep. ecancel_assumption. }
    { rewrite skipn_map, hd_map. reflexivity. }
  Qed.

  Lemma load_list_correct rem l :
    forall (i nextn : nat)
           (name : base_ltype (listZ:=rep.listZ_mem) base_listZ)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (functions : list _)
           (R : Semantics.mem -> Prop),
      (forall (n : nat) (H : nextn <= n), name <> varname_gen n) ->
      length l = i + rem ->
      sep (rep.equiv (t:=base_listZ)
                     l (base_rtype_of_ltype name) locals) R mem ->
      (* load_list returns # vars used, variable names, cmd *)
      let out := load_list (expr.var name) i rem nextn in
      let nvars := fst (fst out) in
      let names' : base_ltype (listZ:=rep.listZ_local) base_listZ
          := snd (fst out) in
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (snd out)
        tr mem locals
        (fun tr' mem' locals' =>
           tr = tr' /\
           mem = mem' /\
           Interface.map.only_differ
             locals (used_varnames nextn nvars) locals' /\
           (forall n,
               (nextn + nvars <= n)%nat ->
               ~ varname_set names' (varname_gen n)) /\
           locally_equivalent (t:=base_listZ)
                              (skipn i l)
                              (base_rtype_of_ltype names') locals').
  Proof.
    induction rem; cbn [fst snd load_list]; intros.
    { straightline.
      cbv [locally_equivalent].
      cbn [rep.Z rep.listZ_local fold_right map
                 equivalent rep.equiv
                 base_rtype_of_ltype rep.rtype_of_ltype
                 varname_set rep.varname_set].
        repeat split.
      { eapply only_differ_zero. }
      { intros. cbv [PropSet.empty_set]. tauto. }
      { rewrite skipn_all by lia. econstructor. } }
    { cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eexists; split; cbv [dlet.dlet].
      { eapply load_list_item_correct; try eassumption.
        cbn [Datatypes.length]; lia. }
      eapply Proper_cmd; [ solve [apply Proper_call] | | ].
      2:{
        eapply IHrem; eauto with lia.
        eapply Proper_sep_iff1; [ | reflexivity | eassumption ].
        eapply equiv_listZ_only_differ_mem_iff1;
          eauto using only_differ_put.
        cbn [varname_set rep.varname_set rep.listZ_mem rep.Z].
        cbv [PropSet.singleton_set]; intros; subst.
        eauto with lia. }
      repeat intro. cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_succ.
      { intros.
        cbn [varname_set rep.varname_set rep.listZ_local rep.Z
                         fold_right] in *.
        apply not_union_iff; split; eauto with lia.
        cbv [PropSet.singleton_set].
        rewrite varname_gen_unique; lia. }
      { cbv [locally_equivalent] in *.
        cbn [map base_rtype_of_ltype
                 Compilers.base_interp
                 rep.rtype_of_ltype rep.listZ_local
                 equivalent rep.equiv ] in *.
        rewrite skipn_nth_default with (d:=0%Z) by lia.
        eapply Forall2_cons; eauto.
        eapply (equiv_Z_only_differ_iff1 (listZ:=rep.listZ_mem)); eauto.
        { eauto using only_differ_sym, only_differ_put. }
        { intros.
          match goal with H : _ |- _ =>
                          apply used_varnames_iff in H; cleanup; subst
          end.
          cbn [varname_set rep.varname_set rep.Z].
          cbv [PropSet.singleton_set PropSet.elem_of].
          rewrite varname_gen_unique; lia. }
        split; [ reflexivity | ].
        eexists; split; [ | reflexivity ].
        rewrite map.get_put_same, hd_skipn_nth_default.
        reflexivity. } }
  Qed.

  Lemma load_all_lists_correct {t} :
    forall (argnames : base_ltype t)
           (args : base.interp t)
           (functions : list _)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (nextn : nat)
           (R : Semantics.mem -> Prop),
        (* lengths of any lists in the arguments *)
        let arglengths := list_lengths_from_value args in
        (* look up variables in argnames *)
        let argvalues := base_rtype_of_ltype argnames in
        (* argnames don't contain variables we could later overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            ~ varname_set argnames (varname_gen n)) ->
        (* argument values are equivalent *)
        sep (equivalent args argvalues locals) R mem ->
        (* load_all_lists returns triple : # fresh variables used,
           new argnames with local lists, and cmd *)
        let out := load_all_lists nextn argnames arglengths in
        let nvars := fst (fst out) in
        (* extract loaded argument values *)
        let argnames' := snd (fst out) in
        let argvalues' := base_rtype_of_ltype argnames' in
        (* translated function produces equivalent results *)
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          (snd out)
          tr mem locals
          (fun tr' mem' locals' =>
             tr = tr' /\
             mem = mem' /\
             Interface.map.only_differ
               locals (used_varnames nextn nvars) locals' /\
             (forall n,
                 (nextn + nvars <= n)%nat ->
                 ~ varname_set argnames' (varname_gen n)) /\
             locally_equivalent args argvalues' locals').
  Proof.
    (* TODO: lots of repeated steps in this proof; automate *)
    induction t;
      cbn [fst snd map load_all_lists varname_set
               locally_equivalent equivalent rep.equiv
               flatten_base_ltype equivalent_flat_base
               base_rtype_of_ltype
               rep.varname_set rep.Z
          ]; break_match; intros;
        repeat match goal with
                 | _ => progress cleanup
                 | H : sep (sep (emp _) _) _ _ |- _ =>
                   apply sep_assoc in H
                 | H : sep (emp _) _ _ |- _ =>
                   apply sep_emp_l in H
                 | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
                   apply sep_ex1_l in H; destruct H
                 | H : False |- _ => tauto
               end.
    { (* base_Z *)
      repeat straightline. cbv [emp].
      repeat match goal with
               |- _ /\ _ => split end;
        eauto using only_differ_zero with lia. }
    { (* product *)
      straightline.
      eapply Proper_cmd; [ solve [apply Proper_call] | | ].
      2:{ eapply IHt1; eauto.
          { intros.
            match goal with
            | H : _ |- _ =>
              setoid_rewrite not_union_iff in H;
                apply H; eauto
            end. }
          { cbn [base_rtype_of_ltype fst snd] in *.
            ecancel_assumption. } }
      repeat intro. cleanup; subst.
      eapply Proper_cmd; [ solve [apply Proper_call] | | ].
      2:{ eapply IHt2; eauto.
          { intros.
            match goal with
            | H : _ |- _ =>
              setoid_rewrite not_union_iff in H;
                apply H; lia
            end. }
          { cbn [base_rtype_of_ltype fst snd] in *.
            eapply Proper_sep_iff1; [ | reflexivity | ].
            { eapply equivalent_only_differ_iff1;
                eauto using equiv_listZ_only_differ_mem, only_differ_sym.
              intros.
              match goal with H : _ |- _ =>
                              rewrite used_varnames_iff in H end.
              cleanup. subst.
              match goal with
              | H : _ |- _ =>
                setoid_rewrite not_union_iff in H;
                  apply H; eauto
              end. }
            ecancel_assumption. } }
      cbn [list_lengths_from_value fst snd] in *.
      repeat intro. cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_step.
      { intros; apply not_union_iff; split;
          match goal with H : _ |- _ => apply H; lia end. }
      { cbv [locally_equivalent locally_equivalent_args] in *.
        cbn [equivalent_args fst rtype_of_ltype].
        apply sep_empty_iff; split; eauto.
        eapply equivalent_only_differ_iff1;
          eauto using equiv_listZ_only_differ_local, only_differ_sym.
        intros.
        match goal with H : _ |- _ =>
                        rewrite used_varnames_iff in H end.
        cleanup. subst.
        match goal with H : _ |- _ => apply H; lia end. } }
  { (* base_listZ *)
    clear IHt.
     cbn [flatten_base_rtype base_rtype_of_ltype] in *.
    eapply Proper_cmd;
      [ solve [apply Proper_call]
      | | eapply load_list_correct; eauto; reflexivity ].
    repeat intro. cleanup; subst.
    repeat match goal with |- _ /\ _ => split end;
      eauto using only_differ_step. }
  Qed.

  Lemma load_arguments_correct {t} :
    forall (argnames : type.for_each_lhs_of_arrow ltype t)
           (args : type.for_each_lhs_of_arrow API.interp_type t)
           (functions : list _)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (nextn : nat)
           (R : Semantics.mem -> Prop),
        (* lengths of any lists in the arguments *)
        let arglengths := list_lengths_from_args args in
        (* look up variables in argnames *)
        let argvalues :=
            type.map_for_each_lhs_of_arrow rtype_of_ltype argnames in
        (* argnames don't contain variables we could later overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            ~ varname_set_args argnames (varname_gen n)) ->
        (* argument values are equivalent *)
        sep (equivalent_args args argvalues locals) R mem ->
        (* load_arguments returns triple : # fresh variables used,
           new argnames with local lists, and cmd *)
        let out := load_arguments nextn argnames arglengths in
        let nvars := fst (fst out) in
        (* extract loaded argument values *)
        let argnames' := snd (fst out) in
        let argvalues' :=
            type.map_for_each_lhs_of_arrow rtype_of_ltype argnames' in
        (* translated function produces equivalent results *)
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          (snd out)
          tr mem locals
          (fun tr' mem' locals' =>
             tr = tr' /\
             mem = mem' /\
             Interface.map.only_differ
               locals (used_varnames nextn nvars) locals' /\
             (forall n,
                 (nextn + nvars <= n)%nat ->
                 ~ varname_set_args argnames' (varname_gen n)) /\
             locally_equivalent_args args argvalues' locals').
  Proof.
    cbv zeta.
    induction t;
      destruct argnames;
      cbn [fst snd load_arguments
               list_lengths_from_args varname_set_args
               type.for_each_lhs_of_arrow equivalent_args
               type.map_for_each_lhs_of_arrow flatten_args
               ]; break_match; cbn [fst snd]; intros.
    { (* base type *)
      straightline.
      repeat match goal with
             | |- _ /\ _ => split end;
        eauto using only_differ_zero; try reflexivity.
      cbv [locally_equivalent_args equivalent_args emp].
      tauto. }
    { (* arrow (base _) _ *)
      cleanup. straightline.
      eapply Proper_cmd.
      3:{
        eapply load_all_lists_correct.
        { intros.
          match goal with
            | H : _ |- _ =>
          setoid_rewrite not_union_iff in H;
            apply H; eauto
          end. }
        { match goal with
          | H : sep (sep ?p ?q) ?r ?m |-
            sep ?p _ ?m =>
            apply sep_assoc in H; apply H
          end. } }
      { apply Proper_call. }
      { repeat intro; cleanup; subst.
        eapply Proper_cmd; [ solve [apply Proper_call] | | ].
        2:{
          eapply IHt2; eauto.
        { intros.
          match goal with
            | H : _ |- _ =>
          setoid_rewrite not_union_iff in H;
            apply H; lia
          end. }
        {
          match goal with
          | H : sep (sep ?p ?q) ?r ?m |- sep _ _ ?m =>
            apply sep_comm, sep_assoc, sep_comm in H;
            eapply Proper_sep_iff1; [ | reflexivity | apply H]
          end.
          eapply equivalent_args_only_differ_iff1;
            eauto using equiv_listZ_only_differ_mem, only_differ_sym.
          intros.
          match goal with H : _ |- _ =>
                          rewrite used_varnames_iff in H end.
          cleanup. subst.
          match goal with
            | H : _ |- _ =>
          setoid_rewrite not_union_iff in H;
            apply H; eauto
          end. } }
        { repeat intro. cleanup. subst.
          repeat match goal with |- _ /\ _ => split end;
            eauto using only_differ_step.
          { intros; apply not_union_iff; split;
              match goal with H : _ |- _ => apply H; lia end. }
          { cbv [locally_equivalent locally_equivalent_args] in *.
            cbn [equivalent_args fst rtype_of_ltype].
            apply sep_empty_iff; split; eauto.
            eapply equivalent_only_differ_iff1;
              eauto using equiv_listZ_only_differ_local, only_differ_sym.
            intros.
            match goal with H : _ |- _ =>
                            rewrite used_varnames_iff in H end.
            cleanup. subst.
            eauto with lia. } } } }
    { (* arrow (arrow _ _) _ *)
      match goal with
      | H : sep (emp False) _ _ |- _ =>
        eapply sep_emp_l in H; tauto
      end. }
  Qed.

  (* idea: pull return list lengths from fiat-crypto type *)
  Lemma store_return_values_correct {t} :
    forall (retnames_local : base_ltype t)
           (retnames_mem : base_ltype t)
           (retlengths : base_list_lengths t)
           (rets : base.interp t)
           (functions : list _)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (R : Semantics.mem -> Prop),
        (* use old values of memory to set up frame for return values *)
        sep (lists_reserved retlengths) R mem ->
        (* rets are stored in local retnames *)
        locally_equivalent
          rets (base_rtype_of_ltype retnames_local) locals ->
        (* translated function produces equivalent results *)
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          (store_return_values retnames_local retnames_mem)
          tr mem locals
          (fun tr' mem' locals' =>
             tr = tr' /\
             sep (equivalent
                    rets (base_rtype_of_ltype retnames_mem) locals')
                 R mem').
  Proof.
  Admitted.
End LoadStoreList.
