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
Require Import Crypto.Bedrock.Util.
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
      list_locs t ->
      Semantics.locals ->
      Semantics.mem ->
      Prop :=
    match t as t0 return base_list_lengths t0 -> list_locs t0 -> _ with
    | base.type.prod a b =>
      fun x y locals => sep (lists_reserved (fst x) (fst y) locals)
                            (lists_reserved (snd x) (snd y) locals)
    | base_listZ =>
      fun n loc locals =>
        (Lift1Prop.ex1
           (fun oldvalues : list Z =>
              sep (emp (length oldvalues = n))
                  (equivalent (t:=base_listZ) (listZ:=rep.listZ_mem)
                              oldvalues loc locals)))
    | base_Z => fun _ _ _ => emp True
    |  _ => fun _ _ _ => emp False
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

  Lemma lists_reserved_0 {listZ:rep.rep base_listZ} start locals:
    Lift1Prop.iff1
      (lists_reserved (t:=base_listZ) 0%nat start locals)
      (emp (exists x, locally_equivalent (t:=base_Z) x start locals)).
  Proof.
    cbv [lists_reserved].
    split; intros;
      repeat match goal with
             | _ => progress (sepsimpl; subst)
             | _ => progress cbn [locally_equivalent equivalent rep.equiv rep.Z] in *
             | H : Datatypes.length _ = 0%nat |- _ =>
               apply length0_nil in H; subst
             | H : rep.equiv _ _ _ _ |- _ => apply equiv_nil_iff1 in H
             | |- Lift1Prop.ex1 _ _ => eexists
             | |- _ /\ _ => split
             | |- rep.equiv [] _ _ _ => apply equiv_nil_iff1
             | _ => solve [eauto using List.length_nil]
             | _ => eexists; split; solve [eauto]
             end.
  Qed.

  (* TODO : move *)
  Lemma undef_on_None
        `{map:map.map} `{ok:map.ok} m k ks :
    map.undef_on m ks ->
    PropSet.elem_of k ks ->
    map.get m k = None.
  Proof.
    intros.
    match goal with H : map.undef_on _ _ |- _ =>
                    specialize (H _ ltac:(eassumption));
                      rewrite map.get_empty in H
    end.
    congruence.
  Qed.

  (* TODO : move *)
  Lemma get_put_same l x y (post:_->Prop) :
    post y ->
    WeakestPrecondition.get (map.put l x y) x post.
  Proof.
    cbv [WeakestPrecondition.get]; intros.
    exists y; rewrite map.get_put_same; tauto.
  Qed.

  (* TODO : move *)
  Lemma getmany_of_tuple_empty
        `{map:map.map} `{ok:map.ok} sz keys :
    sz <> 0%nat ->
    map.getmany_of_tuple (sz:=sz) map.empty keys = None.
  Proof.
    destruct sz; try congruence.
    cbn; intros. rewrite map.get_empty. reflexivity.
  Qed.

  (* TODO : move *)
  Lemma load_empty :
    forall s m a post,
      WeakestPrecondition.load s map.empty a post ->
      WeakestPrecondition.load s m a post.
  Proof.
    intros *.
    cbv [WeakestPrecondition.load
           Memory.load Memory.load_Z Memory.load_bytes].
    rewrite getmany_of_tuple_empty; intros;
      repeat match goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => congruence
             end.
    cbv [Memory.bytes_per]; break_match; try congruence.
    change 0%nat with (Z.to_nat 0).
    pose proof word.width_pos.
    rewrite Z2Nat.inj_iff by (try apply Div.Z.div_nonneg; lia).
    rewrite Z.eq_sym_iff.
    apply Z.lt_neq, Z.div_str_pos; lia.
  Qed.
    
  (* TODO : move *)
  Lemma expr_empty :
    forall e m locals post,
      WeakestPrecondition.expr map.empty locals e post ->
      WeakestPrecondition.expr m locals e post.
  Proof.
    induction e;
      cbn [WeakestPrecondition.expr
             WeakestPrecondition.expr_body];
      cbv [dlet.dlet WeakestPrecondition.literal
                     WeakestPrecondition.get];
      intros; eauto; [ | ].
    { eapply IHe; eauto.
      eapply Proper_expr; [ repeat intro | eassumption ].
      eauto using load_empty. }
    { eapply IHe1; eauto.
      eapply Proper_expr; [ repeat intro | eassumption ].
      cbv beta in *. eapply IHe2; eauto. }
  Qed.

  (* TODO : move *)
  Lemma get_only_differ_undef
        `{map:map.map} `{ok:map.ok} m1 m2 ks k v :
    map.only_differ m1 ks m2 ->
    map.undef_on m1 ks ->
    map.get m1 k = Some v ->
    map.get m2 k = Some v.
  Proof.
    repeat match goal with
           | _ => progress intros
           | H : map.only_differ _ _ _ |- _ =>
             specialize (H k); destruct H
           | H1 : map.undef_on _ ?ks, H2 : PropSet.elem_of ?k ?ks |- _ =>
             eapply undef_on_None in H2; [ | eassumption .. ]
           | _ => congruence
           end.
  Qed.

  (* TODO : move *)
  Lemma expr_only_differ_undef :
    forall e m vset locals locals' post,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      WeakestPrecondition.expr m locals e post ->
      WeakestPrecondition.expr m locals' e post.
  Proof.
    induction e;
      cbn [WeakestPrecondition.expr
             WeakestPrecondition.expr_body];
      cbv [dlet.dlet WeakestPrecondition.literal
                     WeakestPrecondition.get];
      intros; eauto; [ | ].
    { match goal with H : exists _, _ |- _ => destruct H end.
      destruct_head'_and. eexists; eauto using get_only_differ_undef. }
    { eapply IHe1; eauto.
      eapply Proper_expr; [ repeat intro | eassumption ].
      cbv beta in *. eapply IHe2; eauto. }
  Qed.

  (* TODO : move *)
  Lemma equiv_Z_only_differ_undef {listZ:rep.rep base_listZ} :
    forall x y locals locals' vset,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      Lift1Prop.impl1
        (equivalent (t:=base_Z) x y locals)
        (equivalent x y locals').
  Proof.
    cbv [equivalent rep.equiv rep.Z WeakestPrecondition.dexpr].
    repeat intro; sepsimpl; subst.
    eauto using expr_only_differ_undef.
  Qed.

  (* TODO : move *)
  Lemma equiv_listZ_mem_only_differ_undef :
    forall x y locals locals' vset,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      Lift1Prop.impl1
        (equivalent (t:=base_listZ) (listZ:=rep.listZ_mem)
                    x y locals)
        (equivalent x y locals').
  Proof.
    cbn [equivalent rep.equiv rep.listZ_mem]; intros; sepsimpl.
    repeat intro; sepsimpl. eexists.
    eapply Proper_sep_impl1; [ | reflexivity | eassumption ].
    repeat intro.
    eapply (equiv_Z_only_differ_undef (listZ:=rep.listZ_mem)); eauto.
  Qed.

  Lemma lists_reserved_only_differ_undef t :
    forall lengths locs locals locals' vset,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      Lift1Prop.impl1
        (lists_reserved (t:=t) lengths locs locals)
        (lists_reserved lengths locs locals').
  Proof.
    induction t; cbn [lists_reserved];
      break_match; intros; try reflexivity; [ | ].
    { rewrite IHt1, IHt2; try reflexivity; eauto. }
    { repeat intro; sepsimpl; eexists; sepsimpl; eauto.
      eapply equiv_listZ_mem_only_differ_undef; eauto. }
  Qed.

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
    sepsimpl.
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
        apply disjoint_singleton_singleton; eauto using string_dec. }
      repeat intro.
      cbv beta in *; cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_succ.
      { cbn [varname_set rep.varname_set rep.listZ_local rep.Z
                         fold_right] in *.
        intros.
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
        { eapply disjoint_used_varnames_singleton.
          lia. }
        { split;[reflexivity|].
          eexists; split; [ | reflexivity ].
          rewrite map.get_put_same, hd_skipn_nth_default.
          reflexivity. } } }
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
    induction t;      cbn [fst snd map load_all_lists varname_set
               locally_equivalent equivalent rep.equiv
               flatten_base_ltype equivalent_flat_base
               base_rtype_of_ltype
               rep.varname_set rep.Z
          ]; break_match; intros; sepsimpl; [ | | ].
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
              eapply disjoint_used_varnames_lt.
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
        eapply disjoint_used_varnames_lt.
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
        { match goal with
          | H : sep (sep ?p ?q) ?r ?m |- sep _ _ ?m =>
            apply sep_comm, sep_assoc, sep_comm in H;
            eapply Proper_sep_iff1; [ | reflexivity | apply H]
          end.
          eapply equivalent_args_only_differ_iff1;
            eauto using equiv_listZ_only_differ_mem, only_differ_sym.
          intros.
          eapply disjoint_used_varnames_lt.
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
            eapply disjoint_used_varnames_lt.
            intros; cleanup. subst.
            eauto with lia. } } } }
    { (* arrow (arrow _ _) _ *)
      sepsimpl. }
  Qed.

  Lemma store_list_correct :
    forall (start : string)
           (functions : list _)
           (value_names2 value_names1 : list string)
           (rets1 rets2 rets : base.interp base_listZ)
           (i : nat)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (R : Semantics.mem -> Prop),
      let retlengths :=
          list_lengths_from_value (t:=base_listZ) rets2 in
      let loc : list_locs base_listZ := expr.var start in
      let offset := (Z.of_nat i * word_size_in_bytes)%Z in
      let loc' := expr.op bopname.add loc (expr.literal offset) in
      let values1 := map expr.var value_names1 in
      let values2 := map expr.var value_names2 in
      rets = rets1 ++ rets2 ->
      length rets1 = length value_names1 ->
      length rets2 = length value_names2 ->
      length value_names1 = i ->
      (* yet-to-be-stored values *)
      locally_equivalent (listZ:=rep.listZ_local) rets2 values2 locals ->
      (* already-stored values *)
      sep (map:=Semantics.mem)
          (sep (map:=Semantics.mem)
               (rep.equiv (rep:=rep.listZ_mem)
                          rets1 (expr.var start) locals)
               (lists_reserved retlengths loc' locals)) R mem ->
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (store_list (expr.var start) values2 i) tr mem locals
        (fun tr' mem' locals' =>
           tr = tr' /\
           locals = locals' /\
           sep (map:=Semantics.mem)
               (rep.equiv (rep:=rep.listZ_mem)
                          rets (expr.var start) locals') R mem').
  Proof.
    cbv zeta.
    induction value_names2 as [|n0 ?]; destruct rets2 as [|r0 rets2];
      cbn [store_list Datatypes.length locally_equivalent equivalent
                      rep.equiv rep.listZ_local rep.Z rep.listZ_mem];
      intros; subst; try lia; sepsimpl.
    { repeat split; try reflexivity.
      repeat match goal with
             | _ => progress sepsimpl
             | H : _ |- _ =>
               rewrite List.firstn_all, List.skipn_all_exact in H
             | |- Lift1Prop.ex1 _ _ => eexists
             | |- _ /\ _ => split
             | _ => eassumption
             end.
      eapply Proper_sep_iff1 in H1;
        [ | rewrite ?(lists_reserved_0 (listZ:=rep.listZ_local)); reflexivity .. ].
      sepsimpl.
      rewrite app_nil_r.
      ecancel_assumption. }
    { repeat match goal with
             | H : _ |- _ => rewrite word.of_Z_unsigned in H end.
      subst; eexists; split.
      { cbn [WeakestPrecondition.dexpr
               WeakestPrecondition.expr
               WeakestPrecondition.expr_body] in *.
        eapply Proper_get; [ | eassumption ].
        repeat intro; subst.
        reflexivity. }
      cbn [map] in *.
      match goal with
      | H : Forall2 _ (_ :: _) (_ :: _) |- _ => inversion H; subst; clear H
      end.
      sepsimpl.
      eexists; split.
      { cbn [WeakestPrecondition.dexpr
               WeakestPrecondition.expr
               WeakestPrecondition.expr_body] in *.
        eassumption. }
      cbn [lists_reserved
             list_lengths_from_value
             equivalent
             rep.equiv rep.Z rep.listZ_mem] in *.
      sepsimpl.
      match goal with
        H : Datatypes.length ?x = Datatypes.length (_ :: _) |- _ =>
        destruct x; cbn [Datatypes.length] in H; [ lia | ]
      end.
      cbn [map array Semantics.interp_binop] in *.

      (* we now have a Z in context that should be equivalent to the offsetted
         location; destruct WeakestPrecondition.dexpr to expose that equivalence *)
      match goal with
        H : WeakestPrecondition.dexpr _ _ (expr.op _ _ _) ?v |- _ =>
          cbn [WeakestPrecondition.dexpr
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body
                 Semantics.interp_binop] in H;
          cbv [dlet.dlet WeakestPrecondition.literal
                         WeakestPrecondition.get] in H;
          cleanup;
          match goal with H : v = _ |- _ => rewrite H in * end
      end.
      match goal with
      | H1 : (WeakestPrecondition.dexpr _ ?l (expr.var ?x) ?v1),
             H' : (map.get ?l ?x = Some ?v2) |- _ =>
        replace v2 with v1 in *
          by (cbn [WeakestPrecondition.dexpr
                     WeakestPrecondition.expr
                     WeakestPrecondition.expr_body] in H;
              cbv [WeakestPrecondition.get] in H;
              cleanup; congruence)
      end.

      eapply store_word_of_sep; [ ecancel_assumption | ].
      intros. sepsimpl.
      eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
      2:{
        eapply IHvalue_names2 with
            (rets1:= rets1 ++ [r0]) (rets2:=rets2)
            (value_names1:=value_names1 ++ [n0]);
        rewrite ?app_length; cbn [length]; eauto; try lia; [ ].
        {
          (* look at goal and plug in evars very carefully *)
          sepsimpl.
          match goal with H: ?P (expr.var start) (word.of_Z ?x) |- _ =>
                          exists x end.
          sepsimpl; auto.
          match goal with
            H : context [array _ _ (word.add _ _) (map _ ?x)] |- _ =>
            exists x end.
          sepsimpl; auto.
          eexists. sepsimpl.
          { eexists; split; [ eassumption | ].
            cbn [WeakestPrecondition.dexpr
                   WeakestPrecondition.expr
                   WeakestPrecondition.expr_body
                   Semantics.interp_binop].
            cbv [WeakestPrecondition.literal dlet.dlet].
            rewrite <-word.ring_morph_add. reflexivity. }
          match goal with
            H : context [array _ _ (word.add (word.add _ _) _) _] |- _ =>
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
          end.
          rewrite map_app, array_append. cbn [map array].
          match goal with
            |- context [word.add (word.add ?a (word.of_Z (Z.of_nat ?b * ?c))) (word.of_Z ?c)] =>
            replace (word.add (word.add a (word.of_Z (Z.of_nat b * c))) (word.of_Z c)) with
              (word.add a (word.of_Z (Z.of_nat (S b) * c)))
              by (apply word.unsigned_inj;
                  rewrite Nat2Z.inj_succ, <-Z.add_1_r;
                  rewrite !word.unsigned_add, !word.unsigned_of_Z;
                  cbv [word.wrap]; Modulo.pull_Zmod; f_equal; lia)
          end.
          cbn [Compilers.base_interp] in *. (* simplifies implicit types *)
          rewrite !word.ring_morph_add.
          rewrite !map_length.
          match goal with
          | |- Lift1Prop.iff1 ?L ?R =>
            let la := match L with context [scalar ?la] => la end in
            let ra := match R with context [scalar ?ra] => ra end in
            replace ra with la
              by (apply word.unsigned_inj;
                  rewrite !word.unsigned_add, !word.unsigned_of_Z;
                  cbv [word.wrap]; Modulo.pull_Zmod; f_equal; lia)
          end.
          cancel. } }
      cbv beta in *; cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto.
      rewrite app_cons_app_app.
      eassumption. }
  Qed.

  (* TODO : move *)
  Lemma union_comm {E} (s1 s2 : PropSet.set E) :
    PropSet.sameset (PropSet.union s1 s2)
                    (PropSet.union s2 s1).
  Proof.
    apply sameset_iff.
    cbv [PropSet.union PropSet.elem_of].
    intros. rewrite or_comm. reflexivity.
  Qed.

  (* TODO : move *)
  Lemma union_assoc {E} (s1 s2 s3 : PropSet.set E) :
    PropSet.sameset (PropSet.union s1 (PropSet.union s2 s3))
                    (PropSet.union (PropSet.union s1 s2) s3).
  Proof.
    apply sameset_iff.
    cbv [PropSet.union PropSet.elem_of].
    intros. rewrite or_assoc. reflexivity.
  Qed.

  (* TODO : move *)
  Lemma only_differ_union_undef_l m1 m2 k1 k2 :
    map.only_differ m1 (PropSet.union k1 k2) m2 ->
    map.undef_on m1 k2 ->
    map.undef_on m2 k2 ->
    map.only_differ m1 k1 m2.
  Proof.
    intros.
    match goal with H : map.only_differ _ _ _ |- map.only_differ _ _ _ =>
                    let x := fresh "x" in intro x; specialize (H x);
                                            destruct H
    end; [ | tauto ].
    match goal with H : PropSet.elem_of _ (PropSet.union _ _) |- _ =>
                    destruct H end;
      erewrite ?undef_on_None by eauto; tauto.
  Qed.

  (* TODO : move *)
  Lemma undef_on_union_iff m k1 k2 :
    map.undef_on m (PropSet.union k1 k2) <->
    (map.undef_on m k1 /\ map.undef_on m k2).
  Proof.
    cbv [map.undef_on map.agree_on PropSet.union PropSet.elem_of].
    repeat split; intros; destruct_head'_or; destruct_head'_and; eauto.
  Qed.

  Lemma store_return_values_correct {t} init_locals :
    forall (retnames_local : base_ltype t)
           (retnames_mem : base_ltype t)
           (vset : PropSet.set string)
           (rets : base.interp t)
           (locs : list_locs t)
           (functions : list _)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (R : Semantics.mem -> Prop),
      let retlengths := list_lengths_from_value rets in
      sep (lists_reserved retlengths locs init_locals) R mem ->
      map.undef_on init_locals (PropSet.union vset (varname_set retnames_mem)) ->
      map.only_differ init_locals vset locals ->
      (* rets are stored in local retnames *)
      locally_equivalent
        rets (base_rtype_of_ltype retnames_local) locals ->
      (* retnames are disjoint *)
      PropSet.disjoint (varname_set retnames_local)
                       (varname_set retnames_mem) ->
      (* retnames don't contain duplicates *)
      NoDup (flatten_base_ltype retnames_mem) ->
      (* translated function produces equivalent results *)
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (store_return_values retnames_local retnames_mem locs)
        tr mem locals
        (fun tr' mem' locals' =>
           tr = tr' /\
           map.only_differ locals (varname_set retnames_mem) locals' /\
           sep (equivalent
                  rets (base_rtype_of_ltype retnames_mem) locals')
               R mem').
  Proof.
    cbv zeta.
    induction t;
      cbn [fst snd store_return_values lists_reserved
               locally_equivalent equivalent varname_set
               base_rtype_of_ltype rep.rtype_of_ltype
               rep.equiv rep.varname_set rep.Z
               flatten_base_ltype list_lengths_from_value
          ]; break_match; intros; sepsimpl; [ | | ].
    { (* base_Z *)
      repeat straightline.
      eexists; split; [eassumption|].
      cbv [dlet.dlet]; split; [reflexivity|].
      split;
        [ solve [eauto using only_differ_sym, only_differ_put] | ].
      apply sep_emp_l. split; [|assumption].
      cbv [WeakestPrecondition.dexpr
             WeakestPrecondition.expr
             WeakestPrecondition.expr_body
             WeakestPrecondition.get] in *.
      cleanup; subst. eexists.
      rewrite map.get_put_same.
      split; reflexivity. }
    { (* prod *)
      repeat straightline.
      match goal with H : _ |- _ =>
                      pose proof H;
                      apply NoDup_app_iff in H; cleanup end.
      repeat match goal with
             | _ => progress cleanup
             | H : PropSet.disjoint (PropSet.union _ _) _ |- _ =>
               apply disjoint_union_l_iff in H
             | H : PropSet.disjoint _ (PropSet.union _ _) |- _ =>
               apply disjoint_union_r_iff in H
             | H : map.undef_on _ (PropSet.union _ _) |- _ =>
               apply undef_on_union_iff in H
             end.
      eapply Proper_cmd;
        [ solve [apply Proper_call] | repeat intro
          | eapply IHt1; try ecancel_assumption;
            try (apply undef_on_union_iff; split);
            solve [eauto] ].
      cbv beta in *. cleanup; subst.
      eapply Proper_cmd;
        [ solve [apply Proper_call] | repeat intro | ].
      2:{ eapply IHt2 with (vset:=PropSet.union vset (varname_set (fst retnames_mem)));
          try ecancel_assumption; eauto.
          { apply undef_on_union_iff; split; eauto.
            apply undef_on_union_iff; split; eauto. }
          { rewrite union_comm.
            eapply only_differ_trans; eauto. }
          { cbv [locally_equivalent].
            eapply equivalent_only_differ; eauto with equiv.
            symmetry; eauto. } }
      cbv beta in *. cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_sym, only_differ_trans.
      use_sep_assumption. cancel.
      eapply equivalent_only_differ_iff1; eauto with equiv.
      rewrite !varname_set_flatten.
      symmetry.
      eapply NoDup_disjoint; eauto using string_dec. }
    { (* base_listZ *)
      repeat straightline.
      repeat match goal with p := _ |- _ => subst p end.
      repeat match goal with
             | H : map.undef_on _ (PropSet.union _ _) |- _ =>
               apply undef_on_union_iff in H
             end.
      cbn [rep.equiv rep.listZ_mem rep.Z] in *.
      sepsimpl.
      eexists; split.
      { eapply expr_only_differ_undef;
          eauto using expr_empty. }
      eapply Proper_cmd;
        [ solve [apply Proper_call] | repeat intro | ].
      2:{
        eapply store_list_correct with
            (rets:=rets) (rets1:=[]) (rets2:=rets)
            (value_names1:=nil); auto using List.length_nil; [ | | ].
        { cbn [rep.equiv rep.rtype_of_ltype rep.listZ_local] in *.
          eapply Forall.eq_length_Forall2, Forall.Forall2_map_r_iff.
          eauto. }
        { cbn [rep.equiv rep.Z rep.rtype_of_ltype rep.listZ_local] in *.
          sepsimpl; eauto using dexpr_put_same.
          eapply Forall2_impl_strong; eauto.
          intros; sepsimpl.
          match goal with H : _ |- _ => apply in_map_iff in H end.
          cleanup; subst.

          cbn [rep.varname_set rep.listZ_mem rep.Z] in *.
          match goal with H : _ |- _ =>
                          rewrite varname_set_local in H end.
          match goal with H : PropSet.disjoint _ _ |- _ =>
                          apply disjoint_singleton_r_iff in H;
                            eauto using string_dec;
                            cbv [PropSet.of_list] in H
          end.
          cbn [rep.equiv rep.listZ_mem rep.Z].
          sepsimpl.
          apply dexpr_put_diff; [ | eassumption].
          intro; subst; tauto. }
        { apply sep_assoc.
          eapply Proper_sep_iff1;
            [ apply equiv_nil_iff1 | reflexivity | ].
          sepsimpl. eexists.
          apply sep_emp_l; split;
            [ solve [eauto using dexpr_put_same] | ].
          cbn [lists_reserved equivalent rep.equiv rep.listZ_mem rep.Z].
          sepsimpl. eexists.
          sepsimpl; eauto.
          eexists; sepsimpl; [ | ecancel_assumption ].
          cbn [WeakestPrecondition.dexpr
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body].
          apply get_put_same.
          cbn [Semantics.interp_binop].
          cbv [WeakestPrecondition.literal dlet.dlet].
          rewrite <-word.ring_morph_add.
          f_equal; lia. } }
      cbv beta in *. cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_sym, only_differ_put. }
  Qed.
End LoadStoreList.
