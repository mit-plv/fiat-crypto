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

  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  (* separation-logic relation that says space exists in memory for lists
     (other values are ignored) *)
  Fixpoint lists_reserved {t}
    : base_listonly nat t ->
      base_rtype (listZ:=rep.listZ_mem) t ->
      Semantics.locals ->
      Semantics.mem ->
      Prop :=
    match t as t0 return
          base_listonly nat t0 -> base_rtype t0 -> _ with
    | base.type.prod a b =>
      fun x y locals => sep (lists_reserved (fst x) (fst y) locals)
                            (lists_reserved (snd x) (snd y) locals)
    | base_listZ =>
      fun n loc locals =>
        (Lift1Prop.ex1
           (fun oldvalues : list Z =>
              sep (emp (length oldvalues = n))
                  (rep.equiv (rep:=rep.listZ_mem)
                              oldvalues loc locals)))
    | base_Z => fun _ _ _ => emp True
    |  _ => fun _ _ _ => emp False
    end.

  Fixpoint list_lengths_from_value {t}
    : base.interp t -> base_listonly nat t :=
    match t as t0 return base.interp t0 -> base_listonly nat t0 with
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

  Definition lists_reserved_with_initial_context {t}
             (lengths : base_listonly nat (type.final_codomain t))
             (argnames : type.for_each_lhs_of_arrow
                           (ltype (listZ:=rep.listZ_mem)) t)
             (retnames : base_ltype (type.final_codomain t))
             (flat_args : list Semantics.word)
    : Semantics.mem -> Prop :=
    let outptrs :=
        flatten_listonly_base_ltype (fst (extract_listnames retnames)) in
    match map.of_list_zip
            ((flatten_argnames argnames) ++ outptrs)
            flat_args with
    | Some init_locals =>
      lists_reserved lengths (base_rtype_of_ltype retnames) init_locals
    | None => emp True
    end.

  Lemma lists_reserved_0 {listZ:rep.rep base_listZ} start locals:
    Lift1Prop.iff1
      (lists_reserved (t:=base_listZ) 0%nat start locals)
      (emp (exists x, locally_equivalent_base (t:=base_Z) x start locals)).
  Proof.
    cbv [lists_reserved].
    split; intros;
      repeat match goal with
             | _ => progress (sepsimpl; subst)
             | _ => progress cbn [locally_equivalent_base
                                    equivalent_base rep.equiv rep.Z] in *
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
      eapply equiv_listZ_only_differ_undef_mem; eauto. }
  Qed.

  Lemma equivalent_extract_listnames {t} :
    forall (x : base.interp t)
           (names : base_ltype t)
           (locals : Semantics.locals)
           (R : Semantics.mem -> Prop),
    Lift1Prop.iff1
      (sep (equivalent_base x (base_rtype_of_ltype names) locals) R)
      (sep (equivalent_listexcl
              x (map_listexcl (@base_rtype_of_ltype _ rep.listZ_mem)
                              (snd (extract_listnames names))) locals)
           (sep (equivalent_listonly
                   x (map_listonly
                        (base_rtype_of_ltype)
                        (fst (extract_listnames names))) locals) R)).
  Proof.
    induction t;
      cbn [fst snd equivalent_base extract_listnames
               base_rtype_of_ltype rep.rtype_of_ltype
               equivalent_listexcl map_listexcl
               equivalent_listonly map_listonly];
      break_match; intros;
        try match goal with
              |- context [emp False] =>
              split; intros; sepsimpl
            end; [ solve [cancel] | | ].
    { rewrite sep_assoc. (* needed for rewrites for some reason *)
      rewrite IHt1. rewrite IHt2.
      rewrite !sep_assoc.
      cancel.
      (* TODO : this should go by associativity/commutativity; is there a better
      way than manually selecting indices? *)
      cancel_seps_at_indices 0 0; [ reflexivity | ].
      cancel_seps_at_indices 0 1; [ reflexivity | ].
      cancel_seps_at_indices 0 0; [ reflexivity | ].
      reflexivity. }
    { cancel. reflexivity. }
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
               ~ varname_set_base names' (varname_gen n)) /\
           locally_equivalent_base
             (t:=base_listZ)
             (skipn i l)
             (base_rtype_of_ltype names') locals').
  Proof.
    induction rem; cbn [fst snd load_list]; intros.
    { straightline.
      cbv [locally_equivalent_base].
      cbn [rep.Z rep.listZ_local fold_right map
                 equivalent_base rep.equiv
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
      { cbn [varname_set_base
               rep.varname_set rep.listZ_local rep.Z fold_right] in *.
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
          split.
          { cbn [rep.equiv rep.listZ_mem rep.Z] in *.
            sepsimpl_hyps.
            eapply Forall_nth_default; eauto; lia. }
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
            ~ varname_set_base argnames (varname_gen n)) ->
        (* argument values are equivalent *)
        sep (equivalent_base args argvalues locals) R mem ->
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
                 ~ varname_set_base argnames' (varname_gen n)) /\
             locally_equivalent_base args argvalues' locals').
  Proof.
    (* TODO: lots of repeated steps in this proof; automate *)
    induction t;      cbn [fst snd map load_all_lists varname_set
               locally_equivalent_base equivalent_base rep.equiv
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
      let loc := expr.var start in
      let offset := (Z.of_nat i * word_size_in_bytes)%Z in
      let loc' := expr.op bopname.add loc (expr.literal offset) in
      let values1 := map expr.var value_names1 in
      let values2 := map expr.var value_names2 in
      rets = rets1 ++ rets2 ->
      length rets1 = length value_names1 ->
      length rets2 = length value_names2 ->
      length value_names1 = i ->
      (* yet-to-be-stored values *)
      locally_equivalent_base
        (listZ:=rep.listZ_local) rets2 values2 locals ->
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
      cbn [store_list Datatypes.length
                      locally_equivalent_base equivalent_base
                      rep.equiv rep.listZ_local rep.Z rep.listZ_mem];
      intros; subst; try lia; sepsimpl.
    { repeat split; try reflexivity.
      repeat match goal with
             | _ => progress sepsimpl
             | H : _ |- _ =>
               rewrite List.firstn_all, List.skipn_all_exact in H
             | _ => rewrite app_nil_r
             | |- Lift1Prop.ex1 _ _ => eexists
             | |- _ /\ _ => split
             | _ => eassumption
             end.
      match goal with
        H : sep _ _ _ |- _ =>
        eapply Proper_sep_iff1 in H;
          [ | rewrite ?(lists_reserved_0 (listZ:=rep.listZ_local));
              reflexivity .. ]
      end.
      sepsimpl.
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
      cleanup.
      match goal with
      | H1 : (WeakestPrecondition.dexpr _ ?l (expr.var ?x) ?v1),
             H2 : (map.get ?l ?x = Some ?v2) |- _ =>
        replace v2 with v1 in *
          by (cbn [WeakestPrecondition.dexpr
                     WeakestPrecondition.expr
                     WeakestPrecondition.expr_body] in H1;
              cbv [WeakestPrecondition.get] in H1;
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
          sepsimpl; [ solve [eauto using Forall_snoc] .. | ].
          match goal with
            H : context [array _ _ (word.add _ _) (map _ ?x)] |- _ =>
            exists x end.
          sepsimpl; auto.
          match goal with H : Forall _ (_ :: _) |- _ =>
                          inversion H; subst; clear H end.
          match goal with
            H : context [array _ _ (word.add ?a ?b) (map _ ?x)] |- _ =>
            exists (word.unsigned (word.add a b)) end.
          sepsimpl; auto;
            rewrite <-?word.ring_morph_add, ?word.of_Z_unsigned;
            try solve [apply word.unsigned_range; auto]; [ | ].
          { eexists; split; [ eassumption | ].
            cbn [WeakestPrecondition.dexpr
                   WeakestPrecondition.expr
                   WeakestPrecondition.expr_body
                   Semantics.interp_binop].
            cbv [WeakestPrecondition.literal dlet.dlet].
            rewrite <-!word.ring_morph_add.
            f_equal. clear; lia. }
          match goal with
            H : context [array _ _ (word.add (word.add _ _) _) _] |- _ =>
            refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
          end.
          rewrite map_app, array_append. cbn [map array].
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

  Lemma store_return_values_correct {t} init_locals :
    forall (retnames_local : base_ltype t)
           (retnames_mem : base_ltype t)
           (vset : PropSet.set string)
           (rets : base.interp t)
           (functions : list _)
           (tr : Semantics.trace)
           (locals : Semantics.locals)
           (mem : Semantics.mem)
           (R : Semantics.mem -> Prop),
      let out := store_return_values retnames_local retnames_mem in
      let retlengths := list_lengths_from_value rets in
      sep (lists_reserved retlengths
                          (base_rtype_of_ltype retnames_mem)
                          init_locals) R mem ->
      map.undef_on
        init_locals
        (PropSet.union vset
                       (varname_set_listexcl retnames_mem)) ->
      map.only_differ init_locals vset locals ->
      (* rets are stored in local retnames *)
      locally_equivalent_base
        rets (base_rtype_of_ltype retnames_local) locals ->
      (* retnames are disjoint *)
      PropSet.disjoint (varname_set_base retnames_local)
                       (varname_set_base retnames_mem) ->
      (* retnames don't contain duplicates *)
      NoDup (flatten_base_ltype retnames_mem) ->
      (* translated function produces equivalent results *)
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (snd out)
        tr mem locals
        (fun tr' mem' locals' =>
           tr = tr' /\
           retlengths = fst out /\
           map.only_differ
             locals (varname_set_listexcl retnames_mem) locals' /\
           sep (equivalent_base
                  rets (base_rtype_of_ltype retnames_mem) locals')
               R mem').
  Proof.
    cbv zeta.
    induction t;
      cbn [fst snd store_return_values lists_reserved
               locally_equivalent_base equivalent_base
               varname_set_base varname_set_listexcl
               base_rtype_of_ltype rep.rtype_of_ltype
               rep.equiv rep.varname_set rep.Z
               flatten_base_ltype list_lengths_from_value
          ]; break_match; intros; sepsimpl; [ | | ].
    { (* base_Z *)
      repeat straightline.
      eexists; split; [eassumption|].
      cbv [dlet.dlet]; split; [reflexivity|].
      split; [reflexivity|].
      split;
        [ solve [eauto using only_differ_sym, only_differ_put] | ].
      apply sep_emp_l. split; [|assumption].
      cbv [WeakestPrecondition.dexpr
             WeakestPrecondition.expr
             WeakestPrecondition.expr_body
             WeakestPrecondition.get] in *.
      cleanup; subst.
      split; [ lia | ].
      eexists.
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
      2:{ eapply IHt2 with
              (vset:=PropSet.union
                       vset (varname_set_listexcl (fst retnames_mem)));
          try ecancel_assumption; eauto.
          { apply undef_on_union_iff; split; eauto.
            apply undef_on_union_iff; split; eauto. }
          { rewrite union_comm.
            eapply only_differ_trans; eauto. }
          { cbv [locally_equivalent].
            eapply equivalent_only_differ; eauto with equiv.
            eapply subset_disjoint';
              eauto using varname_set_listexcl_subset. } }
      cbv beta in *. cleanup; subst.
      repeat match goal with H : list_lengths_from_value _ = _ |- _ =>
                             rewrite H end.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_sym, only_differ_trans.
      use_sep_assumption. cancel.
      eapply equivalent_only_differ_iff1; eauto with equiv.
      eapply subset_disjoint';
        eauto using varname_set_listexcl_subset; [ ].
      rewrite !varname_set_flatten.
      eapply NoDup_disjoint; eauto using string_dec. }
    { (* base_listZ *)
      repeat straightline.
      repeat match goal with p := _ |- _ => subst p end.
      repeat match goal with
             | H : map.undef_on _ (PropSet.union _ _) |- _ =>
               apply undef_on_union_iff in H
             end.
      cbn [rep.Z rep.listZ_mem rep.equiv rep.rtype_of_ltype] in *.
      sepsimpl.
      eapply Proper_cmd;
        [ solve [apply Proper_call] | repeat intro | ].
      2:{
        eapply store_list_correct with
            (rets:=rets) (rets1:=[]) (rets2:=rets)
            (value_names1:=nil); auto using List.length_nil; [ | ].
        { cbn [rep.equiv rep.rtype_of_ltype rep.listZ_local] in *.
          eapply Forall.eq_length_Forall2, Forall.Forall2_map_r_iff.
          eauto. }
        { apply sep_assoc.
          eapply Proper_sep_iff1;
            [ apply equiv_nil_iff1 | reflexivity | ].
          sepsimpl. eexists.
          apply sep_emp_l; split; [ split | ];
            [ | eapply expr_only_differ_undef; solve [eauto] | ];
            [ lia | ].
          cbn [lists_reserved equivalent rep.equiv rep.listZ_mem rep.Z].
          sepsimpl. eexists.
          sepsimpl; eauto.
          eexists; sepsimpl; try ecancel_assumption; eauto.
          cbn [WeakestPrecondition.dexpr
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body] in *.
          eapply WP_get_only_differ_undef; eauto.
          eapply Proper_get; [ repeat intro | eassumption ].
          cbn [Semantics.interp_binop].
          cbv [WeakestPrecondition.literal dlet.dlet].
          subst. rewrite <-word.ring_morph_add.
          f_equal; lia. } }
      cbv beta in *. cleanup; subst.
      match goal with
      | H : rep.equiv ?x ?y _ _ |- _ =>
        assert  (length x = length y) by
            (eapply Forall.eq_length_Forall2; apply H)
      end.
      cbn [rep.rtype_of_ltype rep.listZ_local rep.Z] in *.
      rewrite !map_length in *.
      repeat match goal with |- _ /\ _ => split end;
        eauto using only_differ_sym, only_differ_put,
        only_differ_empty. }
  Qed.
End LoadStoreList.
