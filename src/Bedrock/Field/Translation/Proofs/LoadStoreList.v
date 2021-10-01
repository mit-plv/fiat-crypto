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
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Translation.Proofs.EquivalenceProperties.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Flatten.
Require Import Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Translation.Flatten.
Require Import Crypto.Bedrock.Field.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Import ListNotations.

Import AbstractInterpretation.Compilers.
Import API.Compilers.
Import Types.Notations.

Section LoadStoreList.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.

  Local Existing Instance rep.Z.

  (* states that access sizes are within machine integer width *)
  Fixpoint base_access_sizes_good {t}
    : base_access_sizes (listZ:=rep.listZ_mem) t -> Prop :=
    match t with
    | base.type.prod a b =>
      fun s => base_access_sizes_good (fst s)
               /\ base_access_sizes_good (snd s)
    | base_listZ =>
      fun s =>
        (Z.of_nat (Memory.bytes_per
                     (width:=width) s) * 8 <= width)%Z
    | _ => fun _ => True
    end.
  Definition access_sizes_good {t}
    : access_sizes (listZ:=rep.listZ_mem) t -> Prop :=
    match t with
    | type.base _ => base_access_sizes_good
    | _ => fun _ => True
    end.
  Fixpoint access_sizes_good_args {t}
    : type.for_each_lhs_of_arrow
        (access_sizes (listZ:=rep.listZ_mem)) t -> Prop :=
    match t with
    | type.base _ => fun _ : unit => True
    | type.arrow _ _ =>
      fun s => access_sizes_good (fst s) /\ access_sizes_good_args (snd s)
    end.

  Lemma access_sizes_good_in_range size :
    base_access_sizes_good (t:=base_listZ) size ->
    (2 ^ (Z.of_nat (Memory.bytes_per
                      (width:=width) size) * 8)
     <= 2 ^ width)%Z.
  Proof.
    cbv [base_access_sizes_good]; intros.
    apply Z.pow_le_mono_r; lia.
  Qed.

  (* states that each list Z is within its access size *)
  Fixpoint within_base_access_sizes {t}
    : base.interp t ->
      base_access_sizes (listZ:=rep.listZ_mem) t -> Prop :=
      match t with
      | base.type.prod a b =>
        fun x s =>
          within_base_access_sizes (fst x) (fst s) /\
          within_base_access_sizes (snd x) (snd s)
      | base_listZ =>
        fun x s =>
          let bytes :=
              Z.of_nat (Memory.bytes_per (width:=width) s) in
          Forall (fun z => 0 <= z < 2 ^ (bytes * 8))%Z x
      | _ => fun _ _ => True
      end.

  Fixpoint within_access_sizes_args {t}
    : type.for_each_lhs_of_arrow API.interp_type t ->
      type.for_each_lhs_of_arrow
        (access_sizes (listZ:=rep.listZ_mem)) t -> Prop :=
    match t with
    | type.base _ => fun _ _ => True
    | type.arrow (type.base s) _ =>
      fun x s =>
        within_base_access_sizes (fst x) (fst s) /\
        within_access_sizes_args (snd x) (snd s)
    | _ => fun _ _ => False
    end.

  (* separation-logic relation that says space exists in memory for lists
     (other values are ignored) *)
  Fixpoint lists_reserved {t}
    : base_listonly nat t ->
      base_rtype (listZ:=rep.listZ_mem) t ->
      base_access_sizes (listZ:=rep.listZ_mem) t ->
      locals ->
      mem ->
      Prop :=
    match t as t0 return
          base_listonly nat t0 -> base_rtype t0 ->
          base_access_sizes (listZ:=rep.listZ_mem) t0 -> _ with
    | base.type.prod a b =>
      fun x y s locals =>
        sep (lists_reserved (fst x) (fst y) (fst s) locals)
            (lists_reserved (snd x) (snd y) (snd s) locals)
    | base_listZ =>
      fun n loc sz locals =>
        (Lift1Prop.ex1
           (fun oldvalues : list Z =>
              sep (emp (length oldvalues = n))
                  (rep.equiv (rep:=rep.listZ_mem)
                              oldvalues loc sz locals)))
    | base_Z => fun _ _ _ _ => emp True
    |  _ => fun _ _ _ _ => emp False
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
             (retsizes : base_access_sizes (type.final_codomain t))
             (flat_args : list word)
    : mem -> Prop :=
    let outptrs :=
        flatten_listonly_base_ltype (fst (extract_listnames retnames)) in
    match map.of_list_zip
            (outptrs ++ (flatten_argnames argnames))
            flat_args with
    | Some init_locals =>
      lists_reserved
        lengths (base_rtype_of_ltype retnames) retsizes init_locals
    | None => emp True
    end.

  Lemma lists_reserved_0 {listZ:rep.rep base_listZ} start sizes :
    forall (locals:locals),
    Lift1Prop.iff1
      (lists_reserved (t:=base_listZ) 0%nat start sizes locals)
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
             | H : rep.equiv _ _ _ _ _ |- _ => apply equiv_nil_iff1 in H
             | |- Lift1Prop.ex1 _ _ => eexists
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- rep.equiv [] _ _ _ _ => apply equiv_nil_iff1
             | _ => solve [eauto using List.length_nil]
             | _ => eexists; split; solve [eauto]
             end.
  Qed.

  Lemma lists_reserved_only_differ_undef t :
    forall lengths locs s locals locals' vset,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      Lift1Prop.impl1
        (lists_reserved (t:=t) lengths locs s locals)
        (lists_reserved lengths locs s locals').
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
           (locals : locals)
           (sizes : base_access_sizes t)
           (R : mem -> Prop),
    Lift1Prop.iff1
      (sep (equivalent_base x (base_rtype_of_ltype names) sizes locals) R)
      (sep (equivalent_listexcl
              x (map_listexcl (fun t => base_rtype_of_ltype (listZ:=rep.listZ_mem)(t:=t))
                              (snd (extract_listnames names))) sizes locals)
           (sep (equivalent_listonly
                   x (map_listonly
                        (base_rtype_of_ltype)
                        (fst (extract_listnames names))) sizes locals) R)).
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
        (size : access_size)
        (name : base_ltype (listZ:=rep.listZ_mem) base_listZ)
        i l :
    forall mem locals R,
      (i < length l)%nat ->
      base_access_sizes_good (t:=base_listZ) size ->
      sep (rep.equiv (t:=base_listZ)
                     l (base_rtype_of_ltype name) size locals) R mem ->
      WeakestPrecondition.dexpr
        mem locals
        (load_list_item (width:=width) size (expr.var name) i)
        (word.of_Z (hd 0%Z (skipn i l))).
  Proof.
    cbv [load_list_item];
      cbn [rep.equiv rep.listZ_mem rep.Z base_rtype_of_ltype
                     rep.rtype_of_ltype rep.listZ_mem ]; intros.
    cbn [WeakestPrecondition.dexpr
           WeakestPrecondition.expr WeakestPrecondition.expr_body] in *.
    sepsimpl; subst.
    match goal with
    | H : context[array] |- _ =>
      eapply Proper_sep_iff1 in H;
        [ | symmetry; apply array_index_nat_inbounds
                        with (n:=i) (default:=0%Z);
            rewrite !map_length in *; lia
          | reflexivity]
    end.
    match goal with
    | H : context[array] |- _ =>
      rewrite !word.ring_morph_mul, !word.of_Z_unsigned in H;
        rewrite <-!word.ring_morph_mul in H
    end.
    straightline.
    eapply Proper_get; [ repeat intro |  eassumption ].
    match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                    apply word.unsigned_inj in H
    end.
    subst. rewrite Nat2Z.inj_mul.
    eexists; split.
    { cbv [Memory.load].
      erewrite load_Z_of_sep; [ reflexivity | ].
      ecancel_assumption. }
    { unfold truncate_Z.
      rewrite Z.land_ones by auto with zarith.
      rewrite Z.mod_small; [ reflexivity | ].
      rewrite <-hd_skipn_nth_default.
      match goal with H : base_access_sizes_good _ |- _ =>
                      apply access_sizes_good_in_range in H end.
      apply Forall_nth_default; auto with zarith. }
  Qed.

  Lemma load_list_correct rem l :
    forall (i nextn : nat)
           (name : base_ltype (listZ:=rep.listZ_mem) base_listZ)
           tr
           (sizes : base_access_sizes
                      (listZ:=rep.listZ_mem) base_listZ)
           (locals : locals)
           (mem : mem)
           (functions : list _)
           (R : _ -> Prop),
      (forall (n : nat) (H : nextn <= n), name <> varname_gen n) ->
      base_access_sizes_good sizes ->
      length l = i + rem ->
      sep (rep.equiv (t:=base_listZ)
                     l (base_rtype_of_ltype name) sizes locals) R mem ->
      (* load_list returns # vars used, variable names, cmd *)
      let out := load_list (width:=width) (varname_gen:=varname_gen) sizes (expr.var name) i rem nextn in
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
             locals (used_varnames (varname_gen:=varname_gen) nextn nvars) locals' /\
           (forall n,
               (nextn + nvars <= n)%nat ->
               ~ varname_set_base names' (varname_gen n)) /\
           locally_equivalent_base
             (t:=base_listZ) (skipn i l)
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
      { intros. cbv [empty_set]. tauto. }
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
          eauto using @only_differ_put with typeclass_instances.
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
        cbv [singleton_set].
        rewrite varname_gen_unique; lia. }
      { cbv [locally_equivalent] in *.
        cbn [map base_rtype_of_ltype
                 Compilers.base_interp
                 rep.rtype_of_ltype rep.listZ_local
                 equivalent rep.equiv ] in *.
        rewrite skipn_nth_default with (d:=0%Z) by lia.
        eapply Forall2_cons; eauto.
        eapply (equiv_Z_only_differ_iff1 (listZ:=rep.listZ_mem)); eauto.
        { eapply only_differ_sym; eassumption. }
        { eapply disjoint_used_varnames_singleton.
          lia. }
        { assert (2 ^ (Z.of_nat (Memory.bytes_per (width:=width) sizes) * 8)
                  <= 2 ^ width)%Z
            by (cbv [base_access_sizes_good] in *;
                apply Z.pow_le_mono_r; lia).
          cbn [rep.equiv rep.listZ_mem rep.Z] in *.
          sepsimpl_hyps.
          match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                          apply word.unsigned_inj in H
          end.
          subst. eexists.
          split;[reflexivity|].
          split.
          { rewrite <-word.unsigned_of_Z_0, map_nth_default_always.
            reflexivity. }
          { eexists; split; [ | reflexivity ].
            rewrite map.get_put_same, hd_skipn_nth_default.
            rewrite <-word.unsigned_of_Z_0.
            rewrite skipn_map, hd_map.
            rewrite !word.of_Z_unsigned.
            reflexivity. } } } }
  Qed.

  Lemma load_all_lists_correct {t} :
    forall (argnames : base_ltype t)
           (argsizes : base_access_sizes t)
           (args : base.interp t)
           (functions : list _)
           tr
           (locals : locals)
           (mem : mem)
           (nextn : nat)
           (R : _ -> Prop),
        (* lengths of any lists in the arguments *)
        let arglengths := list_lengths_from_value args in
        (* look up variables in argnames *)
        let argvalues := base_rtype_of_ltype argnames in
        (* argnames don't contain variables we could later overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            ~ varname_set_base argnames (varname_gen n)) ->
        (* argument sizes are <= integer width *)
        base_access_sizes_good argsizes ->
        (* argument values are equivalent *)
        sep (equivalent_base args argvalues argsizes locals) R mem ->
        (* load_all_lists returns triple : # fresh variables used,
           new argnames with local lists, and cmd *)
        let out := load_all_lists nextn argnames arglengths argsizes in
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
               locals (used_varnames (varname_gen:=varname_gen) nextn nvars) locals' /\
             (forall n,
                 (nextn + nvars <= n)%nat ->
                 ~ varname_set_base argnames' (varname_gen n)) /\
             locally_equivalent_base args argvalues' locals').
  Proof.
    (* TODO: lots of repeated steps in this proof; automate *)
    induction t;
      cbn [fst snd map load_all_lists varname_set
               locally_equivalent_base equivalent_base rep.equiv
               flatten_base_ltype equivalent_flat_base
               base_access_sizes_good
               base_rtype_of_ltype rep.varname_set rep.Z
          ]; break_match; intros; sepsimpl; [ | | ].
    { (* base_Z *)
      repeat straightline. cbv [emp].
      repeat match goal with
               | |- Lift1Prop.ex1 _ _ => eexists
               | |- _ /\ _ => split end;
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
          { use_sep_assumption; cancel.
            cancel_seps_at_indices 0%nat 0%nat; trivial.
            ecancel_done. } }
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
                eauto using equiv_listZ_only_differ_mem, @only_differ_sym with typeclass_instances.
              eapply disjoint_used_varnames_lt.
              match goal with
              | H : _ |- _ =>
                setoid_rewrite not_union_iff in H;
                  apply H; eauto
              end. }
            use_sep_assumption; cancel.
            cancel_seps_at_indices 1%nat 0%nat; trivial.
            ecancel_done. } }
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
          eauto using equiv_listZ_only_differ_local, @only_differ_sym with typeclass_instances.
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
           (argsizes : type.for_each_lhs_of_arrow access_sizes t)
           (args : type.for_each_lhs_of_arrow API.interp_type t)
           (functions : list _)
           tr
           (locals : locals)
           (mem : mem)
           (nextn : nat),
        (* lengths of any lists in the arguments *)
        let arglengths := list_lengths_from_args args in
        (* look up variables in argnames *)
        let argvalues :=
            type.map_for_each_lhs_of_arrow rtype_of_ltype argnames in
        (* argnames don't contain variables we could later overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            ~ varname_set_args argnames (varname_gen n)) ->
        (* argument sizes are <= width *)
        access_sizes_good_args argsizes ->
        (* argument values are equivalent *)
        equivalent_args args argvalues argsizes locals mem ->
        (* load_arguments returns triple : # fresh variables used,
           new argnames with local lists, and cmd *)
        let out := load_arguments nextn argnames arglengths argsizes in
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
               locals (used_varnames (varname_gen:=varname_gen) nextn nvars) locals' /\
             (forall n,
                 (nextn + nvars <= n)%nat ->
                 ~ varname_set_args argnames' (varname_gen n)) /\
             locally_equivalent_args args argvalues' locals').
  Proof.
    cbv zeta.
    induction t;
      destruct argnames;
      cbn [fst snd load_arguments access_sizes_good_args
               list_lengths_from_args varname_set_args
               type.for_each_lhs_of_arrow equivalent_args
               type.map_for_each_lhs_of_arrow flatten_args
               ]; break_match; cbn [fst snd]; intros.
    { (* base type *)
      repeat straightline.
      repeat match goal with
             | |- _ /\ _ => split end;
        eauto using only_differ_zero; reflexivity. }
    { (* arrow (base _) _ *)
      cleanup. straightline.
      eapply Proper_cmd.
      3:{
        eapply load_all_lists_correct; eauto; [ ].
        intros.
        match goal with
        | H : _ |- _ =>
          setoid_rewrite not_union_iff in H;
            apply H; eauto
        end. }
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
        { eapply equivalent_args_only_differ;
            eauto using only_differ_sym with equiv; [ ].
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
            split; [ | solve [eauto] ].
            exists (emp True). sepsimpl; eauto.
            eapply equivalent_only_differ;
              eauto using only_differ_sym with equiv; [ ].
            eapply disjoint_used_varnames_lt.
            intros; cleanup. subst.
            eauto with lia. } } } }
    { (* arrow (arrow _ _) _ *)
      sepsimpl. }
  Qed.

  Lemma store_list_correct :
    forall (size : access_size)
           (start : string)
           (functions : list _)
           (value_names2 value_names1 : list string)
           (rets1 rets2 rets : base.interp base_listZ)
           (i : nat)
           tr
           (locals : locals)
           (m : mem)
           (R : _ -> Prop),
      let retlengths :=
          list_lengths_from_value (t:=base_listZ) rets2 in
      let loc := expr.var start in
      let nbytes := Memory.bytes_per (width:=width) size in
      let offset := expr.literal (Z.of_nat (nbytes * i)) in
      let loc' := expr.op bopname.add loc offset in
      let values1 := map expr.var value_names1 in
      let values2 := map expr.var value_names2 in
      rets = rets1 ++ rets2 ->
      length rets1 = length value_names1 ->
      length rets2 = length value_names2 ->
      length value_names1 = i ->
      (* bounds are OK *)
      Forall (fun x =>
                0 <= x < 2 ^ (Z.of_nat nbytes * 8))%Z rets2 ->
      (* yet-to-be-stored values *)
      locally_equivalent_base
        (listZ:=rep.listZ_local) rets2 values2 locals ->
      base_access_sizes_good (t:=base_listZ) size ->
      (* already-stored values *)
      sep (map:=mem)
          (sep (map:=mem)
               (rep.equiv (rep:=rep.listZ_mem)
                          rets1 (expr.var start) size locals)
               (lists_reserved retlengths loc' size locals)) R m ->
      WeakestPrecondition.cmd
        (WeakestPrecondition.call functions)
        (store_list (width:=width) size (expr.var start) values2 i) tr m locals
        (fun tr' mem' locals' =>
           tr = tr' /\
           locals = locals' /\
           sep (map:=mem)
               (rep.equiv (rep:=rep.listZ_mem)
                          rets (expr.var start) size locals') R mem').
  Proof.
    cbv zeta.
    induction value_names2 as [|n0 ?]; destruct rets2 as [|r0 rets2];
      cbn [store_list Datatypes.length base_access_sizes_good
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
      lazymatch goal with
        H : WeakestPrecondition.dexpr _ _ (expr.op _ _ _) ?v |- _ =>
          cbn [WeakestPrecondition.dexpr
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body
                 Semantics.interp_binop] in H;
          cbv [dlet.dlet WeakestPrecondition.literal
                         WeakestPrecondition.get] in H;
          rewrite ?word.of_Z_unsigned in H;
          cleanup; subst
      end.
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
      repeat match goal with
             | H: word.unsigned _ = word.unsigned _ |- _ =>
               apply word.unsigned_inj in H; subst
             end.
      repeat match goal with
             | H : map word.unsigned ?x = _ :: _ |- _ =>
               destruct x; cbn [map] in H;
                 [ congruence | inversion H; clear H ]
             end.
      cbn [map array] in *.
      eapply store_Z_of_sep; [ ecancel_assumption | ].
      intros. sepsimpl.
      repeat match goal with
             | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
             end.

      eapply Proper_cmd; [ solve [apply Proper_call] | repeat intro | ].
      2:{
        let s :=
            lazymatch goal with
              H : map.get locals0 start = Some ?x |- _ => x end in
        let H := lazymatch goal with
                 | H : sep _ _ ?m |- context [?m] => H end in
        let r1 :=
            lazymatch type of H with
                context [array _ _ s ?xs] => xs end in
        let r2 :=
            lazymatch type of H with
                context [array _ _ (word.add _ _) ?xs] => xs end in
        let r :=
            lazymatch type of H with
              context [truncated_scalar _ _ ?x] => x end in
        apply IHvalue_names2 with
            (rets1:= r1 ++ [r])
            (rets2:=rets2) (R:=R)
            (value_names1:=value_names1 ++ [n0]);
        rewrite ?app_length; cbn [length]; eauto; try lia; [ ].
        { intros.
          (* look at goal and plug in evars very carefully *)
          sepsimpl.
          match goal with H: ?P (expr.var start) ?x |- _ =>
                          exists x end.
          sepsimpl; [ solve [eauto using Forall_snoc] .. | ].
          match goal with
            |- context [map word.unsigned _ =
                        map word.unsigned ?xs ++ [word.unsigned ?x] ] =>
            exists (xs ++ [x])
          end.
          sepsimpl; [ rewrite map_app; reflexivity
                    | solve [eauto using Forall_snoc] | ].
          eexists; sepsimpl; [ reflexivity | solve [eauto] | ].
          match goal with
            H : sep _ _ ?m |- context [?m] =>
            match type of H with
              context [array _ _ (word.add ?a ?b) ?x] =>
              exists x;
                sepsimpl; [solve [auto] .. | ];
                  exists (word.add a b)
            end
          end.
          sepsimpl; [ ].
          eexists; sepsimpl; [ reflexivity | solve [eauto] | ].
          eexists; sepsimpl; [ reflexivity | | ].
          { eexists; split; [ eassumption | ].
            cbn [WeakestPrecondition.dexpr
                   WeakestPrecondition.expr
                   WeakestPrecondition.expr_body
                   Semantics.interp_binop].
            cbv [WeakestPrecondition.literal dlet.dlet].
            match goal with
            | |- context[word.add ?x (word.of_Z ?y)] =>
              progress match x with
                       | word.of_Z _ => idtac
                       | word.add _ _ => idtac
                       | _ => rewrite <-(word.of_Z_unsigned x)
                       end
            end.
            rewrite <-!word.ring_morph_add.
            f_equal. clear; lia. }
          { match goal with
              H : context [array _ _ (word.add (word.add _ _) _) _] |- _ =>
              refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
            end.
            rewrite map_app, array_append. cbn [map array].
            cbn [Compilers.base_interp] in *. (* simplifies implicit types *)
            match goal with
            | |- Lift1Prop.iff1 ?L ?R =>
              let la := match L with
                          context [truncated_scalar _ ?la] => la end in
              let ra := match R with
                          context [truncated_scalar _ ?ra] => ra end in
              replace ra with la
                by (apply word.unsigned_inj;
                    rewrite !word.unsigned_add, !word.unsigned_of_Z;
                    cbv [word.wrap]; Modulo.pull_Zmod; f_equal; lia)
            end.
            cancel. } } }
      cbv beta in *; cleanup; subst.
      repeat match goal with |- _ /\ _ => split end;
        eauto.
      rewrite app_cons_app_app.
      eassumption. }
  Qed.

  Lemma store_return_values_correct {t} init_locals :
    forall (retnames_local : base_ltype t)
           (retnames_mem : base_ltype t)
           (retsizes : base_access_sizes t)
           (vset : set string)
           (rets : base.interp t)
           (functions : list _)
           tr
           (locals : locals)
           (mem : mem)
           (R : _ -> Prop),
      let out := store_return_values retnames_local retnames_mem retsizes in
      let retlengths := list_lengths_from_value rets in
      sep (lists_reserved retlengths
                          (base_rtype_of_ltype retnames_mem)
                          retsizes init_locals) R mem ->
      map.undef_on
        init_locals
        (union vset (varname_set_listexcl retnames_mem)) ->
      map.only_differ init_locals vset locals ->
      (* rets are stored in local retnames *)
      locally_equivalent_base
        rets (base_rtype_of_ltype retnames_local) locals ->
      (* retnames are disjoint *)
      disjoint (varname_set_base retnames_local)
               (varname_set_base retnames_mem) ->
      (* retnames don't contain duplicates *)
      NoDup (flatten_base_ltype retnames_mem) ->
      (* rets bounds obey access sizes *)
      within_base_access_sizes rets retsizes ->
      (* access sizes not larger than integer width *)
      base_access_sizes_good retsizes ->
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
                  rets (base_rtype_of_ltype retnames_mem) retsizes locals')
               R mem').
  Proof.
    cbv zeta.
    induction t;
      cbn [fst snd store_return_values lists_reserved
               locally_equivalent_base equivalent_base
               varname_set_base varname_set_listexcl
               base_rtype_of_ltype rep.rtype_of_ltype
               rep.equiv rep.varname_set rep.Z
               base_access_sizes_good within_base_access_sizes
               flatten_base_ltype list_lengths_from_value
          ]; break_match; intros; sepsimpl; [ | | ].
    { (* base_Z *)
      repeat straightline.
      eexists; split; [eassumption|].
      cbv [dlet.dlet]; split; [reflexivity|].
      split; [reflexivity|].
      split;
        [ solve [eauto using @only_differ_sym, @only_differ_put with typeclass_instances] | ].
      sepsimpl. eexists; sepsimpl; try eassumption; [ ].
      cbv [WeakestPrecondition.dexpr
             WeakestPrecondition.expr
             WeakestPrecondition.expr_body
             WeakestPrecondition.get] in *.
      cleanup; subst.
      rewrite map.get_put_same.
      eexists; split; reflexivity. }
    { (* prod *)
      repeat straightline.
      match goal with H : _ |- _ =>
                      pose proof H;
                      apply NoDup_app_iff in H; cleanup end.
      repeat match goal with
             | _ => progress cleanup
             | H : disjoint (union _ _) _ |- _ =>
               apply disjoint_union_l_iff in H
             | H : disjoint _ (union _ _) |- _ =>
               apply disjoint_union_r_iff in H
             | H : map.undef_on _ (union _ _) |- _ =>
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
              (vset:=union vset (varname_set_listexcl (fst retnames_mem)));
          try ecancel_assumption; eauto.
          { apply undef_on_union_iff; split; eauto.
            apply undef_on_union_iff; split; eauto. }
          { rewrite union_comm.
            eapply only_differ_trans; eauto. }
          { cbv [locally_equivalent].
            eapply equivalent_only_differ; eauto with equiv.
            apply disjoint_sym.
            eapply subset_disjoint_r;
              eauto using varname_set_listexcl_subset. } }
      cbv beta in *. cleanup; subst.
      repeat match goal with H : list_lengths_from_value _ = _ |- _ =>
                             rewrite H end.
      repeat match goal with |- _ /\ _ => split end;
        eauto 10 using @only_differ_sym, @only_differ_trans with typeclass_instances.
      use_sep_assumption. cancel.
      (* TODO: why doesn't cancel handle the below? *)
      cancel_seps_at_indices 0 1; [ reflexivity | ].
      eapply equivalent_only_differ_iff1; eauto with equiv.
      eapply disjoint_sym.
      eapply subset_disjoint_r;
        eauto using varname_set_listexcl_subset; [ ].
      rewrite !varname_set_flatten.
      eapply NoDup_disjoint; eauto using string_dec. }
    { (* base_listZ *)
      repeat straightline.
      repeat match goal with p := _ |- _ => subst p end.
      repeat match goal with
             | H : map.undef_on _ (union _ _) |- _ =>
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
          apply sep_ex1_l.
          eexists; sepsimpl;
            [ | eapply expr_only_differ_undef; solve [eauto] | ];
            [ reflexivity | ].
          cbn [lists_reserved equivalent rep.equiv rep.listZ_mem rep.Z].
          sepsimpl. eexists.
          sepsimpl; eauto.
          eexists; sepsimpl; try ecancel_assumption; eauto.
          cbn [WeakestPrecondition.dexpr
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body] in *.
          eexists; sepsimpl; try eassumption; [ ].
          eexists; sepsimpl; try eassumption; [ ].
          eapply WP_get_only_differ_undef; eauto.
          eapply Proper_get; [ repeat intro | eassumption ].
          cbn [Semantics.interp_binop].
          cbv [WeakestPrecondition.literal dlet.dlet].
          subst.
          apply word.unsigned_inj.
          rewrite word.unsigned_add, word.unsigned_of_Z.
          rewrite Nat2Z.inj_mul. change (Z.of_nat 0) with 0%Z.
          autorewrite with zsimplify_fast.
          cbv [word.wrap]. rewrite word.wrap_unsigned.
          reflexivity. } }
      cbv beta in *. cleanup; subst.
      cbn [rep.rtype_of_ltype rep.listZ_local rep.Z] in *.
      match goal with
      | H : rep.equiv ?x ?y _ _ _ |- _ =>
        assert  (length x = length y)
        by (eapply Forall.eq_length_Forall2; apply H)
      end.
      rewrite !map_length in *.
      intuition trivial.
      eapply only_differ_sym, only_differ_empty. }
  Qed.
End LoadStoreList.
