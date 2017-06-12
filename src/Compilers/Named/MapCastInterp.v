Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.SmartMap.
Require Import Crypto.Compilers.Named.InterpSideConditions.
Require Import Crypto.Compilers.Named.InterpSideConditionsInterp.
Require Import Crypto.Compilers.Named.MapCast.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.RewriteHyp.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code).
  Local Notation pick_type t v := (SmartFlatTypeMap pick_typeb (t:=t) v).
  Context (cast_op : forall t tR (opc : op t tR) args_bs,
              op (pick_type _ args_bs) (pick_type _ (interp_op_bounds t tR opc args_bs)))
          {BoundsContext : Context Name interp_base_type_bounds}
          (BoundsContextOk : ContextOk BoundsContext)
          {interp_base_type : base_type_code -> Type}
          (interp_op : forall src dst,
              op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (interped_op_side_conditions : forall s d, op s d -> interp_flat_type interp_base_type s -> pointed_Prop)
          (cast_backb: forall t b, interp_base_type (pick_typeb t b) -> interp_base_type t).
  Let cast_back : forall t b, interp_flat_type interp_base_type (@pick_type t b) -> interp_flat_type interp_base_type t
    := fun t b => SmartFlatTypeMapUnInterp cast_backb.
  Context {Context : Context Name interp_base_type}
          (ContextOk : ContextOk Context)
          (inboundsb : forall t, interp_base_type_bounds t -> interp_base_type t -> Prop).
  Let inbounds : forall t, interp_flat_type interp_base_type_bounds t -> interp_flat_type interp_base_type t -> Prop
    := fun t => interp_flat_type_rel_pointwise inboundsb (t:=t).
  Context (interp_op_bounds_correct:
             forall t tR opc bs
                    (v : interp_flat_type interp_base_type t)
                    (H : inbounds t bs v)
                    (Hside : to_prop (interped_op_side_conditions _ _ opc v)),
               inbounds tR (interp_op_bounds t tR opc bs) (interp_op t tR opc v))
          (pull_cast_back:
             forall t tR opc bs
                    (v : interp_flat_type interp_base_type (pick_type t bs))
                    (H : inbounds t bs (cast_back t bs v))
                    (Hside : to_prop (interped_op_side_conditions _ _ opc (cast_back t bs v))),
               interp_op t tR opc (cast_back t bs v)
               =
               cast_back _ _ (interp_op _ _ (cast_op _ _ opc bs) v))
          (base_type_dec : DecidableRel (@eq base_type_code))
          (Name_dec : DecidableRel (@eq Name)).

  Local Notation mapf_cast := (@mapf_cast _ op Name _ interp_op_bounds pick_typeb cast_op BoundsContext).
  Local Notation map_cast := (@map_cast _ op Name _ interp_op_bounds pick_typeb cast_op BoundsContext).

  Local Ltac handle_options_step :=
    match goal with
    | _ => progress inversion_option
    | [ H : ?x = Some _ |- context[?x] ] => rewrite H
    | [ H : ?x = None |- context[?x] ] => rewrite H
    | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : Some _ <> None \/ _ |- _ ] => clear H
    | [ H : Some ?x <> Some ?y |- _ ] => assert (x <> y) by congruence; clear H
    | [ H : None <> Some _ |- _ ] => clear H
    | [ H : Some _ <> None |- _ ] => clear H
    | [ H : ?x <> ?x \/ _ |- _ ] => destruct H; [ exfalso; apply H; reflexivity | ]
    | [ H : _ \/ None = Some _ |- _ ] => destruct H; [ | exfalso; clear -H; congruence ]
    | [ H : _ \/ Some _ = None |- _ ] => destruct H; [ | exfalso; clear -H; congruence ]
    | [ H : ?x = Some ?y, H' : ?x = Some ?y' |- _ ]
      => assert (y = y') by congruence; (subst y' || subst y)
    | _ => progress simpl @option_map
    end.

  Local Ltac handle_lookupb_step :=
    let do_eq_dec dec t t' :=
        first [ constr_eq t t'; fail 1
              | lazymatch goal with
                | [ H : t = t' |- _ ] => fail 1
                | [ H : t <> t' |- _ ] => fail 1
                | [ H : t = t' -> False |- _ ] => fail 1
                | _ => destruct (dec t t')
                end ] in
    let do_type_dec := do_eq_dec base_type_dec in
    match goal with
    | _ => progress unfold dec in *
    | _ => handle_options_step
    (* preprocess *)
    | [ H : context[lookupb (extend _ _ _) _] |- _ ]
      => first [ rewrite (lookupb_extend base_type_dec Name_dec) in H by assumption
               | setoid_rewrite (lookupb_extend base_type_dec Name_dec) in H; [ | assumption.. ] ]
    | [ |- context[lookupb (extend _ _ _) _] ]
      => first [ rewrite (fun C => lookupb_extend C base_type_dec Name_dec) by assumption
               | setoid_rewrite (lookupb_extend base_type_dec Name_dec); [ | assumption.. ] ]
    | _ => progress subst
    (* handle multiple hypotheses *)
    | [ H : find_Name _ ?n ?N = Some ?t', H'' : context[find_Name_and_val _ _ ?t ?n ?N ?x ?default] |- _ ]
      => do_type_dec t t'
    (* clear the default value *)
    | [ H : context[find_Name_and_val ?tdec ?ndec ?t ?n (T:=?T) ?N ?V ?default] |- _ ]
      => lazymatch default with None => fail | _ => idtac end;
         rewrite find_Name_and_val_split in H
    (* generic handlers *)
    | [ H : find_Name _ ?n ?N = Some ?t', H' : ?t <> ?t', H'' : context[find_Name_and_val _ _ ?t ?n ?N ?x ?default] |- _ ]
      => erewrite find_Name_and_val_wrong_type in H'' by eassumption
    | [ H : context[find_Name _ _ (SmartFlatTypeMapInterp2 _ _ _)] |- _ ]
      => rewrite find_Name_SmartFlatTypeMapInterp2 with (base_type_code_dec:=base_type_dec) in H
    | [ H : find_Name_and_val _ _ _ _ _ _ _ = None |- _ ]
      => apply find_Name_and_val_None_iff in H
    (* destructers *)
    | [ |- context[find_Name_and_val ?tdec ?ndec ?t ?n ?N ?V ?default] ]
      => destruct (find_Name_and_val tdec ndec t n N V default) eqn:?
    | [ H : context[match find_Name_and_val ?tdec ?ndec ?t ?n ?N ?V ?default with _ => _ end] |- _ ]
      => destruct (find_Name_and_val tdec ndec t n N V default) eqn:?
    | [ H : context[match find_Name ?ndec ?n ?N with _ => _ end] |- _ ]
      => destruct (find_Name ndec n N) eqn:?
    | [ H : context[match base_type_dec ?x ?y with _ => _ end] |- _ ]
      => destruct (base_type_dec x y)
    | [ H : context[match Name_dec ?x ?y with _ => _ end] |- _ ]
      => destruct (Name_dec x y)
    end.

  Local Ltac handle_exists_in_goal :=
    lazymatch goal with
    | [ |- exists v, Some ?k = Some v /\ @?B v ]
      => exists k; split; [ reflexivity | ]
    | [ |- (exists v, None = Some v /\ @?B v) ]
      => exfalso
    | [ |- ?A /\ (exists v, Some ?k = Some v /\ @?B v) ]
      => cut (A /\ B k); [ clear; solve [ intuition eauto ] | cbv beta ]
    | [ |- ?A /\ (exists v, None = Some v /\ @?B v) ]
      => exfalso
    end.
  Local Ltac handle_bounds_side_conditions_step :=
    match goal with
    | [ H : interpf ?e = Some ?v, H' : interpf_side_conditions_gen _ _ _ ?e = Some (_, ?v')%core |- _ ]
      => first [ constr_eq v v'; fail 1
               | assert (Some v = Some v')
                 by (erewrite <- H, snd_interpf_side_conditions_gen_eq, H'; reflexivity);
                 inversion_option; (subst v || subst v') ]
    end.
  Local Ltac fin_inbounds_cast_back_t_step :=
    match goal with
    | [ |- inboundsb _ _ _ /\ _ ]
      => split; [ eapply interp_flat_type_rel_pointwise__find_Name_and_val; eassumption | ]
    | [ |- cast_backb _ _ _ = _ ]
      => eapply find_Name_and_val__SmartFlatTypeMapInterp2__SmartFlatTypeMapUnInterp__Some_Some; [ | eassumption.. ]
    end.
  Local Ltac specializer_t_step :=
    match goal with
    | [ H : ?T, H' : ?T |- _ ] => clear H
    | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
    | [ H : ?x = Some _, IH : forall a b, ?x = Some _ -> _ |- _ ]
      => specialize (IH _ _ H)
    | [ H : ?x = Some _, IH : forall a, ?x = Some _ -> _ |- _ ]
      => specialize (IH _ H)
    | [ H : forall t n v, lookupb ?ctx n = _ -> _, H' : lookupb ?ctx ?n' = _ |- _ ]
      => specialize (H _ _ _ H')
    | _ => progress specialize_by auto
    end.

  Local Ltac break_t_step :=
    first [ progress destruct_head'_ex
          | progress destruct_head'_and ].

  Local Ltac t_step :=
    first [ progress intros
          | break_t_step
          | handle_lookupb_step
          | handle_exists_in_goal
          | solve [ auto ]
          | specializer_t_step
          | fin_inbounds_cast_back_t_step
          | handle_options_step
          | handle_bounds_side_conditions_step ].
  Local Ltac t := repeat t_step.

  Local Ltac do_specialize_IHe :=
    repeat match goal with
           | [ IH : context[interpf ?e], H' : interpf (ctx:=?ctx) ?e = _ |- _ ]
             => let check_tac _ := (rewrite H' in IH) in
                first [ specialize (IH ctx); check_tac ()
                      | specialize (fun a => IH a ctx); check_tac ()
                      | specialize (fun a b => IH a b ctx); check_tac () ]
           | [ IH : context[mapf_cast _ ?e], H' : mapf_cast ?ctx ?e = _ |- _ ]
             => let check_tac _ := (rewrite H' in IH) in
                first [ specialize (IH ctx); check_tac ()
                      | specialize (fun a => IH a ctx); check_tac ()
                      | specialize (fun a b => IH a b ctx); check_tac () ]
           | [ H : forall x y z, Some _ = Some _ -> _ |- _ ]
             => first [ specialize (H _ _ _ eq_refl)
                      | specialize (fun x => H x _ _ eq_refl) ]
           | [ H : forall x y, Some _ = Some _ -> _ |- _ ]
             => first [ specialize (H _ _ eq_refl)
                      | specialize (fun x => H x _ eq_refl) ]
           | _ => progress specialize_by_assumption
           end.

  Lemma mapf_cast_correct
        {t} (e:exprf base_type_code op Name t)
    : forall
      (oldValues:Context)
      (newValues:Context)
      (varBounds:BoundsContext)
      {b} e' (He':mapf_cast varBounds e = Some (existT _ b e'))
      (Hctx:forall {t} n v,
          lookupb (t:=t) oldValues n = Some v
          -> exists b, lookupb (t:=t) varBounds n = Some b
                       /\ @inboundsb _ b v
                       /\ exists v', lookupb (t:=pick_typeb t b) newValues n = Some v'
                                     /\ cast_backb t b v' = v)
      r (Hr:interpf (interp_op:=interp_op) (ctx:=oldValues) e = Some r)
      r' (Hr':interpf (interp_op:=interp_op) (ctx:=newValues) e' = Some r')
      (Hside : prop_of_option (interpf_side_conditions interp_op interped_op_side_conditions oldValues e))
    , interpf (interp_op:=interp_op_bounds) (ctx:=varBounds) e = Some b
      /\ @inbounds _ b r /\ cast_back _ _ r' = r.
  Proof using Type*.
    induction e; simpl interpf; simpl mapf_cast; unfold option_map, cast_back in *; intros;
      unfold interpf_side_conditions in *; simpl in Hside;
      repeat (repeat handle_options_step; break_match_hyps; inversion_option; inversion_sigma; autorewrite with push_to_prop in *; simpl in *; unfold option_map in *; subst; try tauto).
    { destruct (Hctx _ _ _ Hr) as [b' [Hb'[Hb'v[v'[Hv' Hv'v]]]]]; clear Hctx Hr; subst.
      repeat match goal with
               [H: ?e = Some ?x, G:?e = Some ?x' |- _] =>
               pose proof (eq_trans (eq_sym G) H); clear G; inversion_option; subst
             end.
      auto. }
    { do_specialize_IHe.
      repeat (handle_options_step || destruct_head_and || specialize_by_assumption).
      subst; intuition eauto; try (symmetry; rewrite_hyp ?*; eauto);
        repeat handle_bounds_side_conditions_step; auto. }
    { cbv [LetIn.Let_In] in *.
      do_specialize_IHe.
      destruct_head'_and.
      destruct IHe1 as [IHe1_eq IHe1]; rewrite_hyp *; try assumption.
      { apply IHe2; clear IHe2; try reflexivity; [ | t ].
        intros ??? Hlookup.
        let b := fresh "b" in
        let H' := fresh "H'" in
        match goal with |- exists b0, ?v = Some b0 /\ _ => destruct v as [b|] eqn:H' end;
          [ exists b; split; [ reflexivity | ] | exfalso ];
          revert Hlookup H'; t. } }
    { do_specialize_IHe.
      t. }
  Qed.

  Lemma map_cast_correct
        {t} (e:expr base_type_code op Name t)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : forall
        (oldValues:Context)
        (newValues:Context)
        (varBounds:BoundsContext)
        {b} e' (He':map_cast varBounds e input_bounds = Some (existT _ b e'))
        (Hctx:forall {t} n v,
            lookupb (t:=t) oldValues n = Some v
            -> exists b, lookupb (t:=t) varBounds n = Some b
                         /\ @inboundsb _ b v
                         /\ exists v', lookupb (t:=pick_typeb t b) newValues n = Some v'
                                       /\ cast_backb t b v' = v)
        v v' (Hv : @inbounds _ input_bounds v /\ cast_back _ _ v' = v)
        r (Hr:interp (interp_op:=interp_op) (ctx:=oldValues) e v = Some r)
        r' (Hr':interp (interp_op:=interp_op) (ctx:=newValues) e' v' = Some r')
        (Hside : prop_of_option (interp_side_conditions interp_op interped_op_side_conditions oldValues e v))
        , interp (interp_op:=interp_op_bounds) (ctx:=varBounds) e input_bounds = Some b
          /\ @inbounds _ b r /\ cast_back _ _ r' = r.
  Proof using Type*.
    unfold map_cast, option_map, interp; simpl; intros.
    repeat first [ progress subst
                 | progress inversion_option
                 | progress inversion_sigma
                 | progress break_match_hyps
                 | progress destruct_head' sigT
                 | progress simpl in * ].
    eapply mapf_cast_correct; try eassumption.
    t.
  Qed.
End language.
