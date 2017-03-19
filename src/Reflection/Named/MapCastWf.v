Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.ContextProperties.
Require Import Crypto.Reflection.Named.ContextProperties.SmartMap.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Reflection.Named.MapCast.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.

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
          (cast_backb: forall t b, interp_base_type (pick_typeb t b) -> interp_base_type t).
  Let cast_back : forall t b, interp_flat_type interp_base_type (@pick_type t b) -> interp_flat_type interp_base_type t
    := fun t b => SmartFlatTypeMapUnInterp cast_backb.
  Context {Context : Context Name interp_base_type}
          (ContextOk : ContextOk Context)
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
    | _ => progress unfold option_map in *
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
      => first [ rewrite (fun C => lookupb_extend C base_type_dec Name_dec) in H by assumption
               | setoid_rewrite (fun C => lookupb_extend C base_type_dec Name_dec) in H; [ | assumption.. ] ]
    | [ |- context[lookupb (extend _ _ _) _] ]
      => first [ rewrite (fun C => lookupb_extend C base_type_dec Name_dec) by assumption
               | setoid_rewrite (fun C => lookupb_extend C base_type_dec Name_dec); [ | assumption.. ] ]
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
    | [ |- exists v, Some ?k = Some v ]
      => exists k; reflexivity
    | [ |- (exists v, None = Some v /\ @?B v) ]
      => exfalso
    | [ |- ?A /\ (exists v, Some ?k = Some v /\ @?B v) ]
      => cut (A /\ B k); [ clear; solve [ intuition eauto ] | cbv beta ]
    | [ |- ?A /\ (exists v, None = Some v /\ @?B v) ]
      => exfalso
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
    first [ progress subst
          | progress destruct_head'_ex
          | progress destruct_head'_and
          | progress inversion_option
          | progress inversion_sigma
          | progress autorewrite with push_prop_of_option in *
          | progress break_match_hyps ].

  Local Ltac do_specialize_IHe :=
    repeat match goal with
           | [ IH : context[mapf_cast _ ?e], H' : mapf_cast ?ctx ?e = _ |- _ ]
             => let check_tac _ := (rewrite H' in IH) in
                first [ specialize (IH ctx); check_tac ()
                      | specialize (fun a => IH a ctx); check_tac ()
                      | specialize (fun a b => IH a b ctx); check_tac () ]
           | [ H : forall x y z w, Some _ = Some _ -> _ |- _ ]
             => first [ specialize (H _ _ _ _ eq_refl)
                      | specialize (fun x y => H x y _ _ eq_refl) ]
           | [ H : forall x y z, Some _ = Some _ -> _ |- _ ]
             => first [ specialize (H _ _ _ eq_refl)
                      | specialize (fun x => H x _ _ eq_refl) ]
           | [ H : forall x y, Some _ = Some _ -> _ |- _ ]
             => first [ specialize (H _ _ eq_refl)
                      | specialize (fun x => H x _ eq_refl) ]
           | _ => progress specialize_by_assumption
           | [ H : forall a b, prop_of_option (Named.wff a ?e) -> _, H' : prop_of_option (Named.wff _ ?e) |- _ ]
             => specialize (fun b => H _ b H')
           | [ H : forall a b, prop_of_option (Named.wff a ?e) -> _, H' : forall v, prop_of_option (Named.wff _ ?e) |- _ ]
             => specialize (fun b v => H _ b (H' v))
           | [ H : forall b v, _ -> prop_of_option (Named.wff b ?e) |- prop_of_option (Named.wff ?ctx ?e) ]
             => specialize (H ctx)
           end.

  Local Ltac t_step :=
    first [ progress intros
          | progress simpl in *
          | break_t_step
          | handle_lookupb_step
          | handle_exists_in_goal
          | apply conj
          | solve [ auto | exfalso; auto ]
          | specializer_t_step
          | progress do_specialize_IHe
          | match goal with
            | [ IH : forall v, _ -> ?T, v' : interp_flat_type _ _ |- ?T ]
              => apply (IH (cast_back _ _ v')); clear IH
            end ].
  Local Ltac t := repeat t_step.


  Lemma wff_mapf_cast
        {t} (e:exprf base_type_code op Name t)
    : forall
        (oldValues:Context)
        (newValues:Context)
        (varBounds:BoundsContext)
        {b} e' (He':mapf_cast varBounds e = Some (existT _ b e'))
        (Hwf : prop_of_option (Named.wff oldValues e))
        (Hctx:forall {t} n v,
            lookupb (t:=t) oldValues n = Some v
            -> exists b, lookupb (t:=t) varBounds n = Some b
                         /\ exists v', lookupb (t:=pick_typeb t b) newValues n = Some v'),
      prop_of_option (Named.wff newValues e').
  Proof. induction e; t. Qed.

  Lemma wf_map_cast
        {t} (e:expr base_type_code op Name t)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : forall
        (oldValues:Context)
        (newValues:Context)
        (varBounds:BoundsContext)
        {b} e' (He':map_cast varBounds e input_bounds = Some (existT _ b e'))
        (Hwf : Named.wf oldValues e)
        (Hctx:forall {t} n v,
            lookupb (t:=t) oldValues n = Some v
            -> exists b, lookupb (t:=t) varBounds n = Some b
                         /\ exists v', lookupb (t:=pick_typeb t b) newValues n = Some v'),
      Named.wf newValues e'.
  Proof.
    unfold Named.wf, map_cast, option_map, interp; simpl; intros.
    repeat first [ progress subst
                 | progress inversion_option
                 | progress inversion_sigma
                 | progress break_match_hyps
                 | progress destruct_head' sigT
                 | progress simpl in * ].
    match goal with v : _ |- _ => specialize (Hwf (cast_back _ _ v)) end.
    eapply wff_mapf_cast; eauto; [].
    t.
  Qed.
End language.
