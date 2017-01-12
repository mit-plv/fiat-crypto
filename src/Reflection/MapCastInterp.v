Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.RewriteHyp.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type1 : base_type_code -> Type}
          {interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op1 : forall src dst, op src dst -> interp_flat_type interp_base_type1 src -> interp_flat_type interp_base_type1 dst)
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t)).
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op src1 dst1)
                                (opc2 : op src2 dst2)
                                (args1' : @exprf base_type_code op ovar src1)
                                (args2 : interp_flat_type interp_base_type2 src2),
              @exprf base_type_code op ovar dst1).

  Context (R' : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop).
  Local Notation R x y := (interp_flat_type_rel_pointwise R' x y).
  Section gen_Prop.
    Context (P : Type) (and : P -> P -> P) (True : P).
    Context (bound_is_good : forall t, interp_base_type2 t -> P).
    Local Notation bounds_are_good
      := (@interp_flat_type_rel_pointwise1_gen_Prop _ _ P and True bound_is_good _).
    Fixpoint bounds_are_recursively_good_gen_Prop {t} (e : exprf base_type_code op t) : P
      := match e with
         | LetIn tx ex tC eC
           => and (@bounds_are_recursively_good_gen_Prop tx ex)
                  (@bounds_are_recursively_good_gen_Prop tC (eC (interpf interp_op2 ex)))
         | Op t1 tR opc args as e'
           => and (@bounds_are_recursively_good_gen_Prop _ args)
                  (bounds_are_good (interpf interp_op2 e'))
         | TT => True
         | Var t v => bound_is_good _ v
         | Pair tx ex ty ey
           => and (@bounds_are_recursively_good_gen_Prop _ ex)
                  (@bounds_are_recursively_good_gen_Prop _ ey)
         end.
  End gen_Prop.
  Definition bounds_are_recursively_goodb
    := bounds_are_recursively_good_gen_Prop bool andb true.
  Global Arguments bounds_are_recursively_goodb _ {_} !_ / .
  Definition bounds_are_recursively_good
    := @bounds_are_recursively_good_gen_Prop Prop and True.
  Global Arguments bounds_are_recursively_good _ {_} !_ / .
  Lemma bounds_are_recursively_good_iff_bool
        R t x
    : is_true (@bounds_are_recursively_goodb R t x)
      <-> @bounds_are_recursively_good (fun t x => is_true (R t x)) t x.
  Proof.
    unfold is_true.
    clear; induction x; simpl in *; rewrite ?Bool.andb_true_iff;
      try setoid_rewrite interp_flat_type_rel_pointwise1_gen_Prop_iff_bool;
      rewrite_hyp ?*; intuition congruence.
  Qed.
  Definition bounds_are_recursively_good_gen_Prop_iff_bool
    : forall R t x,
      is_true (@bounds_are_recursively_good_gen_Prop bool _ _ R t x)
      <-> @bounds_are_recursively_good_gen_Prop Prop _ _ (fun t x => is_true (R t x)) t x
    := bounds_are_recursively_good_iff_bool.

  Context (bound_is_good : forall t, interp_base_type2 t -> Prop).
  Local Notation bounds_are_good
    := (@interp_flat_type_rel_pointwise1 _ _ bound_is_good).
  Lemma bounds_are_good_when_recursively_good {t} e
    : @bounds_are_recursively_good bound_is_good t e -> bounds_are_good (interpf interp_op2 e).
  Proof.
    induction e; simpl; unfold LetIn.Let_In; intuition auto.
  Qed.
  Local Hint Resolve bounds_are_good_when_recursively_good.

  Local Notation G_invariant_holds G
    := (forall t x x',
           List.In (existT _ t (x, x')%core) G -> R' t x x')
         (only parsing).

  Context (interpf_transfer_op
           : forall G t tR opc ein eout ebounds,
              wff G ein ebounds
              -> G_invariant_holds G
              -> interpf interp_op1 ein = interpf interp_op1 eout
              -> bounds_are_recursively_good bound_is_good ebounds
              -> bounds_are_good (interp_op2 t tR opc (interpf interp_op2 ebounds))
              -> interpf interp_op1 (transfer_op interp_base_type1 t tR t tR opc opc eout (interpf interp_op2 ebounds))
                 = interpf interp_op1 (Op opc ein)).

  Context (R_transfer_op
           : forall G t tR opc ein eout ebounds,
              wff G ein ebounds
              -> G_invariant_holds G
              -> interpf interp_op1 ein = interpf interp_op1 eout
              -> bounds_are_recursively_good bound_is_good ebounds
              -> bounds_are_good (interp_op2 t tR opc (interpf interp_op2 ebounds))
              -> R (interpf interp_op1 (transfer_op interp_base_type1 t tR t tR opc opc eout (interpf interp_op2 ebounds)))
                   (interpf interp_op2 (Op opc ebounds))).

  Local Notation mapf_interp_cast
    := (@mapf_interp_cast
          base_type_code base_type_code interp_base_type2
          op op interp_op2 failv
          transfer_op).
  Local Notation map_interp_cast
    := (@map_interp_cast
          base_type_code base_type_code interp_base_type2
          op op interp_op2 failv
          transfer_op).
  Local Notation MapInterpCast
      := (@MapInterpCast
            base_type_code interp_base_type2
            op interp_op2 failv
            transfer_op).

  (* Local *) Hint Resolve <- List.in_app_iff.
  Local Hint Resolve (fun t T => @interp_flat_type_rel_pointwise_flatten_binding_list _ _ _ t T R').

  Local Ltac break_t
    := first [ progress subst
             | progress inversion_wf
             | progress invert_expr_subst
             | progress inversion_sigma
             | progress inversion_prod
             | progress destruct_head sig
             | progress destruct_head sigT
             | progress destruct_head ex
             | progress destruct_head and
             | progress destruct_head prod
             | progress split_and
             | progress break_match_hyps ].

  Local Ltac fin_False :=
    lazymatch goal with
    | [ H : False |- _ ] => exfalso; assumption
    end.

  Local Ltac fin_t0 :=
    solve [ constructor; eauto
          | eauto
          | auto
          | hnf; auto ].

  Local Ltac handle_list_t :=
    match goal with
    | _ => progress cbv [LetIn.Let_In duplicate_types] in *
    | [ H : List.In _ (_ ++ _) |- _ ] => apply List.in_app_or in H
    | [ H : List.In _ (List.map _ _) |- _ ]
      => rewrite List.in_map_iff in H
    | _ => rewrite <- flatten_binding_list_flatten_binding_list2
    | [ H : appcontext[flatten_binding_list2] |- _ ]
      => rewrite <- flatten_binding_list_flatten_binding_list2 in H
    | [ H : context[flatten_binding_list (SmartVarfMap _ _) (SmartVarfMap _ _)] |- _ ]
      => rewrite flatten_binding_list_SmartVarfMap in H
    | [ H : context[flatten_binding_list2 (SmartVarfMap _ _) (SmartVarfMap _ _)] |- _ ]
      => rewrite flatten_binding_list2_SmartVarfMap in H
    | [ H : context[flatten_binding_list2 (SmartVarfMap _ _) _] |- _ ]
      => rewrite flatten_binding_list2_SmartVarfMap1 in H
    | [ H : context[flatten_binding_list2 _ (SmartVarfMap _ _)] |- _ ]
      => rewrite flatten_binding_list2_SmartVarfMap2 in H
    | _ => rewrite <- flatten_binding_list_flatten_binding_list2
    | _ => rewrite List.in_map_iff
    | [ H : context[List.In _ (_ ++ _)] |- _ ]
      => setoid_rewrite List.in_app_iff in H
    end.

  Local Ltac wff_t :=
    match goal with
    | [ |- wff _ _ _ ] => constructor
    | [ H : _ |- wff _ (mapf_interp_cast _ _ _) (mapf_interp_cast _ _ _) ]
      => eapply H; eauto; []; clear H
    | _ => solve [ eauto using wff_in_impl_Proper ]
    end.

  Local Ltac R_t :=
    match goal with
    | [ |- R' _ _ _ ] => eapply interp_flat_type_rel_pointwise_flatten_binding_list; eauto
    | [ H : forall x y, _ -> R _ _ |- R _ _ ] => apply H; eauto; []
    | [ H : forall x y, _ -> _ -> R _ _ |- R _ _ ] => apply H; eauto; []
    end.

  Local Ltac misc_t :=
    match goal with
    | _ => progress specialize_by eauto
    | [ |- exists _, _ ]
      => eexists (existT _ _ _)
    | [ |- _ /\ _ ] => split
    | [ H : _ = _ |- _ ] => rewrite H
    | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : forall x y, _ -> _ -> _ = _ |- interpf _ _ = interpf _ _ ]
      => apply H
    end.

  Local Ltac t_step :=
    first [ intro
          | fin_False
          | progress break_t
          | fin_t0
          | progress simpl in *
          | wff_t
          | handle_list_t
          | progress destruct_head' or
          | misc_t
          | R_t ].

  Lemma interpf_mapf_interp_cast_and_rel
        G
        {t1} e1 ebounds
        (Hgood : bounds_are_recursively_good bound_is_good ebounds)
        (HG : G_invariant_holds G)
        (Hwf : wff G e1 ebounds)
    : interpf interp_op1 (@mapf_interp_cast interp_base_type1 t1 e1 t1 ebounds)
      = interpf interp_op1 e1
      /\ R (interpf interp_op1 (@mapf_interp_cast interp_base_type1 t1 e1 t1 ebounds))
           (interpf interp_op2 ebounds).
  Proof. induction Hwf; repeat t_step. Qed.

  Local Hint Resolve interpf_mapf_interp_cast_and_rel.

  Lemma interpf_mapf_interp_cast
        G
        {t1} e1 ebounds
        (Hgood : bounds_are_recursively_good bound_is_good ebounds)
        (HG : G_invariant_holds G)
        (Hwf : wff G e1 ebounds)
    : interpf interp_op1 (@mapf_interp_cast interp_base_type1 t1 e1 t1 ebounds)
      = interpf interp_op1 e1.
  Proof. eapply interpf_mapf_interp_cast_and_rel; eassumption. Qed.

  Lemma interp_map_interp_cast_and_rel
        {t1} e1 ebounds
        args2
        (Hgood : bounds_are_recursively_good bound_is_good (invert_Abs ebounds args2))
        (Hwf : wf e1 ebounds)
    : forall x,
      R x args2
      -> interp interp_op1 (@map_interp_cast interp_base_type1 t1 e1 t1 ebounds args2) x
         = interp interp_op1 e1 x
         /\ R (interp interp_op1 (@map_interp_cast interp_base_type1 t1 e1 t1 ebounds args2) x)
              (interp interp_op2 ebounds args2).
  Proof. destruct Hwf; intros; eapply interpf_mapf_interp_cast_and_rel; eauto. Qed.

  Lemma interp_map_interp_cast
        {t1} e1 ebounds
        args2
        (Hgood : bounds_are_recursively_good bound_is_good (invert_Abs ebounds args2))
        (Hwf : wf e1 ebounds)
    : forall x,
      R x args2
      -> interp interp_op1 (@map_interp_cast interp_base_type1 t1 e1 t1 ebounds args2) x
         = interp interp_op1 e1 x.
  Proof. intros; eapply interp_map_interp_cast_and_rel; eassumption. Qed.

  Lemma InterpMapInterpCastAndRel
        {t} e
        args
        (Hwf : Wf e)
        (Hgood : bounds_are_recursively_good bound_is_good (invert_Abs (e interp_base_type2) args))
    : forall x,
      R x args
      -> Interp interp_op1 (@MapInterpCast t e args) x
         = Interp interp_op1 e x
         /\ R (Interp interp_op1 (@MapInterpCast t e args) x)
              (Interp interp_op2 e args).
  Proof. apply interp_map_interp_cast_and_rel; auto. Qed.

  Lemma InterpMapInterpCast
        {t} e
        args
        (Hwf : Wf e)
        (Hgood : bounds_are_recursively_good bound_is_good (invert_Abs (e interp_base_type2) args))
    : forall x,
      R x args
      -> Interp interp_op1 (@MapInterpCast t e args) x
         = Interp interp_op1 e x.
  Proof. apply interp_map_interp_cast; auto. Qed.
End language.
