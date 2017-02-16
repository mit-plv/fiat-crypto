(** * PHOAS interpretation function for any retract of [var:=interp_base_type] *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.InterpByIso.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.DestructHead.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation interpf_retr := (@interpf_retr base_type_code op interp_base_type interp_op).
  Local Notation interp_retr := (@interp_retr base_type_code op interp_base_type interp_op).

  Lemma interpf_retr_id {t} (e : @exprf interp_base_type t)
    : interpf_retr (fun _ x => x) (fun _ x => x) e = interpf interp_op e.
  Proof.
    induction e; simpl; cbv [LetIn.Let_In]; rewrite_hyp ?*; rewrite ?SmartVarfMap_id; reflexivity.
  Qed.
  Lemma interp_retr_id {t} (e : @expr interp_base_type t)
    : interp_type_gen_rel_pointwise_hetero
        (fun _ => eq)
        (fun _ => eq)
        (interp_retr (fun _ x => x) (fun _ x => x) e)
        (interp interp_op e).
  Proof.
    induction e; simpl; repeat intro; subst; auto using interpf_retr_id.
  Qed.

  Section with_var2.
    Context {var1 var2 : base_type_code -> Type}
            (var1_of_interp : forall t, interp_base_type t -> var1 t)
            (interp_of_var1 : forall t, var1 t -> interp_base_type t)
            (var2_of_interp : forall t, interp_base_type t -> var2 t)
            (interp_of_var2 : forall t, var2 t -> interp_base_type t)
            (interp_of_var12 : forall t x, interp_of_var1 t (var1_of_interp t x)
                                           = interp_of_var2 t (var2_of_interp t x)).
    Hint Rewrite @flatten_binding_list_SmartVarfMap @List.in_map_iff @List.in_app_iff.
    Lemma wff_interpf_retr G {t} (e1 : @exprf var1 t) (e2 : @exprf var2 t)
          (HG : forall t x1 x2,
              List.In (existT _ t (x1, x2)) G
              -> interp_of_var1 t x1 = interp_of_var2 t x2)
          (Hwf : wff G e1 e2)
      : interpf_retr var1_of_interp interp_of_var1 e1
        = interpf_retr var2_of_interp interp_of_var2 e2.
    Proof.
      induction Hwf; simpl; rewrite_hyp ?*; try reflexivity; auto.
      { match goal with H : _ |- _ => apply H end; intros.
        repeat first [ progress repeat autorewrite with core in *
                     | progress subst
                     | progress inversion_sigma
                     | progress inversion_prod
                     | progress simpl in *
                     | progress destruct_head' ex
                     | progress destruct_head' and
                     | progress destruct_head' or
                     | progress destruct_head' sigT
                     | progress destruct_head' prod
                     | progress rewrite_hyp !*
                     | solve [ auto ] ].
        do 2 apply f_equal.
        eapply interp_flat_type_rel_pointwise_flatten_binding_list with (R':=fun _ => eq); [ eassumption | ].
        apply lift_interp_flat_type_rel_pointwise_f_eq; reflexivity. }
    Qed.
    Lemma wf_interp_retr G {t} (e1 : @expr var1 t) (e2 : @expr var2 t)
          (HG : forall t x1 x2,
              List.In (existT _ t (x1, x2)) G
              -> interp_of_var1 t x1 = interp_of_var2 t x2)
          (Hwf : wf G e1 e2)
      : interp_type_gen_rel_pointwise_hetero
          (fun _ => eq)
          (fun _ => eq)
          (interp_retr var1_of_interp interp_of_var1 e1)
          (interp_retr var2_of_interp interp_of_var2 e2).
    Proof.
      induction Hwf; simpl; repeat intro; subst; eauto using wff_interpf_retr.
      match goal with H : _ |- _ => apply H end.
      simpl; intros; destruct_head' or; auto.
      inversion_sigma; inversion_prod; repeat subst; unfold SmartVarfMap; simpl; auto.
    Qed.
  End with_var2.

  Section with_var.
    Context {var : base_type_code -> Type}
            (var_of_interp : forall t, interp_base_type t -> var t)
            (interp_of_var : forall t, var t -> interp_base_type t)
            (var_is_retract : forall t x, interp_of_var t (var_of_interp t x) = x).
    Lemma wff_interpf_retr_correct G {t} (e1 : @exprf var t) (e2 : @exprf interp_base_type t)
          (HG : forall t x1 x2,
              List.In (existT _ t (x1, x2)) G
              -> interp_of_var t x1 = x2)
          (Hwf : wff G e1 e2)
      : interpf_retr var_of_interp interp_of_var e1 = interpf interp_op e2.
    Proof.
      erewrite wff_interpf_retr, interpf_retr_id; eauto.
    Qed.
    Lemma wf_interp_retr_correct G {t} (e1 : @expr var t) (e2 : @expr interp_base_type t)
          (HG : forall t x1 x2,
              List.In (existT _ t (x1, x2)) G
              -> interp_of_var t x1 = x2)
          (Hwf : wf G e1 e2)
      : interp_type_gen_rel_pointwise_hetero
          (fun _ => eq)
          (fun _ => eq)
          (interp_retr var_of_interp interp_of_var e1)
          (interp interp_op e2).
    Proof.
    Admitted.
  End with_var.
End language.
