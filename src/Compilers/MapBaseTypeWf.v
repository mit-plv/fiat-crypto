Require Import Coq.Bool.Sumbool.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.MapBaseType.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.

Section language.
  Context {base_type_code1 base_type_code2 : Type}
          {op1 : flat_type base_type_code1 -> flat_type base_type_code1 -> Type}
          {op2 : flat_type base_type_code2 -> flat_type base_type_code2 -> Type}
          (f_base : base_type_code1 -> base_type_code2)
          (f_op : forall var1 s d,
              op1 s d
              -> exprf _ op1 (var:=var1) s
              -> option (op2 (lift_flat_type f_base s) (lift_flat_type f_base d))).

  Local Hint Constructors wf wff or.

  Local Notation mapf_base_type :=
    (@mapf_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).
  Local Notation map_base_type :=
    (@map_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).

  Section with_var.
    Context {var1 var1' : base_type_code1 -> Type}
            {var2 var2' : base_type_code2 -> Type}
            (f_var12 : forall t, var1 t -> var2 (f_base t))
            (f_var21 : forall t, var2 (f_base t) -> var1 t)
            (f_var'12 : forall t, var1' t -> var2' (f_base t))
            (f_var'21 : forall t, var2' (f_base t) -> var1' t)
            (failb : forall t, exprf _ op2 (var:=var2) (Tbase t))
            (failb' : forall t, exprf _ op2 (var:=var2') (Tbase t))
            (Hwf_failb : forall t G, wff G (failb t) (failb' t))
            (Hwf_f_op : forall G s d opc e1 e2,
                wff G e1 e2
                -> f_op var1 s d opc e1 = f_op var1' s d opc e2)
            (Hvar12 : forall t v, f_var12 t (f_var21 t v) = v)
            (Hvar'12 : forall t v, f_var'12 t (f_var'21 t v) = v).

    Lemma wff_mapf_base_type G G' {t}
          (e : exprf base_type_code1 op1 (var:=var1) t)
          (e' : exprf base_type_code1 op1 (var:=var1') t)
          (HG : forall t x x',
              List.In (existT _ t (x, x')) G
              -> List.In (existT _ (f_base t) (f_var12 _ x, f_var'12 _ x')) G')
          (Hwf : wff G e e')
      : wff G'
            (mapf_base_type f_var12 f_var21 failb e)
            (mapf_base_type f_var'12 f_var'21 failb' e').
    Proof.
      revert dependent G'; induction Hwf;
        repeat first [ progress simpl in *
                     | progress intros
                     | progress inversion_option
                     | progress subst
                     | break_innermost_match_step
                     | progress specialize_by_assumption
                     | apply wff_SmartPairf_SmartValf
                     | solve [ eauto using In_flatten_binding_list_untransfer_interp_flat_type ]
                     | match goal with
                       | [ |- wff _ _ _ ] => constructor
                       | [ H : _ |- _ ] => apply H; try setoid_rewrite List.in_app_iff
                       | [ H : f_op _ ?s ?d ?opc ?e = ?x, H' : f_op _ ?s ?d ?opc ?e' = ?y |- _ ]
                         => assert (x = y) by (rewrite <- H, <- H'; eauto); clear H'
                       end
                     | progress destruct_head'_or ].
    Qed.

    Lemma wf_map_base_type {t}
          (e : expr base_type_code1 op1 (var:=var1) t)
          (e' : expr base_type_code1 op1 (var:=var1') t)
          (Hwf : wf e e')
      : wf
          (map_base_type f_var12 f_var21 failb e)
          (map_base_type f_var'12 f_var'21 failb' e').
    Proof.
      destruct Hwf; constructor; simpl; intros.
      eapply wff_mapf_base_type; [ | eauto ].
      eauto using In_flatten_binding_list_untransfer_interp_flat_type.
    Qed.
  End with_var.

  Section MapBaseType.
    Context (failb : forall var t, exprf _ op2 (var:=var) (Tbase t))
            (Hwf_failb : forall var1 var2 G t, wff G (failb var1 t) (failb var2 t))
            (Hwf_f_op : forall var1 var1' s d opc G e1 e2,
                wff G e1 e2
                -> f_op var1 s d opc e1 = f_op var1' s d opc e2)
            {t} (e : Expr base_type_code1 op1 t)
            (Hwf : Wf e).

    Lemma Wf_MapBaseType'
      : Wf (MapBaseType' f_base f_op failb e).
    Proof using Hwf Hwf_failb Hwf_f_op.
      intros var1 var2; apply wf_map_base_type; eauto.
    Qed.

    Lemma Wf_MapBaseType
          r
          (H : MapBaseType f_base f_op failb e = Some r)
      : Wf r.
    Proof using Hwf Hwf_failb Hwf_f_op.
      cbv [MapBaseType] in *; break_innermost_match_hyps; inversion_option; subst.
      apply Wf_MapBaseType'.
    Qed.
  End MapBaseType.
End language.

Hint Resolve @Wf_MapBaseType' : wf.
