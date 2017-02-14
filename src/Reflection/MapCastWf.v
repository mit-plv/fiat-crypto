Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t)).
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op src1 dst1)
                                (opc2 : op src2 dst2)
                                (args1' : @exprf base_type_code op ovar src1)
                                (args2 : interp_flat_type interp_base_type src2),
              @exprf base_type_code op ovar dst1).

  Local Notation interp_flat_type_ivarf_wff G a b
    := (forall t x y,
           List.In (existT _ t (x, y)%core) (flatten_binding_list a b)
           -> wff G x y)
         (only parsing).

  Section with_var.
    Context {ovar1 ovar2 : base_type_code -> Type}.

    Context (wff_transfer_op
             : forall G src1 dst1 src2 dst2 opc1 opc2 args1 args1' args2,
                wff G (var1:=ovar1) (var2:=ovar2) args1 args1'
                -> wff G
                       (@transfer_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args1 args2)
                       (@transfer_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args1' args2)).
    Local Notation mapf_interp_cast
      := (@mapf_interp_cast
            base_type_code base_type_code interp_base_type
            op op interp_op2 failv
            transfer_op).
    Local Notation map_interp_cast
      := (@map_interp_cast
            base_type_code base_type_code interp_base_type
            op op interp_op2 failv
            transfer_op).

    Local Notation G1eTf
      := (fun t : base_type_code => interp_flat_type ovar1 (Tbase t) * interp_flat_type ovar2 (Tbase t))%type.
    Local Notation G2eTf
      := (fun t : base_type_code => ovar1 t * ovar2 t)%type.
    Local Notation GbeTf
      := (fun t : base_type_code => interp_flat_type ovar1 (Tbase t) * interp_base_type t)%type.

    (*  Definition Gse_related' {t} (G1e : G1eTf t) (Gbe : GbeTf t) (G2e G2eTf t) : Prop
    := fst G1e = fst Gbe /\

    := exists (pf1 : projT1 G1e = projT1 G2e

                                         Definition Gse_related (G1e : sigT G1eTf) (G2e : sigT G2eTf) (G3e : sigT G3eTf) : Prop
    := exists (pf1 : projT1 G1e = projT1 G2e
                   /\

  Local Notation G3eT
    := {t : base_type_code &
            ((interp_flat_type ivarf1 (Tbase t) * interp_flat_type ivarf2 (Tbase t))
             * (ovar1 t * ovar2 t)
             * interp_base_type t)%type }.
  Local Notation G3T
    := (list G3eT).

  Definition G3e_to_G1e

     *)
    (* Local *) Hint Resolve <- List.in_app_iff.

    Local Ltac break_t
      := first [ progress subst
               | progress inversion_wff
               | progress invert_expr_subst
               | progress inversion_sigma
               | progress inversion_prod
               | progress destruct_head sig
               | progress destruct_head sigT
               | progress destruct_head ex
               | progress destruct_head and
               | progress destruct_head prod
               | progress break_match_hyps ].

    Lemma wff_mapf_interp_cast
          G1 Gbounds
          {t1} e1 e2 ebounds
          (Hwf_bounds : wff Gbounds e1 ebounds)
          (Hwf : wff G1 e1 e2)
      : wff G1
            (@mapf_interp_cast ovar1 t1 e1 t1 ebounds)
            (@mapf_interp_cast ovar2 t1 e2 t1 ebounds).
    Proof.
      revert dependent Gbounds; revert ebounds;
      induction Hwf;
        repeat match goal with
               | _ => solve [ exfalso; assumption ]
               | _ => intro
               | _ => progress break_t
               | _ => solve [ constructor; eauto
                            | eauto
                            | auto
                            | hnf; auto ]
               | _ => progress simpl in *
               | [ H : List.In _ (_ ++ _) |- _ ] => apply List.in_app_or in H
               | _ => progress destruct_head or
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- wff _ (mapf_interp_cast _ _ _ _) (mapf_interp_cast _ _ _ _) ]
                 => eapply H; eauto; []; clear H
               | _ => solve [ eauto using wff_SmartVarf, wff_in_impl_Proper ]
               end.
    Qed.

    (*Lemma wf_map_interp_cast
          {t1} e1 e2 ebounds
          args2
          (Hwf_bounds : wf e1 ebounds)
          (Hwf : wf e1 e2)
      : wf (@map_interp_cast ovar1 t1 e1 t1 ebounds args2)
           (@map_interp_cast ovar2 t1 e2 t1 ebounds args2).
    Proof.
      destruct Hwf;
        repeat match goal with
               | _ => solve [ constructor; eauto
                            | eauto using wff_mapf_interp_cast
                            | exfalso; assumption ]
               | _ => intro
               | _ => progress break_t
               | [ |- wf _ _ ] => constructor
               | _ => solve [ eauto using wff_SmartVarf, wff_in_impl_Proper ]
               end.
    Qed.*)
  End with_var.

  Section gen.
    Context (wff_transfer_op
             : forall ovar1 ovar2 G src1 dst1 src2 dst2 opc1 opc2 e1 e2 args2,
                wff G (var1:=ovar1) (var2:=ovar2) e1 e2
                -> wff G
                       (@transfer_op ovar1 src1 dst1 src2 dst2 opc1 opc2 e1 args2)
                       (@transfer_op ovar2 src1 dst1 src2 dst2 opc1 opc2 e2 args2)).

    Axiom proof_admitted : False.
    Local Notation MapInterpCast
      := (@MapInterpCast
            base_type_code interp_base_type
            op interp_op2 failv
            transfer_op).

    Lemma Wf_MapInterpCast
          {t} e
          args
          (Hwf : Wf e)
      : Wf (@MapInterpCast t e args).
    Proof.
      revert wff_transfer_op.
      case proof_admitted.
      (*intros ??; apply wf_map_interp_cast; auto.*)
    Qed.
  End gen.
End language.

Hint Resolve Wf_MapInterpCast : wf.
