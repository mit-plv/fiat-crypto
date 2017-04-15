(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Import Crypto.Compilers.CommonSubexpressionEliminationDenote.
Require Import Crypto.Compilers.CommonSubexpressionEliminationWf.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Decidable.

Section symbolic.
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (interp_op : forall s d (opc : op s d), interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
          (symbolize_op : forall s d, op s d -> op_code)
          (denote_op : forall s d, op_code -> option (op s d)).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr)
          (inline_symbolic_expr_in_lookup : bool).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type_gen := interp_flat_type.
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Local Notation denote_symbolic_expr := (@denote_symbolic_expr base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op denote_op interp_base_type interp_op).

  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.
  Local Instance op_code_dec : DecidableRel (@eq op_code)
    := dec_rel_of_bool_dec_rel op_code_beq op_code_bl op_code_lb.

  Lemma interpf_flatten_binding_list T t x y v s
        (H : List.In (existT _ t (x, y)) (flatten_binding_list (var2:=interp_base_type) (t:=T) (symbolicify_smart_var v s) v))
    : fst x = y.
  Proof.
    revert dependent s; induction T;
      repeat first [ progress simpl in *
                   | reflexivity
                   | tauto
                   | progress destruct_head or
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | rewrite List.in_app_iff in *
                   | progress intros
                   | solve [ eauto ] ].
  Qed.

  (*Lemma interpf_symbolize_exprf_injective
        s
    : forall G0 G1 t e0 e1 e0' e1'
             (HG0 : forall t x y, In (existT _ t (x, y)) G0 -> fst x = y)
             (HG1 : forall t x y, In (existT _ t (x, y)) G1 -> fst x = y)
             (Hwf0 : wff G0 (t:=t) e0 e0')
             (Hwf1 : wff G1 (t:=t) e1 e1')
             (Hs0 : symbolize_exprf e0 = Some s)
             (Hs1 : symbolize_exprf e1 = Some s),
      interpf interp_op e0' = interpf interp_op e1'.
  Proof.
    induction s; intros;
      destruct Hwf0;
      try (invert_one_expr e1; break_innermost_match; try exact I; intros);
      try (invert_one_expr e1'; break_innermost_match; try exact I; intros);
      try solve [ repeat first [ reflexivity
                               | progress subst
                               | progress destruct_head'_sig
                               | progress destruct_head'_and
                               | progress destruct_head'_prod
                               | progress inversion_option
                               | congruence
                               | progress simpl in *
                               | progress unfold option_map in *
                               | progress inversion_wf_constr
                               | break_innermost_match_hyps_step
                               | match goal with
                                 | [ HG : forall t x y, In _ ?G -> fst x = y, H : In _ ?G |- _ ]
                                   => pose proof (HG _ _ _ H); progress subst
                                 end ] ].
    Focus 3.
    { simpl in *.
    Focus 3.
    try reflexivity;
        simpl in *.
      inversion_expr.
        .
      inversion_wf.
    move s at top; reverse.
                ->

*)



Check @symbolize_exprf.

  Local Arguments lookupb : simpl never.
  Local Arguments extendb : simpl never.
  Lemma interpf_csef G t e1 e2
        (HG : forall t x y, In (existT _ t (x, y)) G -> fst x = y)
        (m : @SymbolicExprContext (interp_flat_type_gen _))
        (HGm : forall t s v,
            lookupb m s = Some v
            -> forall k,
                List.In k (flatten_binding_list (@symbolicify_smart_var interp_base_type t v s) v)
                -> List.In k G)
        (Hm : forall t sv v,
            lookupb m sv = Some v
            -> denote_symbolic_expr m t sv = Some v)
        (Hwf : wff G e1 e2)
    : interpf interp_op (@csef interp_base_type t e1 m) = interpf interp_op e2.
  Proof.
    cbv beta in *.
      revert dependent m;
        induction Hwf; simpl; cbv [LetIn.Let_In symbolize_var]; intros; eauto;
          rewrite_hyp ?* by eauto; try reflexivity; eauto.
      (*{ break_match; break_match_hyps; try congruence; inversion_prod; inversion_option; subst;
          simpl; unfold LetIn.Let_In;
            [ match goal with
              | [ Hm : forall t e1 e2 s v, symbolize_exprf _ = _ -> _, H' : symbolize_exprf _ = _ |- _ ]
                => erewrite (Hm _ _ _ _ _ H') by eassumption
              end
            | rewrite_hyp !* by eauto
            | rewrite_hyp !* by eauto ];
            match goal with
            | [ H : context[interpf interp_op (csef _ _)] |- _ ] => erewrite H; [ reflexivity | | eauto | eauto ]
            end;
            intros *;
            try solve [ repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                         | setoid_rewrite in_app_iff
                         | progress break_innermost_match
                         | progress subst
                         | progress simpl in *
                         | progress inversion_prod
                         | progress inversion_option
                         | progress destruct_head or
                         | solve [ eauto using interpf_flatten_binding_list ]
                         | progress intros ] ].
        admit.
        admit.
        admit. }*)
  Admitted.

  Lemma interpf_prepend_prefix t e prefix
    : interpf interp_op (@prepend_prefix _ t e prefix) = interpf interp_op e.
  Proof.
    induction prefix; simpl; [ reflexivity | unfold LetIn.Let_In; assumption ].
  Qed.

  Lemma interp_cse prefix t e1 e2
        (Hwf : wf e1 e2)
    : forall x, interp interp_op (@cse interp_base_type prefix t e1 empty) x = interp interp_op e2 x.
  Proof.
    destruct Hwf; simpl; intros.
    etransitivity; [ | eapply interpf_prepend_prefix ].
    eapply interpf_csef; eauto;
      [ ..
      | eapply wff_prepend_prefix; [ .. | solve [ eauto ] ] ].
    { intros; eapply interpf_flatten_binding_list; eassumption. }
    { admit. }
    { admit. }
  Admitted.

  Lemma InterpCSE t (e : Expr t)
        (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
        (*(Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
        (Hprefix : forall var1 var2 n t1 t2 e1 e2,
            nth_error (prefix var1) n = Some (existT _ t1 e1)
            -> nth_error (prefix var2) n = Some (existT _ t2 e2)
            -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)*)
        (Hwf : Wf e)
    : forall x, Interp interp_op (@CSE t e prefix) x = Interp interp_op e x.
  Proof.
    apply interp_cse; auto.
  Qed.
End symbolic.

Hint Rewrite @InterpCSE using solve_wf_side_condition : reflective_interp.
