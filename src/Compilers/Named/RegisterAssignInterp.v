Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.RegisterAssign.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
          {InName OutName : Type}
          {InContext : Context InName (fun _ : base_type_code => OutName)}
          {ReverseContext : Context OutName (fun _ : base_type_code => InName)}
          {InContextOk : ContextOk InContext}
          {ReverseContextOk : ContextOk ReverseContext}
          {InName_beq : InName -> InName -> bool}
          {InterpInContext : Context InName interp_base_type}
          {InterpOutContext : Context OutName interp_base_type}
          {InterpInContextOk : ContextOk InterpInContext}
          {InterpOutContextOk : ContextOk InterpOutContext}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {OutName_dec : DecidableRel (@eq OutName)}
          (InName_bl : forall n1 n2, InName_beq n1 n2 = true -> n1 = n2)
          (InName_lb : forall n1 n2, n1 = n2 -> InName_beq n1 n2 = true).

  Local Instance InName_dec : DecidableRel (@eq InName)
    := dec_rel_of_bool_dec_rel InName_beq InName_bl InName_lb.

  Local Notation register_reassignf := (@register_reassignf base_type_code op InName OutName InContext ReverseContext InName_beq).
  Local Notation register_reassign := (@register_reassign base_type_code op InName OutName InContext ReverseContext InName_beq).

  Local Ltac t_find T :=
    induction T;
    repeat first [ progress subst
                 | progress inversion_option
                 | progress simpl in *
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress destruct_head'_and
                 | repeat apply conj; congruence
                 | progress cbv [cast_if_eq] in *
                 | progress eliminate_hprop_eq
                 | solve [ eauto ]
                 | match goal with
                   | [ |- context[@find_Name_and_val ?base_type_code ?Name ?base_type_code_dec ?Name_dec ?var' ?t ?n ?T ?N ?V ?default] ]
                     => lazymatch default with
                        | None => fail
                        | _ => rewrite (@find_Name_and_val_split base_type_code base_type_code_dec Name Name_dec var' t n T N V default)
                        end
                   | [ H : context[@find_Name_and_val ?base_type_code ?Name ?base_type_code_dec ?Name_dec ?var' ?t ?n ?T ?N ?V ?default] |- _ ]
                     => lazymatch default with
                        | None => fail
                        | _ => rewrite (@find_Name_and_val_split base_type_code base_type_code_dec Name Name_dec var' t n T N V default) in H
                        end
                   | [ H : forall a b, find_Name_and_val _ _ _ _ _ _ _ = Some _ -> _ |- find_Name_and_val _ _ _ _ _ _ _ = Some _ -> _ ]
                     => let H' := fresh in intro H'; pose proof (H _ _ H')
                   | [ H : forall a b, find_Name_and_val _ _ _ _ _ _ _ = Some _ -> _, H' : find_Name_and_val _ _ _ _ _ _ _ = Some _ |- _ ]
                     => specialize (H _ _ H')
                   | [ H : ?x = Some ?a, H' : ?y = Some ?b |- _ ]
                     => assert (a = b) by congruence; progress subst
                   end ].


  Lemma find_Name_and_val_OutToIn t T NI NO n_in n_out
    : find_Name_and_val base_type_code_dec OutName_dec (T:=T) t n_out NO NI None = Some n_in
      -> find_Name InName_dec n_in NI <> None.
  Proof using Type. t_find T. Qed.
  Lemma find_Name_and_val_InToOut t T NI NO n_in n_out
    : find_Name_and_val base_type_code_dec InName_dec (T:=T) t n_in NI NO None = Some n_out
      -> find_Name OutName_dec n_out NO <> None.
  Proof using Type. t_find T. Qed.

  Lemma lookupb_extend_helper {ctxi : InContext} {ctxr : ReverseContext} {t T NI NO n_in n_out}
        (H0 : lookupb t (extend (t:=T) ctxi NI NO) n_in = Some n_out)
        (H1 : lookupb t (extend (t:=T) ctxr NO NI) n_out = Some n_in)
    : ((lookupb t ctxi n_in = Some n_out /\ lookupb t ctxr n_out = Some n_in)
       /\ (find_Name _ n_in NI = None /\ find_Name _ n_out NO = None))
      \/ (find_Name_and_val _ _ t n_in NI NO None = Some n_out
          /\ find_Name_and_val _ _ t n_out NO NI None = Some n_in).
  Proof using InContextOk ReverseContextOk.
    rewrite (@lookupb_extend base_type_code _ InName _) in H0 by assumption.
    rewrite (@lookupb_extend base_type_code _ OutName _) in H1 by assumption.
    repeat first [ progress subst
                 | match goal with
                   | [ H : find_Name_and_val _ _ _ _ _ _ ?x = _ |- _ ]
                     => lazymatch x with
                        | None => fail
                        | _ => rewrite find_Name_and_val_split in H
                        end
                   end
                 | break_innermost_match_hyps_step
                 | congruence
                 | solve [ auto
                         | exfalso; eapply find_Name_and_val_OutToIn; eassumption
                         | exfalso; eapply find_Name_and_val_InToOut; eassumption ] ].
  Qed.

  Lemma find_Name_and_val_same_val {var' t T n_in n_out NI NO V v1 v2}
        (H0 : find_Name_and_val base_type_code_dec InName_dec t (T:=T) (var':=var') n_in NI V None = Some v1)
        (H1 : find_Name_and_val base_type_code_dec OutName_dec t (T:=T) n_out NO V None = Some v2)
        (H2 : find_Name_and_val base_type_code_dec InName_dec t n_in NI NO None = Some n_out)
        (H3 : find_Name_and_val base_type_code_dec OutName_dec t n_out NO NI None = Some n_in)
    : v1 = v2.
  Proof using Type.
    t_find T;
      match goal with
      | [ H : _ = None |- _ ]
        => first [ eapply find_Name_and_val_OutToIn in H; [ | eassumption ]
                 | eapply find_Name_and_val_InToOut in H; [ | eassumption ] ];
             destruct H
      end.
  Qed.

  Lemma find_Name_and_val_same_oval {var' t T n_in n_out NI NO V}
        (H2 : find_Name_and_val base_type_code_dec InName_dec t n_in NI NO None = Some n_out)
        (H3 : find_Name_and_val base_type_code_dec OutName_dec t n_out NO NI None = Some n_in)
    : find_Name_and_val base_type_code_dec InName_dec t (T:=T) (var':=var') n_in NI V None
      = find_Name_and_val base_type_code_dec OutName_dec t (T:=T) n_out NO V None.
  Proof using Type.
    t_find T;
      match goal with
      | [ H : _ = None |- _ ]
        => first [ eapply find_Name_and_val_OutToIn in H; [ | eassumption ]
                 | eapply find_Name_and_val_InToOut in H; [ | eassumption ] ];
             destruct H
      end.
  Qed.

  Local Ltac t :=
    repeat first [ reflexivity
                 | assumption
                 | progress subst
                 | progress inversion_option
                 | progress simpl in *
                 | progress intros *
                 | progress intros
                 | progress destruct_head'_and
                 | progress destruct_head'_or
                 | match goal with
                   | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                   | [ H : _ = Some ?v1, H' : _ = Some ?v2 |- _ ]
                     => is_var v1; is_var v2;
                        assert (v1 = v2) by eauto; progress subst
                   | [ H : lookupb (extend _ _ _) _ = Some _, H' : lookupb (extend _ _ _) _ = Some _ |- _ ]
                     => pose proof (lookupb_extend_helper H H'); clear H H'
                   | [ H : find_Name_and_val _ _ _ _ _ _ ?x = _ |- _ ]
                     => lazymatch x with
                        | None => fail
                        | _ => rewrite find_Name_and_val_split in H
                        end
                   | [ |- context[@find_Name_and_val ?base_type_code ?Name ?base_type_code_dec ?Name_dec ?var' ?t ?n ?T ?N ?V ?default] ]
                     => lazymatch default with
                        | None => fail
                        | _ => rewrite (@find_Name_and_val_split base_type_code base_type_code_dec Name Name_dec var' t n T N V default)
                        end
                   | [ H : _ |- _ ]
                     => first [ rewrite (@lookupb_remove base_type_code InName _) in H
                              | rewrite (@lookupb_remove base_type_code OutName _) in H
                              | rewrite (@lookupb_extend base_type_code _ InName _) in H
                              | rewrite (@lookupb_extend base_type_code _ OutName _) in H
                              | rewrite find_Name_and_val_different in H by assumption ]
                   end
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress cbv [option_map LetIn.Let_In] in *
                 | solve [ eauto using find_Name_and_val_same_val ]
                 | match goal with
                   | [ H : _ |- ?v1 = ?v2 ]
                     => is_var v1; is_var v2;
                        eapply H; [ | eassumption | eassumption | eassumption ]; clear H
                   end ].

  Lemma interpf_register_reassignf
        ctxi ctxr t e new_names
        (ctxi_interp : InterpInContext)
        (ctxr_interp : InterpOutContext)
        eout
        v1 v2
    : (forall t (n_in : InName) (n_out : OutName) v1 v2,
          lookupb t ctxi n_in = Some n_out
          -> lookupb t ctxr n_out = Some n_in
          -> lookupb t ctxi_interp n_in = Some v1
          -> lookupb t ctxr_interp n_out = Some v2
          -> v1 = v2)
      -> @register_reassignf ctxi ctxr t e new_names = Some eout
      -> interpf (interp_op:=interp_op) (ctx:=ctxr_interp) eout = Some v1
      -> interpf (interp_op:=interp_op) (ctx:=ctxi_interp) e = Some v2
      -> v1 = v2.
  Proof using InContextOk InName_bl InName_lb InterpInContextOk InterpOutContextOk OutName_dec ReverseContextOk base_type_code_dec.
    revert ctxi ctxr new_names ctxi_interp ctxr_interp eout v1 v2.
    induction e; t.
  Qed.

  Lemma interp_register_reassign
        ctxi ctxr t e new_names
        (ctxi_interp : InterpInContext)
        (ctxr_interp : InterpOutContext)
        eout
        v1 v2 x
    : (forall t (n_in : InName) (n_out : OutName) v1 v2,
          lookupb t ctxi n_in = Some n_out
          -> lookupb t ctxr n_out = Some n_in
          -> lookupb t ctxi_interp n_in = Some v1
          -> lookupb t ctxr_interp n_out = Some v2
          -> v1 = v2)
      -> @register_reassign ctxi ctxr t e new_names = Some eout
      -> interp (interp_op:=interp_op) (ctx:=ctxr_interp) eout x = Some v1
      -> interp (interp_op:=interp_op) (ctx:=ctxi_interp) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InName_bl InName_lb InterpInContextOk InterpOutContextOk OutName_dec ReverseContextOk base_type_code_dec.
    destruct e; unfold interp, register_reassign, option_map in *.
    break_innermost_match; try congruence.
    intros; inversion_option; subst; simpl in *.
    eapply interpf_register_reassignf; [ | eassumption.. ].
    t.
  Qed.

  Lemma Interp_register_reassign
        t e new_names
        eout
        v1 v2 x
    : @register_reassign empty empty t e new_names = Some eout
      -> Interp (Context:=InterpOutContext) (interp_op:=interp_op) eout x = Some v1
      -> Interp (Context:=InterpInContext) (interp_op:=interp_op) e x = Some v2
      -> v1 = v2.
  Proof using InContextOk InName_bl InName_lb InterpInContextOk InterpOutContextOk OutName_dec ReverseContextOk base_type_code_dec.
    apply interp_register_reassign; intros *.
    rewrite !lookupb_empty; congruence.
  Qed.
End language.
