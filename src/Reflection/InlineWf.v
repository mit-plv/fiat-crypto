(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).
  Local Notation wf := (@wf base_type_code interp_base_type op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Local Ltac t_fin_step tac :=
      match goal with
      | _ => assumption
      | _ => progress simpl in *
      | _ => progress subst
      | _ => progress inversion_sigma
      | _ => setoid_rewrite List.in_app_iff
      | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
      | _ => progress intros
      | _ => solve [ eauto ]
      | _ => solve [ intuition (subst; eauto) ]
      | [ H : forall (x : prod _ _) (y : prod _ _), _ |- _ ] => specialize (fun x x' y y' => H (x, x') (y, y'))
      | _ => rewrite !List.app_assoc
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ |- _ ] => apply H
      | _ => eapply wff_in_impl_Proper; [ solve [ eauto ] | ]
      | _ => progress tac
      | [ |- wff _ _ _ ] => constructor
      | [ |- wf _ _ _ ] => constructor
      end.
    Local Ltac t_fin tac := repeat t_fin_step tac.

    Local Hint Constructors Syntax.wff.
    Local Hint Resolve List.in_app_or List.in_or_app.

    Local Ltac small_inversion_helper wf G0 e2 :=
      let t0 := match type of wf with wff (t:=?t0) _ _ _ => t0 end in
      let e1 := match goal with
                | |- context[wff _ (inline_constf ?e1) (inline_constf e2)] => e1
                end in
      pattern G0, t0, e1, e2;
      lazymatch goal with
      | [ |- ?retP _ _ _ _ ]
        => first [ refine (match wf in @Syntax.wff _ _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Const _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfConst _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Syntax.wff _ _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Var _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfVar _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Syntax.wff _ _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Op _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfOp _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Syntax.wff _ _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Let _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfLet _ _ _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Syntax.wff _ _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Pair _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfPair _ _ _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end) ]
      end.

    Local Hint Constructors or.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.
    Local Hint Resolve wff_SmartVar.
    Local Hint Resolve wff_SmartConst.

    Fixpoint wff_inline_constf {t} e1 e2 G G'
             (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf t * exprf t)%type) t (x, x')) G'
                            -> wff G x x')
             (wf : wff G' e1 e2)
             {struct e1}
      : @wff var1 var2 G t (inline_constf e1) (inline_constf e2).
    Proof.
      (*revert H.
      set (e1v := e1) in *.
      destruct e1 as [ | | ? ? ? args | tx ex tC0 eC0 | ? ex ? ey ];
        [ clear wff_inline_constf
        | clear wff_inline_constf
        | generalize (match e1v return match e1v with Let _ _ _ _ => _ | _ => _ end with
                      | Op _ _ _ args => wff_inline_constf _ args
                      | _ => I
                      end);
          clear wff_inline_constf
        | generalize (match e1v return match e1v with Let _ _ _ _ => _ | _ => _ end with
                      | Let _ ex _ eC => wff_inline_constf _ ex
                      | _ => I
                      end);
          generalize (match e1v return match e1v with Let _ _ _ _ => _ | _ => _ end with
                      | Let _ ex _ eC => fun x => wff_inline_constf _ (eC x)
                      | _ => I
                      end);
          clear wff_inline_constf
        | generalize (match e1v return match e1v with Let _ _ _ _ => _ | _ => _ end with
                      | Pair _ ex _ ey => wff_inline_constf _ ex
                      | _ => I
                      end);
          generalize (match e1v return match e1v with Let _ _ _ _ => _ | _ => _ end with
                      | Pair _ ex _ ey => wff_inline_constf _ ey
                      | _ => I
                      end);
          clear wff_inline_constf ];
        revert G;
        (* alas, Coq's refiner isn't smart enough to figure out these small inversions for us *)
        small_inversion_helper wf G' e2;
        t_fin idtac;
        repeat match goal with
               | [ H : context[(_ -> wff _ (inline_constf ?e) (inline_constf _))%type], e2 : exprf _ |- _ ]
                 => is_var e; not constr_eq e e2; specialize (H e2)
               | [ H : context[wff _ (@inline_constf ?A ?B ?C ?D ?E ?e) _] |- context[match @inline_constf ?A ?B ?C ?D ?E ?e with _ => _ end] ]
                 => destruct (@inline_constf A B C D E e)
               | [ H : context[wff _ _ (@inline_constf ?A ?B ?C ?D ?E ?e)] |- context[match @inline_constf ?A ?B ?C ?D ?E ?e with _ => _ end] ]
                 => destruct (@inline_constf A B C D E e)
               | [ IHwf : forall x y : list _, _, H1 : forall z : _, _, H2 : wff _ _ _ |- _ ]
                 => solve [ specialize (IHwf _ _ H1 H2); inversion IHwf ]
               | [ |- wff _ _ _ ] => constructor
               end.
      3:t_fin idtac.
      4:t_fin idtac.
      { match goal with
        | [ H : _ |- _ ] => eapply H; [ | solve [ eauto ] ]; t_fin idtac
        end. }*)
    Abort.
  End with_var.
End language.
