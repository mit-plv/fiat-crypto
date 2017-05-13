(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.InterpProofs.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Util.Sigma Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.


Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Hint Extern 1 => eapply interpf_SmartVarVarf.

  Local Ltac t_fin :=
    repeat match goal with
           | _ => reflexivity
           | _ => progress unfold LetIn.Let_In
           | _ => progress simpl in *
           | _ => progress intros
           | _ => progress inversion_sigma
           | _ => progress inversion_prod
           | _ => solve [ intuition eauto | eauto | symmetry; eauto ]
           | _ => apply (f_equal (interp_op _ _ _))
           | _ => apply (f_equal2 (@pair _ _))
           | _ => progress specialize_by assumption
           | _ => progress subst
           | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
           | [ H : or _ _ |- _ ] => destruct H
           | _ => progress break_match
           | _ => rewrite <- !surjective_pairing
           | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : _ |- _ ] => apply H
           | [ H : _ |- _ ] => rewrite H
           | [ H : _ |- _ ] => erewrite H by reflexivity
           | _ => rewrite interpf_SmartVarf
           end.

  Lemma interpf_under_letsf' let_bind_op_args bind_pairs {t tC} (ex : exprf t) (eC : _ -> exprf tC)
        (eC_resp : forall x y,
            x = interpf interp_op y
            -> interpf interp_op (eC (inr y)) = interpf interp_op (eC (inl x)))
    : interpf interp_op (under_letsf' let_bind_op_args bind_pairs ex eC)
      = let x := interpf interp_op ex in interpf interp_op (eC (inl x)).
  Proof using Type.
    clear -eC_resp; revert bind_pairs.
    induction ex; t_fin.
  Qed.

  Lemma interpf_under_letsf let_bind_op_args {t tC} (ex : exprf t) (eC : _ -> exprf tC)
        (eC_resp : forall x y,
            interpf interp_op x = interpf interp_op y
            -> interpf interp_op (eC x) = interpf interp_op (eC y))
    : interpf interp_op (under_letsf let_bind_op_args ex eC)
      = let x := interpf interp_op ex in interpf interp_op (eC (SmartMap.SmartVarf x)).
  Proof using Type.
    unfold under_letsf; rewrite interpf_under_letsf'; t_fin.
  Qed.

  Section gen.
    Context (let_bind_op_args : bool).

    Lemma interpf_linearizef_gen {t} e
      : interpf interp_op (linearizef_gen let_bind_op_args (t:=t) e) = interpf interp_op e.
    Proof using Type.
      clear.
      induction e;
        repeat first [ progress rewrite ?interpf_under_letsf, ?interpf_SmartVarf
                     | progress simpl
                     | t_fin ].
    Qed.

    Local Hint Resolve interpf_linearizef_gen.

    Lemma interp_linearize_gen {t} e
      : forall x, interp interp_op (linearize_gen let_bind_op_args (t:=t) e) x = interp interp_op e x.
    Proof using Type.
      induction e; simpl; eauto.
    Qed.

    Lemma InterpLinearize_gen {t} (e : Expr t)
      : forall x, Interp interp_op (Linearize_gen let_bind_op_args e) x = Interp interp_op e x.
    Proof using Type.
      unfold Interp, Linearize_gen.
      eapply interp_linearize_gen.
    Qed.
  End gen.

  Definition interpf_linearizef {t} e
    : interpf interp_op (linearizef (t:=t) e) = interpf interp_op e
    := interpf_linearizef_gen _ e.
  Definition interpf_a_normalf {t} e
    : interpf interp_op (a_normalf (t:=t) e) = interpf interp_op e
    := interpf_linearizef_gen _ e.

  Definition interp_linearize {t} e
    : forall x, interp interp_op (linearize (t:=t) e) x = interp interp_op e x
    := interp_linearize_gen _ e.
  Definition interp_a_normal {t} e
    : forall x, interp interp_op (a_normal (t:=t) e) x = interp interp_op e x
    := interp_linearize_gen _ e.

  Definition InterpLinearize {t} (e : Expr t)
    : forall x, Interp interp_op (Linearize e) x = Interp interp_op e x
    := InterpLinearize_gen _ e.
  Definition InterpANormal {t} (e : Expr t)
    : forall x, Interp interp_op (ANormal e) x = Interp interp_op e x
    := InterpLinearize_gen _ e.
End language.

Hint Rewrite @interpf_under_letsf : reflective_interp.
Hint Rewrite @InterpLinearize_gen @interp_linearize_gen @interpf_linearizef_gen @InterpLinearize @interp_linearize @interpf_linearizef @InterpANormal @interp_a_normal @interpf_a_normalf : reflective_interp.
