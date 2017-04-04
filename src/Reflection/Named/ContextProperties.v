Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.ContextProperties.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.BreakMatch.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var)
          (base_type_code_dec : DecidableRel (@eq base_type_code))
          (Name_dec : DecidableRel (@eq Name))
          (ContextOk : ContextOk Context).

  Local Notation find_Name := (@find_Name base_type_code Name Name_dec).
  Local Notation find_Name_and_val := (@find_Name_and_val base_type_code Name base_type_code_dec Name_dec).

  Lemma lookupb_eq_cast
    : forall (ctx : Context) n t t' (pf : t = t'),
      lookupb ctx n t' = option_map (fun v => eq_rect _ var v _ pf) (lookupb ctx n t).
  Proof.
    intros; subst; edestruct lookupb; reflexivity.
  Defined.
  Lemma lookupb_extendb_eq
    : forall (ctx : Context) n t t' (pf : t = t') v,
      lookupb (extendb ctx n (t:=t) v) n t' = Some (eq_rect _ var v _ pf).
  Proof.
    intros; subst; apply lookupb_extendb_same; assumption.
  Defined.

  Lemma lookupb_extend (ctx : Context)
        T N t n v
    : lookupb (extend ctx N (t:=T) v) n t
      = find_Name_and_val t n N v (lookupb ctx n t).
  Proof using ContextOk. revert ctx; induction T; t. Qed.

  Lemma find_Name_and_val_Some_None
        {var' var''}
        {t n T N}
        {x : interp_flat_type var' T}
        {y : interp_flat_type var'' T}
        {default default' v}
        (H0 : @find_Name_and_val var' t n T N x default = Some v)
        (H1 : @find_Name_and_val var'' t n T N y default' = None)
    : default = Some v /\ default' = None.
  Proof using Type.
    revert dependent default; revert dependent default'; induction T; t.
  Qed.

  Lemma find_Name_and_val_default_to_None
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N <> None)
    : @find_Name_and_val var' t n T N x default
      = @find_Name_and_val var' t n T N x None.
  Proof using Type. revert default; induction T; t. Qed.
  Hint Rewrite @find_Name_and_val_default_to_None using congruence : ctx_db.

  Lemma find_Name_and_val_different
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = None)
    : @find_Name_and_val var' t n T N x default = default.
  Proof using Type. revert default; induction T; t. Qed.
  Hint Rewrite @find_Name_and_val_different using assumption : ctx_db.

  Lemma find_Name_and_val_wrong_type_iff
        {var'}
        {t t' n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = Some t')
    : t <> t'
      <-> @find_Name_and_val var' t n T N x default = None.
  Proof using Type. split; revert default; induction T; t. Qed.
  Lemma find_Name_and_val_wrong_type
        {var'}
        {t t' n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = Some t')
        (Ht : t <> t')
    : @find_Name_and_val var' t n T N x default = None.
  Proof using Type. eapply find_Name_and_val_wrong_type_iff; eassumption. Qed.
  Hint Rewrite @find_Name_and_val_wrong_type using congruence : ctx_db.

  Lemma find_Name_find_Name_and_val_wrong {var' n t' T V N}
    : find_Name n N = Some t'
      -> @find_Name_and_val var' t' n T N V None = None
      -> False.
  Proof using Type. induction T; t. Qed.

  Lemma find_Name_and_val_None_iff
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
    : (@find_Name n T N <> Some t
       /\ (@find_Name n T N <> None \/ default = None))
      <-> @find_Name_and_val var' t n T N x default = None.
  Proof using Type.
    destruct (@find_Name n T N) eqn:?; unfold not; t;
      try solve [ eapply find_Name_and_val_wrong_type; [ eassumption | congruence ]
                | eapply find_Name_find_Name_and_val_wrong; eassumption
                | left; congruence ].
  Qed.

  Lemma find_Name_and_val_split
        {var' t n T N V default}
    : @find_Name_and_val var' t n T N V default
      = match @find_Name n T N with
        | Some t' => if dec (t = t')
                     then @find_Name_and_val var' t n T N V None
                     else None
        | None => default
        end.
  Proof using Type.
    t; erewrite find_Name_and_val_wrong_type by solve [ eassumption | congruence ]; reflexivity.
  Qed.
  Lemma find_Name_and_val_find_Name_Some
        {var' t n T N V v}
        (H : @find_Name_and_val var' t n T N V None = Some v)
    : @find_Name n T N = Some t.
  Proof using Type.
    rewrite find_Name_and_val_split in H; break_match_hyps; subst; congruence.
  Qed.
End with_context.

Ltac find_Name_and_val_default_to_None_step :=
  match goal with
  | [ H : context[find_Name_and_val ?tdec ?ndec _ _ _ _ ?default] |- _ ]
    => lazymatch default with None => fail | _ => idtac end;
       rewrite (find_Name_and_val_split tdec ndec (default:=default)) in H
  | [ |- context[find_Name_and_val ?tdec ?ndec _ _ _ _ ?default] ]
    => lazymatch default with None => fail | _ => idtac end;
       rewrite (find_Name_and_val_split tdec ndec (default:=default))
  end.
Ltac find_Name_and_val_default_to_None := repeat find_Name_and_val_default_to_None_step.
