Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type interp_base_type.
  Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

  Lemma interpf_SmartVarf t v
    : Syntax.interpf interp_op (SmartVarf (t:=t) v) = v.
  Proof.
    unfold SmartVarf; induction t;
      repeat match goal with
             | _ => reflexivity
             | _ => progress simpl in *
             | _ => progress rewrite_hyp *
             | _ => rewrite <- surjective_pairing
             end.
  Qed.

  Lemma interpf_SmartConstf {t t'} v x x'
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf base_type_code interp_base_type op (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartConstf v) v))
    : interpf interp_op x = x'.
  Proof.
    clear -Hin.
    induction t'; simpl in *.
    { intuition (inversion_sigma; inversion_prod; subst; eauto). }
    { apply List.in_app_iff in Hin.
      intuition (inversion_sigma; inversion_prod; subst; eauto). }
  Qed.

  Lemma interpf_SmartVarVarf {t t'} v x x'
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf base_type_code interp_base_type op (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartVarVarf v) v))
    : interpf interp_op x = x'.
  Proof.
    clear -Hin.
    induction t'; simpl in *.
    { intuition (inversion_sigma; inversion_prod; subst; eauto). }
    { apply List.in_app_iff in Hin.
      intuition (inversion_sigma; inversion_prod; subst; eauto). }
  Qed.

  Lemma interpf_SmartVarVarf_eq {t t'} v v' x x'
        (Heq : v = v')
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf base_type_code interp_base_type op (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartVarVarf v') v))
    : interpf interp_op x = x'.
  Proof.
    subst; eapply interpf_SmartVarVarf; eassumption.
  Qed.
End language.
