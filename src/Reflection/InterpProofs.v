Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

  Lemma interpf_LetIn tx ex tC eC
    : Syntax.interpf interp_op (LetIn (tx:=tx) ex (tC:=tC) eC)
      = dlet x := Syntax.interpf interp_op ex in
        Syntax.interpf interp_op (eC x).
  Proof. reflexivity. Qed.

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

  Lemma interpf_SmartVarVarf {t t'} v x x'
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf base_type_code op (Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') (SmartVarVarf v) v))
    : interpf interp_op x = x'.
  Proof.
    clear -Hin.
    induction t'; simpl in *; try tauto.
    { intuition (inversion_sigma; inversion_prod; subst; eauto). }
    { apply List.in_app_iff in Hin.
      intuition (inversion_sigma; inversion_prod; subst; eauto). }
  Qed.

  Lemma interpf_SmartVarVarf_eq {t t'} v v' x x'
        (Heq : v = v')
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf base_type_code op (Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') (SmartVarVarf v') v))
    : interpf interp_op x = x'.
  Proof.
    subst; eapply interpf_SmartVarVarf; eassumption.
  Qed.
End language.
