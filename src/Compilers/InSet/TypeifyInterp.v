Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InSet.Syntax.
Require Import Crypto.Compilers.InSet.Typeify.


Local Ltac t :=
  repeat first [ reflexivity
               | progress simpl in *
               | apply (f_equal2 (@pair _ _))
               | solve [ auto ]
               | progress cbv [LetIn.Let_In]
               | progress autorewrite with core
               | progress intros
               | match goal with
                 | [ v : _ * _ |- _ ] => destruct v
                 | [ H : _ |- _ ] => rewrite H
                 end ].

Section language.
  Context {base_type_code : Set}
          {op : flat_type base_type_code -> flat_type base_type_code -> Set}
          {interp_base_type : base_type_code -> Set}.

  Lemma typeify_untypeify_interp_flat_type {t} v
    : @typeify_interp_flat_type base_type_code interp_base_type t (untypeify_interp_flat_type v) = v.
  Proof using Type. induction t; t. Qed.
  Lemma untypeify_typeify_interp_flat_type {t} v
    : @untypeify_interp_flat_type base_type_code interp_base_type t (typeify_interp_flat_type v) = v.
  Proof using Type. induction t; t. Qed.
  Hint Rewrite @typeify_untypeify_interp_flat_type @untypeify_typeify_interp_flat_type.

  Section gen.
    Context {interp_op : forall s d, op s d -> Compilers.Syntax.interp_flat_type interp_base_type s -> Compilers.Syntax.interp_flat_type interp_base_type d}
            {interp_op' : forall s d, op s d -> InSet.Syntax.interp_flat_type interp_base_type s -> InSet.Syntax.interp_flat_type interp_base_type d}
            (untypeify_interp_op
             : forall s d opc args,
                untypeify_interp_flat_type (interp_op s d opc args)
                = interp_op' s d opc (untypeify_interp_flat_type args))
            (typeify_interp_op
             : forall s d opc args,
                typeify_interp_flat_type (interp_op' s d opc args)
                = interp_op s d opc (typeify_interp_flat_type args)).

    Local Notation interpf := (Compilers.Syntax.interpf interp_op).
    Local Notation interpf' := (InSet.Syntax.interpf interp_op').
    Local Notation typeify := (typeify (var:=interp_base_type)).

    Lemma interpf_typeify {t} e
      : interpf (typeify e) = typeify_interp_flat_type (t:=t) (interpf' e).
    Proof using typeify_interp_op. induction e; t. Qed.
    Lemma interpf_untypeify {t} e
      : interpf' (untypeify e) = untypeify_interp_flat_type (t:=t) (interpf e).
    Proof using untypeify_interp_op. induction e; t. Qed.

    Lemma interpf_typeify_untypeify {t} e
      : interpf (typeify (untypeify (t:=t) e)) = interpf e.
    Proof using Type. induction e; t. Qed.
    Lemma interpf_untypeify_typeify {t} e
      : interpf' (untypeify (t:=t) (typeify e)) = interpf' e.
    Proof using Type. induction e; t. Qed.
  End gen.
End language.

Module Compilers.
  Import Compilers.Syntax.
  Section language.
    Context {base_type_code : Set}
            {op : flat_type base_type_code -> flat_type base_type_code -> Set}
            {interp_base_type : base_type_code -> Set}
            {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}.

    Hint Rewrite @typeify_untypeify_interp_flat_type @untypeify_typeify_interp_flat_type.

    Local Notation interp_op' :=
      (fun s d opc args => untypeify_interp_flat_type (interp_op s d opc (typeify_interp_flat_type args))).

    Local Notation interpf := (Compilers.Syntax.interpf interp_op).
    Local Notation interpf' := (InSet.Syntax.interpf interp_op').
    Local Notation typeify := (typeify (var:=interp_base_type)).

    Lemma interpf_typeify {t} e
      : interpf (typeify e) = typeify_interp_flat_type (t:=t) (interpf' e).
    Proof using Type. apply interpf_typeify; t. Qed.
    Lemma interpf_untypeify {t} e
      : interpf' (untypeify e) = untypeify_interp_flat_type (t:=t) (interpf e).
    Proof using Type. apply interpf_untypeify; t. Qed.
  End language.
End Compilers.

Module InSet.
  Import InSet.Syntax.
  Section language.
    Context {base_type_code : Set}
            {op : flat_type base_type_code -> flat_type base_type_code -> Set}
            {interp_base_type : base_type_code -> Set}
            {interp_op' : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}.

    Hint Rewrite @typeify_untypeify_interp_flat_type @untypeify_typeify_interp_flat_type.

    Local Notation interp_op :=
      (fun s d opc args => typeify_interp_flat_type (interp_op' s d opc (untypeify_interp_flat_type args))).

    Local Notation interpf := (Compilers.Syntax.interpf interp_op).
    Local Notation interpf' := (InSet.Syntax.interpf interp_op').
    Local Notation typeify := (typeify (var:=interp_base_type)).

    Lemma interpf_typeify {t} e
      : interpf (typeify e) = typeify_interp_flat_type (t:=t) (interpf' e).
    Proof using Type. apply interpf_typeify; t. Qed.
    Lemma interpf_untypeify {t} e
      : interpf' (untypeify e) = untypeify_interp_flat_type (t:=t) (interpf e).
    Proof using Type. apply interpf_untypeify; t. Qed.
  End language.
End InSet.
