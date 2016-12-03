Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {var : base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation Tbase := (@Tbase base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op var).
  Local Notation expr := (@expr base_type_code interp_base_type op var).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).

  Definition invert_Const {t} (e : exprf t) : option (interp_type t)
    := match e with Const _ v => Some v | _ => None end.
  Definition invert_Var {t} (e : exprf (Tbase t)) : option (var t)
    := match e in Syntax.exprf _ _ _ t'
             return option (var match t' with
                                | Syntax.Tbase t' => t'
                                | _ => t
                                end)
       with
       | Var _ v => Some v
       | _ => None
       end.
  Definition invert_Op {t} (e : exprf t) : option { t1 : flat_type & op t1 t * exprf t1 }%type
    := match e with Op _ _ opc args => Some (existT _ _ (opc, args)) | _ => None end.
  Definition invert_LetIn {A} (e : exprf A) : option { B : _ & exprf B * (Syntax.interp_flat_type var B -> exprf A) }%type
    := match e in Syntax.exprf _ _ _ t return option { B : _ & _ * (_ -> exprf t) }%type with
       | LetIn _ ex _ eC => Some (existT _ _ (ex, eC))
       | _ => None
       end.
  Definition invert_Pair {A B} (e : exprf (Prod A B)) : option (exprf A * exprf B)
    := match e in Syntax.exprf _ _ _ t
             return option match t with
                           | Prod _ _ => _
                           | _ => unit
                           end with
       | Pair _ x _ y => Some (x, y)%core
       | _ => None
       end.

  Local Ltac t' :=
    repeat first [ intro
                 | progress simpl in *
                 | reflexivity
                 | tauto
                 | progress subst
                 | progress inversion_option
                 | progress inversion_sigma
                 | progress break_match ].
  Local Ltac t :=
    lazymatch goal with
    | [ |- _ = Some ?v -> ?e = _ ]
      => revert v;
         refine match e with
                | Const _ _ => _
                | _ => _
                end
    end;
    t'.

  Lemma invert_Const_Some {t e v}
    : @invert_Const t e = Some v -> e = Const v.
  Proof. t. Qed.

  Lemma invert_Var_Some {t e v}
    : @invert_Var t e = Some v -> e = Var v.
  Proof. t. Qed.

  Lemma invert_Op_Some {t e v}
    : @invert_Op t e = Some v -> e = Op (fst (projT2 v)) (snd (projT2 v)).
  Proof. t. Qed.

  Lemma invert_LetIn_Some {t e v}
    : @invert_LetIn t e = Some v -> e = LetIn (fst (projT2 v)) (snd (projT2 v)).
  Proof. t. Qed.

  Lemma invert_Pair_Some {A B e v}
    : @invert_Pair A B e = Some v -> e = Pair (fst v) (snd v).
  Proof. t. Qed.
End language.

Global Arguments invert_Const {_ _ _ _ _} _.
Global Arguments invert_Var {_ _ _ _ _} _.
Global Arguments invert_Op {_ _ _ _ _} _.
Global Arguments invert_LetIn {_ _ _ _ _} _.
Global Arguments invert_Pair {_ _ _ _ _ _} _.
