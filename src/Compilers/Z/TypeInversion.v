Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Util.FixCoqMistakes.

Section language.
  Section flat.
    Context (P : flat_type base_type -> Type).

    Local Ltac t :=
      let H := fresh in
      intro H; intros;
      match goal with
      | [ p : _ |- _ ] => specialize (H _ p)
      end;
      cbv beta iota in *;
      try specialize (H eq_refl); simpl in *;
      try assumption.

    Definition preinvert_TbaseTZ (Q : P (Tbase TZ) -> Type)
      : (forall t (p : P t), match t return P t -> Type with Tbase TZ => Q | _ => fun _ => True end p)
        -> forall p, Q p.
    Proof. t. Defined.

    Definition preinvert_TbaseTWord (Q : forall t, P (Tbase (TWord t)) -> Type)
      : (forall t (p : P t), match t return P t -> Type with Tbase (TWord _) => Q _ | _ => fun _ => True end p)
        -> forall t p, Q t p.
    Proof. t. Defined.
  End flat.
End language.

Ltac preinvert_one_type e :=
  lazymatch type of e with
  | ?P (Tbase TZ)
    => revert dependent e;
       refine (preinvert_TbaseTZ P _ _)
  | ?P (Tbase (TWord ?T))
    => is_var T;
       move e at top;
       revert dependent T;
       refine (preinvert_TbaseTWord P _ _)
  | _ => Compilers.TypeInversion.preinvert_one_type e
  end.
