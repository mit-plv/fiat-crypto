Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.

Fixpoint small_Decidable' {bound n} : forall (p : Tuple.tuple' Z n), Decidable (small (n:=S n) bound p).
Proof.
  refine match n as n return forall p : Tuple.tuple' Z n, id (Decidable (small (n:=S n) bound p)) with
         | 0
           => fun p : Z
              => if dec (0 <= p < bound)%Z then left _ else right _
         | S n'
           => fun p : Tuple.tuple' Z n' * Z
              => if dec (0 <= snd p < bound)%Z
                 then if dec (small (n:=S n') bound (fst p))%Z
                      then left _
                      else right _
                 else right _
         end;
    unfold id, small in *; simpl in *;
      [ clear small_Decidable' n
      | clear small_Decidable' n
      | clear small_Decidable'; simpl in *.. ];
      [ abstract (simpl in *; intros; destruct_head'_or; subst; auto; exfalso; assumption)
      | abstract (simpl in *; intros; destruct_head'_or; subst; auto; exfalso; assumption)
      | abstract (destruct p; simpl in *; intros; destruct_head'_or; subst; auto).. ].
Defined.

Global Instance small_Decidable {bound n} : forall (p : Tuple.tuple Z n), Decidable (small bound p).
Proof.
  destruct n; simpl; [ left | apply small_Decidable' ].
  intros ??; exfalso; assumption.
Defined.
