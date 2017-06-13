(** * Basic Peano-arithmetic-like properties of ℤ *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.
Module Z.
  (** We need versions of [succ] and [pred] that reduce to [Pos.succ] and [Pos.pred] *)
  Definition succ' (z : Z) : Z
    := match z with
       | 0 => 1
       | -1 => 0
       | Z.pos x => Z.pos (Pos.succ x)
       | Z.neg x => Z.neg (Pos.pred x)
       end.
  Definition pred' (z : Z) : Z
    := match z with
       | 0 => -1
       | 1 => 0
       | Z.pos x => Z.pos (Pos.pred x)
       | Z.neg x => Z.neg (Pos.succ x)
       end.
  Lemma succ'_succ z : Z.succ' z = Z.succ z.
  Proof.
    unfold succ'; break_match; try reflexivity.
    rewrite <- Pos2Z.inj_succ; reflexivity.
  Qed.
  Lemma pred'_pred z : Z.pred' z = Z.pred z.
  Proof.
    unfold pred'; break_match; try reflexivity.
    unfold Z.pred; simpl.
    rewrite Pos.add_1_r; reflexivity.
  Qed.

  Section rect.
    Context (P : Z -> Type)
            (P0 : P 0)
            (Psucc : forall z, P z -> P (Z.succ' z))
            (Ppred : forall z, P z -> P (Z.pred' z)).

    Definition peano_rect z : P z
      := match z return P z with
         | 0 => P0
         | Z.pos x => Pos.peano_rect (fun p => P (Z.pos p)) (Psucc _ P0) (fun p => Psucc (Z.pos p)) x
         | Z.neg x => Pos.peano_rect (fun p => P (Z.neg p)) (Ppred _ P0) (fun p => Ppred (Z.neg p)) x
         end.

    Lemma peano_rect_base
      : peano_rect 0 = P0.
    Proof. reflexivity. Qed.
    Lemma peano_rect_succ z
      : 0 <= z -> peano_rect (Z.succ' z) = Psucc z (peano_rect z).
    Proof.
      unfold peano_rect; destruct z; simpl; try reflexivity;
        rewrite ?Pos.peano_rect_succ;
        try reflexivity.
      intro; exfalso; lia.
    Qed.
    Lemma peano_rect_pred z
      : z <= 0 -> peano_rect (Z.pred' z) = Ppred z (peano_rect z).
    Proof.
      unfold peano_rect; destruct z; simpl; try reflexivity;
        rewrite ?Pos.peano_rect_succ;
        try reflexivity.
      intro; exfalso; lia.
    Qed.
  End rect.
End Z.
