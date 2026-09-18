From Stdlib Require Import BinPosDef NArith Lia Morphisms_Prop.
From Corelib Require Import Program.Wf.

Local Open Scope positive_scope.
#[local] Coercion N.pos : positive >-> N.
(** Append two sequences *)

Fixpoint app (p q:positive) : positive :=
  match q with
  | q~0 => (app p q)~0
  | q~1 => (app p q)~1
  | 1 => p~1
  end.

Module Pos.
  Definition of_N n : positive := match n with N.pos n => n | _ => xH end.

  Definition lt_dec a b : {a<b}+{~a<b}. Proof. simple refine (
    match Pos.compare a b as c return {c = Lt} + {c <> Lt} with
    | Lt => left eq_refl | _ => right _
    end); abstract discriminate.
  Defined.
  
  Lemma lt_wf : well_founded Pos.lt.
  Proof.
    unshelve eapply Morphisms_Prop.well_founded_morphism.
    { exact (fun a b => N.lt a b). }
    { repeat intro; hnf; lia. }
    { eapply measure_wf with (R:=N.lt), N.lt_wf_0. }
  Qed.

  Lemma gt_wf c : well_founded (fun a b : positive => b < a <= c).
  Proof.
    unshelve eapply Morphisms_Prop.well_founded_morphism.
    { exact (fun a b => (b < a <= c)%N). }
    { repeat intro; hnf; lia. }
    { eapply measure_wf with (R:=(fun a b => (b < a <= c)%N)), N.gt_wf. }
  Qed.

  Lemma divide_1_r a : Pos.divide a 1 <-> a = 1.
  Proof. split. { inversion_clear 1. nia. } { intros []. exists 1. nia. } Qed.


  Definition pow_N p n :=
    match n with
    | N0 => xH
    | Npos q => Pos.pow p q
    end.

  Lemma Npos_pow_N p n : N.pos (Pos.pow_N p n) = N.pow p n.
  Proof. cbv [pow_N]; case n; trivial. Qed.

  Definition pow_pred p q := Pos.pow_N p (Pos.pred_N q).

  Lemma Npos_pow_pred p q : N.pos (Pos.pow_pred p q) = N.pow p (Pos.pred_N q).
  Proof. cbv [pow_pred pow_N]; case Pos.pred_N; trivial. Qed.
End Pos.
