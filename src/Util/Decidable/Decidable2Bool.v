Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Local Open Scope Z_scope.

Create HintDb dec2bool discriminated.

Lemma dec_Z_lt_to_bool a b
  : (if dec (a < b) then true else false) = Z.ltb a b.
Proof.
  destruct (Z.ltb a b) eqn:?; break_match; Z.ltb_to_lt; try reflexivity; omega.
Qed.
Hint Rewrite dec_Z_lt_to_bool : dec2bool.
Lemma dec_Z_le_to_bool a b
  : (if dec (a <= b) then true else false) = Z.leb a b.
Proof.
  destruct (Z.leb a b) eqn:?; break_match; Z.ltb_to_lt; try reflexivity; omega.
Qed.
Hint Rewrite dec_Z_le_to_bool : dec2bool.
Lemma dec_Z_eq_to_bool a b
  : (if dec (a = b) then true else false) = Z.eqb a b.
Proof.
  destruct (Z.eqb a b) eqn:?; break_match; Z.ltb_to_lt; try reflexivity; omega.
Qed.
Hint Rewrite dec_Z_eq_to_bool : dec2bool.
Lemma dec_nat_eq_to_bool a b
  : (if dec (a = b) then true else false) = Nat.eqb a b.
Proof.
  destruct (Nat.eqb a b) eqn:H; break_match; try reflexivity.
  { apply beq_nat_true in H; congruence. }
  { rewrite Nat.eqb_refl in H; congruence. }
Qed.
Hint Rewrite dec_nat_eq_to_bool : dec2bool.
Lemma dec_bool_eq_to_bool_if a b
  : (if dec (a = b :> bool) then true else false) = if b then a else negb a.
Proof.
  destruct a, b; reflexivity.
Qed.
Hint Rewrite dec_bool_eq_to_bool_if : dec2bool.
Lemma dec_not_negb {P} {H : Decidable P}
  : (if dec (not P) then true else false)
    = negb (if dec P then true else false).
Proof.
  do 2 edestruct dec; try reflexivity; tauto.
Qed.
Hint Rewrite @dec_not_negb : dec2bool.
Lemma dec_Q_le_to_bool a b
  : (if dec (a <= b)%Q then true else false) = Qle_bool a b.
Proof.
  destruct (Qle_bool a b) eqn:?; cbv [Qle Qle_bool] in *;
    break_match; Z.ltb_to_lt; try reflexivity; omega.
Qed.
Hint Rewrite dec_Q_le_to_bool : dec2bool.
Lemma dec_True_to_bool
  : (if dec True then true else false) = true.
Proof. reflexivity. Qed.
Hint Rewrite dec_True_to_bool : dec2bool.
Lemma dec_False_to_bool
  : (if dec False then true else false) = false.
Proof. reflexivity. Qed.
Hint Rewrite dec_False_to_bool : dec2bool.
Lemma dec_ifb_to_bool {b : bool} {A B} {HA : Decidable A} {HB : Decidable B}
  : (if dec (if b then A else B) then true else false)
    = if b then (if dec A then true else false) else (if dec B then true else false).
Proof. destruct b; reflexivity. Qed.
Hint Rewrite @dec_ifb_to_bool : dec2bool.
Lemma dec_and_to_bool {A B} {HA : Decidable A} {HB : Decidable B}
  : (if dec (A /\ B) then true else false)
    = andb (if dec A then true else false) (if dec B then true else false).
Proof. do 3 edestruct dec; try reflexivity; tauto. Qed.
Hint Rewrite @dec_and_to_bool : dec2bool.
Lemma dec_or_to_bool {A B} {HA : Decidable A} {HB : Decidable B}
  : (if dec (A \/ B) then true else false)
    = orb (if dec A then true else false) (if dec B then true else false).
Proof. do 3 edestruct dec; try reflexivity; tauto. Qed.
Hint Rewrite @dec_or_to_bool : dec2bool.
Lemma dec_fieldwise_to_bool {A B R n} {H : forall x y, Decidable (R x y)} x y
  : (if dec (@Tuple.fieldwise A B n R x y) then true else false)
    = @Tuple.fieldwiseb A B n (fun x y => if dec (R x y) then true else false) x y.
Proof.
  destruct (dec _) as [H'|H'].
  { symmetry; rewrite Tuple.fieldwiseb_fieldwise; [ eassumption | ].
    intros; edestruct dec; split; auto; discriminate. }
  { destruct (Tuple.fieldwiseb _ _ _) eqn:H''; [ | reflexivity ].
    rewrite Tuple.fieldwiseb_fieldwise in H''.
    { exfalso; apply H', H''. }
    { intros; edestruct dec; split; auto; discriminate. } }
Qed.
Hint Rewrite @dec_fieldwise_to_bool : dec2bool.
Lemma dec_tuple_eq_to_bool T {H : DecidableRel (@eq T)} n (x y : Tuple.tuple T n)
  : (if dec (x = y) then true else false) = Tuple.fieldwiseb (fun x y => if dec (x = y) then true else false) x y.
Proof.
  destruct (dec _) as [H'|H'], (Tuple.fieldwiseb _ _ _) eqn:H''; try reflexivity;
    rewrite <- Tuple.fieldwise_eq_iff in H';
    first [ exfalso; rewrite Tuple.fieldwiseb_fieldwise in H''
          | rewrite <- H''; clear H''; symmetry; rewrite Tuple.fieldwiseb_fieldwise ];
    try eassumption; eauto; intros; destruct dec; split; auto; congruence.
Qed.
Hint Rewrite dec_tuple_eq_to_bool : dec2bool.

Require Import Crypto.Util.ListUtil.Forall.
Lemma dec_Forall_to_bool {A P} {H : forall x, Decidable (P x)} ls
  : (if dec (@Forall A P ls) then true else false)
    = Forallb (fun x => if dec (P x) then true else false) ls.
Proof.
  destruct (dec _) as [H'|H'], (Forallb _ _) eqn:H'';
    try reflexivity; [ symmetry; rewrite <- H''; clear H'' | exfalso; apply H' ];
      [ rewrite Forall_Forallb_iff; [ eassumption | ]
      | rewrite <- Forall_Forallb_iff; [ eassumption | ] ];
      intros; cbv beta; destruct (dec _); intuition; try congruence.
Qed.
Hint Rewrite @dec_Forall_to_bool : dec2bool.

Ltac dec2bool_split_hyp H :=
  lazymatch type of H with
  | _ /\ _ => destruct H as [H _]; dec2bool_split_hyp H
  | andb _ _ = true => apply Bool.andb_true_iff in H; destruct H as [H _]; dec2bool_split_hyp H
  | ?e = true => is_evar e; apply Bool.andb_true_iff in H; destruct H as [_ H]
  end.

Ltac premake_parameter_package _ :=
  let H := fresh in
  eexists; intro H;
  unshelve econstructor;
  repeat match goal with
         | [ |- context[cbv_minus_then_vm_decide_package ?x ?y] ]
           => change (cbv_minus_then_vm_decide_package x y) with (vm_decide_package y)
         | [ |- context[vm_compute_reflexivity_package ?x] ]
           => change (vm_compute_reflexivity_package ?x) with (vm_decide_package x)
         end;
  autounfold with dec2bool;
  repeat autorewrite with dec2bool.
Ltac push_dec_to_hyps precheck :=
  let rec check R :=
      lazymatch R with
      | Z.ltb _ _ => idtac
      | Z.leb _ _ => idtac
      | Z.eqb _ _ => idtac
      | Qle_bool _ _ => idtac
      | Nat.eqb _ _ => idtac
      | negb ?b => check b
      | true => idtac
      | false => idtac
      | match ?b with true => ?a | false => ?c end
        => check a; check b; check c
      | andb ?a ?b => check a; check b
      | orb ?a ?b => check a; check b
      | (fun (a : ?A) => ?R)
        => let dummy := constr:(fun (a : A) =>
                                  let R' := R in
                                  ltac:(let R'' := (eval cbv beta delta [R'] in R') in
                                        check R'';
                                        exact I)) in
           idtac
      | ?R => precheck R
      end in
  repeat lazymatch goal with
         | [ |- vm_decide_package (Tuple.fieldwiseb _ _ _ = true) ]
           => cbv [vm_decide_package];
              rewrite Tuple.fieldwiseb_fieldwise, <- Tuple.fieldwiseb_fieldwise
                by (intros; autorewrite with dec2bool; apply reflexivity)
         | [ |- vm_decide_package (Forallb _ _ = true) ]
           => cbv [vm_decide_package];
              rewrite Forall_Forallb_iff, <- Forall_Forallb_iff
                by (intros; autorewrite with dec2bool; apply reflexivity)
         | [ H : ?e = true |- vm_decide_package (?R = true) ]
           => check R; dec2bool_split_hyp H; cbv [vm_decide_package]; exact H
         | [ H : ?e = true |- Tuple.fieldwiseb ?R ?t1 ?t2 = true ]
           => check (fun a b => R a b); dec2bool_split_hyp H; cbv [vm_decide_package]; exact H
         | [ H : ?e = true |- Forallb ?R ?ls = true ]
           => check (fun a => R a); dec2bool_split_hyp H; cbv [vm_decide_package]; exact H
         end.
Ltac make_parameter_package_for_vm_decide precheck :=
  premake_parameter_package ();
  unshelve (push_dec_to_hyps precheck);
  exact true.
