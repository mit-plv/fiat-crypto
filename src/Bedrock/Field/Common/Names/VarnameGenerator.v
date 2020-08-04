Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Strings.String.
Local Open Scope string_scope.

Definition unique (gen : nat -> string) : Prop :=
  forall i j, gen i = gen j <-> i = j.
Definition disjoint (gen1 gen2 : nat -> string) : Prop :=
  forall n m, gen1 n <> gen2 m.

Section prefix_generator.
  Context (pre : string).

  Definition prefix_name_gen (x : nat) : string :=
    pre ++ Z.to_string (Z.of_nat x).

  Lemma prefix_name_gen_unique : unique prefix_name_gen.
  Proof.
    cbv [unique]; intros.
    pose proof (Decimal.Z.of_to (Z.of_nat i)).
    pose proof (Decimal.Z.of_to (Z.of_nat j)).
    split; intros; [ | subst; reflexivity ].
    match goal with H : _ |- _ => apply append_eq_r_iff in H end.
    apply Nat2Z.inj. congruence.
  Qed.

  Lemma prefix_name_gen_prefix i :
    prefix pre (prefix_name_gen i) = true.
  Proof.
    apply prefix_correct.
    cbv [prefix_name_gen]; induction pre; intros.
    { cbn [length]. apply substring_0_0. }
    { cbn. congruence. }
  Qed.

  Lemma prefix_name_gen_startswith v i :
    v = prefix_name_gen i ->
    startswith pre v = true.
  Proof.
    intros; subst. cbv [startswith].
    apply eqb_eq. symmetry. apply prefix_correct.
    apply prefix_name_gen_prefix.
  Qed.
End prefix_generator.

Section disjoint.
  Lemma prefix_generator_disjoint pre1 pre2 :
    prefix pre1 pre2 = false ->
    prefix pre2 pre1 = false ->
    disjoint (prefix_name_gen pre1) (prefix_name_gen pre2).
  Proof.
    cbv [disjoint prefix_name_gen]; intros.
    let H := fresh in
    intro H; apply append_eq_prefix in H; destruct H;
      congruence.
  Qed.
End disjoint.

Section defaults.
  Definition default_inname_gen : nat -> string :=
    prefix_name_gen "in".
  Definition default_outname_gen : nat -> string :=
    prefix_name_gen "out".
  Definition default_varname_gen : nat -> string :=
    prefix_name_gen "x".

  Lemma outname_gen_inname_gen_disjoint :
    disjoint default_outname_gen default_inname_gen.
  Proof. apply prefix_generator_disjoint; reflexivity. Qed.
  Lemma inname_gen_varname_gen_disjoint :
    disjoint default_inname_gen default_varname_gen.
  Proof. apply prefix_generator_disjoint; reflexivity. Qed.
  Lemma outname_gen_varname_gen_disjoint :
    disjoint default_outname_gen default_varname_gen.
  Proof. apply prefix_generator_disjoint; reflexivity. Qed.
End defaults.
