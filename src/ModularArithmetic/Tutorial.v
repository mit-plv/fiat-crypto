Require Import BinInt Zpower ZArith Znumtheory.
Require Import Spec.ModularArithmetic ModularArithmetic.PrimeFieldTheorems.


(* Example for modular arithmetic with a concrete modulus in a section *)
Section Mod24.
  (* Set notations + - * / refer to F operations *)
  Local Open Scope F_scope.

  (* Specify modulus *)
  Let q := 24.
  
  (* Boilerplate for letting Z numbers be interpreted as field elements *)
  Local Coercion ZToFq := ZToField : BinNums.Z -> F q. Hint Unfold ZToFq.

  (* Boilerplate for [ring]. Similar boilerplate works for [field] if
  the modulus is prime . *)
  Add Ring Fring_q : (@Fring_theory q)
    (morphism (@Fring_morph q),
     preprocess [unfold ZToFq; Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Lemma sumOfSquares : forall a b: F q, (a+b)^2 = a^2 + ZToField 2*a*b + b^2.
  Proof.
    intros.
    ring.
  Qed.
End Mod24.

(* Example for modular arithmetic with an abstract modulus in a section *)
Section Modq.
  Context {q:Z} {prime_q:prime q}.
  Existing Instance prime_q.

  (* Set notations + - * / refer to F operations *)
  Local Open Scope F_scope.
  
  (* Boilerplate for letting Z numbers be interpreted as field elements *)
  Local Coercion ZToFq := ZToField : BinNums.Z -> F q. Hint Unfold ZToFq.

  (* Boilerplate for [field]. Similar boilerplate works for [ring] if
  the modulus is not prime . *)
  Add Field Ffield_q' : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [unfold ZToFq; Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Lemma sumOfSquares' : forall a b: F q, (a+b)^2 = a^2 + ZToField 2*a*b + b^2.
  Proof.
    intros.
    field.
  Qed.
End Modq.

(*** The old way: Modules ***)

Module Modulus31 <: PrimeModulus.
  Definition modulus := 2^5 - 1.
  Lemma prime_modulus : prime modulus.
  Admitted.
End Modulus31.

Module Modulus127 <: PrimeModulus.
  Definition modulus := 2^127 - 1.
  Lemma prime_modulus : prime modulus.
  Admitted.
End Modulus127.

Module Example31.
  (* Then we can construct a field with that modulus *)
  Module Import Field := FieldModulo Modulus31.
  Import Modulus31.

  (* And pull in the appropriate notations *)
  Local Open Scope F_scope.

  (* First, let's solve a ring example*)
  Lemma ring_example: forall x: F modulus, x * (ZToField 2) = x + x.
  Proof.
    intros.
    ring.
  Qed.

  (* Unfortunately, the [ring] and [field] tactics need syntactic
    (not definitional) equality to recognize the ring in question.
    Therefore, it is necessary to explicitly rewrite the modulus
    (usually hidden by implicitn arguments) match the one passed to
    [FieldModulo]. *)
  Lemma ring_example': forall x: F (2^5-1), x * (ZToField 2) = x + x.
  Proof.
    intros.
    change (2^5-1)%Z with modulus.
    ring.
  Qed.

  (* Then a field example (we have to know we can't divide by zero!) *)
  Lemma field_example: forall x y z: F modulus, z <> 0 ->
    x * (y / z) / z = x * y / (z ^ 2).
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

  (* Then an example with exponentiation *)
  Lemma exp_example: forall x: F modulus, x ^ 2 + ZToField 2 * x + 1 = (x + 1) ^ 2.
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

  (* In general, the rule I've been using is:

     - If our goal looks like x = y:

        + If we need to use assumptions to prove the goal, then before
          we apply field,

          * Perform all relevant substitutions (especially subst)

          * If we have something more complex, we're probably going
            to have to performe some sequence of "replace X with Y"
            and solve out the subgoals manually before we can use
            field.

        + Else, just use field directly

     - If we just want to simplify terms and put them into a canonical
       form, then field_simplify or ring_simplify should do the trick.
       Note, however, that the canonical form has lots of annoying "/1"s

     - Otherwise, do a "replace X with Y" to generate an equality
       so that we can use field in the above case

     *)

End Example31.

(* Notice that the field tactics work whether we know what the modulus is *)
Module TimesZeroTransparentTestModule.
  Module Import Theory := FieldModulo Modulus127.
  Import Modulus127.
  Local Open Scope F_scope.

  Lemma timesZero : forall a : F modulus, a*0 = 0.
    intros.
    field.
  Qed.
End TimesZeroTransparentTestModule.

(* Or if we don't (i.e. it's opaque) *)
Module TimesZeroParametricTestModule (M: PrimeModulus).
  Module Theory := FieldModulo M.
  Import Theory M.
  Local Open Scope F_scope.

  Lemma timesZero : forall a : F modulus, a*0 = 0.
    intros.
    field.
  Qed.

  Lemma realisticFraction : forall x y d : F modulus, (x * 1 + y * 0) / (1 + d * x * 0 * y * 1) = x.
  Proof.
    intros.
    field; try exact Fq_1_neq_0.
  Qed.

  Lemma biggerFraction : forall XP YP ZP TP XQ YQ ZQ TQ d : F modulus, 
   ZQ <> 0 ->
   ZP <> 0 ->
   ZP * ZQ * ZP * ZQ + d * XP * XQ * YP * YQ <> 0 ->
   ZP * ZToField 2 * ZQ * (ZP * ZQ) + XP * YP * ZToField 2 * d * (XQ * YQ) <> 0 ->
   ZP * ZToField 2 * ZQ * (ZP * ZQ) - XP * YP * ZToField 2 * d * (XQ * YQ) <> 0 ->

   ((YP + XP) * (YQ + XQ) - (YP - XP) * (YQ - XQ)) *
   (ZP * ZToField 2 * ZQ - XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ)) /
   ((ZP * ZToField 2 * ZQ - XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ)) *
    (ZP * ZToField 2 * ZQ + XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ))) =
   (XP / ZP * (YQ / ZQ) + YP / ZP * (XQ / ZQ)) / (1 + d * (XP / ZP) * (XQ / ZQ) * (YP / ZP) * (YQ / ZQ)).
  Proof.
    intros.
    field; assumption.
  Qed.
End TimesZeroParametricTestModule.

