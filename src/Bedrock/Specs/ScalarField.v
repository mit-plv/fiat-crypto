Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.NumTheoryUtil.
Local Open Scope Z_scope.

Class ScalarFieldParameters :=
  { (** mathematical parameters **)
    L_pos : positive; (* modulus *)
    L : Z := Z.pos L_pos;
    scalarbits : Z;

    (** function names for bedrock2 **)
    sctestbit : string;
  }.

Class ScalarFieldParameters_ok
      {scalar_field_parameters : ScalarFieldParameters} :=
  { L_prime : Znumtheory.prime L;
    scalarbits_eq : scalarbits = Z.log2_up L;
  }.

Class ScalarRepresentation
      {scalar_field_parameters : ScalarFieldParameters}
      {semantics : Semantics.parameters} :=
  { scalar : Type;
    sceval : scalar -> F L_pos;
    Scalar : word -> scalar -> Semantics.mem -> Prop;
  }.

Section FunctionSpecs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.

  Definition spec_of_sctestbit : spec_of sctestbit :=
    (forall! (x : scalar) (px wi : word)
           (b:=Z.testbit (F.to_Z (sceval x)) (word.unsigned wi)),
        (fun Rr mem =>
           (exists Ra, (Scalar px x * Ra)%sep mem)
           /\ Rr mem)
          ===>
          sctestbit @ [px; wi] returns rets
          ===>
          (liftexists r,
           emp (rets = [r]
                /\ r = word.of_Z (Z.b2z b)))).
End FunctionSpecs.

Section SpecProperties.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}
          {scalar_field_parameters_ok : ScalarFieldParameters_ok}
          {scalar_representation : ScalarRepresentation}.

  Lemma sceval_range k :
    0 <= F.to_Z (sceval k) < 2 ^ scalarbits.
  Proof.
    pose proof (Znumtheory.prime_ge_2 (Z.pos L_pos) L_prime).
    pose proof (@F.to_Z_range L_pos (sceval k) ltac:(lia)).
    pose proof (Z.log2_log2_up_spec (Z.pos L_pos) ltac:(lia)).
    rewrite scalarbits_eq. change L with (Z.pos L_pos). lia.
  Qed.

  Lemma scalarbits_pos : 0 < scalarbits.
  Proof.
    rewrite scalarbits_eq. apply Z.log2_up_pos.
    apply lt_1_p. apply L_prime.
  Qed.
End SpecProperties.
