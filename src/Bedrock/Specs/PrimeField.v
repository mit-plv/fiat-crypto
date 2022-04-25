Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Section PrimeField.

Class PrimeFieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : F M_pos; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

    (* special wrapper for copy so that compilation lemmas can recognize it *)
    fe_copy := (@id (F M_pos));

    (** function names **)
    mul : string; add : string; sub : string; opp : string;
    square : string; scmula24 : string; inv : string;
    from_bytes : string; to_bytes : string;
    select_znz : string;

    felem_copy : string;
    from_word : string;
  }.

  Class PrimeFieldParameters_ok {field_parameters : PrimeFieldParameters} := {
    M_prime : Znumtheory.prime M
  }.

  Section Specialized.
    Context {params : PrimeFieldParameters}
            {params_ok : @PrimeFieldParameters_ok params}
            {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.

    Instance Field : (@field (F M_pos) (@eq (F M_pos)) (F.zero) (F.one) F.opp F.add F.sub F.mul F.inv F.div).
    Proof.
      exact (@F.field_modulo M_pos M_prime).
    Defined.

    Instance prime_field_parameters : FieldParameters.
    Proof.
      econstructor.
        - exact (@F.zero M_pos).
        - exact (@F.one M_pos).
        - exact (@F.opp M_pos).
        - exact (@F.inv M_pos).
        - exact (@F.add M_pos).
        - exact (@F.sub M_pos).
        - exact (@F.mul M_pos).
        - exact (@F.div M_pos).
        - apply F.eq_dec.
        - exact (a24).
        - exact mul.
        - exact add.
        - exact sub.
        - exact opp.
        - exact square.
        - exact scmula24.
        - exact inv.
        - exact from_bytes.
        - exact to_bytes.
        - exact select_znz.
        - exact felem_copy.
        - exact from_word.
    Defined. 

    Instance prime_field_parameters_ok : @AbstractField.FieldParameters_ok prime_field_parameters.
    Proof.
      constructor. apply Field.
    Defined.

    Context {locals : map.map string word}
            {ext_spec : bedrock2.Semantics.ExtSpec}
            {field_representation : FieldRepresentation}
            {field_representation_ok : FieldRepresentation_ok}.
      
    Instance spec_of_from_word : spec_of from_word :=
      fnspec! from_word (pout x : word) / out R,
      { requires tr mem0 :=
          (FElem pout out * R)%sep mem0;
        ensures tr' mem' :=
          tr = tr' /\
          exists X, feval X = F.of_Z _ (word.unsigned x)
              /\ bounded_by tight_bounds X
              /\ (FElem pout X * R)%sep mem' }.

    (* Parameters for word-by-word Montgomery arithmetic*)
      Definition r := 2 ^ width.
      Definition m' := Z.modinv (- M) r.
      Definition r' := Z.modinv (r) M.
    
      Definition from_mont_model x := F.mul x (@F.of_Z M_pos (r' ^ (Z.of_nat felem_size_in_words)%Z)).
      Definition to_mont_model x := F.mul x (@F.of_Z M_pos (r ^ (Z.of_nat felem_size_in_words)%Z)).
    
      Instance un_from_mont {from_mont : string} : UnOp from_mont :=
        {| un_model := from_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
    
      Instance un_to_mont {to_mont : string} : UnOp to_mont :=
        {| un_model := to_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds|}.

  End Specialized.
End PrimeField.
