Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
From bedrock2 Require Import BasicC64Semantics.

Require bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Tactics.Tactics.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars bedrock2.Array bedrock2.Loops.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.ZnWords.

Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Import ZArith.
Require Import coqutil.Z.Lia.

Require Import Crypto.Arithmetic.WordByWordMontgomery.

Section WithParameters.
  
  Import List.
  Import WordByWordMontgomery.
  
  Context {prime: Z} (r := 32) {ri : Z}.
  Context {ri_correct: (ri * r) mod prime = 1}.
  (* prime is the modulus; r is the word size; ri is the inverse of r mod prime *)
  Context {word: word.word r} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
 
  (* Old notation:

  Local Infix "*" := sep. Local Infix "*" := sep : type_scope.

  Fail Instance spec_of_redc_alt : spec_of "redc_alt" := fun functions =>
       forall Astart A Bstart B Sstart S (len: word) t m R,
         (* A and B are lists of length len, they correspond to arrays starting at Astart and Bstart respectively *)
         word.unsigned len = Z.of_nat (List.length A) ->
         (array scalar (word.of_Z 8) Astart A m) ->
         word.unsigned len = Z.of_nat (List.length B) ->
         (array scalar (word.of_Z 8) Bstart B m) ->
         word.unsigned len = Z.of_nat (List.length S) ->
         (array scalar (word.of_Z 8) Sstart S * R)%sep m ->
         
        WeakestPrecondition.call functions
          "redc_alt" t m (Astart :: Bstart :: len :: nil )
          (fun t' m' rets => t=t' /\ word.unsigned len = Z.of_nat (List.length rets) /\
                               ( @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) *
                                 @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) *
                                  ri ) mod prime =
                                 @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned rets) mod prime /\
                               (array scalar (word.of_Z 8) Sstart rets * R )%sep m' ).
*)
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

  (* redc_alt ought to take in small arrays A and B, and output an array S *)
  (* S should be small, and should evaluate mod the prime to the same thing as 
     A * B * R^-1 *)
  
  Fail Instance spec_of_redc_alt : spec_of "redc_alt" :=
    fnspec! "redc_alt" Astart Bstart Sstart (len: word) / A (aval: Z) B (bval: Z) S Ra Rb R,
    { requires t m :=
        m =* array scalar (word.of_Z 8) Astart A * Ra /\
        m =* array scalar (word.of_Z 4) Bstart B * Rb /\
        m =* array scalar (word.of_Z 4) Sstart S * R /\
        word.unsigned len = Z.of_nat (List.length A)  /\
        word.unsigned len = Z.of_nat (List.length B)  /\
        word.unsigned len = Z.of_nat (List.length S) /\
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) = aval /\
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval;                                       
      ensures t' m' := t=t' /\ exists S',
          m' =* array scalar (word.of_Z 4) Sstart S' * R /\
          ( aval * bval * ri ) mod prime =
            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
    }.

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * R^-1 modulo the prime *)
  
  Fail Instance spec_of_redc_step : spec_of "redc_step" := 
    fnspec! "redc_step" a Bstart Sstart (len: word) / B (bval: Z) S (sval: Z) R Rb,
      { requires t m :=
          m =* array scalar (word.of_Z 4) Bstart B * Rb /\
          m =* array scalar (word.of_Z 4) Sstart S * R /\
          word.unsigned len = Z.of_nat (List.length B) /\
          word.unsigned len = Z.of_nat (List.length S) /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) = sval;
        ensures t' m' := t=t' /\ exists S',
            m' =* array scalar (word.of_Z 4) Sstart S' * R /\
              ((word.unsigned a) * bval * ri + sval) mod prime =
                @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
      }.
  
  
End WithParameters.
