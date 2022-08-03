Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties
  Syntax Semantics BasicC64Semantics ProgramLogic Scalars Array Loops ZnWords.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import coqutil.Map.Interface.
From coqutil.Word Require Import Interface Properties.

From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import Coq.ZArith.ZArith.
From coqutil.Z Require Import div_mod_to_equations Lia.

Require Import Crypto.Arithmetic.WordByWordMontgomery.

Section WithParameters.
  
  Import List.
  Import WordByWordMontgomery.
  
  Context {prime: Z} (r := 32) {ri : Z}.
  Context {ri_correct: (ri * r) mod prime = 1}.
  (* prime is the modulus; r is the word size; ri is the inverse of r mod prime *)
  Context {word: word.word r} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

  (* redc_alt ought to take in small arrays A and B, and output an array S *)
  (* S should be small, and should evaluate mod the prime to the same thing as 
     A * B * R^-1 *)
  
  Instance spec_of_redc_alt : spec_of "redc_alt" :=
    fnspec! "redc_alt" Astart Bstart Sstart len / A (aval: Z) B (bval: Z) S Ra Rb R,
    { requires t m :=
        m =* array scalar (word.of_Z 4) Astart A * Ra /\
        m =* array scalar (word.of_Z 4) Bstart B * Rb /\
        m =* array scalar (word.of_Z 4) Sstart S * R /\
        word.unsigned len = Z.of_nat (List.length A)  /\
        word.unsigned len = Z.of_nat (List.length B)  /\
        word.unsigned len = Z.of_nat (List.length S) /\
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) = aval /\ 
        @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval;                                       
      ensures t' m' :=  t=t' /\ exists S', 
          m' =* array scalar (word.of_Z 4) Sstart S' * R /\
          ( aval * bval * ri ) mod prime =
            @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
    }.

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * R^-1 modulo the prime *)
  
  Instance spec_of_redc_step : spec_of "redc_step" := 
    fnspec! "redc_step" a Bstart Sstart len / B (bval: Z) S (sval: Z) R Rb,
      { requires t m :=
          m =* array scalar (word.of_Z 4) Bstart B * Rb /\
          m =* array scalar (word.of_Z 4) Sstart S * R /\
          word.unsigned len = Z.of_nat (List.length B) /\
          word.unsigned len = Z.of_nat (List.length S) /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) = bval /\
          @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S) = sval;
        ensures t' m' := t=t' /\ exists S',
            m' =* array scalar (word.of_Z 4) Sstart S' * R /\
              ((word.unsigned a) * bval + sval) * ri mod prime =
                @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
      }.  
  
  Definition redc_alt : func :=
    let redc_step : String.string := "redc_step" in 
    ("redc_alt", (["Astart"; "Bstart"; "Sstart"; "len"], [], bedrock_func_body:(
    i = $0;
    while (i < len) { 
         store4(Sstart + $4*i, $0);
         i = i << $1          
    };
    i = $0;       
    while (i < len) {
        redc_step ( load4(Astart + $4*i), Bstart, Sstart, len );
        i = i << $1
      }
    ))).
  
  Section OuterLoop.
    
    Context {redc_step_body : cmd}.
    Definition redc_step : func
      := ("redc_step", (["a"; "Bstart"; "Sstart"; "len"], [],  redc_step_body  )).
    Fail Context {redc_step_ok : program_logic_goal_for_function! redc_step}.
             (* "No matching clauses for match." *)
    
    Theorem redc_alt_ok :
      program_logic_goal_for_function! redc_alt.
    Proof. Admitted. 
    
  End OuterLoop.
  
End WithParameters.
