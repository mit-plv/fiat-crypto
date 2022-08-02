Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties
  Semantics BasicC64Semantics ProgramLogic Scalars Array Loops ZnWords.
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
  
  Fail Instance spec_of_redc_alt : spec_of "redc_alt" :=
    fnspec! "redc_alt" Astart Bstart Sstart (len: word) / A (aval: Z) B (bval: Z) S Ra Rb R,
    { requires t m :=
        m =* array scalar (word.of_Z 4) Astart A * Ra /\
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
              ((word.unsigned a) * bval + sval) * ri mod prime =
                @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned S') mod prime
      }.
  
  
End WithParameters.

(*   
The command has indeed failed with message:
Unable to satisfy the following constraints:
UNDEFINED EVARS:
 ?X106==[prime (r:=32) ri ri_correct word mem word_ok mem_ok functions Astart Bstart Sstart len A aval B
          bval S Ra Rb R t m |- map.map String.string word.rep] (parameter locals of @call) {?locals}
 ?X107==[prime (r:=32) ri ri_correct word mem word_ok mem_ok functions Astart Bstart Sstart len A aval B
          bval S Ra Rb R t m |- ExtSpec] (parameter ext_spec of @call) {?ext_spec}
 ?X109==[prime (r:=32) ri ri_correct word mem word_ok mem_ok functions Astart Bstart Sstart len A aval B
          bval S Ra Rb R {t} {m} |- Bitwidth.Bitwidth r] (parameter BW of @call) {?BW}
 ?X141==[prime (r:=32) ri ri_correct word mem word_ok mem_ok functions Astart Bstart Sstart len A aval B
          bval S {Ra} {Rb} {R} {t} {m} {t'} {m'} {rets} {S'} |- map.map word.rep Init.Byte.byte]
          (parameter map of @sep) {?map}
TYPECLASSES:?X106 ?X107 ?X109 ?X141
SHELF:
FUTURE GOALS STACK:?X148 ?X147 ?X146 ?X145 ?X144 ?X143 ?X142 ?X141 ?X135 ?X133 ?X132 ?X131 ?X129 ?X128
?X127 ?X126 ?X125 ?X124 ?X123 ?X122 ?X121 ?X120 ?X119 ?X118 ?X117 ?X116 ?X115 ?X113 ?X112 ?X109 ?X107
?X106 ?X97 ?X96 ?X95 ?X94 ?X93 ?X88 ?X87 ?X86 ?X85 ?X84 ?X83 ?X82 ?X81 ?X80 ?X79 ?X78 ?X77 ?X76 ?X75 ?X74
?X73 ?X72 ?X60 ?X58 ?X54 ?X53 ?X41 ?X39 ?X35 ?X34 ?X25 ?X23 ?X19 ?X18 ?X17 ?X16 ?X15 ?X14 ?X13 ?X12 ?X11
?X10 ?X9 ?X8 ?X7 ?X6
*)
