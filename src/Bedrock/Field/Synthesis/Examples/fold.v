Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties
  Syntax Semantics BasicC64Semantics ProgramLogic Scalars Array Loops ZnWords.
From bedrock2.Map Require Import Separation SeparationLogic.
Require Import coqutil.Map.Interface.
From coqutil.Word Require Import Interface Properties.

From coqutil.Tactics Require Import Tactics letexists eabstract.
From coqutil.Z Require Import Lia.

Section WithParameters.
  
  Import List.

  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  
  
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

  Context {f: list word -> word -> list word}.

  (* What we aim to show: given a function f from list word -> word -> list word, and given a bedrock
      program that accomplishes that function, we can loop the program as follows to get fold_left f: *)

    Definition loop : func :=
    let body : String.string := "body" in 
    ("loop", (["Astart"; "Alen"; "Bstart"; "Blen"], [], bedrock_func_body:(
    i = $0;       
    while (i < Blen) {
        body ( Astart, Alen, load4(Bstart + $4*i) ); 
        i = i << $1
      }
    ))).

    (* Here is an attempt to write specifications of that idea; both parts fail *)

    Fail Instance spec_of_body : spec_of "body" :=
      fnspec! "body" Astart Alen b / A Ra,
        { requires t m :=
            m =* array scalar (word.of_Z 4) Astart A * Ra /\
              word.unsigned Alen = Z.of_nat (List.length A);
          ensures t' m' := t=t' /\ exists A',
              m' =* array scalar (word.of_Z 4) Astart A' * Ra /\
                A' = f A b
        }.

    Fail Instance spec_of_loop : spec_of "loop" :=
      fnspec! "loop" Astart Alen Bstart Blen / A Ra B Rb,
        {requires t m :=
              m =* array scalar (word.of_Z 4) Astart A * Ra /\
              word.unsigned Alen = Z.of_nat (List.length A) /\
              m =* array scalar (word.of_Z 4) Bstart B * Rb /\  
              word.unsigned Blen = Z.of_nat (List.length B);
          ensures t' m' := t=t' /\ exists A',
              m' =* array scalar (word.of_Z 4) Astart A' * Ra /\
              A' = List.fold_left f A B
        }.

    (* The error messages we get look the same as the one I was running into before, which I solved just by moving
         around parameters blindly until it passed through: *)

   (*Unable to satisfy the following constraints:
      UNDEFINED EVARS:
      ?X94==[word mem word_ok mem_ok f functions Astart Alen Bstart Blen A Ra B Rb t m
                  |- map.map String.string word] (parameter locals of @call) {?locals}
      ?X95==[word mem word_ok mem_ok f functions Astart Alen Bstart Blen A Ra B Rb t m |- ExtSpec]
                  (parameter ext_spec of @call) {?ext_spec}
      ?X97==[word mem word_ok mem_ok f functions Astart Alen Bstart Blen A Ra B Rb {t} {m}
                  |- Bitwidth.Bitwidth 32] (parameter BW of @call) {?BW}
      ?X133==[word mem word_ok mem_ok f functions Astart Alen Bstart Blen A {Ra} {B} {Rb} {t} {m} {t'} {m'}
                   {rets} {A'} |- map.map word Init.Byte.byte] (parameter map of @sep) {?map}
      TYPECLASSES:?X94 ?X95 ?X97 ?X133
      SHELF:
      FUTURE GOALS STACK:?X136 ?X135 ?X134 ?X133 ?X132 ?X131 ?X125 ?X123 ?X119 ?X118 ?X117 ?X116 ?X115       ?X114 ?X113 ?X112 ?X111 ?X110 ?X107 ?X106 ?X105 ?X104 ?X103 ?X97 ?X95 ?X94 ?X89 ?X84 ?X72 ?X70 ?X66 ?X6      5 ?X64?X59 ?X50 ?X48 ?X44 ?X43 ?X42 ?X41 ?X40 ?X39 ?X38 ?X37 ?X36 ?X35 ?X34 ?X33 ?X32) *)

    (* From playing with things, I think in this case the problem is coming from the fact that f is an existential
       variable -- but I'm not really sure why that's a problem. Notably, if we make f a ghost variable instead... *)

    Instance spec_of_body' : spec_of "body'" :=
      fnspec! "body'" Astart Alen b / A Ra f',
        { requires t m :=
            m =* array scalar (word.of_Z 4) Astart A * Ra /\
              word.unsigned Alen = Z.of_nat (List.length A);
          ensures t' m' := t=t' /\ exists A',
              m' =* array scalar (word.of_Z 4) Astart A' * Ra /\
                A' = f' A b
        }.

    (* ... it passes through fine. Is this a necessary part of how bedrock2 works, or am I missing how to use this
     properly? Here, just for record of the behavior, is the similar problem I ran into with my redc specs: *)

    Require Import Crypto.Arithmetic.WordByWordMontgomery.
    Import WordByWordMontgomery.
    Context {prime: Z} (r := 32) {ri : Z}.
    Context {ri_correct: (ri * r) mod prime = 1}.

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

    (* The above spec goes through perfectly fine. But this, slightly different, seemingly also correct version doesn't: *)
    
    Fail Instance spec_of_redc_step : spec_of "redc_step" := 
    fnspec! "redc_step" a Bstart Sstart (len : word) / B (bval: Z) S (sval: Z) R Rb,
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

    (*Instead, it gives the same error message as before. But len definitely /is/ of type word, otherwise we 
       couldn't be doing things like (word.unsigned len), so why should annotating that break things?*)


    
      (*Here's the theorem I would eventually want to prove, if I can sort out these spec problems. I'm pretty 
        sure it would imply rather directly the more specific case of our Montgomery loop. *)
      Fail Theorem loop_ok : 
      program_logic_goal_for_function! loop.
  
End WithParameters.
