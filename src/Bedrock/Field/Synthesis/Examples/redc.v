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
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Local Infix "*" := sep. Local Infix "*" := sep : type_scope.
  
  Import List.
  Import WordByWordMontgomery.

  (* redc_alt ought to take in small arrays A and B, and output an array S *)
  (* S should be between 0 and the prime, and should evaluate mod the prime to the same thing as 
     A * B * R^-1 *)

  (* redc_step ought to take in small arrays B and S, and value a, and output an array S' *)
  (* S' should be small, and should eval to the same as (a * B + S) * R^-1 modulo the prime *)
  
  Fail Instance spec_of_redc_alt : spec_of "redc_alt" := fun functions =>
       forall Astart A Bstart B Sstart len prime r ri t m,
         (* A and B are lists of length len, they correspond to arrays starting at Astart and Bstart respectively *)
         word.unsigned len = Z.of_nat (List.length A) ->
         (array scalar (word.of_Z 8) Astart A m) ->
         word.unsigned len = Z.of_nat (List.length B) ->
         (array scalar (word.of_Z 8) Bstart B m) ->
         (* prime is the modulus; r is the word size; ri is the inverse of r mod prime *)
         (r * @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned ri) ) mod prime = 1 ->
        
        WeakestPrecondition.call functions
          "redc_alt" t m (Astart :: Bstart :: len :: nil )
          (fun t' m' rets => t=t' /\ word.unsigned len = Z.of_nat (List.length rets) /\
                               ( @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned A) *
                                 @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned B) *
                                 @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned ri) ) mod prime =
                                 @eval r (Z.to_nat (word.unsigned len)) (List.map word.unsigned rets) mod prime /\
                                 sep (fun m'' => array scalar (word.of_Z 8) Sstart rets m) (fun m'' => m'' = m) m' ).

(* Error:
Unable to satisfy the following constraints:
In environment:
word : Interface.word 32
mem : map.map word.rep (Init.Byte.byte : Type)
word_ok : word.ok word
mem_ok : map.ok mem
functions : list (prod String.string (prod (prod (list String.string) (list String.string)) cmd))
Astart : word.rep
A : list word.rep
Bstart : word.rep
B : list word.rep
len : word.rep
prime, r : Z
ri : list word.rep
t : trace
m : map.rep
t' : trace
m' : map.rep
rets : list word.rep

?word : "Interface.word ?width"*)
  
End WithParameters.
