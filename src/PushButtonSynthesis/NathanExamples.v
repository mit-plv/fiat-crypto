Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.

Require Import Crypto.PushButtonSynthesis.Primitives.
  
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance ToString.C.OutputCAPI.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Existing Instance default_output_options.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : emit_primitives_opt := true.

Context (wordsize := 64 )
  (m := 2^255 - 19)
  (s := 2^Z.log2_up m)
  (n := Z.to_nat (Qceiling (Z.log2_up s / wordsize)))
  (m' := Z.modinv (-m) (2^wordsize)).

Local Notation standard_bounds num:= (Some (saturated_bounds num wordsize)).
  
Local Notation tightest_sat_bounds val := (Some (saturated_bounds (
                                                     Z.to_nat (Qceiling (Z.log2_up (2^Z.log2_up val) / wordsize))
                                                   ) wordsize)).

Definition evalm := Eval cbv in m.
Definition evaln := Eval cbv in n.
Definition evalm' := Eval cbv in m'.

Time Compute
  (Pipeline.BoundsPipeline
     true None [64; 128]
     (ltac:( let r:= Reify(
                        WordByWordMontgomery.mulmod wordsize evaln evalm evalm'
                      ) in
             exact r)
      )
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
            ).

Time Compute
  (Pipeline.BoundsPipelineToString
     "nathantest_" "nathantest_mul_25519"
     true true None [64; 128] wordsize
     (ltac:( let r:= Reify(
                        WordByWordMontgomery.mulmod wordsize evaln evalm evalm'
                      ) in
             exact r)
)
           (fun _ _ => [])
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
            (None, (None, tt))
            None
    : Pipeline.ErrorT _   ).

(* with @ signs
Time Compute
  (Pipeline.BoundsPipeline
     true None [64; 128]
     (ltac:( let r:= Reify(
                        WordByWordMontgomery.mulmod
                      ) in
             exact r) @ GallinaReify.Reify(wordsize)
                            @ GallinaReify.Reify(n)
                            @ GallinaReify.Reify(m)
                            @ GallinaReify.Reify(m') )
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
  ).

Time Compute
  (Pipeline.BoundsPipelineToString
     "nathantest_" "nathantest_mul_25519"
     true true None [64; 128] wordsize
     (ltac:( let r:= Reify(
                        WordByWordMontgomery.mulmod
                      ) in
             exact r)
                            @ GallinaReify.Reify(wordsize)
                            @ GallinaReify.Reify(n)
                            @ GallinaReify.Reify(m)
                            @ GallinaReify.Reify(m') )
           (fun _ _ => [])
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
            (None, (None, tt))
            None
    : Pipeline.ErrorT _   ).
 *)

(*trying this the alternate way in PushButtonSynthesis*)
(*
Time Definition multree := (Pipeline.BoundsPipeline
     true None [64; 128]
     (ltac:( let r:= Reify(
                        WordByWordMontgomery.mulmod
                      ) in
             exact r) @ GallinaReify.Reify(wordsize)
                            @ GallinaReify.Reify(n)
                            @ GallinaReify.Reify(m)
                            @ GallinaReify.Reify(m') )
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
  ).

Fail Eval cbv beta in
        FromPipelineToString!
          wordsize "MEAP" "mul" multree
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " whyyyyyyyyyyyyyy."]%string)
             (mul_correct wordsize n m WordByWordMontgomery.valid (WordByWordMontgomery.from_montgomerymod wordsize n m m'))).
*)

(*synthesizing code for redc*)

Check WordByWordMontgomery.redc_body.
(*redc_body needs Z, nat, list Z, list Z, Z, nat*)
(*in the arithmetic file, these are the things corresponding to the names lgr, k, R_numlimbs, N, B, and pred_A_numlimbs in some order i think*)
Print WordByWordMontgomery.redc_body.
(*order appears to be lgr, R_numlimbs, N, B, k, pred_A_numlimbs?*)
Print WordByWordMontgomery.redc.
Print WordByWordMontgomery.mulmod.
Context (B: list Z).
Definition N := Partition.Partition.partition (UniformWeight.uweight wordsize) n m.
Check N.
Definition evalN := Eval cbv in N.
(*
  Definition mulmod (a b : list Z) : list Z := @redc bitwidth n m_enc n a b m'.
   lgr, R_numlimbs, N, A_numlimbs, A, B, k *)

Definition B_test : list Z := (1233777779335::614233244556::4242424242::nil).


Check WordByWordMontgomery.redc. (*Z, nat, list Z, nat, list Z, list Z, Z,*)
Print WordByWordMontgomery.redc.
(* lgr, R_numlimbs, N, A_numlimbs, A, B, k*)
Print WordByWordMontgomery.mulmod.
(*bitwidth, n, m, m' a b*)
(*WordByWordMontgomery.redc bitwidth n m_enc n a b m'*)

Time Compute
  (Pipeline.BoundsPipeline
     true None [64; 128]
     (ltac:( let r:= Reify(
                        fun A B => WordByWordMontgomery.redc wordsize evaln evalN (length A) A B evalm'
                      ) in
             exact r)
      )
            (standard_bounds n, (standard_bounds n, tt))
            (standard_bounds n)
            ).

Time Compute
  (Pipeline.BoundsPipelineToString
     "nathantest_" "nathantest_redc_25519"
     true true None [64; 128] wordsize
     (ltac:( let r:= Reify(
                        fun A B => WordByWordMontgomery.redc wordsize evaln evalN (length A) A B evalm'
                      ) in
             exact r)
)
           (fun _ _ => [])
            (standard_bounds (7), (standard_bounds (n), tt))
            (standard_bounds n)
            (None, (None, tt))
            None
    : Pipeline.ErrorT _   ).


(*stepping through a small redc loop*)
Time Compute WordByWordMontgomery.redc_body wordsize evaln evalN [0;0;3;2;0] evalm' ([1;2;3], [0;0;0;0;0]).
Time Compute WordByWordMontgomery.redc_body wordsize evaln evalN [0;0;3;2;0] evalm' ([2; 3], [0;3;2;0;0]).
Time Compute WordByWordMontgomery.redc_body wordsize evaln evalN [0;0;3;2;0] evalm' ([3], [3;8;4;0;0]).
Time Compute Rows.conditional_sub (fun n => 2^(n*wordsize)) _ [18446744073709551613; 12; 9223372036854775814; 5339846968705396520; 0] evalN.
(*bricks my computer -- idk why
Time Compute WordByWordMontgomery.redc wordsize evaln evalN _ [1;2;3] [0;0;3;2;0] evalm'. *)
Time Compute WordByWordMontgomery.redc wordsize evaln evalN 3 [1;2;3] [0;0;3;2;0] evalm'.

(*lets try to synthesize code for a single montgomery step*)

Definition big_bound := Some r[0 ~> 99999999999999999999999999999999999999999999999]%zrange.

(*
Time Compute
  (Pipeline.BoundsPipeline
     true None [64;128]
     (ltac:( let r:= Reify(
      fun B => @WordByWordMontgomery.redc_body wordsize evaln evalN B evalm'
                       ) in exact r))
       (Some [Some r[0 ~> 5]%zrange; Some r[0~>5]%zrange], (Some 1%nat, (Some [Some r[0 ~> 5]%zrange; Some r[0~>5]%zrange], Some [Some r[0 ~> 5]%zrange; Some r[0~>5]%zrange], tt)))
       (*(None, None)*)
       (Some
               (repeat big_bound 10),
            Some
               (repeat big_bound 10))
    ).
 *)

Check @WordByWordMontgomery.redc_body.

Definition singl_redc := fun S A B => @WordByWordMontgomery.redc_body wordsize evaln evalN B evalm' (pred (length A)) (A, S).
Definition predA_numlimbs := 4%nat.

Time Compute
  (Pipeline.BoundsPipeline
     true None [64;128]
     (ltac:( let r:= Reify(
                         singl_redc
                       ) in exact r))

     (standard_bounds n, (standard_bounds (S predA_numlimbs), (standard_bounds n, tt)))
       (standard_bounds predA_numlimbs, standard_bounds n)
    ).

Time Compute
  (Pipeline.BoundsPipelineToString
     "nathantest_" "nathantest_one_redc_25519_5to4"
     true true None [64; 128] wordsize
     (ltac:( let r:= Reify( singl_redc ) in exact r))
           (fun _ _ => [])
            (standard_bounds n, (standard_bounds (S predA_numlimbs), (standard_bounds n, tt)))
            (standard_bounds predA_numlimbs,  standard_bounds n)
            (None, (None, (None, tt)))
            (None, None)
    : Pipeline.ErrorT _   ).

(*
   Local Existing Instance Compilers.ToString.C.OutputCAPI.
    Local Instance : widen_carry_opt := true.
    Local Instance : unfold_value_barrier_opt := true.
    Local Instance : should_split_multiret_opt := true.
    Local Instance : should_split_mul_opt := true.
    Local Instance : no_select_opt := true.
    Local Instance : only_signed_opt := false.
    Local Existing Instance default_low_level_rewriter_method.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := false.
    Local Instance : inline_opt := false.
    Local Instance : inline_internal_opt := false.
    Local Existing Instance AbstractInterpretation.default_Options.
    Local Existing Instance default_documentation_options.
    Local Existing Instance default_output_options.
    Local Existing Instance default_language_naming_conventions.

*)
