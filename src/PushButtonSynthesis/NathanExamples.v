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

(*synthesizing mulmod*)

Context (wordsize := 64 )
  (m := 2^255 - 19)
  (s := 2^Z.log2_up m)
  (n := Z.to_nat (Qceiling (Z.log2_up s / wordsize)))
  (m' := Z.modinv (-m) (2^wordsize)).

Local Notation standard_bounds num:= (Some (saturated_bounds num wordsize)).

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

(*synthesizing redc*)

Definition N := Partition.Partition.partition (UniformWeight.uweight wordsize) n m.
Definition evalN := Eval cbv in N.

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
(*same loop all at once *)
Time Compute WordByWordMontgomery.redc wordsize evaln evalN 3 [1;2;3] [0;0;3;2;0] evalm'.

(*synthesizing code for a single Montgomery step*)

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
