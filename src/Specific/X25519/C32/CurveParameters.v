Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-19
Base: 25.5
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 10%nat.
  Definition bitwidth : Z := 32.
  Definition s : Z := 2^255.
  Definition c : list limb := [(1, 19)].
  Definition carry_chain1 := Eval vm_compute in Some (seq 0 (pred sz)).
  Definition carry_chain2 := Some [0;1]%nat.

  Definition a24 := 121665%Z.
  Definition coef_div_modulus : nat := 2. (* add 2*modulus before subtracting *)

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz)
    := Some (fun a b =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in_9, in_8, in_7, in_6, in_5, in_4, in_3, in_2, in_1, in_0) := a in
      let '(in2_9, in2_8, in2_7, in2_6, in2_5, in2_4, in2_3, in2_2, in2_1, in2_0) := b in
      dlet output_0 := in2_0 * in_0 in
dlet output_1 :=       in2_0 * in_1 +
                    in2_1 * in_0 in
dlet output_2 :=  2 *  in2_1 * in_1 +
                    in2_0 * in_2 +
                    in2_2 * in_0 in
dlet output_3 :=       in2_1 * in_2 +
                    in2_2 * in_1 +
                    in2_0 * in_3 +
                    in2_3 * in_0 in
dlet output_4 :=       in2_2 * in_2 +
               2 * (in2_1 * in_3 +
                    in2_3 * in_1) +
                    in2_0 * in_4 +
                    in2_4 * in_0 in
dlet output_5 :=       in2_2 * in_3 +
                    in2_3 * in_2 +
                    in2_1 * in_4 +
                    in2_4 * in_1 +
                    in2_0 * in_5 +
                    in2_5 * in_0 in
dlet output_6 :=  2 * (in2_3 * in_3 +
                    in2_1 * in_5 +
                    in2_5 * in_1) +
                    in2_2 * in_4 +
                    in2_4 * in_2 +
                    in2_0 * in_6 +
                    in2_6 * in_0 in
dlet output_7 :=       in2_3 * in_4 +
                    in2_4 * in_3 +
                    in2_2 * in_5 +
                    in2_5 * in_2 +
                    in2_1 * in_6 +
                    in2_6 * in_1 +
                    in2_0 * in_7 +
                    in2_7 * in_0 in
dlet output_8 :=       in2_4 * in_4 +
               2 * (in2_3 * in_5 +
                    in2_5 * in_3 +
                    in2_1 * in_7 +
                    in2_7 * in_1) +
                    in2_2 * in_6 +
                    in2_6 * in_2 +
                    in2_0 * in_8 +
                    in2_8 * in_0 in
dlet output_9 :=       in2_4 * in_5 +
                    in2_5 * in_4 +
                    in2_3 * in_6 +
                    in2_6 * in_3 +
                    in2_2 * in_7 +
                    in2_7 * in_2 +
                    in2_1 * in_8 +
                    in2_8 * in_1 +
                    in2_0 * in_9 +
                    in2_9 * in_0 in
dlet output_10 := 2 * (in2_5 * in_5 +
                    in2_3 * in_7 +
                    in2_7 * in_3 +
                    in2_1 * in_9 +
                    in2_9 * in_1) +
                    in2_4 * in_6 +
                    in2_6 * in_4 +
                    in2_2 * in_8 +
                    in2_8 * in_2 in
dlet output_11 :=      in2_5 * in_6 +
                    in2_6 * in_5 +
                    in2_4 * in_7 +
                    in2_7 * in_4 +
                    in2_3 * in_8 +
                    in2_8 * in_3 +
                    in2_2 * in_9 +
                    in2_9 * in_2 in
dlet output_12 :=      in2_6 * in_6 +
               2 * (in2_5 * in_7 +
                    in2_7 * in_5 +
                    in2_3 * in_9 +
                    in2_9 * in_3) +
                    in2_4 * in_8 +
                    in2_8 * in_4 in
dlet output_13 :=      in2_6 * in_7 +
                    in2_7 * in_6 +
                    in2_5 * in_8 +
                    in2_8 * in_5 +
                    in2_4 * in_9 +
                    in2_9 * in_4 in
dlet output_14 := 2 * (in2_7 * in_7 +
                    in2_5 * in_9 +
                    in2_9 * in_5) +
                    in2_6 * in_8 +
                    in2_8 * in_6 in
dlet output_15 :=      in2_7 * in_8 +
                    in2_8 * in_7 +
                    in2_6 * in_9 +
                    in2_9 * in_6 in
dlet output_16 :=      in2_8 * in_8 +
               2 * (in2_7 * in_9 +
                    in2_9 * in_7) in
dlet output_17 :=      in2_8 * in_9 +
                    in2_9 * in_8 in
dlet output_18 := 2 *  in2_9 * in_9 in
dlet output_8 := output_8 + output_18 << 4 in
dlet output_8 := output_8 + output_18 << 1 in
dlet output_8 := output_8 + output_18 in
dlet output_7 := output_7 + output_17 << 4 in
dlet output_7 := output_7 + output_17 << 1 in
dlet output_7 := output_7 + output_17 in
dlet output_6 := output_6 + output_16 << 4 in
dlet output_6 := output_6 + output_16 << 1 in
dlet output_6 := output_6 + output_16 in
dlet output_5 := output_5 + output_15 << 4 in
dlet output_5 := output_5 + output_15 << 1 in
dlet output_5 := output_5 + output_15 in
dlet output_4 := output_4 + output_14 << 4 in
dlet output_4 := output_4 + output_14 << 1 in
dlet output_4 := output_4 + output_14 in
dlet output_3 := output_3 + output_13 << 4 in
dlet output_3 := output_3 + output_13 << 1 in
dlet output_3 := output_3 + output_13 in
dlet output_2 := output_2 + output_12 << 4 in
dlet output_2 := output_2 + output_12 << 1 in
dlet output_2 := output_2 + output_12 in
dlet output_1 := output_1 + output_11 << 4 in
dlet output_1 := output_1 + output_11 << 1 in
dlet output_1 := output_1 + output_11 in
dlet output_0 := output_0 + output_10 << 4 in
dlet output_0 := output_0 + output_10 << 1 in
dlet output_0 := output_0 + output_10 in
(output_9, output_8, output_7, output_6, output_5, output_4, output_3, output_2, output_1, output_0)
            ).

  Definition square_code : option (Z^sz -> Z^sz)
    := Some (fun a =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in_9, in_8, in_7, in_6, in_5, in_4, in_3, in_2, in_1, in_0) := a in
dlet output_0 :=       in_0 * in_0 in
dlet output_1 :=  2 *  in_0 * in_1 in
dlet output_2 :=  2 * (in_1 * in_1 +
                    in_0 * in_2) in
dlet output_3 :=  2 * (in_1 * in_2 +
                    in_0 * in_3) in
dlet output_4 :=       in_2 * in_2 +
               4 *  in_1 * in_3 +
               2 *  in_0 * in_4 in
dlet output_5 :=  2 * (in_2 * in_3 +
                    in_1 * in_4 +
                    in_0 * in_5) in
dlet output_6 :=  2 * (in_3 * in_3 +
                    in_2 * in_4 +
                    in_0 * in_6 +
               2 *  in_1 * in_5) in
dlet output_7 :=  2 * (in_3 * in_4 +
                    in_2 * in_5 +
                    in_1 * in_6 +
                    in_0 * in_7) in
dlet output_8 :=       in_4 * in_4 +
               2 * (in_2 * in_6 +
                    in_0 * in_8 +
               2 * (in_1 * in_7 +
                    in_3 * in_5)) in
dlet output_9 :=  2 * (in_4 * in_5 +
                    in_3 * in_6 +
                    in_2 * in_7 +
                    in_1 * in_8 +
                    in_0 * in_9) in
dlet output_10 := 2 * (in_5 * in_5 +
                    in_4 * in_6 +
                    in_2 * in_8 +
               2 * (in_3 * in_7 +
                    in_1 * in_9)) in
dlet output_11 := 2 * (in_5 * in_6 +
                    in_4 * in_7 +
                    in_3 * in_8 +
                    in_2 * in_9) in
dlet output_12 :=      in_6 * in_6 +
               2 * (in_4 * in_8 +
               2 * (in_5 * in_7 +
                    in_3 * in_9)) in
dlet output_13 := 2 * (in_6 * in_7 +
                    in_5 * in_8 +
                    in_4 * in_9) in
dlet output_14 := 2 * (in_7 * in_7 +
                    in_6 * in_8 +
               2 *  in_5 * in_9) in
dlet output_15 := 2 * (in_7 * in_8 +
                    in_6 * in_9) in
dlet output_16 :=      in_8 * in_8 +
               4 *  in_7 * in_9 in
dlet output_17 := 2 *  in_8 * in_9 in
dlet output_18 := 2 *  in_9 * in_9 in
dlet output_8 := output_8 + output_18 << 4 in
dlet output_8 := output_8 + output_18 << 1 in
dlet output_8 := output_8 + output_18 in
dlet output_7 := output_7 + output_17 << 4 in
dlet output_7 := output_7 + output_17 << 1 in
dlet output_7 := output_7 + output_17 in
dlet output_6 := output_6 + output_16 << 4 in
dlet output_6 := output_6 + output_16 << 1 in
dlet output_6 := output_6 + output_16 in
dlet output_5 := output_5 + output_15 << 4 in
dlet output_5 := output_5 + output_15 << 1 in
dlet output_5 := output_5 + output_15 in
dlet output_4 := output_4 + output_14 << 4 in
dlet output_4 := output_4 + output_14 << 1 in
dlet output_4 := output_4 + output_14 in
dlet output_3 := output_3 + output_13 << 4 in
dlet output_3 := output_3 + output_13 << 1 in
dlet output_3 := output_3 + output_13 in
dlet output_2 := output_2 + output_12 << 4 in
dlet output_2 := output_2 + output_12 << 1 in
dlet output_2 := output_2 + output_12 in
dlet output_1 := output_1 + output_11 << 4 in
dlet output_1 := output_1 + output_11 << 1 in
dlet output_1 := output_1 + output_11 in
dlet output_0 := output_0 + output_10 << 4 in
dlet output_0 := output_0 + output_10 << 1 in
dlet output_0 := output_0 + output_10 in
(output_9, output_8, output_7, output_6, output_5, output_4, output_3, output_2, output_1, output_0)
            ).

  Definition upper_bound_of_exponent : option (Z -> Z) := None.
  Definition allowable_bit_widths : option (list nat) := None.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := None.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End Curve.
