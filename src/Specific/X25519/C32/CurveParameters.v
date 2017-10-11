Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-19
Base: 25.5
***)

Definition curve : CurveParameters :=
  {|
    sz := 10%nat;
    bitwidth := 32;
    s := 2^255;
    c := [(1, 19)];
    carry_chains := Some [seq 0 (pred 10); [0; 1]]%nat;

    a24 := Some 121665;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some false;
    montgomery := false;

    mul_code := Some (fun a b =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in9, in8, in7, in6, in5, in4, in3, in2, in1, in0) := a in
      let '(in29, in28, in27, in26, in25, in24, in23, in22, in21, in20) := b in
      dlet output0 :=       in20 * in0 in
      dlet output1 :=       in20 * in1 +
                            in21 * in0 in
      dlet output2 :=  2 *  in21 * in1 +
                            in20 * in2 +
                            in22 * in0 in
      dlet output3 :=       in21 * in2 +
                            in22 * in1 +
                            in20 * in3 +
                            in23 * in0 in
      dlet output4 :=       in22 * in2 +
                       2 * (in21 * in3 +
                            in23 * in1) +
                            in20 * in4 +
                            in24 * in0 in
      dlet output5 :=       in22 * in3 +
                            in23 * in2 +
                            in21 * in4 +
                            in24 * in1 +
                            in20 * in5 +
                            in25 * in0 in
      dlet output6 :=  2 * (in23 * in3 +
                            in21 * in5 +
                            in25 * in1) +
                            in22 * in4 +
                            in24 * in2 +
                            in20 * in6 +
                            in26 * in0 in
      dlet output7 :=       in23 * in4 +
                            in24 * in3 +
                            in22 * in5 +
                            in25 * in2 +
                            in21 * in6 +
                            in26 * in1 +
                            in20 * in7 +
                            in27 * in0 in
      dlet output8 :=       in24 * in4 +
                       2 * (in23 * in5 +
                            in25 * in3 +
                            in21 * in7 +
                            in27 * in1) +
                            in22 * in6 +
                            in26 * in2 +
                            in20 * in8 +
                            in28 * in0 in
      dlet output9 :=       in24 * in5 +
                            in25 * in4 +
                            in23 * in6 +
                            in26 * in3 +
                            in22 * in7 +
                            in27 * in2 +
                            in21 * in8 +
                            in28 * in1 +
                            in20 * in9 +
                            in29 * in0 in
      dlet output10 := 2 * (in25 * in5 +
                            in23 * in7 +
                            in27 * in3 +
                            in21 * in9 +
                            in29 * in1) +
                            in24 * in6 +
                            in26 * in4 +
                            in22 * in8 +
                            in28 * in2 in
      dlet output11 :=      in25 * in6 +
                            in26 * in5 +
                            in24 * in7 +
                            in27 * in4 +
                            in23 * in8 +
                            in28 * in3 +
                            in22 * in9 +
                            in29 * in2 in
      dlet output12 :=      in26 * in6 +
                       2 * (in25 * in7 +
                            in27 * in5 +
                            in23 * in9 +
                            in29 * in3) +
                            in24 * in8 +
                            in28 * in4 in
      dlet output13 :=      in26 * in7 +
                            in27 * in6 +
                            in25 * in8 +
                            in28 * in5 +
                            in24 * in9 +
                            in29 * in4 in
      dlet output14 := 2 * (in27 * in7 +
                            in25 * in9 +
                            in29 * in5) +
                            in26 * in8 +
                            in28 * in6 in
      dlet output15 :=      in27 * in8 +
                            in28 * in7 +
                            in26 * in9 +
                            in29 * in6 in
      dlet output16 :=      in28 * in8 +
                       2 * (in27 * in9 +
                            in29 * in7) in
      dlet output17 :=      in28 * in9 +
                            in29 * in8 in
      dlet output18 := 2 *  in29 * in9 in
      dlet output8 := output8 + output18 << 4 in
      dlet output8 := output8 + output18 << 1 in
      dlet output8 := output8 + output18 in
      dlet output7 := output7 + output17 << 4 in
      dlet output7 := output7 + output17 << 1 in
      dlet output7 := output7 + output17 in
      dlet output6 := output6 + output16 << 4 in
      dlet output6 := output6 + output16 << 1 in
      dlet output6 := output6 + output16 in
      dlet output5 := output5 + output15 << 4 in
      dlet output5 := output5 + output15 << 1 in
      dlet output5 := output5 + output15 in
      dlet output4 := output4 + output14 << 4 in
      dlet output4 := output4 + output14 << 1 in
      dlet output4 := output4 + output14 in
      dlet output3 := output3 + output13 << 4 in
      dlet output3 := output3 + output13 << 1 in
      dlet output3 := output3 + output13 in
      dlet output2 := output2 + output12 << 4 in
      dlet output2 := output2 + output12 << 1 in
      dlet output2 := output2 + output12 in
      dlet output1 := output1 + output11 << 4 in
      dlet output1 := output1 + output11 << 1 in
      dlet output1 := output1 + output11 in
      dlet output0 := output0 + output10 << 4 in
      dlet output0 := output0 + output10 << 1 in
      dlet output0 := output0 + output10 in
      (output9, output8, output7, output6, output5, output4, output3, output2, output1, output0)
            );

    square_code := Some (fun a =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in9, in8, in7, in6, in5, in4, in3, in2, in1, in0) := a in
      dlet output0 :=       in0 * in0 in
      dlet output1 :=  2 *  in0 * in1 in
      dlet output2 :=  2 * (in1 * in1 +
                            in0 * in2) in
      dlet output3 :=  2 * (in1 * in2 +
                            in0 * in3) in
      dlet output4 :=       in2 * in2 +
                       4 *  in1 * in3 +
                       2 *  in0 * in4 in
      dlet output5 :=  2 * (in2 * in3 +
                            in1 * in4 +
                            in0 * in5) in
      dlet output6 :=  2 * (in3 * in3 +
                            in2 * in4 +
                            in0 * in6 +
                       2 *  in1 * in5) in
      dlet output7 :=  2 * (in3 * in4 +
                            in2 * in5 +
                            in1 * in6 +
                            in0 * in7) in
      dlet output8 :=       in4 * in4 +
                       2 * (in2 * in6 +
                            in0 * in8 +
                       2 * (in1 * in7 +
                            in3 * in5)) in
      dlet output9 :=  2 * (in4 * in5 +
                            in3 * in6 +
                            in2 * in7 +
                            in1 * in8 +
                            in0 * in9) in
      dlet output10 := 2 * (in5 * in5 +
                            in4 * in6 +
                            in2 * in8 +
                       2 * (in3 * in7 +
                            in1 * in9)) in
      dlet output11 := 2 * (in5 * in6 +
                            in4 * in7 +
                            in3 * in8 +
                            in2 * in9) in
      dlet output12 :=      in6 * in6 +
                       2 * (in4 * in8 +
                       2 * (in5 * in7 +
                            in3 * in9)) in
      dlet output13 := 2 * (in6 * in7 +
                            in5 * in8 +
                            in4 * in9) in
      dlet output14 := 2 * (in7 * in7 +
                            in6 * in8 +
                       2 *  in5 * in9) in
      dlet output15 := 2 * (in7 * in8 +
                            in6 * in9) in
      dlet output16 :=      in8 * in8 +
                       4 *  in7 * in9 in
      dlet output17 := 2 *  in8 * in9 in
      dlet output18 := 2 *  in9 * in9 in
      dlet output8 := output8 + output18 << 4 in
      dlet output8 := output8 + output18 << 1 in
      dlet output8 := output8 + output18 in
      dlet output7 := output7 + output17 << 4 in
      dlet output7 := output7 + output17 << 1 in
      dlet output7 := output7 + output17 in
      dlet output6 := output6 + output16 << 4 in
      dlet output6 := output6 + output16 << 1 in
      dlet output6 := output6 + output16 in
      dlet output5 := output5 + output15 << 4 in
      dlet output5 := output5 + output15 << 1 in
      dlet output5 := output5 + output15 in
      dlet output4 := output4 + output14 << 4 in
      dlet output4 := output4 + output14 << 1 in
      dlet output4 := output4 + output14 in
      dlet output3 := output3 + output13 << 4 in
      dlet output3 := output3 + output13 << 1 in
      dlet output3 := output3 + output13 in
      dlet output2 := output2 + output12 << 4 in
      dlet output2 := output2 + output12 << 1 in
      dlet output2 := output2 + output12 in
      dlet output1 := output1 + output11 << 4 in
      dlet output1 := output1 + output11 << 1 in
      dlet output1 := output1 + output11 in
      dlet output0 := output0 + output10 << 4 in
      dlet output0 := output0 + output10 << 1 in
      dlet output0 := output0 + output10 in
      (output9, output8, output7, output6, output5, output4, output3, output2, output1, output0)
            );

    upper_bound_of_exponent := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
