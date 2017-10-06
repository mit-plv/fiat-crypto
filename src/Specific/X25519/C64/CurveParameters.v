Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-19
Base: 51
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 5%nat.
  Definition bitwidth : Z := 64.
  Definition s : Z := 2^255.
  Definition c : list limb := [(1, 19)].
  Definition carry_chains : option (list (list nat)) := Eval vm_compute in Some [seq 0 (pred sz); [0; 1]]%nat.

  Definition a24 : option Z := Some 121665.
  Definition coef_div_modulus : nat := 2%nat. (* add 2*modulus before subtracting *)

  Definition goldilocks : bool := false.

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz)
    := Some (fun a b =>
      (* Micro-optimized form from curve25519-donna-c64 by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(r4, r3, r2, r1, r0) := a in
      let '(s4, s3, s2, s1, s0) := b in
      dlet t0  :=  r0 * s0 in
      dlet t1  :=  r0 * s1 + r1 * s0 in
      dlet t2  :=  r0 * s2 + r2 * s0 + r1 * s1 in
      dlet t3  :=  r0 * s3 + r3 * s0 + r1 * s2 + r2 * s1 in
      dlet t4  :=  r0 * s4 + r4 * s0 + r3 * s1 + r1 * s3 + r2 * s2 in

      dlet r4 := r4 * 19 in
      dlet r1 := r1 * 19 in
      dlet r2 := r2 * 19 in
      dlet r3 := r3 * 19 in

      dlet t0 := t0 + r4 * s1 + r1 * s4 + r2 * s3 + r3 * s2 in
      dlet t1 := t1 + r4 * s2 + r2 * s4 + r3 * s3 in
      dlet t2 := t2 + r4 * s3 + r3 * s4 in
      dlet t3 := t3 + r4 * s4 in
      (t4, t3, t2, t1, t0)
            ).

  Definition square_code : option (Z^sz -> Z^sz)
    := Some (fun a =>
      (* Micro-optimized form from curve25519-donna-c64 by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(r4, r3, r2, r1, r0) := a in
      dlet d0 := r0 * 2 in
      dlet d1 := r1 * 2 in
      dlet d2 := r2 * 2 * 19 in
      dlet d419 := r4 * 19 in
      dlet d4 := d419 * 2 in

      dlet t0 := r0 * r0 + d4 * r1 + (d2 * (r3     )) in
      dlet t1 := d0 * r1 + d4 * r2 + (r3 * (r3 * 19)) in
      dlet t2 := d0 * r2 + r1 * r1 + (d4 * (r3     )) in
      dlet t3 := d0 * r3 + d1 * r2 + (r4 * (d419   )) in
      dlet t4 := d0 * r4 + d1 * r3 + (r2 * (r2     )) in
      (t4, t3, t2, t1, t0)
            ).

  Definition upper_bound_of_exponent : option (Z -> Z) := None.
  Definition allowable_bit_widths : option (list nat) := None.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := None.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End Curve.
