Require Import Crypto.Specific.FancyMachine256.Core.
Require Import Crypto.ModularArithmetic.Montgomery.ZBounded.
Require Import Crypto.ModularArithmetic.Montgomery.ZProofs.

Section expression.
  Context (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops) (modulus : Z) (m' : Z) (Hm : modulus <> 0) (H : 0 <= modulus < 2^256) (Hm' : 0 <= m' < 2^256).
  Let H' : 0 <= 256 <= 256. omega. Qed.
  Let H'' : 0 < 256. omega. Qed.
  Definition ldi' : load_immediate
                     (@ZBounded.SmallT (2 ^ 256) (2 ^ 256) modulus
                                       (@ZLikeOps_of_ArchitectureBoundedOps 128 ops modulus 256)) := _.
  Let isldi : is_load_immediate ldi' := _.
  Let props'
      ldi_modulus ldi_0 Hldi_modulus Hldi_0
    := ZLikeProperties_of_ArchitectureBoundedOps_Factored ops modulus ldi_modulus ldi_0 Hldi_modulus Hldi_0 H 256 H' H''.
  Definition pre_f' ldi_modulus ldi_0 Hldi_modulus Hldi_0 lm'
    := (fun v => (reduce_via_partial (2^256) modulus (props := props' ldi_modulus ldi_0 Hldi_modulus Hldi_0) lm' I Hm (fst v, snd v))).
  Definition pre_f := pre_f' _ _ eq_refl eq_refl (ldi' m').

  Definition f := (fun v => pflet ldi_modulus, Hldi_modulus := ldi' modulus in
                            dlet lm' := ldi' m' in
                            pflet ldi_0, Hldi_0 := ldi' 0 in
                            proj1_sig (pre_f' ldi_modulus ldi_0 Hldi_modulus Hldi_0 lm' v)).

  Local Arguments proj1_sig _ _ !_ / .
  Local Arguments ZBounded.CarryAdd / _ _ _ _ _ _.
  Local Arguments ZBounded.ConditionalSubtract / _ _ _ _ _ _.
  Local Arguments ZBounded.ConditionalSubtractModulus / _ _ _ _ _.
  Local Arguments ZLikeOps_of_ArchitectureBoundedOps / _ _ _ _.
  Local Arguments ZBounded.DivBy_SmallBound / _ _ _ _ _.
  Local Arguments f / _.
  Local Arguments pre_f' / _ _ _ _ _ _.
  Local Arguments ldi' / .
  Local Arguments reduce_via_partial / _ _ _ _ _ _ _ _.
  Local Arguments Core.mul_double / _ _ _ _ _ _ _ _ _ _.
  Local Opaque Let_In Let_In_pf.

  Definition expression'
    := Eval simpl in f.
  Local Transparent Let_In Let_In_pf.
  Definition expression
    := Eval cbv beta delta [expression' fst snd Let_In Let_In_pf] in expression'.

  Definition expression_eq v : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) I).
  Definition expression_correct
             R' HR0 HR1
             v
             Hv
    : fancy_machine.decode (expression v) = _
    := @ZBounded.reduce_via_partial_correct (2^256) modulus _ (props' _ _ eq_refl eq_refl) (ldi' m') I Hm R' HR0 HR1 (fst v, snd v) I Hv.
End expression.

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Definition rexpression : Syntax.Expr base_type op (Arrow (tZ * tZ * tW * tW) tW).
  Proof.
    let v := (eval cbv beta delta [expression] in
                 (fun modulus_m'_x_y => let '(modulusv, m'v, xv, yv) := modulus_m'_x_y in
                                        expression ops modulusv m'v (xv, yv))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in rexpression.

  (*Compute DefaultRegisters rexpression_simple.*)

  Definition registers
    := [RegMod; RegPInv; lo; hi; RegMod; RegPInv; RegZero; y; t1; SpecialCarryBit; y;
       t1; SpecialCarryBit; y; t1; t2; scratch+3; SpecialCarryBit; t1; SpecialCarryBit; t2;
       scratch+3; SpecialCarryBit; t1; SpecialCarryBit; t2; SpecialCarryBit; lo; SpecialCarryBit; hi; y;
       SpecialCarryBit; lo; lo].

  Definition compiled_syntax
    := Eval lazy in AssembleSyntax rexpression_simple registers.

  Context (modulus m' : Z)
          (props : fancy_machine.arithmetic ops).

  Let result (v : Tuple.tuple fancy_machine.W 2) := Syntax.Interp interp_op rexpression_simple (modulus, m', fst v, snd v).

  Let assembled_result (v : Tuple.tuple fancy_machine.W 2) : fancy_machine.W := Core.Interp compiled_syntax (modulus, m', fst v, snd v).

  Theorem sanity : result = expression ops modulus m'.
  Proof.
    reflexivity.
  Qed.

  Theorem assembled_sanity : assembled_result = expression ops modulus m'.
  Proof.
    reflexivity.
  Qed.

  Local Infix "≡₂₅₆" := (Z.equiv_modulo (2^256)).
  Local Infix "≡" := (Z.equiv_modulo modulus).

  Section correctness.
    Context R' (* modular inverse of 2^256 *)
            (H0 : modulus <> 0)
            (H1 : 0 <= modulus < 2^256)
            (H2 : 0 <= m' < 2^256)
            (H3 : 2^256 * R' ≡ 1)
            (H4 : modulus * m' ≡₂₅₆ -1)
            (v : Tuple.tuple fancy_machine.W 2)
            (H5 : 0 <= decode v <= 2^256 * modulus).
    Theorem correctness
      : fancy_machine.decode (result v) = (decode v * R') mod modulus.
    Proof.
      replace m' with (fancy_machine.decode (fancy_machine.ldi m'))
        in H4
        by (apply decode_load_immediate; trivial; exact _).
      rewrite sanity; destruct v; apply expression_correct; assumption.
    Qed.
    Theorem assembled_correctness
      : fancy_machine.decode (assembled_result v) = (decode v * R') mod modulus.
    Proof.
      replace m' with (fancy_machine.decode (fancy_machine.ldi m'))
        in H4
        by (apply decode_load_immediate; trivial; exact _).
      rewrite assembled_sanity; destruct v; apply expression_correct; assumption.
    Qed.
  End correctness.
End reflected.

Print compiled_syntax.
(* compiled_syntax =
fun ops : fancy_machine.instructions (2 * 128) =>
λn (RegMod, RegPInv, lo, hi),
slet RegMod := RegMod in
slet RegPInv := RegPInv in
slet RegZero := ldi 0 in
c.Mul128(y, c.LowerHalf(lo), c.LowerHalf(RegPInv)),
c.Mul128(t1, c.UpperHalf(lo), c.LowerHalf(RegPInv)),
c.Add(y, y, c.LeftShifted{t1, 128}),
c.Mul128(t1, c.UpperHalf(RegPInv), c.LowerHalf(lo)),
c.Add(y, y, c.LeftShifted{t1, 128}),
c.Mul128(t1, c.LowerHalf(y), c.LowerHalf(RegMod)),
c.Mul128(t2, c.UpperHalf(y), c.UpperHalf(RegMod)),
c.Mul128(scratch+3, c.UpperHalf(y), c.LowerHalf(RegMod)),
c.Add(t1, t1, c.LeftShifted{scratch+3, 128}),
c.Addc(t2, t2, c.RightShifted{scratch+3, 128}),
c.Mul128(scratch+3, c.UpperHalf(RegMod), c.LowerHalf(y)),
c.Add(t1, t1, c.LeftShifted{scratch+3, 128}),
c.Addc(t2, t2, c.RightShifted{scratch+3, 128}),
c.Add(lo, lo, t1),
c.Addc(hi, hi, t2),
c.Selc(y, RegMod, RegZero),
c.Sub(lo, hi, y),
c.Addm(lo, lo, RegZero),
Return lo
     : forall ops : fancy_machine.instructions (2 * 128),
       expr base_type op Register (Tbase TZ * Tbase TZ * Tbase TW * Tbase TW -> Tbase TW)
*)
