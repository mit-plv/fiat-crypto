Require Import Crypto.Specific.NISTP256.FancyMachine256.Core.
Require Import LegacyArithmetic.BarretReduction.
Require Import Crypto.Arithmetic.BarrettReduction.HAC.

(** Useful for arithmetic in the field of integers modulo the order of the curve25519 base point *)
Section expression.
  Let b : Z := 2.
  Let k : Z := 253.
  Let offset : Z := 3.
  Context (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops).
  Context (m μ : Z)
          (m_pos : 0 < m).
  Let base_pos : 0 < b. reflexivity. Qed.
  Context (k_good : m < b^k)
          (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *).
  Let offset_nonneg : 0 <= offset. unfold offset; omega. Qed.
  Let k_big_enough : offset <= k. unfold offset, k; omega. Qed.
  Context (m_small : 3 * m <= b^(k+offset))
          (m_large : b^(k-offset) <= m + 1).
  Context (H : 0 <= m < 2^256).
  Let H' : 0 <= 250 <= 256. omega. Qed.
  Let H'' : 0 < 250. omega. Qed.
  Local Notation SmallT := (@ZBounded.SmallT (2 ^ 256) (2 ^ 250) m
                                  (@ZLikeOps_of_ArchitectureBoundedOps 128 ops m _)).
  Definition ldi' : load_immediate SmallT := _.
  Let isldi : is_load_immediate ldi' := _.
  Context (μ_range : 0 <= b ^ (2 * k) / m < b ^ (k + offset)).
  Definition μ' : SmallT := ldi' μ.
  Let μ'_eq : ZBounded.decode_small μ' = μ.
  Proof.
    unfold ZBounded.decode_small, ZLikeOps_of_ArchitectureBoundedOps, μ'.
    apply (decode_load_immediate _ _).
    rewrite μ_good; apply μ_range.
  Qed.

  Let props'
      ldi_modulus ldi_0 Hldi_modulus Hldi_0
    := ZLikeProperties_of_ArchitectureBoundedOps_Factored ops m ldi_modulus ldi_0 Hldi_modulus Hldi_0 H 250 H' H''.

  Definition pre_f' ldi_modulus ldi_0 ldi_μ Hldi_modulus Hldi_0 (Hldi_μ : ldi_μ = ldi' μ)
    := (fun v => (@barrett_reduce m b k μ offset m_pos base_pos μ_good offset_nonneg k_big_enough m_small m_large _ (props' ldi_modulus ldi_0 Hldi_modulus Hldi_0) ldi_μ I (eq_trans (f_equal _ Hldi_μ) μ'_eq)  (fst v, snd v))).

  Definition pre_f := pre_f' _ _ _ eq_refl eq_refl eq_refl.

  Local Arguments μ' / .
  Local Arguments ldi' / .
  Local Arguments Core.mul_double / _ _ _ _ _ _ _ _ _ _.
  Local Opaque Let_In Let_In_pf.

  Definition expression'
    := Eval simpl in
        (fun v => pflet ldi_modulus, Hldi_modulus := fancy_machine.ldi m in
                  pflet ldi_μ, Hldi_μ := fancy_machine.ldi μ in
                  pflet ldi_0, Hldi_0 := fancy_machine.ldi 0 in
                  proj1_sig (pre_f' ldi_modulus ldi_0 ldi_μ Hldi_modulus Hldi_0 Hldi_μ v)).
  Local Transparent Let_In Let_In_pf.
  Definition expression
    := Eval cbv beta iota delta [expression' fst snd Let_In Let_In_pf] in expression'.

  Definition expression_eq v (H : 0 <= _ < _) : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) H).
End expression.

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Definition rexpression : Syntax.Expr base_type op (Arrow (tZ * tZ * tW * tW) tW).
  Proof.
    let v := (eval cbv beta delta [expression] in (fun mμxy => let '(mv, μv, xv, yv) := mμxy in expression ops mv μv (xv, yv))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in rexpression.

  (*Compute DefaultRegisters rexpression_simple.*)

  Definition registers
    := [RegMod; RegMuLow; x; xHigh; RegMod; RegMuLow; RegZero; tmp; q; qHigh; scratch+3;
       SpecialCarryBit; q; SpecialCarryBit; qHigh; scratch+3; SpecialCarryBit; q; SpecialCarryBit; qHigh; tmp;
       scratch+3; SpecialCarryBit; tmp; scratch+3; SpecialCarryBit; tmp; SpecialCarryBit; tmp; q; out].

  Definition compiled_syntax
    := Eval lazy in AssembleSyntax rexpression_simple registers.

  Context (m μ : Z)
          (props : fancy_machine.arithmetic ops).

  Let result (v : Tuple.tuple fancy_machine.W 2) := Syntax.Interp (@interp_op _) rexpression_simple (m, μ, fst v, snd v).
  Let assembled_result (v : Tuple.tuple fancy_machine.W 2) : fancy_machine.W := Core.Interp compiled_syntax (m, μ, fst v, snd v).

  Theorem sanity : result = expression ops m μ.
  Proof using Type.
    reflexivity.
  Qed.

  Theorem assembled_sanity : assembled_result = expression ops m μ.
  Proof using Type.
    reflexivity.
  Qed.

  Section correctness.
    Let b : Z := 2.
    Let k : Z := 253.
    Let offset : Z := 3.
    Context (H0 : 0 < m)
            (H1 : μ = b^(2 * k) / m)
            (H2 : 3 * m <= b^(k + offset))
            (H3 : b^(k - offset) <= m + 1)
            (H4 : 0 <= m < 2^(k + offset))
            (H5 : 0 <= b^(2 * k) / m < b^(k + offset))
            (v : Tuple.tuple fancy_machine.W 2)
            (H6 : 0 <= decode v < b^(2 * k)).
    Theorem correctness : fancy_machine.decode (result v) = decode v mod m.
    Proof using H0 H1 H2 H3 H4 H5 H6 props.
      rewrite sanity; destruct v.
      apply expression_eq; assumption.
    Qed.
    Theorem assembled_correctness : fancy_machine.decode (assembled_result v) = decode v mod m.
    Proof using H0 H1 H2 H3 H4 H5 H6 props.
      rewrite assembled_sanity; destruct v.
      apply expression_eq; assumption.
    Qed.
  End correctness.
End reflected.

Print compiled_syntax.
(* compiled_syntax =
fun ops : fancy_machine.instructions (2 * 128) =>
λn (RegMod, RegMuLow, x, xHigh),
nlet RegMod := RegMod in
nlet RegMuLow := RegMuLow in
nlet RegZero := ldi 0 in
c.Rshi(tmp, xHigh, x, 250),
c.Mul128(q, c.LowerHalf(tmp), c.LowerHalf(RegMuLow)),
c.Mul128(qHigh, c.UpperHalf(tmp), c.UpperHalf(RegMuLow)),
c.Mul128(scratch+3, c.UpperHalf(tmp), c.LowerHalf(RegMuLow)),
c.Add(q, q, c.LeftShifted{scratch+3, 128}),
c.Addc(qHigh, qHigh, c.RightShifted{scratch+3, 128}),
c.Mul128(scratch+3, c.UpperHalf(RegMuLow), c.LowerHalf(tmp)),
c.Add(q, q, c.LeftShifted{scratch+3, 128}),
c.Addc(qHigh, qHigh, c.RightShifted{scratch+3, 128}),
c.Mul128(tmp, c.LowerHalf(qHigh), c.LowerHalf(RegMod)),
c.Mul128(scratch+3, c.UpperHalf(qHigh), c.LowerHalf(RegMod)),
c.Add(tmp, tmp, c.LeftShifted{scratch+3, 128}),
c.Mul128(scratch+3, c.UpperHalf(RegMod), c.LowerHalf(qHigh)),
c.Add(tmp, tmp, c.LeftShifted{scratch+3, 128}),
c.Sub(tmp, x, tmp),
c.Addm(q, tmp, RegZero),
c.Addm(out, q, RegZero),
Return out
     : forall ops : fancy_machine.instructions (2 * 128),
       expr base_type op Register (Tbase TZ * Tbase TZ * Tbase TW * Tbase TW -> Tbase TW)
*)
