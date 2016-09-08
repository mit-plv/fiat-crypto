Require Import Crypto.Experiments.FancyMachine256.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZHandbook.

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
  Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops m H 250 H' H''.
  Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops m 250).
  Local Existing Instances props' ops'.
  Local Notation fst' := (@fst fancy_machine.W fancy_machine.W).
  Local Notation snd' := (@snd fancy_machine.W fancy_machine.W).
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

  Definition pre_f v
    := (@barrett_reduce m b k μ offset m_pos base_pos μ_good offset_nonneg k_big_enough m_small m_large ops' props' μ' I μ'_eq (fst' v, snd' v)).

  Local Arguments μ' / .
  Local Arguments ldi' / .

  Definition expression'
    := Eval simpl in
        (fun v => proj1_sig (pre_f v)).
  Definition expression
    := Eval cbv beta iota delta [expression' fst snd] in
        fun v => let RegMod := fancy_machine.ldi m in
                 let RegMu := fancy_machine.ldi μ in
                 let RegZero := fancy_machine.ldi 0 in
                 expression' v.

  Definition expression_eq v (H : 0 <= _ < _) : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) H).
End expression.

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Definition rexpression : Syntax.Expr base_type (interp_base_type _) op (Arrow TZ (Arrow TZ (Arrow TW (Arrow TW (Tbase TW))))).
  Proof.
    let v := (eval cbv beta delta [expression] in (fun m μ x y => expression ops m μ (x, y))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in rexpression.

  Context (m μ : Z)
          (props : fancy_machine.arithmetic ops).

  Let result (v : tuple fancy_machine.W 2) := Syntax.Interp (interp_op _) rexpression_simple m μ (fst v) (snd v).

  Theorem sanity : result = expression ops m μ.
  Proof.
    reflexivity.
  Qed.

  Theorem correctness
          (b : Z := 2)
          (k : Z := 253)
          (offset : Z := 3)
          (H0 : 0 < m)
          (H1 : μ = b^(2 * k) / m)
          (H2 : 3 * m <= b^(k + offset))
          (H3 : b^(k - offset) <= m + 1)
          (H4 : 0 <= m < 2^(k + offset))
          (H5 : 0 <= b^(2 * k) / m < b^(k + offset))
          (v : tuple fancy_machine.W 2)
          (H6 : 0 <= decode v < b^(2 * k))
    : fancy_machine.decode (result v) = decode v mod m.
  Proof.
    rewrite sanity; destruct v.
    apply expression_eq; assumption.
  Qed.
End reflected.

Definition compiled_syntax
  := Eval vm_compute in
      (fun ops => AssembleSyntax ops (rexpression_simple _) (@RegMod :: @RegMuLow :: nil)%list).

Print compiled_syntax.
(* compiled_syntax =
fun (_ : fancy_machine.instructions (2 * 128)) (var : base_type -> Type) =>
λ x x0 : var TW,
c.Rshi(x1, x0, x, 250),
c.Mul128(x2, c.UpperHalf(x1), c.UpperHalf(RegMuLow)),
c.Mul128(x3, c.UpperHalf(x1), c.LowerHalf(RegMuLow)),
c.Mul128(x4, c.LowerHalf(x1), c.LowerHalf(RegMuLow)),
c.Add(x6, x4, c.LeftShifted{x3, 128}),
c.Addc(x8, x2, c.RightShifted{x3, 128}),
c.Mul128(x9, c.UpperHalf(RegMuLow), c.LowerHalf(x1)),
c.Add(_, x6, c.LeftShifted{x9, 128}),
c.Addc(x13, x8, c.RightShifted{x9, 128}),
c.Mul128(x14, c.LowerHalf(x13), c.LowerHalf(RegMod)),
c.Mul128(x15, c.UpperHalf(x13), c.LowerHalf(RegMod)),
c.Add(x17, x14, c.LeftShifted{x15, 128}),
c.Mul128(x18, c.UpperHalf(RegMod), c.LowerHalf(x13)),
c.Add(x20, x17, c.LeftShifted{x18, 128}),
c.Sub(x22, x, x20),
c.Addm(x23, x22, RegZero),
c.Addm(x24, x23, RegZero),
Return x24
     : fancy_machine.instructions (2 * 128) -> forall var : base_type -> Type, syntax
*)
