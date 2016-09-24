Require Import Crypto.Specific.FancyMachine256.Core.
Require Import Crypto.ModularArithmetic.Montgomery.ZBounded.
Require Import Crypto.ModularArithmetic.Montgomery.ZProofs.

Section expression.
  Context (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops) (modulus : Z) (m' : Z) (Hm : modulus <> 0) (H : 0 <= modulus < 2^256) (Hm' : 0 <= m' < 2^256).
  Let H' : 0 <= 256 <= 256. omega. Qed.
  Let H'' : 0 < 256. omega. Qed.
  Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops modulus H 256 H' H''.
  Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops modulus 256).
  Local Notation fst' := (@fst fancy_machine.W fancy_machine.W).
  Local Notation snd' := (@snd fancy_machine.W fancy_machine.W).
  Definition ldi' : load_immediate
                     (@ZBounded.SmallT (2 ^ 256) (2 ^ 256) modulus
                                       (@ZLikeOps_of_ArchitectureBoundedOps 128 ops modulus 256)) := _.
  Let isldi : is_load_immediate ldi' := _.
  Definition pre_f := (fun v => (reduce_via_partial (2^256) modulus (props := props') (ldi' m') I Hm (fst' v, snd' v))).
  Definition f := (fun v => proj1_sig (pre_f v)).

  Local Arguments proj1_sig _ _ !_ / .
  Local Arguments ZBounded.CarryAdd / .
  Local Arguments ZBounded.ConditionalSubtract / .
  Local Arguments ZBounded.ConditionalSubtractModulus / .
  Local Arguments ZLikeOps_of_ArchitectureBoundedOps / .
  Local Arguments ZBounded.DivBy_SmallBound / .
  Local Arguments f / .
  Local Arguments pre_f / .
  Local Arguments ldi' / .
  Local Arguments reduce_via_partial / .

  Definition expression'
    := Eval simpl in f.
  Definition expression
    := Eval cbv beta delta [expression' fst snd] in
        fun v => let RegMod := fancy_machine.ldi modulus in
                 let RegPInv := fancy_machine.ldi m' in
                 let RegZero := fancy_machine.ldi 0 in
                 expression' v.
  Definition expression_eq v : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) I).
  Definition expression_correct
             R' HR0 HR1
             v
             Hv
    : fancy_machine.decode (expression v) = _
    := @ZBounded.reduce_via_partial_correct (2^256) modulus _ props' (ldi' m') I Hm R' HR0 HR1 v I Hv.
End expression.

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Definition rexpression : Syntax.Expr base_type (interp_base_type _) op (Arrow TZ (Arrow TZ (Arrow TW (Arrow TW (Tbase TW))))).
  Proof.
    let v := (eval cbv beta delta [expression] in (fun modulus m' x y => expression ops modulus m' (x, y))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in rexpression.

  Context (modulus m' : Z)
          (props : fancy_machine.arithmetic ops).

  Let result (v : tuple fancy_machine.W 2) := Syntax.Interp (interp_op _) rexpression_simple modulus m' (fst v) (snd v).

  Theorem sanity : result = expression ops modulus m'.
  Proof.
    reflexivity.
  Qed.

  Local Infix "≡₂₅₆" := (Z.equiv_modulo (2^256)).
  Local Infix "≡" := (Z.equiv_modulo modulus).

  Theorem correctness
          R' (* modular inverse of 2^256 *)
          (H0 : modulus <> 0)
          (H1 : 0 <= modulus < 2^256)
          (H2 : 0 <= m' < 2^256)
          (H3 : 2^256 * R' ≡ 1)
          (H4 : modulus * m' ≡₂₅₆ -1)
          (v : tuple fancy_machine.W 2)
          (H5 : 0 <= decode v <= 2^256 * modulus)
    : fancy_machine.decode (result v) = (decode v * R') mod modulus.
  Proof.
    replace m' with (fancy_machine.decode (fancy_machine.ldi m')) in H4
      by (apply decode_load_immediate; trivial; exact _).
    rewrite sanity; destruct v; apply expression_correct; assumption.
  Qed.
End reflected.

Definition compiled_syntax
  := Eval vm_compute in
      (fun ops => AssembleSyntax ops (rexpression_simple _) (@RegMod :: @RegPInv :: nil)%list).

Print compiled_syntax.
(* compiled_syntax =
fun (_ : fancy_machine.instructions (2 * 128)) (var : base_type -> Type) =>
λ x x0 : var TW,
c.Mul128(x1, c.LowerHalf(x), c.LowerHalf(RegPInv)),
c.Mul128(x2, c.UpperHalf(x), c.LowerHalf(RegPInv)),
c.Add(x4, x1, c.LeftShifted{x2, 128}),
c.Mul128(x5, c.UpperHalf(RegPInv), c.LowerHalf(x)),
c.Add(x7, x4, c.LeftShifted{x5, 128}),
c.Mul128(x8, c.UpperHalf(x7), c.UpperHalf(RegMod)),
c.Mul128(x9, c.UpperHalf(x7), c.LowerHalf(RegMod)),
c.Mul128(x10, c.LowerHalf(x7), c.LowerHalf(RegMod)),
c.Add(x12, x10, c.LeftShifted{x9, 128}),
c.Addc(x14, x8, c.RightShifted{x9, 128}),
c.Mul128(x15, c.UpperHalf(RegMod), c.LowerHalf(x7)),
c.Add(x17, x12, c.LeftShifted{x15, 128}),
c.Addc(x19, x14, c.RightShifted{x15, 128}),
c.Add(_, x, x17),
c.Addc(x23, x0, x19),
c.Selc(x24, RegMod, RegZero),
c.Sub(x26, x23, x24),
c.Addm(x27, x26, RegZero),
Return x27
     : fancy_machine.instructions (2 * 128) -> forall var : base_type -> Type, syntax
*)
