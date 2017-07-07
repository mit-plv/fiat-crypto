Require Coq.ZArith.Znumtheory Coq.Numbers.BinNums.

Require Crypto.Arithmetic.ModularArithmeticPre.

Delimit Scope positive_scope with positive.
Bind Scope positive_scope with BinPos.positive.
Infix "+" := BinPos.Pos.add : positive_scope.
Infix "*" := BinPos.Pos.mul : positive_scope.
Infix "-" := BinPos.Pos.sub : positive_scope.
Infix "^" := BinPos.Pos.pow : positive_scope.

Delimit Scope N_scope with N.
Bind Scope N_scope with BinNums.N.
Infix "+" := BinNat.N.add : N_scope.
Infix "*" := BinNat.N.mul : N_scope.
Infix "-" := BinNat.N.sub : N_scope.
Infix "/" := BinNat.N.div : N_scope.
Infix "^" := BinNat.N.pow : N_scope.

Delimit Scope Z_scope with Z.
Bind Scope Z_scope with BinInt.Z.
Infix "+" := BinInt.Z.add : Z_scope.
Infix "*" := BinInt.Z.mul : Z_scope.
Infix "-" := BinInt.Z.sub : Z_scope.
Infix "/" := BinInt.Z.div : Z_scope.
Infix "^" := BinInt.Z.pow : Z_scope.
Infix "mod" := BinInt.Z.modulo (at level 40, no associativity) : Z_scope.

Local Open Scope Z_scope.
Global Coercion BinInt.Z.pos : BinPos.positive >-> BinInt.Z.
Global Coercion BinInt.Z.of_N : BinNums.N >-> BinInt.Z.
Global Set Printing Coercions.

Module F.
  Definition F (m : BinPos.positive) := { z : BinInt.Z | z = z mod m }.
  Local Obligation Tactic := cbv beta; auto using ModularArithmeticPre.Z_mod_mod.
  Program Definition of_Z  m  (a:BinNums.Z) : F m := a mod m.
  Definition to_Z {m} (a:F m) : BinNums.Z := proj1_sig a.

  Section FieldOperations.
    Context {m : BinPos.positive}.
    Definition zero : F m := of_Z m 0.
    Definition one : F m := of_Z m 1.

    Definition add (a b:F m) : F m := of_Z m (to_Z a + to_Z b).
    Definition mul (a b:F m) : F m := of_Z m (to_Z a * to_Z b).
    Definition opp (a : F m) : F m := of_Z m (0 - to_Z a).
    Definition sub (a b:F m) : F m := add a (opp b).

    Definition inv_with_spec : { inv : F m -> F m
                               | inv zero = zero
                                 /\ ( Znumtheory.prime m ->
                                      forall a, a <> zero -> mul (inv a) a = one )
                               } := ModularArithmeticPre.inv_impl.
    Definition inv : F m -> F m := Eval hnf in proj1_sig inv_with_spec.
    Definition div (a b:F m) : F m := mul a (inv b).

    Definition pow_with_spec : { pow : F m -> BinNums.N -> F m
                               | forall a, pow a 0%N = one
                                           /\ forall x, pow a (1 + x)%N = mul a (pow a x)
                               } := ModularArithmeticPre.pow_impl.
    Definition pow : F m -> BinNums.N -> F m := Eval hnf in proj1_sig pow_with_spec.
  End FieldOperations.

  Definition of_nat m (n:nat) := F.of_Z m (BinInt.Z.of_nat n).
  Definition to_nat {m} (x:F m) := BinInt.Z.to_nat (F.to_Z x).
  Notation nat_mod := of_nat (only parsing).

  Definition of_N m n := F.of_Z m (BinInt.Z.of_N n).
  Definition to_N {m} (x:F m) := BinInt.Z.to_N (F.to_Z x).
  Notation N_mod := of_N (only parsing).

  Notation Z_mod := of_Z (only parsing).
End F.

Notation F := F.F.
Delimit Scope F_scope with F.
Bind Scope F_scope with F.F.
Infix "+" := F.add : F_scope.
Infix "*" := F.mul : F_scope.
Infix "-" := F.sub : F_scope.
Infix "/" := F.div : F_scope.
Infix "^" := F.pow : F_scope.
Notation "0" := F.zero : F_scope.
Notation "1" := F.one : F_scope.
