Require Coq.ZArith.Znumtheory Coq.Numbers.BinNums.

Require Crypto.ModularArithmetic.Pre.

Delimit Scope N_scope with N.
Infix "+" := BinNat.N.add : N_scope.
Infix "*" := BinNat.N.mul : N_scope.
Infix "-" := BinNat.N.sub : N_scope.
Infix "/" := BinNat.N.div : N_scope.
Infix "^" := BinNat.N.pow : N_scope.

Delimit Scope Z_scope with Z.
Infix "+" := BinInt.Z.add : Z_scope.
Infix "*" := BinInt.Z.mul : Z_scope.
Infix "-" := BinInt.Z.sub : Z_scope.
Infix "/" := BinInt.Z.div : Z_scope.
Infix "^" := BinInt.Z.pow : Z_scope.
Infix "mod" := BinInt.Z.modulo (at level 40, no associativity) : Z_scope.
Local Open Scope Z_scope.

Definition F (modulus : BinInt.Z) := { z : BinInt.Z | z = z mod modulus }.
Definition ZToField {m} (a:BinNums.Z) : F m := exist _ (a mod m) (Pre.Z_mod_mod a m).
Coercion FieldToZ {m} (a:F m) : BinNums.Z := proj1_sig a.

Section FieldOperations.
  Context {m : BinInt.Z}.
  Definition zero : F m := ZToField 0.
  Definition one : F m := ZToField 1.

  Definition add (a b:F m) : F m := ZToField (a + b).
  Definition mul (a b:F m) : F m := ZToField (a * b).
  Definition opp (a : F m) : F m := ZToField (0 - a).
  Definition sub (a b:F m) : F m := add a (opp b).

  Definition inv_with_spec : { inv : F m -> F m
                             | inv zero = zero
                             /\ ( Znumtheory.prime m ->
                                 forall a, a <> zero -> mul (inv a) a = one )
                             } := Pre.inv_impl.
  Definition inv : F m -> F m := Eval hnf in proj1_sig inv_with_spec.
  Definition div (a b:F m) : F m := mul a (inv b).

  Definition pow_with_spec : { pow : F m -> BinNums.N -> F m
                             | forall a, pow a 0%N = one
                             /\ forall x, pow a (1 + x)%N = mul a (pow a x)
                             } := Pre.pow_impl.
  Definition pow : F m -> BinNums.N -> F m := Eval hnf in proj1_sig pow_with_spec.
End FieldOperations.

Delimit Scope F_scope with F.
Arguments F _%Z.
Arguments ZToField _%Z _%Z : simpl never, clear implicits.
Arguments add {_} _%F _%F : simpl never.
Arguments mul {_} _%F _%F : simpl never.
Arguments sub {_} _%F _%F : simpl never.
Arguments div {_} _%F _%F : simpl never.
Arguments pow {_} _%F _%N : simpl never.
Arguments inv {_} _%F : simpl never.
Arguments opp {_} _%F : simpl never.
Infix "+" := add : F_scope.
Infix "*" := mul : F_scope.
Infix "-" := sub : F_scope.
Infix "/" := div : F_scope.
Infix "^" := pow : F_scope.
Notation "0" := (ZToField _ 0) : F_scope.
Notation "1" := (ZToField _ 1) : F_scope.