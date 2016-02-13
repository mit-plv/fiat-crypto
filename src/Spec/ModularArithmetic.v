Require Znumtheory BinNums.

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
Coercion FieldToZ {m} (a:F m) : BinNums.Z := proj1_sig a.

Section FieldOperations.
  Context {m : BinInt.Z}.

  Let Fm := F m. (* Note: if inlined, coercions say "anomaly please report" *)
  Coercion unfoldFm (a:Fm) : F m := a.
  Coercion ZToField (a:BinNums.Z) : Fm := exist _ (a mod m) (Pre.Z_mod_mod a m).
  
  Definition add (a b:Fm) : Fm := ZToField (a + b).
  Definition mul (a b:Fm) : Fm := ZToField (a * b).

  Definition opp_with_spec : { opp | forall x, add x (opp x) = 0 } := Pre.opp_impl.
  Definition opp : F m -> F m := Eval hnf in proj1_sig opp_with_spec.
  Definition sub (a b:Fm) : Fm := add a (opp b).

  Parameter inv : Fm -> Fm. 
  Axiom F_inv_spec : Znumtheory.prime m -> forall (a:Fm), mul a (inv a) = 1 /\ inv 0 = 0.
  Definition div (a b:Fm) : Fm := mul a (inv b).

  Parameter pow : Fm -> BinNums.N ->  Fm. 
  Axiom F_pow_spec : forall a, pow a 0%N = 1 /\ forall x, pow a (1 + x)%N = mul a (pow a x).
End FieldOperations.

Delimit Scope F_scope with F.
Arguments F _%Z.
Arguments ZToField {_} _%Z : simpl never.
Arguments add {_} _%F _%F : simpl never.
Arguments mul {_} _%F _%F : simpl never.
Arguments sub {_} _%F _%F : simpl never.
Arguments div {_} _%F _%F : simpl never.
Arguments pow {_} _%F _%N : simpl never.
Arguments inv {_} _%F : simpl never.
Arguments opp {_} _%F : simpl never.
Local Open Scope F_scope.
Infix "+" := add : F_scope.
Infix "*" := mul : F_scope.
Infix "-" := sub : F_scope.
Infix "/" := div : F_scope.
Infix "^" := pow : F_scope.
Notation "0" := (ZToField 0) : F_scope.
Notation "1" := (ZToField 1) : F_scope.