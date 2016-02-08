Require Znumtheory BinInt BinNums.

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
Section FieldOperations.
  Context {m : BinInt.Z}.

  Let Fm := F m. (* TODO: if inlined, coercions say "anomaly please report" *)
  Coercion ZToField (a:BinInt.Z) : Fm := exist _ (a mod m) (Pre.Z_mod_mod a m).
  Coercion FieldToZ (a:Fm) : BinInt.Z := proj1_sig a.

  Definition add (a b:Fm) : Fm := ZToField (a + b).
  Definition mul (a b:Fm) : Fm := ZToField (a * b).

  Parameter opp : Fm -> Fm. 
  Axiom F_opp_spec : forall (a:Fm), add a (opp a) = 0 /\ opp a = opp a mod m.
  Definition sub (a b:Fm) : Fm := add a (opp b).

  Parameter inv : Fm -> Fm. 
  Axiom F_inv_spec : forall (a:Fm), mul a (inv a) = 1 /\ inv 0 = 0 /\ inv a = inv a mod m.
  Definition div (a b:Fm) : Fm := mul a (inv b).

  Parameter pow : Fm -> BinNums.N ->  Fm. 
  Axiom F_pow_spec : forall a, pow a 0%N = 1 /\ forall x y, pow a (x + y)%N = pow a x * pow a y.
End FieldOperations.

Delimit Scope F_scope with F.
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
