Require Import Crypto.Spec.ModularArithmetic.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.EdDSA.

Require Crypto.Arithmetic.PrimeFieldTheorems. (* to know that Z mod p is a field *)
Require Crypto.Curves.Edwards.AffineProofs.

(* these 2 proofs can be generated using https://github.com/andres-erbsen/safecurves-primes *)
Axiom prime_q : Znumtheory.prime (2^255-19). Global Existing Instance prime_q.
Axiom prime_l : Znumtheory.prime (2^252 + 27742317777372353535851937790883648493). Global Existing Instance prime_l.

Section Ed25519.

  Local Open Scope Z_scope.

  Definition q : BinPos.positive := 2^255 - 19.
  Definition Fq : Type := F q.

  Definition l : BinPos.positive := 2^252 + 27742317777372353535851937790883648493.
  Definition Fl : Type := F l.

  Local Open Scope F_scope.

  Definition a : Fq := F.opp 1.
  Definition d : Fq := F.opp (F.of_Z _ 121665) / (F.of_Z _ 121666).

  Local Open Scope nat_scope.

  Definition b : nat := 256.
  Definition n : nat := b - 2.
  Definition c : nat := 3.

  Context {SHA512: forall n : nat, Word.word n -> Word.word 512}.

  Local Instance char_gt_e : 
    @Ring.char_ge (@F q) eq F.zero F.one F.opp F.add F.sub F.mul
                  (BinNat.N.succ_pos BinNat.N.two).
  Proof. eapply Hierarchy.char_ge_weaken;
           [apply (_:Ring.char_ge q)|Decidable.vm_decide]. Qed.
    

  Definition E : Type := E.point
                           (F:=Fq) (Feq:=Logic.eq) (Fone:=F.one) (Fadd:=F.add) (Fmul:=F.mul)
                           (a:=a) (d:=d).

  Local Obligation Tactic := Decidable.vm_decide. (* to prove that B is on curve *)

  Program Definition B : E :=
    (F.of_Z q 15112221349535400772501151409588531511454012693041857206046113283949847762202,
     F.of_Z q 4 / F.of_Z q 5).

  Local Infix "++" := Word.combine.
  Local Notation bit b := (Word.WS b Word.WO : Word.word 1).

  Definition Fencode {len} {m} : F m -> Word.word len :=
    fun x : F m => (Word.NToWord _ (BinIntDef.Z.to_N (F.to_Z x))).
  Definition sign (x : F q) : bool := BinIntDef.Z.testbit (F.to_Z x) 0.
  Definition Eenc : E -> Word.word b := fun P =>
    let '(x,y) := E.coordinates P in Fencode (len:=b-1) y ++ bit (sign x).
  Definition Senc : Fl -> Word.word b := Fencode (len:=b).

  Lemma nonzero_a : a <> 0%F.
  Proof using Type. Crypto.Util.Decidable.vm_decide. Qed.
  Lemma square_a : exists sqrt_a : Fq, (sqrt_a * sqrt_a)%F = a.
  Proof using Type. pose (@PrimeFieldTheorems.F.Decidable_square q _ ltac:(Crypto.Util.Decidable.vm_decide) a); Crypto.Util.Decidable.vm_decide. Qed.
  Lemma nonsquare_d : forall x : Fq, (x * x)%F <> d.
  Proof using Type. pose (@PrimeFieldTheorems.F.Decidable_square q _ ltac:(Crypto.Util.Decidable.vm_decide) d); Crypto.Util.Decidable.vm_decide. Qed.

  Let add := E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d).
  Let zero := E.zero(nonzero_a:=nonzero_a)(d:=d).
  (* TODO: move scalarmult_ref to Spec? *)
  Let mul := ScalarMult.scalarmult_ref(zero:=zero)(add:=add)(opp:=AffineProofs.E.opp(nonzero_a:=nonzero_a)).

  Definition ed25519 (l_order_B: (mul l B = zero)%E) :
    EdDSA (E:=E) (Eadd:=add) (Ezero:=zero) (ZEmul:=mul) (B:=B)
          (Eopp:=Crypto.Curves.Edwards.AffineProofs.E.opp(nonzero_a:=nonzero_a)) (* TODO: move defn *)
          (Eeq:=E.eq) (* TODO: move defn *)
          (l:=l) (b:=b) (n:=n) (c:=c)
          (Eenc:=Eenc) (Senc:=Senc) (H:=SHA512).
  Proof using Type.
    split; try exact _.
    Crypto.Util.Decidable.vm_decide.
    Crypto.Util.Decidable.vm_decide.
    Crypto.Util.Decidable.vm_decide.
    Crypto.Util.Decidable.vm_decide.
    Crypto.Util.Decidable.vm_decide.
    exact l_order_B.
  Qed.
End Ed25519.
