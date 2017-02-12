Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.EdDSA.

Require ModularArithmetic.PrimeFieldTheorems. (* to know that Z mod p is a field *)

(* TODO: move this to a separate file *)
Require Crypto.Util.Decidable.
Require Crypto.Util.Tactics.SpecializeBy.
Module Pre.
  Local Open Scope F_scope.
  Lemma curve25519_params_ok {prime_q:Znumtheory.prime (2^255-19)} :
  @E.twisted_edwards_params (F (2 ^ 255 - 19)) (@eq (F (2 ^ 255 - 19))) (@F.zero (2 ^ 255 - 19))
    (@F.one (2 ^ 255 - 19)) (@F.opp (2 ^ 255 - 19)) (@F.add (2 ^ 255 - 19)) (@F.sub (2 ^ 255 - 19)) (@F.mul (2 ^ 255 - 19))
    (@F.opp (2 ^ 255 - 19) 1)
    (@F.opp (2 ^ 255 - 19) (F.of_Z (2 ^ 255 - 19) 121665) / F.of_Z (2 ^ 255 - 19) 121666).
  Proof.
    pose (@PrimeFieldTheorems.F.Decidable_square (2^255-19) _);
      SpecializeBy.specialize_by Decidable.vm_decide; split; try Decidable.vm_decide_no_check.
    { intros n one_le_n n_le_two.
      assert ((n = 1 \/ n = 2)%N) as Hn by admit; destruct Hn; subst; Decidable.vm_decide. }
  Admitted.
End Pre.
(* these 2 proofs can be generated using https://github.com/andres-erbsen/safecurves-primes *)
Axiom prime_q : Znumtheory.prime (2^255-19). Global Existing Instance prime_q.
Axiom prime_l : Znumtheory.prime (2^252 + 27742317777372353535851937790883648493). Global Existing Instance prime_l.

Section Ed25519.

  Local Open Scope Z_scope.

  Definition q : BinNums.Z := 2^255 - 19.
  Definition Fq : Type := F q.

  Definition l : BinNums.Z := 2^252 + 27742317777372353535851937790883648493.
  Definition Fl : Type := F l.

  Local Open Scope F_scope.

  Definition a : Fq := F.opp 1.
  Definition d : Fq := F.opp (F.of_Z _ 121665) / (F.of_Z _ 121666).

  Local Open Scope nat_scope.

  Definition b : nat := 256.
  Definition n : nat := b - 2.
  Definition c : nat := 3.

  Context {H: forall n : nat, Word.word n -> Word.word (b + b)}.

  Global Instance curve_params :
    E.twisted_edwards_params
      (F:=Fq) (Feq:=Logic.eq) (Fzero:=F.zero) (Fone:=F.one) (Fopp:=F.opp) (Fadd:=F.add) (Fsub:=F.sub) (Fmul:=F.mul)
      (a:=a) (d:=d). Proof Pre.curve25519_params_ok.

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

  Require Import Crypto.Util.Decidable.
  Definition ed25519 :
    CompleteEdwardsCurveTheorems.E.eq (BinInt.Z.to_nat l * B)%E E.zero -> (* TODO: prove this earlier than Experiments/Ed25519? *)
    EdDSA (E:=E) (Eadd:=E.add) (Ezero:=E.zero) (EscalarMult:=E.mul) (B:=B)
          (Eopp:=Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.E.opp) (* TODO: move defn *)
          (Eeq:=Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.E.eq) (* TODO: move defn *)
          (l:=l) (b:=b) (n:=n) (c:=c)
          (Eenc:=Eenc) (Senc:=Senc) (H:=H).
  Proof. split; try (assumption || exact _); vm_decide. Qed.
End Ed25519.
