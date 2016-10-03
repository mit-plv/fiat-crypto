Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.EdDSA.

Require ModularArithmetic.PrimeFieldTheorems. (* to know that Z mod p is a field *)

Section Ed25519.

  Local Open Scope Z_scope.

  Definition q : BinNums.Z := 2^255 - 19.
  Definition Fq : Type := F q.

  Definition l : BinNums.Z := 252 + 27742317777372353535851937790883648493.
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
      (F:=Fq) (Feq:=Logic.eq) (Fzero:=F.zero) (Fone:=F.one) (Fadd:=F.add) (Fmul:=F.mul)
      (a:=a) (d:=d).
  Admitted. (* TODO(andreser): prove in a separate file *)

  Definition E : Type := E.point
                           (F:=Fq) (Feq:=Logic.eq) (Fone:=F.one) (Fadd:=F.add) (Fmul:=F.mul)
                           (a:=a) (d:=d).

  Axiom B : E. (* TODO(andreser) *)

  Axiom Eenc : E -> Word.word b. (* TODO(jadep) *)
  Axiom Senc : Fl -> Word.word b. (* TODO(jadep) *)

  (* these 2 proofs can be generated using https://github.com/andres-erbsen/safecurves-primes *)
  Axiom prime_q : Znumtheory.prime q. Existing Instance prime_q.
  Axiom prime_l : Znumtheory.prime l. Existing Instance prime_l.

  Require Import Crypto.Util.Decidable.
  Definition ed25519 :
    EdDSA (E:=E) (Eadd:=E.add) (Ezero:=E.zero) (EscalarMult:=E.mul) (B:=B)
          (Eopp:=Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.E.opp) (* TODO: move defn *)
          (Eeq:=Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.E.eq) (* TODO: move defn *)
          (l:=l) (b:=b) (n:=n) (c:=c)
          (Eenc:=Eenc) (Senc:=Senc) (H:=H).
  Admitted. (* TODO(andreser): prove in a separate file *)
End Ed25519.