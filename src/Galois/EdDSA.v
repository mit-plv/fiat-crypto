Require Import ZArith.
Require Import List.
Require Import Bedrock.Word.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Galois.BaseSystem Crypto.Galois.GaloisTheory.
Require Import Util.ListUtil Util.CaseUtil Util.ZUtil.
Require Import VerdiTactics.
Local Open Scope Z_scope.

Module Type GFEncoding (Import M : Modulus).
  Module Import GF := GaloisTheory M.
  Parameter b : nat.
  Parameter decode : word (b - 1) -> GF.
  Parameter encode : GF -> word (b - 1).
  Axiom consistent : forall x, decode(encode x) = x.
End GFEncoding.

Module Type PointFormatsSpec (Import Q : Modulus).
  Module Import GT := GaloisTheory Q.

  Parameter a : GF.
  Axiom a_square: exists x, (x * x = a)%GF.

  Parameter d : GF.
  Axiom d_not_square : forall x, ((x * x = d)%GF -> False).

  Record point := mkPoint{x : GF; y : GF}.
  Parameter id : point.

  Parameter onCurve : point -> Prop.

  Parameter scalar_mul : GF -> point -> point.
  Axiom scalar_mul_onCurve : forall x P, onCurve P -> onCurve (scalar_mul x P).

  Parameter add : point -> point -> point.
  Axiom add_onCurve : forall P Q, onCurve P -> onCurve Q -> onCurve (add P Q).
  Axiom add_id : forall P, add P id = P.

End PointFormatsSpec.

Module Type EdDSAParams (Import Q : Modulus) (Import Enc : GFEncoding Q) (PF : PointFormatsSpec Q).
  (* Spec from https://eprint.iacr.org/2015/677.pdf *)

  (*
  * An odd prime power q.
  * Choosing q sufficiently large is important for security,
  *   since the size of q constrains the size of l below.
  * There are additional security concerns when q is not chosen to be prime.
  *)
  Definition q := modulus.
  Axiom q_odd : Z.odd q = true.

  (*
  * An integer b with 2^(b − 1) > q.
  * EdDSA public keys have exactly b bits,
  *   and EdDSA signatures have exactly 2b bits.
  *)
  Axiom b_valid : 2^((Z.of_nat b) - 1) > q.

  (* A (b − 1)-bit encoding of elements of the finite field Fq. *)
  Import Enc.GF.

  (*
  * A cryptographic hash function H producing 2b-bit output.
  * Conservative hash functions are recommended and do not have much
  *   impact on the total cost of EdDSA.
  *)
  Parameter H : forall n, word n -> word (2 * b).

  (*
  * An integer c \in {2, 3}. Secret EdDSA scalars are multiples of 2c.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took c = 3.
  *)
  Parameter c : nat.
  Axiom c_valid : (c = 2)%nat \/ (c = 3)%nat.

  (*
  * An integer n with c \leq n \leq b.
  * Secret EdDSA scalars have exactly n + 1 bits, with the top bit
  *   (the 2n position) always set and the bottom c bits always cleared.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took n = b−2.
  * Choosing n sufficiently large is important for security:
  *   standard “kangaroo” attacks use approximately 1.36\sqrt(2n−c) additions
  *   on average to determine an EdDSA secret key from an EdDSA public key.
  *)
  Parameter n : nat.
  Axiom n_gte_c : (n >= c)%nat.
  Axiom n_lte_b : (n <= b)%nat.

  (*
  * A nonzero square element a of Fq.
  * The usual recommendation for best performance is a = −1 if q mod 4 = 1,
  *   and a = 1 if q mod 4 = 3.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took a = −1 (and required q mod 4 = 1).
  *)
  Definition a := PF.a.

  (*
  * A non-square element d of Fq.
  * The exact choice of d (together with a and q) is important for security,
  *   and is the main topic considered in “curve selection”.
  *)
  Definition d := PF.d.

  (*
  *  An element B \neq (0, 1) of the set
  *    E = {(x, y) \in Fq x Fq : ax^2 + y^2 = 1 + dx^2y^2}.
  *  This set forms a group with neutral element 0 = (0, 1) under the
  *    twisted Edwards addition law.
  *)
  Parameter B : PF.point.
  Axiom B_valid : PF.onCurve B.
  Axiom B_not_identity : B = PF.id -> False.

  (*
  * An odd prime l such that lB = 0 and (2^c)l = #E.
  * The number #E is part of the standard data provided for an elliptic
  *   curve E.
  * Choosing l sufficiently large is important for security: standard “rho”
  *   attacks use approximately 0.886√l additions on average to determine an
  *   EdDSA secret key from an EdDSA public key.
  *)
  Parameter l : Prime.
  Axiom l_odd : Z.odd l = true.

  (*
  * A “prehash” function H'.
  * PureEdDSA means EdDSA where H0 is the identity function, i.e. H'(M) = M.
  * HashEdDSA means EdDSA where H0 generates a short output, no matter how
  *   long the message is; for example, H'(M) = SHA-512(M).
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took H0 as the identity function.
  *)
  Parameter H'_out_len : nat -> nat.
  Parameter H' : forall n, word n -> word (H'_out_len n).

End EdDSAParams.

Module Type EdDSA (Q : Modulus) (Import Enc : GFEncoding Q) (Import PF : PointFormatsSpec Q) (Import P : EdDSAParams Q Enc PF).
  Import Enc.GF.
  Parameter encode_point : point -> word b.
  Parameter decode_point : word b -> point.

  Module Type Key.
    Parameter secret : word b.
    Definition whdZ {n} (w : word (S n)) := if (whd w) then 1 else 0.
    Fixpoint word_sum (n : nat) (coef : nat -> Z) : word n -> Z :=
      match n with
        | 0%nat => fun w => 0
        | S n' => fun w => (word_sum n' (fun i => coef (S i)) (wtl w)) + ((coef n') * whdZ w)
      end.
    Definition s := two_power_nat n + word_sum b two_power_nat secret.
    Definition public := H b (encode_point (scalar_mul (inject s) B)).
  End Key.

End EdDSA.
