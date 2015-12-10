Require Import ZArith.
Require Import List.
Require Import Bedrock.Word.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Galois.BaseSystem Crypto.Galois.GaloisTheory.
Require Import Util.ListUtil Util.CaseUtil Util.ZUtil.
Require Import VerdiTactics.
Local Open Scope Z_scope.

Module Type EdDSAParams.
  (* Spec from https://eprint.iacr.org/2015/677.pdf *)

  (*
  * An odd prime power q.
  * Choosing q sufficiently large is important for security,
  *   since the size of q constrains the size of l below.
  * There are additional security concerns when q is not chosen to be prime.
  *)
  Parameter q : Prime.
  Axiom q_odd : Z.odd q = true.

  Module Modulus_q <: Modulus.
    Definition modulus := q.
  End Modulus_q.
  Module Import Defs := TwistedEdwardsDefs Modulus_q.

  (*
  * An integer b with 2^(b − 1) > q.
  * EdDSA public keys have exactly b bits,
  *   and EdDSA signatures have exactly 2b bits.
  *)
  Parameter b : nat.
  Axiom b_valid : 2^((Z.of_nat b) - 1) > q.

  (* A (b − 1)-bit encoding of elements of the finite field Fq. *)
  Parameter decode : word (b - 1) -> GF.
  Parameter encode : GF -> word (b - 1).
  Axiom consistent : forall x, decode( encode x) = x.

  (*
  * A cryptographic hash function H producing 2b-bit output.
  * Conservative hash functions are recommended and do not have much
  *   impact on the total cost of EdDSA.
  *)
  Parameter H : forall n, word n -> word (b + b).

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
  Parameter a : twistedA.

  (*
  * A non-square element d of Fq.
  * The exact choice of d (together with a and q) is important for security,
  *   and is the main topic considered in “curve selection”.
  *)
  Parameter d : twistedD.

  Module Parameters <: TwistedEdwardsParams Modulus_q.
    Definition a := a.
    Definition d := d.
    Module D := Defs.
  End Parameters.

  Module Export Facts := CompleteTwistedEdwardsFacts Modulus_q Parameters.

  (*
  *  An element B \neq (0, 1) of the set
  *    E = {(x, y) \in Fq x Fq : ax^2 + y^2 = 1 + dx^2y^2}.
  *  This set forms a group with neutral element 0 = (0, 1) under the
  *    twisted Edwards addition law.
  *)
  Parameter B : point.
  Axiom B_valid : onCurve B.
  Axiom B_not_identity : B = zero -> False.

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

Module Type EdDSA (Import P : EdDSAParams).
  Parameter encode_point : point -> word b.
  Parameter decode_point : word b -> point.
  Parameter secret : Type.
  Parameter public : secret -> word b.
  Parameter signature : secret -> forall n, word n -> word (b + b).
End EdDSA.

Module EdDSAImpl (Import P : EdDSAParams) <: EdDSA P.
  Definition encode_point (p : point) := wzero b. (* TODO *)
  Definition decode_point (w : word b) := zero.  (* TODO *)

  Definition leading_ones n := natToWord b (wordToNat (wone n)).
  Definition c_to_n_window := wxor (leading_ones c) (leading_ones n).
  (* Precompute s and the high half of H(k) *)
  Record secret := mkSecret{
    key : word b;
    s : Z;
    hash_high : word b;
    s_def : s =  wordToZ (wand c_to_n_window key);
    hash_high_def : hash_high = split2 b b (H b key)
  }.

  (* Needs scalar multiplication:
  * Definition public (sk : secret) := H b (encode_point (scalar_mul (inject (s sk)) B)). *)

  Definition signature (sk : secret) n (w : word n) := wzero (b + b).

End EdDSAImpl.
