Require Import ZArith.
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
  Axiom q_odd : q > 2.

  Module Modulus_q <: Modulus.
    Definition modulus := q.
  End Modulus_q.
  Module Export CurveDefs := TwistedEdwardsDefs Modulus_q.

  (*
  * An integer b with 2^(b − 1) > q.
  * EdDSA public keys have exactly b bits,
  *   and EdDSA signatures have exactly 2b bits.
  *)
  (* Note: the parameter pred_b is (b - 1) to make proofs about the (b-1)-bit
  * encoding easier *)
  Parameter b : nat.
  Coercion Z.of_nat : nat >-> Z.
  Axiom b_valid : 2^(b - 1) > q.
  Definition secretkey : Type := word b.
  Definition publickey : Type := word b.
  Definition signature : Type := word (b + b).

  (* A (b − 1)-bit encoding of elements of the finite field Fq. *)
  Parameter decode_scalar : word (b - 1) -> GF.
  Parameter encode_scalar : GF -> word (b - 1).
  Axiom decode_encode_scalar_consistent : forall x, decode_scalar (encode_scalar x) = x.
  Axiom encode_decode_scalar_consistent : forall x, encode_scalar (decode_scalar x) = x.

  (*
  * A cryptographic hash function H producing 2b-bit output.
  * Conservative hash functions are recommended and do not have much
  *   impact on the total cost of EdDSA.
  *)
  Parameter H : forall {n}, word n -> word (b + b).

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
  Axiom n_ge_c : n >= c.
  Axiom n_le_b : (n <= b)%nat.

  (*
  * A nonzero square element a of Fq.
  * The usual recommendation for best performance is a = −1 if q mod 4 = 1,
  *   and a = 1 if q mod 4 = 3.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took a = −1 (and required q mod 4 = 1).
  *)
  Parameter a : GF.
  Axiom a_nonzero : a <> 0%GF.
  Axiom a_square : exists x, x * x = a.

  (*
  * A non-square element d of Fq.
  * The exact choice of d (together with a and q) is important for security,
  *   and is the main topic considered in “curve selection”.
  *)
  Parameter d : GF.
  Axiom d_nonsquare : forall x, x * x <> d.

  Module Parameters <: TwistedEdwardsParams Modulus_q.
    Module Defs := CurveDefs.
    Definition a : GF := a.
    Definition a_nonzero := a_nonzero.
    Definition a_square := a_square.
    Definition d := d.
    Definition d_nonsquare := d_nonsquare.
  End Parameters.

  Module Export Curve := CompleteTwistedEdwardsCurve Modulus_q Parameters.

  (*
  *  An element B \neq (0, 1) of the set
  *    E = {(x, y) \in Fq x Fq : ax^2 + y^2 = 1 + dx^2y^2}.
  *  This set forms a group with neutral element 0 = (0, 1) under the
  *    twisted Edwards addition law.
  *)
  Parameter B : point.
  Axiom B_not_identity : B <> zero.
  Axiom B_valid : onCurve B.
  Hint Resolve B_valid.

  (*
  * An odd prime l such that lB = 0 and (2^c)l = #E.
  * The number #E is part of the standard data provided for an elliptic
  *   curve E.
  * Choosing l sufficiently large is important for security: standard “rho”
  *   attacks use approximately 0.886√l additions on average to determine an
  *   EdDSA secret key from an EdDSA public key.
  *)
  Parameter l : Prime.
  Axiom l_odd : l > 2.
  (* TODO: (2^c)l = #E *)

  (*
  * A “prehash” function H'.
  * PureEdDSA means EdDSA where H0 is the identity function, i.e. H'(M) = M.
  * HashEdDSA means EdDSA where H0 generates a short output, no matter how
  *   long the message is; for example, H'(M) = SHA-512(M).
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took H0 as the identity function.
  *)
  Parameter H'_out_len : nat -> nat.
  Parameter H' : forall {n}, word n -> word (H'_out_len n).

End EdDSAParams.

(* TODO : where should this be? *)
Definition wfirstn {m} {n} (w : word m) (H : (n <= m)%nat) : word n.
  replace m with (n + (m - n))%nat in * by (symmetry; apply le_plus_minus; apply H)
.
  exact (split1 n (m - n) w).
Defined.

Lemma wtl_WS : forall b {n} (w : word n), wtl (WS b w) = w.
Proof.
  auto.
Qed.

Module Type EdDSA (Import P : EdDSAParams).
  Local Infix "++" := combine.
  Local Infix "*" := scalarMult.
  Local Infix "+" := unifiedAdd.

  (* From [https://eprint.iacr.org/2015/677.pdf]: x is negative if the 
  * (b − 1)-bit encoding of x is lexicographically larger than the 
  * (b − 1)-bit encoding of −x *)
  Definition sign_bit x : word 1 := 
    match (wordToNat (encode_scalar x) ?= wordToNat (encode_scalar (GFopp x)))%nat with
    | Gt => wone 1
    | _ => wzero 1
    end.

  (* TODO: move eventually *)
  Lemma b_gt_0 : b > 0.
  Proof.
    pose proof b_valid.
    pose proof q_odd.
    destruct b; boring.
  Qed.
  
  Parameter encode_point : point -> word b.
  Definition encode_point_ref (P : point) : word b.
    replace b with (b - 1 + 1)%nat by abstract (pose proof b_gt_0; omega).
    apply (combine (encode_scalar (projY P)) (sign_bit (projX P))).
  Defined.
  Axiom encode_point_spec : forall P, encode_point P = encode_point_ref P.
  Parameter decode_point : word b -> option point.
  Axiom decode_point_spec : forall P, onCurve P ->
    decode_point (encode_point P) = Some P.

  Definition s (sk : secretkey) :=
    let N := wordToNat (wfirstn sk n_le_b) in
    ((N - (NPeano.modulo N (pow2 c))) * pow2 c)%nat.
  Parameter public : secretkey -> publickey.
  Axiom public_spec : forall sk, public sk = encode_point ((s sk) * B).

  Parameter sign : secretkey -> forall {n}, word n -> signature.
  Axiom sign_spec : forall sk {n} (M : word n), sign sk M = 
    let r := wordToNat (H ((split2 b b (H sk)) ++ M)) in
    let R := r * B in
    let S := NPeano.modulo (r + ((s sk) * wordToNat (H ((encode_point R) ++ (public sk) ++ M))))%nat (Z.to_nat l) in
    (encode_point R) ++ (natToWord b S).

  Parameter verify : publickey -> signature -> forall {n}, word n -> bool.
  Axiom verify_spec : forall A_ sig {n} (M : word n), verify A_ sig M = true <->
    let R_ := split1 b b sig in
    let S_ := split2 b b sig in
    let S := wordToNat S_ in
    match (decode_point A_) with
    | None => False
    | Some A => match (decode_point R_) with
                | None => False
                | Some R => S * B = R + (wordToNat (H (R_ ++ A_ ++ M )) * A)
                end
    end.

  (* for signature (R_, S_), R_ = encode_point (r * B) *) 
  Lemma decode_sign_split1 : forall (sk : secretkey) {n} (M : word n),
    split1 b b (sign sk M) = encode_point ((wordToNat (H ((split2 b b (H sk)) ++ M))) * B).
  Proof.
    intros. pose proof (sign_spec sk M).
    simpl in H0. rewrite H0; clear H0.
    apply split1_combine.
  Qed.
  
  (* for signature (R_, S_), S_ = encode_scalar (r + H(R_, A_, M)s) *) 
  Lemma decode_sign_split2 : forall (sk : secretkey) {n} (M : word n),
    split2 b b (sign sk M) =
    let r := wordToNat (H ((split2 b b (H sk)) ++ M)) in
    natToWord b (NPeano.modulo (r + ((s sk) * wordToNat (H ((encode_point (r * B)) ++ (public sk) ++ M)))) (Z.to_nat l)).
  Proof.
    intros. rewrite sign_spec; simpl.
    rewrite split2_combine.
    f_equal.
  Qed.

  Lemma verification_principle : forall n,
    NPeano.modulo n (Z.to_nat l) * B = n * B.
  Admitted.

  Lemma l_bound : (Z.to_nat l < pow2 b)%nat.
  Admitted.

  Lemma l_gt_zero : (Z.to_nat l <> 0)%nat.
  Admitted.

  (* TODO : move to TwistedEdwardsFacts *)
  Lemma scalarMultOnCurve : forall n P, onCurve P -> onCurve (n * P).
  Proof.
    intros; induction n0; boring.
  Admitted.
  Hint Resolve scalarMultOnCurve.

  (* TODO : move somewhere else (EdDSAFacts?) *)
  Lemma verify_valid_passes : forall sk {n} (M : word n),
    verify (public sk) (sign sk M) M = true.
  Proof.
    intros; rewrite verify_spec.
    intros; subst R_.
    rewrite decode_sign_split1.
    rewrite public_spec.
    rewrite decode_point_spec by auto.
    rewrite decode_point_spec by auto.
    subst S S_.
    rewrite decode_sign_split2; simpl.
    remember (wordToNat (H (split2 b b (H sk) ++ M))) as r.
    rewrite public_spec.
    remember (wordToNat
      (H (encode_point (r * B) ++ encode_point (s sk * B) ++ M))).
    assert (N.of_nat (NPeano.modulo (r + s sk * n1) (Z.to_nat l)) < Npow2 b)%N. {
      remember (r + s sk * n1)%nat.
      pose proof (NPeano.Nat.mod_upper_bound n2 (Z.to_nat l) l_gt_zero).
      pose proof l_bound.
      pose proof (lt_trans _ (Z.to_nat l) (pow2 b) H0 H1).
      clear H0 H1.
      apply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    }
    rewrite (wordToNat_natToWord_idempotent b 
      (NPeano.modulo (r + s sk * n1) (Z.to_nat l)) H0); clear H0.
    rewrite verification_principle.
  Admitted. (* relies on group properties, e.g. distributivity, exp *)

End EdDSA.
