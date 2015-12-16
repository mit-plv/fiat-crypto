Require Import ZArith NPeano.
Require Import Bedrock.Word.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Galois.BaseSystem Crypto.Galois.GaloisTheory.
Require Import Util.ListUtil Util.CaseUtil Util.ZUtil.
Require Import VerdiTactics.

(* TODO : where should this be? *)
Definition wfirstn {m} {n} (w : word m) (H : (n <= m)%nat) : word n.
  replace m with (n + (m - n))%nat in * by (symmetry; apply le_plus_minus; apply H)
.
  exact (split1 n (m - n) w).
Defined.

Class Encoding (T B:Type) := {
  enc : T -> B ;
  dec : B -> option T ;
  encoding_valid : forall x, dec (enc x) = Some x  
}.
Notation "'encoding' 'of' T 'as' B" := (Encoding T B) (at level 50).

(* Spec from <https://eprint.iacr.org/2015/677.pdf> *)
Module Type EdDSAParams.
  Open Scope Z_scope.
  Coercion Z.of_nat : nat >-> Z.
  Coercion Z.to_nat : Z >-> nat.

  Parameter q : Prime.
  Axiom q_odd : q > 2.
  (* Choosing q sufficiently large is important for security, since the size of
  * q constrains the size of l below. *)

  (* GF is the finite field of integers modulo q *)
  Module Modulus_q <: Modulus.
    Definition modulus := q.
  End Modulus_q.
  Module Export GFDefs := GaloisDefs Modulus_q.

  Parameter b : nat.
  Axiom b_valid : 2^(b - 1) > q.
  Notation secretkey := (word b) (only parsing).
  Notation publickey := (word b) (only parsing).
  Notation signature := (word (b + b)) (only parsing).

  Parameter H : forall {n}, word n -> word (b + b).
  (* A cryptographic hash function. Conservative hash functions are recommended
  * and do not have much impact on the total cost of EdDSA. *)

  Parameter c : nat.
  Axiom c_valid : (c = 2 \/ c = 3)%nat.
  (* Secret EdDSA scalars are multiples of 2^c. The original specification of
  *  EdDSA did not include this parameter: it implicitly took c = 3. *)

  Parameter n : nat.
  Axiom n_ge_c : (n >= c)%nat.
  Axiom n_le_b : (n <= b)%nat.
  (* Secret EdDSA scalars have exactly n + 1 bits, with the top bit
  *   (the 2n position) always set and the bottom c bits always cleared.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took n = b−2.
  * Choosing n sufficiently large is important for security:
  *   standard “kangaroo” attacks use approximately 1.36\sqrt(2n−c) additions
  *   on average to determine an EdDSA secret key from an EdDSA public key *)

  Parameter a : GF.
  Axiom a_nonzero : a <> 0%GF.
  Axiom a_square : exists x, x^2 = a.
  (* The usual recommendation for best performance is a = −1 if q mod 4 = 1,
  *   and a = 1 if q mod 4 = 3.
  * The original specification of EdDSA did not include this parameter:
  *   it implicitly took a = −1 (and required q mod 4 = 1). *)

  Parameter d : GF.
  Axiom d_nonsquare : forall x, x^2 <> d.
  (* The exact choice of d (together with a and q) is important for security,
  *   and is the main topic considered in “curve selection”. *)

  (* E = {(x, y) \in Fq x Fq : ax^2 + y^2 = 1 + dx^2y^2}.
  *  This set forms a group with neutral element 0 = (0, 1) under the
  *    twisted Edwards addition law. *)
  Module CurveParameters <: TwistedEdwardsParams Modulus_q.
    Module GFDefs := GFDefs.
    Definition a : GF := a.
    Definition a_nonzero := a_nonzero.
    Definition a_square := a_square.
    Definition d := d.
    Definition d_nonsquare := d_nonsquare.
  End CurveParameters.
  Module Export Curve := CompleteTwistedEdwardsCurve Modulus_q CurveParameters.

  Parameter B : point. (* element of E *)
  Axiom B_not_identity : B <> zero.

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
  Axiom l_order_B : scalarMult l B = zero.
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

  Parameter FqEncoding : encoding of GF as word (b-1).
  Parameter FlEncoding : encoding of {s:Z | s = s mod l} as word (b-1).
  Parameter PointEncoding : encoding of point as word b.
End EdDSAParams.
  
Module Type EdDSA (Import P : EdDSAParams).
  Infix "++" := combine.
  Infix "*" := scalarMult.
  Infix "+" := unifiedAdd.
  Infix "mod" := modulo.

  Definition curveKey sk := (let N := wordToNat (wfirstn sk n_le_b) in N - (N mod 2^c))%nat.
  Definition  randKey (sk:secretkey) := split2 b b (H sk).

  Parameter public : secretkey -> publickey.
  Axiom public_spec : forall sk, public sk = enc ((curveKey sk) * B).

  (* TODO: use GF for both GF(q) and GF(l) *)
  Parameter sign : publickey -> secretkey -> forall {n}, word n -> signature.
  Axiom sign_spec : forall A_ sk {n} (M : word n), sign A_ sk M = 
    let r := wordToNat (H (randKey sk  ++ M)) in
    let R := r * B in
    let S := (r + curveKey sk * wordToNat (H (enc R ++ A_ ++ M)))%nat mod (Z.to_nat l) in
    enc R ++ natToWord b S.

  Parameter verify : publickey -> forall {n}, word n -> signature -> bool.
  Axiom verify_spec : forall A_ sig {n} (M : word n), verify A_ M sig  = true <-> (
    let R_ := split1 b b sig in
    let S_ := split2 b b sig in
    let S := wordToNat S_ in
    exists A, dec A_ = Some A /\
    exists R, dec R_ = Some R /\
    S * B = R + (wordToNat (H (R_ ++ A_ ++ M )) * A) ).
End EdDSA.

Module EdDSAFacts (Import P : EdDSAParams) (Import Impl : EdDSA P).
  (* for signature (R_, S_), R_ = encode_point (r * B) *) 
  Lemma decode_sign_split1 : forall A_ sk {n} (M : word n),
    split1 b b (sign A_ sk M) = enc ((wordToNat (H (randKey sk ++ M))) * B).
  Proof.
    intros. pose proof (sign_spec A_ sk M).
    simpl in H0. rewrite H0; clear H0.
    apply split1_combine.
  Qed.
  
  (* for signature (R_, S_), S_ = encode_scalar (r + H(R_, A_, M)s) *) 
  Lemma decode_sign_split2 : forall sk {n} (M : word n),
    split2 b b (sign (public sk) sk M) =
    let r := wordToNat (H (randKey sk ++ M)) in
    natToWord b (NPeano.modulo (r + ((curveKey sk) * wordToNat (H ((enc (r * B)) ++ (public sk) ++ M)))) (Z.to_nat l)).
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

  (* TODO : move somewhere else (EdDSAFacts?) *)
  Lemma verify_valid_passes : forall sk {n} (M : word n),
    verify (public sk) M (sign (public sk) sk M) = true.
  Proof.
    intros; rewrite verify_spec.
    intros; subst R_.
    rewrite decode_sign_split1.
    rewrite public_spec.
    exists (curveKey sk * B); intuition; [apply encoding_valid|].
    exists (wordToNat (H (randKey sk ++ M)) * B); intuition; [apply encoding_valid|].
    subst S S_.
    rewrite decode_sign_split2.
    remember (wordToNat (H (randKey sk ++ M))) as r.
    rewrite public_spec.
    cbv zeta.
    remember (wordToNat
      (H (enc (r * B) ++ enc (curveKey sk * B) ++ M))) as c; simpl in Heqc.
    assert (N.of_nat (NPeano.modulo (r + curveKey sk * c) (Z.to_nat l)) < Npow2 b)%N as Hlt. {
      remember (r + curveKey sk * c)%nat as t.
      pose proof (NPeano.Nat.mod_upper_bound t (Z.to_nat l) l_gt_zero).
      pose proof l_bound.
      pose proof (lt_trans _ (Z.to_nat l) (pow2 b) H0 H1).
      clear H0 H1.
      apply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    }
    rewrite wordToNat_natToWord_idempotent by auto.
    rewrite verification_principle.
    admit. (* relies on group properties, e.g. distributivity, exp *)
  Qed.
End EdDSAFacts.
