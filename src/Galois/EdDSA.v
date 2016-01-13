Require Import ZArith NPeano.
Require Import Bedrock.Word.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Galois.BaseSystem Crypto.Galois.ZGaloisField Crypto.Galois.GaloisTheory.
Require Import Util.ListUtil Util.CaseUtil Util.ZUtil.
Require Import VerdiTactics.

Local Open Scope nat_scope.
Local Coercion Z.to_nat : Z >-> nat.

(* TODO : where should this be? *)
Definition wfirstn {m} {n} (w : word m) (H : n <= m) : word n.
  refine (split1 n (m - n) (match _ in _ = N return word N with
                            | eq_refl => w
                            end)); abstract omega.
Defined.

Class Encoding (T B:Type) := {
  enc : T -> B ;
  dec : B -> option T ;
  encoding_valid : forall x, dec (enc x) = Some x  
}.
Notation "'encoding' 'of' T 'as' B" := (Encoding T B) (at level 50).

(* Spec from <https://eprint.iacr.org/2015/677.pdf> *)
Module Type EdDSAParams.
  Parameter q : Prime.
  Axiom q_odd : q > 2.

  (* Choosing q sufficiently large is important for security, since the size of
   * q constrains the size of l below. *)

  (* GF is the finite field of integers modulo q *)
  Module Modulus_q <: Modulus.
    Definition modulus := q.
  End Modulus_q.

  Parameter b : nat.
  Axiom b_valid : (2^(Z.of_nat b - 1) > q)%Z.
  Notation secretkey := (word b) (only parsing).
  Notation publickey := (word b) (only parsing).
  Notation signature := (word (b + b)) (only parsing).

  Parameter H : forall {n}, word n -> word (b + b).
  (* A cryptographic hash function. Conservative hash functions are recommended
   * and do not have much impact on the total cost of EdDSA. *)

  Parameter c : nat.
  Axiom c_valid : c = 2 \/ c = 3.
  (* Secret EdDSA scalars are multiples of 2^c. The original specification of
   * EdDSA did not include this parameter: it implicitly took c = 3. *)

  Parameter n : nat.
  Axiom n_ge_c : n >= c.
  Axiom n_le_b : n <= b.

  Module Import GFDefs := ZGaloisField Modulus_q.
  Local Open Scope GF_scope.

  (* Secret EdDSA scalars have exactly n + 1 bits, with the top bit
   *   (the 2n position) always set and the bottom c bits always cleared.
   * The original specification of EdDSA did not include this parameter:
   *   it implicitly took n = b−2.
   * Choosing n sufficiently large is important for security:
   *   standard “kangaroo” attacks use approximately 1.36\sqrt(2n−c) additions
   *   on average to determine an EdDSA secret key from an EdDSA public key *)

  Parameter a : GF.
  Axiom a_nonzero : a <> 0%GF.
  Axiom a_square : exists x, x * x = a.
  (* The usual recommendation for best performance is a = −1 if q mod 4 = 1,
   *   and a = 1 if q mod 4 = 3.
   * The original specification of EdDSA did not include this parameter:
   *   it implicitly took a = −1 (and required q mod 4 = 1). *)

  Parameter d : GF.
  Axiom d_nonsquare : forall x, x^2 <> d.
  (* The exact choice of d (together with a and q) is important for security,
   *   and is the main topic considered in “curve selection”. *)

  (* E = {(x, y) \in Fq x Fq : ax^2 + y^2 = 1 + dx^2y^2}.
   * This set forms a group with neutral element 0 = (0, 1) under the
   *   twisted Edwards addition law. *)
  Module CurveParameters <: TwistedEdwardsParams Modulus_q.
    Module GFDefs := GFDefs.
    Definition char_gt_2 : inject 2 <> 0.
    Admitted. (* follows from q_odd *)
    Definition a : GF := a.
    Definition a_nonzero := a_nonzero.
    Definition a_square := a_square.
    Definition d := d.
    Definition d_nonsquare := d_nonsquare.
  End CurveParameters.
  Module Export Facts := CompleteTwistedEdwardsFacts Modulus_q CurveParameters.
  Module Export Curve := Facts.Curve.
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
  Axiom l_odd : (l > 2)%nat.
  Axiom l_order_B : scalarMult l B = zero.
  (* TODO: (2^c)l = #E *)

  (*
   * A “prehash” function H'.
   * PureEdDSA means EdDSA where H' is the identity function, i.e. H'(M) = M.
   * HashEdDSA means EdDSA where H' generates a short output, no matter how
   *   long the message is; for example, H'(M) = SHA-512(M).
   * The original specification of EdDSA did not include this parameter:
   *   it implicitly took H0 as the identity function.
   *)
  Parameter H'_out_len : nat -> nat.
  Parameter H' : forall {n}, word n -> word (H'_out_len n).

  Parameter FqEncoding : encoding of GF as word (b-1).
  Parameter FlEncoding : encoding of {s:nat | s mod l = s} as word b.
  Parameter PointEncoding : encoding of point as word b.
  
End EdDSAParams.

Hint Rewrite Nat.mod_mod using omega.

Ltac arith' := intros; autorewrite with core; try (omega || congruence).

Ltac arith := arith';
             repeat match goal with
                    | [ H : _ |- _ ] => rewrite H; arith'
                    end.

Definition modularNat (l : nat) (l_odd : l > 2) (n : nat) : {s : nat | s mod l = s}.
  exists (n mod l); abstract arith.
Defined.

Module Type EdDSA (Import P : EdDSAParams).
  Infix "++" := combine.
  Infix "*" := scalarMult.
  Infix "+" := unifiedAdd.
  Coercion wordToNat : word >-> nat.

  Definition curveKey sk := let N := wfirstn sk n_le_b in
    (N - (N mod pow2 c) + pow2 n)%nat.
  Definition randKey (sk:secretkey) := split2 b b (H sk).
  Definition modL := modularNat l l_odd.

  Parameter public : secretkey -> publickey.
  Axiom public_spec : forall sk, public sk = enc (curveKey sk * B).

  (* TODO: use GF for both GF(q) and GF(l) *)
  Parameter sign : publickey -> secretkey -> forall {n}, word n -> signature.
  Axiom sign_spec : forall A_ sk {n} (M : word n), sign A_ sk M = 
    let r := H (randKey sk ++ M) in
    let R := r * B in
    let s := curveKey sk in
    let S := (r + H (enc R ++ public sk ++ M) * s)%nat in
    enc R ++ enc (modL S).

  Parameter verify : publickey -> forall {n}, word n -> signature -> bool.
  Axiom verify_spec : forall A_ sig {n} (M : word n), verify A_ M sig  = true <-> (
    let R_ := split1 b b sig in
    let S_ := split2 b b sig in
    exists A, dec A_ = Some A /\
    exists R, dec R_ = Some R /\
    exists S : {s:nat | s mod l = s}, dec S_ = Some S /\
    proj1_sig S * B = R + wordToNat (H (R_ ++ A_ ++ M)) * A).
End EdDSA.

Module EdDSAFacts (Import P : EdDSAParams) (Import Impl : EdDSA P).
  Hint Rewrite sign_spec split1_combine split2_combine.

  (* for signature (R_, S_), R_ = encode_point (r * B) *) 
  Lemma decode_sign_split1 : forall A_ sk {n} (M : word n),
    split1 b b (sign A_ sk M) = enc (wordToNat (H (randKey sk ++ M)) * B).
  Proof.
    arith.
  Qed.
  Hint Rewrite decode_sign_split1.

  (* for signature (R_, S_), S_ = encode_scalar (r + H(R_, A_, M)s) *) 
  Lemma decode_sign_split2 : forall sk {n} (M : word n),
    split2 b b (sign (public sk) sk M) =
    let r := H (randKey sk ++ M) in
    let R := r * B in
    let s := curveKey sk in
    let S := (r + (H ((enc R) ++ (public sk) ++ M) * s))%nat in
    enc (modL S).
  Proof.
    arith.
  Qed.
  Hint Rewrite decode_sign_split2.

  Lemma zero_times : forall n, 0 * n = zero.
  Proof.
    auto.
  Qed.

  Lemma zero_plus : forall n, zero + n = n.
  Proof.
    intros; rewrite twistedAddComm; apply zeroIsIdentity.
  Qed.

  Lemma times_S : forall n m, S n * m = m + n * m.
  Proof.
    auto.
  Qed.

  Lemma times_S_nat : forall n m, (S n * m = m + n * m)%nat.
  Proof.
    auto.
  Qed.

  Hint Rewrite plus_O_n plus_Sn_m times_S times_S_nat.
  Hint Rewrite zeroIsIdentity zero_times zero_plus twistedAddAssoc.

  Lemma scalarMult_distr : forall n0 m, (n0 + m) * B = Curve.unifiedAdd (n0 * B) (m * B).
  Proof.
    induction n0; arith.
  Qed.
  Hint Rewrite scalarMult_distr.

  Lemma scalarMult_assoc : forall (n0 m : nat), n0 * (m * B) = (n0 * m) * B.
  Proof.
    induction n0; arith.
  Qed.
  Hint Rewrite scalarMult_assoc.

  Lemma scalarMult_zero : forall m, m * zero = zero.
  Proof.
    induction m; arith.
  Qed.
  Hint Rewrite scalarMult_zero.
  Hint Rewrite l_order_B.

  Lemma l_order_B' : forall x, l * x * B = zero.
  Proof.
    intros; rewrite mult_comm; rewrite <- scalarMult_assoc; arith.
  Qed.

  Hint Rewrite l_order_B'.

  Lemma scalarMult_mod_l : forall n0, n0 mod l * B = n0 * B.
  Proof.
    intros.
    rewrite (div_mod n0 l) at 2 by (generalize l_odd; omega).
    arith.
  Qed.
  Hint Rewrite scalarMult_mod_l.

  Hint Rewrite verify_spec public_spec.

  Hint Resolve @encoding_valid.

  Lemma verify_valid_passes : forall sk {n} (M : word n),
    verify (public sk) M (sign (public sk) sk M) = true.
  Proof.
    arith; simpl.
    repeat eexists; eauto; simpl; arith.
  Qed.

End EdDSAFacts.
