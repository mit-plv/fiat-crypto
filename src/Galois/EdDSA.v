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
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion Z.to_nat : Z >-> nat.

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
  Parameter FlEncoding : encoding of {s:nat | s = (s mod (Z.to_nat l))%nat} as word b.
  Parameter PointEncoding : encoding of point as word b.
  
End EdDSAParams.

Definition modularZ (m z : Z) : {s : Z | s = (s mod m)%Z}.
  exists (z mod m)%Z.
  symmetry; apply (Zmod_mod z m).
Defined.

Definition modularNat (l : Z) (l_odd : (l > 2)%Z) (n : nat) : {s : nat | s = s mod (Z.to_nat l)}.
  exists (n mod (Z.to_nat l)).
  symmetry; apply (Nat.mod_mod n (Z.to_nat l)); auto.
  assert (l > 0)%Z by omega.
  intuition.
  replace 0 with (Z.to_nat 0%Z) in H0 by auto.
  assert (l = 0)%Z.
  rewrite (Z2Nat.inj l 0%Z) by omega; auto.
  omega.
Defined.

Module Type EdDSA (Import P : EdDSAParams).
  Infix "++" := combine.
  Infix "*" := scalarMult.
  Infix "+" := unifiedAdd.

  Definition curveKey sk := (let N := wordToNat (wfirstn sk n_le_b) in N - (N mod 2^c))%nat.
  Definition  randKey (sk:secretkey) := split2 b b (H sk).
  Definition modL := modularNat l l_odd.

  Parameter public : secretkey -> publickey.
  Axiom public_spec : forall sk, public sk = enc ((curveKey sk) * B).

  (* TODO: use GF for both GF(q) and GF(l) *)
  Parameter sign : publickey -> secretkey -> forall {n}, word n -> signature.
  Axiom sign_spec : forall A_ sk {n} (M : word n), sign A_ sk M = 
    let r := wordToNat (H (randKey sk ++ M)) in
    let R := r * B in
    let c := wordToNat (H ((enc R) ++ (public sk) ++ M)) in
    let S := (r + ((curveKey sk) * c))%nat in
    enc R ++ enc (modL S).

  Parameter verify : publickey -> forall {n}, word n -> signature -> bool.
  Axiom verify_spec : forall A_ sig {n} (M : word n), verify A_ M sig  = true <-> (
    let R_ := split1 b b sig in
    let S_ := split2 b b sig in
    exists A, dec A_ = Some A /\
    exists R, dec R_ = Some R /\
    exists S : {s:nat | s = (s mod (Z.to_nat l))%nat}, dec S_ = Some S /\
    (proj1_sig S) * B = R + (wordToNat (H (R_ ++ A_ ++ M )) * A) ).
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

  Lemma l_nonzero_nat : Z.to_nat l <> 0%nat.
  Proof.
    pose proof l_odd.
    destruct l; destruct x; boring.
    assert (p0 > 2)%positive by auto.
    rewrite Pos2Nat.inj_gt in H2.
    omega.
    pose proof (Zlt_neg_0 p0); omega.
  Qed.

  (* for signature (R_, S_), S_ = encode_scalar (r + H(R_, A_, M)s) *) 
  Lemma decode_sign_split2 : forall sk {n} (M : word n),
    split2 b b (sign (public sk) sk M) =
    let r := wordToNat (H (randKey sk ++ M)) in
    let R' := r * B in
    let c' := wordToNat (H ((enc R') ++ (public sk) ++ M)) in
    let S' := (r + ((curveKey sk) * c'))%nat in
    enc (modL S').
  Proof.
    intros. rewrite sign_spec; simpl.
    rewrite split2_combine.
    f_equal.
  Qed.

  Lemma scalarMult_distr : forall n m, (n + m) * B = Curve.unifiedAdd (n * B) (m * B).
  Proof.
    intros; induction n0. {
      rewrite plus_O_n.
      unfold scalarMult at 2.
      rewrite (twistedAddComm zero (m * B)).
      rewrite zeroIsIdentity; auto.
    } {
      rewrite plus_Sn_m. simpl.
      rewrite IHn0.
      rewrite twistedAddAssoc; auto.
    }
  Qed.

  Lemma scalarMult_assoc : forall (n0 m : nat), n0 * (m * B) = (n0 * m) * B.
  Proof.
    intros; induction n0; simpl; auto.
    rewrite IHn0.
    rewrite scalarMult_distr; reflexivity.
  Qed.

  Lemma scalarMult_zero : forall m, m * zero = zero.
  Proof.
    induction m; auto.
    unfold scalarMult at 1.
    fold scalarMult; rewrite IHm.
    rewrite zeroIsIdentity; auto.
  Qed.

  Lemma scalarMult_mod_l : forall n, (n mod (Z.to_nat l)) * B = n * B.
  Proof.
    intros.
    rewrite (div_mod n0 (Z.to_nat l)) at 2 by apply l_nonzero_nat.
    rewrite scalarMult_distr.
    rewrite mult_comm.
    rewrite <- scalarMult_assoc.
    replace ((Z.to_nat l) * B) with zero by (symmetry; apply l_order_B).
    rewrite scalarMult_zero.
    rewrite twistedAddComm.
    rewrite zeroIsIdentity; reflexivity.
  Qed.

  Lemma wordToNat_posToWord_Ztopos : forall sz z,
    (0 < z) ->
    (N.pos (Z.to_pos z) < Npow2 sz)%N ->
    wordToNat (posToWord sz (Z.to_pos z)) = Z.to_nat z.
  Proof.
    intros.
    rewrite posToWord_nat.
    rewrite wordToNat_natToWord_idempotent by (rewrite positive_nat_N; auto).
    rewrite (Nat2Z.inj _ (Z.to_nat z)); auto.
    rewrite positive_nat_Z.
    rewrite Z2Pos.id by auto.
    rewrite Z2Nat.id by omega; reflexivity.
  Qed.

  (* TODO : move somewhere else (EdDSAFacts?) *)
  Lemma verify_valid_passes : forall sk {n} (M : word n),
    verify (public sk) M (sign (public sk) sk M) = true.
  Proof.
    intros; rewrite verify_spec.
    intros; subst R_ S_.
    rewrite decode_sign_split1.
    rewrite decode_sign_split2.
    rewrite public_spec.
    remember (wordToNat (H (randKey sk ++ M))) as r.
    do 3 (eexists; intuition; [apply encoding_valid|]).
    cbv zeta.
    remember ( wordToNat
      (H (enc (r * B) ++ enc (curveKey sk * B) ++ M))) as c; simpl in Heqc.
    simpl.
    rewrite scalarMult_mod_l.
    rewrite scalarMult_distr.
    f_equal.
    rewrite scalarMult_assoc.
    rewrite mult_comm; f_equal.
  Qed.

End EdDSAFacts.
