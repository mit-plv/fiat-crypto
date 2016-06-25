Require Import Crypto.Spec.Encoding.

Section EncodingTheorems.
  Context {A B : Type} {E : canonical encoding of A as B}.

  Lemma encoding_inj : forall x y, enc x = enc y -> x = y.
  Proof.
    intros.
    assert (dec (enc x) = dec (enc y)) as dec_enc_eq by (f_equal; auto).
    do 2 rewrite encoding_valid in dec_enc_eq.
    inversion dec_enc_eq; auto.
  Qed.

End EncodingTheorems.
