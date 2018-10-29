Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Require Import Crypto.lattice.Bytes Crypto.lattice.Matrix.
Require Import Crypto.lattice.PolynomialRing.
Require Import Crypto.lattice.Spec.
Local Open Scope Z_scope.

(* This parameter set is too small to be useful; its purpose is to be small enough for manual simplification so the definitions can be sanity-checked. *)
Module Kyber32.
  Definition n := 32%nat.
  Definition k := 1%nat.
  Definition q := 5%positive.
  Definition log2q := Eval compute in (Pos.size q).
  Definition eta := 3%nat.
  Definition du := 5%positive.
  Definition dv := 1%positive.
  Definition dt := 5%positive.

  Definition pksize := Eval compute in (KyberSpec.pksize k n dt).
  Definition sksize := Eval compute in (KyberSpec.sksize k n log2q).
  Definition ciphertextsize := Eval compute in (KyberSpec.ciphertextsize k n du dv).
  Definition msgsize := Eval compute in (KyberSpec.msgsize n).

  (* For now, use a dummy NTT function that does nothing *)
  Definition Rq_NTT := @PolynomialRing.Rq n q.
  Definition NTT (x : @PolynomialRing.Rq n q) : Rq_NTT := x.
  Definition NTT_inv (x : Rq_NTT) : @PolynomialRing.Rq n q := x.
  Definition NTT_to_F (x : Rq_NTT) : tuple (F (2^log2q)) n := map (fun y => F.of_Z _ (F.to_Z y)) x.
  Definition NTT_of_F (x : tuple (F (2^log2q)) n) : Rq_NTT := map (fun y => F.of_Z _ (F.to_Z y)) x.
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.
  Lemma nmod8 : (n mod 8 = 0)%nat. Proof. reflexivity. Qed.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen
         stream byte
         k eta n q log2q dt
         XOF PRF G
         (F q) (F.to_Z) (F.of_Z q)
         (@PolynomialRing.add n q)
         _ (@PolynomialRing.zero n q) (@PolynomialRing.add n q) (@PolynomialRing.mul n q)
         NTT NTT_inv NTT_to_F
         nmod8
         nat_to_byte bytes_to_stream stream_to_bytes
         bytes_to_bits bits_to_bytes
         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc
         stream byte
         k eta n q dt du dv
         XOF PRF
         (F q) (F.to_Z) (F.of_Z q)
         (@PolynomialRing.add n q)
         _ (@PolynomialRing.zero n q) (@PolynomialRing.add n q) (@PolynomialRing.mul n q)
         NTT NTT_inv
         nmod8
         byte0 nat_to_byte bytes_to_stream stream_to_bytes
         bytes_to_bits bits_to_bytes
         pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec
         byte
         k n q log2q du dv
         (F q) F.to_Z (F.of_Z q)
         (@PolynomialRing.sub n q)
         _ (@PolynomialRing.zero n q) (@PolynomialRing.add n q) (@PolynomialRing.mul n q)
         NTT NTT_inv NTT_of_F
         nmod8
         byte0
         bytes_to_bits bits_to_bytes
         sk c.

  Derive encode SuchThat
         (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 x,
             (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9
          , x10, x11, x12, x13, x14, x15, x16, x17, x18, x19
          , x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
          , x30, x31) = x ->
               encode x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 = @KyberSpec.encode byte n nmod8 bits_to_bytes 1 x) As encode_eq.
  Proof.
    intros. subst x.
    cbv - [PolynomialRing.bits_to_bytes byte Tuple.flat_map KyberSpec.F_to_bits Tuple.flat_map F id].
    cbv [Tuple.flat_map]. Tuple.to_default false.
    cbn - [Z.testbit]. cbv - [F byte] in encode.
    exact eq_refl.
  Qed.

  Local Ltac decode_simpl :=
    cbv - [map F KyberSpec.split_array bytes_to_bits get_bit KyberSpec.bits_to_F];
    cbv [bytes_to_bits Tuple.flat_map];
    rewrite <-Tuple.on_tuple_default_eq with (d:= false);
    cbv [map map' Tuple.seq List.seq from_list_default from_list_default'];
    cbn [fst snd];
    cbv [KyberSpec.split_array KyberSpec.bits_to_F];
    cbn - [F F.of_Z Z.shiftl Z.add get_bit].

  Derive decode1 SuchThat
         (forall c0 c1 c2 c3 c,
             (c0, c1, c2, c3) = c ->
             decode1 c0 c1 c2 c3 = @KyberSpec.decode byte n bytes_to_bits 1 c) As decode1_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  Derive decode3 SuchThat
         (forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c,
             (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11) = c ->
             decode3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
             = @KyberSpec.decode byte n bytes_to_bits 3 c) As decode3_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  Derive decode5 SuchThat
         (forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c,
             (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19) = c ->
             decode5 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19
             = @KyberSpec.decode byte n bytes_to_bits 5 c) As decode5_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  (* TODO : prove and move to ListUtil *)
  Lemma fold_right_ext {A B} f g x l :
    (forall b a, f b a = g b a) ->
    @fold_right A B f x l = fold_right g x l.
  Admitted.

  Derive matrix_mul111 SuchThat
         (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
                 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                 x30 x31 x
                 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
                 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
                 y30 y31 y,
             (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
              x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
              x20, x21, x22, x23, x24, x25, x26, x27, x28, x29,
              x30, x31) = x ->
             (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9,
              y10, y11, y12, y13, y14, y15, y16, y17, y18, y19,
              y20, y21, y22, y23, y24, y25, y26, y27, y28, y29,
              y30, y31) = y ->
             matrix_mul111
                 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
                 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                 x30 x31
                 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
                 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
                 y30 y31 =
             @Matrix.mul Rq_NTT PolynomialRing.zero PolynomialRing.add PolynomialRing.mul 1 1 1 x y) As matrix_mul_eq.
  Proof.
    intros. subst x y.
    cbv [Matrix.mul Matrix.sum Matrix.get].
    cbv [PolynomialRing.zero n repeat append].
    cbv [List.seq seq from_list_default from_list_default'].
    cbv [map map'].
    cbv [List.map nth_default hd hd'].
    cbv [PolynomialRing.mul Lists.to_associational map2 on_tuple2].
    rewrite !to_list_from_list.
    cbv [List.seq seq from_list_default from_list_default'].
    cbv [to_list to_list' ListUtil.map2].
    cbv [Lists.assoc_mul Lists.multerm List.flat_map List.map app].
    cbn [fst snd Nat.add].
    cbv [Lists.from_associational Lists.from_associational'].
    erewrite fold_right_ext with (g := fun xi => on_tuple_default _ _)
      by (intros; cbv [update_nth]; Tuple.to_default (@F.zero q); reflexivity).
    cbv - [matrix_mul111 PolynomialRing.add F.add F.mul F F.of_Z].
    cbv [PolynomialRing.add].
    cbv [map2 on_tuple2].
    Tuple.to_default (@F.zero q).
    cbn.
    destruct (F.commutative_ring_modulo q).
    destruct commutative_ring_ring.
    destruct ring_commutative_group_add.
    destruct commutative_group_group.
    destruct group_monoid.
    destruct monoid_is_left_identity, monoid_is_right_identity.
    progress rewrite ?left_identity, ?right_identity.
    subst matrix_mul111; reflexivity.
  Qed.

  Local Notation "subst! v 'for' x 'in' e" := (match v with x => e end) (at level 200).
  Derive Dec' SuchThat
         (forall (sk0 sk1 sk2 sk3 sk4 sk5 sk6 sk7 sk8 sk9 sk10 sk11
                      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
                      c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23: byte) sk c,
             (sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11) = sk ->
             (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23) = c ->
             Dec' sk0 sk1 sk2 sk3 sk4 sk5 sk6 sk7 sk8 sk9 sk10 sk11 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23
               = Dec sk c) As Dec'_correct.
  Proof.
    intros. subst sk c.
    cbv [Dec KyberSpec.Dec].
    cbv - [byte] in Dec'.
    cbv [NTT NTT_inv].
    cbv [KyberSpec.polyvec_decode].
    cbv [KyberSpec.polyvec_encode].
    erewrite <-encode_eq.
    2 : {
    cbv [Nat.div Pos.to_nat du dv k n log2q Nat.divmod fst Pos.iter_op Nat.add Nat.mul].
    cbv [Pos.pow Pos.iter Pos.mul].
    cbv [KyberSpec.bits_to_F KyberSpec.bits_to_Z KyberSpec.F_to_bits KyberSpec.split_array].
    cbv [firstn skipn].
    Tuple.to_default byte0.
    cbn [Nat.add to_list to_list' List.firstn List.skipn].
    cbv [seq List.seq from_list_default from_list_default'].
    cbn [map map' fst snd Nat.add Nat.mul nth_default hd hd' tl tl'].
    erewrite <-decode1_eq by reflexivity.
    erewrite <-decode3_eq by reflexivity.
    erewrite <-decode5_eq by reflexivity.

    cbv [decode3].
    cbv [NTT_of_F].
    cbn [n map map' fst snd].
    cbv [log2q].
    rewrite !F.to_Z_of_Z.
    rewrite !Z.mod_0_l by congruence.

    cbv [decode5 decode1].
    cbv [map2 on_tuple2].
    cbv [KyberSpec.polyvec_decompress KyberSpec.poly_decompress].
    cbn [map map' fst snd].

    erewrite <-matrix_mul_eq by reflexivity. cbv [matrix_mul111].
    rewrite !F.to_Z_of_Z.
    autorewrite with zsimplify_fast.
    change (Z.shiftr 1 1) with 0.
    rewrite !(@Ring.mul_0_l (F q) _ (F.of_Z q 0%Z)) by apply F.commutative_ring_modulo.
    destruct (F.commutative_ring_modulo q).
    destruct commutative_ring_ring.
    destruct ring_commutative_group_add.
    destruct commutative_group_group.
    destruct group_monoid.
    destruct monoid_is_left_identity, monoid_is_right_identity.
    rewrite !left_identity. rewrite !right_identity.
    
    cbv [PolynomialRing.sub PolynomialRing.opp].
    cbn [map map' fst snd].
    cbv [PolynomialRing.add map2].
    Tuple.to_default (@F.zero q).
    cbn [to_list to_list'].
    cbn [ListUtil.map2 from_list_default from_list_default'].
    rewrite !left_identity.

    cbv [KyberSpec.poly_compress map map' fst snd].
    rewrite <-!F.of_Z_mul.
    rewrite <-!F.of_Z_add.
    rewrite <-!F.of_Z_opp.
    rewrite !F.to_Z_of_Z.
    autorewrite with zsimplify_fast.
    reflexivity. }

    cbv [encode]. rewrite !F.to_Z_of_Z.
    subst Dec'; reflexivity.
  Abort.
End Kyber32.