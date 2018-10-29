Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Require Import Crypto.lattice.PolynomialRing.
Local Open Scope Z_scope.

(* Basic matrix operations *)
Module Matrix.
  Section matrix.
    Context (T : Type) (Tzero : T) (Tadd : T -> T -> T) (Tmul : T -> T -> T).
    Definition matrix n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)
    Definition matrix_get {n m} (A : matrix n m) (i j : nat) : T :=
      nth_default Tzero j (nth_default (repeat Tzero m) i A).
    Local Notation "A [ i ][ j ]" := (matrix_get A i j) (at level 0).
    Local Infix "*" := Tmul.

    Definition sum : list T -> T := fold_right Tadd Tzero.
    Definition matrix_mul n m p (A : matrix n m) (B : matrix m p) : matrix n p :=
      map (fun j => (* forall j := 0...n *)
             map (fun i => (* forall i := 0...p *)
                    (* AB[i][j] = sum_{k=0}{m} A[i][k] * B[k][j] *)
                    sum (List.map (fun k => A[i][k] * B[k][j]) (List.seq 0 m)))
                 (seq 0 p))
          (seq 0 n).
    Definition matrix_transpose n m (A : matrix n m) : matrix m n :=
      map (fun j => map (fun i => A[j][i]) (seq 0 n)) (seq 0 m).
  End matrix.
End Matrix.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)
Module KyberSpec.
  Import Tuple. Import Matrix.
  Section KyberSpec.
    Context {stream byte : Type}. (* type of bytes and bytestreams *)
    Local Notation byte_array n := (tuple byte n).
    Local Notation bit_array n := (tuple bool n).

    (* Kyber parameters *)
    Context (k eta n : nat) (q log2q : positive)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : stream -> stream) (* "extendable output function" *)
            (PRF : byte_array 32 * byte -> stream) (* pseudorandom function *)
            (H : stream -> byte_array 32)
            (G : stream -> byte_array 32 * byte_array 32). (* hash function *)

    Context (Fq : Type). (* Type of coefficients *)
    Context {Fqeq Fqzero Fqone Fqopp Fqadd Fqsub Fqmul Fqinv Fqdiv}
            (* Operations on coefficients form a field *)
            (Fqfield : @field Fq Fqeq Fqzero Fqone Fqopp Fqadd Fqsub Fqmul Fqinv Fqdiv).
    Context (Fq_to_Z : Fq -> Z) (Fq_of_Z : Z -> Fq). (* Convert to and from Coq integers *)

    Notation Rq := (tuple Fq n). (* Type of polynomials (n-tuple of coefficients) *)
    Context {Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul}
            (* Operations on polynomials form a ring *)
            (Rqring : @ring Rq Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul).

    (* NTT domain *)
    Context (Rq_NTT : Type) (* Type of polynomials in NTT domain *)
            {Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul}
            (* Operations on NTT-domain polynomials form a ring *)
            (Rq_NTTring : @ring Rq_NTT Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul).
    Context (NTT : Rq -> Rq_NTT) (NTT_inv : Rq_NTT -> Rq). (* Convert to and from NTT domain *)
    Context (NTT_of_F :tuple (F (2^log2q)) n -> Rq_NTT) (NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n). (* Convert to and from integers *)

    Context (nmod8 : (n mod 8 = 0)%nat). (* This is necessary for encodings *)

    (* More parameters about bytes *)
    Context (default_byte : byte) (nat_to_byte : nat -> byte)
            (bytes_to_stream : forall n, byte_array n -> stream)
            (stream_to_bytes : forall n, stream -> byte_array n)
            (bytes_to_bits : forall l, byte_array l -> bit_array (8*l))
            (bits_to_bytes : forall lx8 l (H:lx8 = (8*l)%nat),
                bit_array lx8 -> tuple byte l).
    Arguments bytes_to_bits {l}. Arguments bits_to_bytes {lx8}.
    Let nth_bit {l} (B : bit_array l) i := nth_default false i B.


    (* Algorithm 1 *)
    Axiom parse : stream -> Rq_NTT. (* TODO *)

    Section compression.
      Definition poly_compress (d : positive) : Rq -> tuple (F (2 ^ d)) n :=
        map  (fun x : Fq => F.of_Z _ ((Z.shiftl (Fq_to_Z x) d + (q / 2)) / q)).
      Definition poly_decompress {d : positive} : tuple (F (2 ^ d)) n -> Rq :=
        map (fun x : F (2 ^ d) => Fq_of_Z (Z.shiftr (F.to_Z x * q + 2^(d-1)) d)).
      Definition polyvec_compress {m} d
        : tuple Rq m -> matrix (F (2^d)) m n := map (poly_compress d).
      Definition polyvec_decompress {m d}
        : matrix (F (2^d)) m n -> tuple Rq m := map (poly_decompress).
    End compression.

    Section sample.
      (* Equivalent to \sum_{j=0}^{len-1} B[j] *)
      Definition sum_bits {n} start len (B : bit_array n) :=
        fold_right
          (fun j => Z.add (Z.b2z (nth_bit B (start + j))))
          0 (List.seq 0 len).

      (* Algorithm 2 *)
      (* NOTE : The output is not meant to represent the input, just preserve the input's randomness. *)
      Definition CBD_sample (B : byte_array (64*eta)) : Rq :=
        let B' := bytes_to_bits B in
        map (fun i =>
               let a := sum_bits (2*i*eta) eta B' in
               let b := sum_bits (2*i*eta+eta) eta B' in
               Fq_of_Z (a - b))
            (Tuple.seq 0 n).
    End sample.

    Section encoding.
      Section helpers.
        (* Splits a tuple into m chunks of n elements each *)
        Definition split_array {T} n m {nm} (* nm = n * m *)
                   (d : T) (A : tuple T nm) : tuple (tuple T n) m :=
          map (fun i => map (fun j => nth_default d (i*m+j) A) (seq 0 n)) (seq 0 m).
        Definition bits_to_Z {n} (B : bit_array n) :=
          List.fold_right
            (fun i acc => acc + Z.shiftl (Z.b2z (nth_bit B i)) (Z.of_nat i))
            0 (List.seq 0 n).
        Definition bits_to_F m {n} (B : bit_array n) :=
          F.of_Z m (bits_to_Z B).
        Definition Z_to_bits (x : Z) n : bit_array n :=
          map (fun i => Z.testbit x (Z.of_nat i)) (seq 0 n).
        Definition F_to_bits {m} (x : F m) n : bit_array n :=
          Z_to_bits (F.to_Z x) n.
        Lemma encode_sizes_ok l : (l * n = 8 * ((n / 8) * l))%nat.
        Proof. rewrite (Nat.div_mod n 8) at 1 by congruence. rewrite nmod8; lia. Qed.
      End helpers.


      Definition decode {l} (B : byte_array ((n/8)*Pos.to_nat l))
        : tuple (F (2^l)) n :=
        let B' := bytes_to_bits B in
        map (bits_to_F (2^l)) (split_array (Pos.to_nat l) n false B').
      Definition encode {l} (t : tuple (F (2^l)) n)
        : byte_array ((n/8) * Pos.to_nat l) :=
        bits_to_bytes _ (encode_sizes_ok _) (flat_map (fun x => F_to_bits x (Pos.to_nat l)) t).
      Definition polyvec_decode {k l}
                 (B : byte_array ((n/8)*Pos.to_nat l*k))
        : matrix (F (2^l)) k n :=
        map decode
            (split_array ((n/8)*Pos.to_nat l) k default_byte B).
      Definition polyvec_encode {k l}
                 (A : matrix (F (2^l)) k n)
        : byte_array ((n/8)*Pos.to_nat l*k) :=
        Tuple.flat_map encode A.
    End encoding.

    Definition pksize := (n / 8 * Pos.to_nat dt * k + 32)%nat.
    Definition sksize := (n / 8 * Pos.to_nat log2q * k)%nat.
    Definition ciphertextsize := (n / 8 * Pos.to_nat du * k + n / 8 * Pos.to_nat dv * 1)%nat.
    Definition msgsize := (n / 8 * Pos.to_nat 1)%nat.
    Local Hint Transparent pksize sksize ciphertextsize msgsize.

    (* Some notations and definitions to make things clearer *)
    Local Notation matrix_mul := (matrix_mul Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul).
    Local Notation matrix_transpose := (matrix_transpose Rq_NTT Rq_NTTzero).
    Definition polyvec_add {k} : tuple Rq k -> tuple Rq k -> tuple Rq k := map2 Rqadd.
    Local Infix "+" := polyvec_add : polyvec_scope. Delimit Scope polyvec_scope with poly.
    Local Infix "||" := Tuple.concat.

    Definition gen_matrix (seed : byte_array 32) (transposed : bool)
      : matrix Rq_NTT k k
      := map (fun i => map (fun j =>
                              let i := nat_to_byte i in
                              let j := nat_to_byte j in
                              let inp := if transposed
                                         then (append j (append i seed))
                                         else (append i (append j seed)) in
                              parse (XOF (bytes_to_stream _ inp)))
                           (Tuple.seq 0 k))
             (Tuple.seq 0 k).
    Definition gen_a := fun seed => gen_matrix seed false.
    Definition gen_at := fun seed => gen_matrix seed true.
    Definition getnoise (seed : byte_array 32) (nonce : nat) : Rq :=
      CBD_sample (stream_to_bytes _ (PRF (seed, nat_to_byte nonce))).

    (* Algorithm 3 *)
    (* d should be chosen uniformly at random *)
    Definition KeyGen (d : byte_array 32)
      : byte_array pksize * byte_array sksize :=
      let '(rho, sigma) := G (bytes_to_stream _ d) in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (getnoise sigma) (Tuple.seq 0 k) in
      let e := map (getnoise sigma) (Tuple.seq k k) in
      let s' := map NTT s in
      let t := (map NTT_inv (matrix_mul k k 1 A s') + e)%poly in
      let pk := polyvec_encode (polyvec_compress dt t) || rho in
      let sk := polyvec_encode (map NTT_to_F s') in
      (pk, sk).

    Definition Enc (pk : byte_array pksize)
               (coins : byte_array 32) (msg : byte_array msgsize)
      : byte_array ciphertextsize :=
      let t := polyvec_decompress (polyvec_decode (Tuple.firstn _ pk)) in
      let rho := Tuple.skipn (n / 8 * Pos.to_nat dt * k) pk in
      let At := gen_at rho in
      let r := map (getnoise coins) (Tuple.seq 0 k) in
      let e1 := map (getnoise coins) (Tuple.seq k k) in
      let e2 : tuple Rq 1 := getnoise coins (2*k)%nat in
      let r' := map NTT r in
      let u := (map NTT_inv (matrix_mul k k 1 At r') + e1)%poly in
      let t' := map NTT t in
      let tTr : tuple Rq 1 := NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k t') r') in
      let v := (tTr + e2 + (poly_decompress (decode msg)))%poly in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      c1 || c2.

    Definition Dec (sk : byte_array sksize)
               (c : byte_array ciphertextsize)
      : byte_array msgsize :=
      let u := polyvec_decompress (polyvec_decode (firstn _ c)) in
      let v := polyvec_decompress (polyvec_decode (skipn _ c)) in
      let s' := map NTT_of_F (polyvec_decode sk) in
      let u' := map NTT u in
      let sTu := NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k s') u') in
      let m := encode (poly_compress 1 (Rqsub v sTu)) in
      m.
  End KyberSpec.
End KyberSpec.

Module Bytes.
  Definition byte := tuple bool 8.
  Definition byte0 : byte := repeat false 8.
  Definition byte_array := tuple byte.
  Definition stream : Type := {n & byte_array n}.
  Definition get_bit (b : byte) (n : nat) := nth_default false n b.
  Definition get_byte (s : stream) (n : nat) := nth_default byte0 n (projT2 s).
  Definition stream_to_bytes n (s : stream) : byte_array n := map (get_byte s) (Tuple.seq 0 n).
  Definition bytes_to_stream n (b : byte_array n) : stream := existT _ n b.
  Definition nat_to_byte (n : nat) : byte := map (Nat.testbit n) (Tuple.seq 0 8).
  Definition bytes_to_bits l (B : byte_array l)
    : tuple bool (8*l) :=
    Tuple.flat_map (fun b => map (get_bit b) (Tuple.seq 0 8)) B.
  Definition bits_to_bytes lx8 l (H : lx8 = (8*l)%nat) (B : tuple bool lx8)
    : byte_array l :=
    map (fun i => (map (fun j => nth_default false (i*8+j) B) (Tuple.seq 0 8))) (Tuple.seq 0 l).
End Bytes.

Module Kyber512.
  Import Bytes.
  Definition n := 512%nat.
  Definition k := 2%nat.
  Definition q := 7681%positive.
  Definition log2q := Eval compute in (Pos.size q).
  Definition eta := 5%nat.
  Definition du := 11%positive.
  Definition dv := 3%positive.
  Definition dt := 11%positive.

  Definition pksize := Eval compute in (KyberSpec.pksize k n dt).
  Definition sksize := Eval compute in (KyberSpec.sksize k n log2q).
  Definition ciphertextsize := Eval compute in (KyberSpec.ciphertextsize k n du dv).
  Definition msgsize := Eval compute in (KyberSpec.msgsize n).

  Axiom Rq_NTT : Type.
  Axiom Rq_NTTadd : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTmul : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTzero : Rq_NTT.
  Axiom NTT : @PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> @PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
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
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
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
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
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
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
         NTT NTT_inv NTT_of_F
         nmod8
         byte0
         bytes_to_bits bits_to_bytes
         sk c.
End Kyber512.

Module Kyber32.
  Import Bytes.
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

  Definition Rq_NTT := @PolynomialRing.Rq n q.
  Definition NTT (x : @PolynomialRing.Rq n q) : Rq_NTT := x.
  Definition NTT_inv (x : Rq_NTT) : @PolynomialRing.Rq n q := x.
  Definition NTT_to_F (x : Rq_NTT) : tuple (F (2^log2q)) n := map (fun y => F.of_Z _ (F.to_Z y)) x.
  Definition NTT_of_F (x : tuple (F (2^log2q)) n) : Rq_NTT := map (fun y => F.of_Z _ (F.to_Z y)) x.
  (*
  Axiom Rq_NTT : Type.
  Axiom Rq_NTTadd : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTmul : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTzero : Rq_NTT.
  Axiom NTT : PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
   *)
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
             @Matrix.matrix_mul Rq_NTT PolynomialRing.zero PolynomialRing.add PolynomialRing.mul 1 1 1 x y) As matrix_mul_eq.
  Proof.
    intros. subst x y.
    cbv [Matrix.matrix_mul Matrix.sum Matrix.matrix_get].
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