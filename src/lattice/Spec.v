Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Require Import Crypto.lattice.Matrix.
Local Open Scope Z_scope.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)
(* Note: Number-theoretic transforms (NTT) have been removed in this
specification, since their specification is that they are equivalent
to normal multiplication. *)
Module KyberSpec.
  Import Tuple.
  Section KyberSpec.
    Context {stream byte : Type}. (* type of bytes and bytestreams *)
    Local Notation byte_array n := (tuple byte n).
    Local Notation bit_array n := (tuple bool n).

    (* Kyber parameters *)
    Context (k eta n : nat) (q : positive) (q_nbits : nat)
            (dt du dv : nat) (* fields into which elements are compressed *)
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
    Axiom parse : stream -> Rq. (* TODO *)

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

    Section helpers.
      (* Splits a tuple into m chunks of n elements each *)
      Definition split_array {T} n m {nm} (* nm = n * m *)
                 (d : T) (A : tuple T nm) : tuple (tuple T n) m :=
        map (fun i => map (fun j => nth_default d (i*m+j) A) (seq 0 n)) (seq 0 m).
      Lemma encode_sizes_ok l : (l * n = 8 * ((n / 8) * l))%nat.
      Proof. rewrite (Nat.div_mod n 8) at 1 by congruence. rewrite nmod8; lia. Qed.
      Definition bits_to_Z {n} (B : bit_array n) :=
        List.fold_right
          (fun i acc => acc + Z.shiftl (Z.b2z (nth_bit B i)) (Z.of_nat i))
          0 (List.seq 0 n).
      Definition bits_to_Fq (B : bit_array q_nbits) :=
        Fq_of_Z (bits_to_Z B).
      Definition Z_to_bits n (x : Z) : bit_array n :=
        map (fun i => Z.testbit x (Z.of_nat i)) (seq 0 n).
      Definition Fq_to_bits (x : Fq) : bit_array q_nbits :=
        Z_to_bits _ (Fq_to_Z x).
      Definition matrix_map {A B m n} (f : A -> B) :
        Matrix.matrix A m n -> Matrix.matrix B m n := map (map f).
    End helpers.

    Section compression.
      Definition poly_compress (d : nat) : Rq -> tuple (bit_array d) n :=
        map  (fun x : Fq => Z_to_bits d ((Z.shiftl (Fq_to_Z x) (Z.of_nat d) + (q / 2)) / q)).
      Definition poly_decompress {d : nat} : tuple (bit_array d) n -> Rq :=
        map (fun x : bit_array d =>
               Fq_of_Z (Z.shiftr (bits_to_Z x * q + 2^(Z.of_nat d-1)) (Z.of_nat d))).
      Definition polyvec_compress {m} d
        : tuple Rq m -> Matrix.matrix (bit_array d) m n := map (poly_compress d).
      Definition polyvec_decompress {m d}
        : Matrix.matrix (bit_array d) m n -> tuple Rq m := map (poly_decompress).
    End compression.

    Section encoding.
      (* Algorithm 3 *)
      Definition decode {l} (B : byte_array ((n/8)*l))
        : tuple (bit_array l) n :=
        let B' := bytes_to_bits B in
        split_array l n false B'.
      Definition encode {l} (t : tuple (bit_array l) n)
        : byte_array ((n/8) * l) :=
        bits_to_bytes _ (encode_sizes_ok _) (flat_map id t).
      Definition polyvec_decode {k l}
                 (B : byte_array ((n/8)*l*k))
        : Matrix.matrix (bit_array l) k n :=
        map decode
            (split_array ((n/8)*l) k default_byte B).
      Definition polyvec_encode {k l}
                 (A : Matrix.matrix (bit_array l) k n)
        : byte_array ((n/8)*l*k) :=
        Tuple.flat_map encode A.
    End encoding.

    Definition pksize := (n / 8 * dt * k + 32)%nat.
    Definition sksize := (n / 8 * q_nbits * k)%nat.
    Definition ciphertextsize := (n / 8 *du * k + n / 8 * dv * 1)%nat.
    Definition msgsize := (n / 8 * Pos.to_nat 1)%nat.
    Local Hint Transparent pksize sksize ciphertextsize msgsize.

    (* Some notations and definitions to make things clearer *)
    Local Notation matrix_mul := (Matrix.mul Rq Rqzero Rqadd Rqmul).
    Local Notation matrix_transpose := (Matrix.transpose Rq Rqzero).
    Definition polyvec_add {k} : tuple Rq k -> tuple Rq k -> tuple Rq k := map2 Rqadd.
    Local Infix "+" := polyvec_add : polyvec_scope. Delimit Scope polyvec_scope with poly.
    Local Infix "||" := Tuple.concat.

    Definition gen_matrix (seed : byte_array 32) (transposed : bool)
      : Matrix.matrix Rq k k
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

    (* Algorithm 4 *)
    (* d should be chosen uniformly at random *)
    Definition KeyGen (d : byte_array 32)
      : byte_array pksize * byte_array sksize :=
      let '(rho, sigma) := G (bytes_to_stream _ d) in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (getnoise sigma) (Tuple.seq 0 k) in
      let e := map (getnoise sigma) (Tuple.seq k k) in
      let t := ((matrix_mul k k 1 A s) + e)%poly in
      let pk := polyvec_encode (polyvec_compress dt t) || rho in
      let sk := polyvec_encode (matrix_map Fq_to_bits s) in
      (pk, sk).


    (* Algorithm 5 *)
    Definition Enc (pk : byte_array pksize)
               (coins : byte_array 32) (msg : byte_array msgsize)
      : byte_array ciphertextsize :=
      let t := polyvec_decompress (polyvec_decode (Tuple.firstn _ pk)) in
      let rho := Tuple.skipn (n / 8 * dt * k) pk in
      let At := gen_at rho in
      let r := map (getnoise coins) (Tuple.seq 0 k) in
      let e1 := map (getnoise coins) (Tuple.seq k k) in
      let e2 : tuple Rq 1 := getnoise coins (2*k)%nat in
      let u := ((matrix_mul k k 1 At r) + e1)%poly in
      let tTr : tuple Rq 1 := (matrix_mul 1 k 1 (matrix_transpose 1 k t) r) in
      let v := (tTr + e2 + (poly_decompress (decode msg)))%poly in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      c1 || c2.

    (* Algorithm 6 *)
    Definition Dec (sk : byte_array sksize)
               (c : byte_array ciphertextsize)
      : byte_array msgsize :=
      let u := polyvec_decompress (polyvec_decode (firstn _ c)) in
      let v := polyvec_decompress (polyvec_decode (skipn _ c)) in
      let s := matrix_map bits_to_Fq (polyvec_decode sk) in
      let sTu := matrix_mul 1 k 1 (matrix_transpose 1 k s) u in
      let m := encode (poly_compress 1 (Rqsub v sTu)) in
      m.
  End KyberSpec.
End KyberSpec.