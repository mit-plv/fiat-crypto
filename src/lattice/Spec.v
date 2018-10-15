Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Tuple.
Local Open Scope Z_scope.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)


(* TODO: move to ListUtil *)
Lemma length_flat_map {A B} (f : A -> list B) l n :
  (forall a, In a l -> length (f a) = n) ->
  length (flat_map f l) = (n * (length l))%nat.
Proof.
  induction l; cbn [flat_map]; intros;
    repeat match goal with
           | _ => progress autorewrite with distr_length
           | _ => rewrite Nat.mul_succ_r
           | H : _ |- _ => rewrite H by auto using in_eq, in_cons
           | _ => omega
           end.
Qed.

(* TODO: make an actual tuple-land definition *)
Module Tuple.
  Definition seq start len := from_list_default 0%nat len (seq start len).
  Check on_tuple.
  Program Definition flat_map {A B n m} (f : A -> tuple B m) (t : tuple A n)
    : tuple B (m * n) :=
    on_tuple (List.flat_map (fun a => to_list m (f a))) _ t.
  Next Obligation.
    apply length_flat_map.
    intros; apply length_to_list.
  Defined.
  Program Definition concat {T n m} (t1 : tuple T n) (t2 : tuple T m)
    : tuple T (n + m) :=
    on_tuple2 (@List.app T) _ t1 t2.
  Next Obligation. apply app_length. Defined.
  Program Definition firstn {T} n {m} (t : tuple T (n + m)) : tuple T n :=
    on_tuple (List.firstn n) _ t.
  Next Obligation. autorewrite with distr_length. lia. Defined.
  Program Definition skipn {T} n {m} (t : tuple T (n + m)) : tuple T m :=
    on_tuple (List.skipn n) _ t.
  Next Obligation. autorewrite with distr_length. lia. Defined.
  Program Definition coerce {T n} m (t : tuple T n) (H : n = m)
    : tuple T m := from_list m (to_list n t) _.
  Next Obligation. apply length_to_list. Defined.
End Tuple.

Module PolynomialRing.
  Section PolynomialRing.
    Context (n : nat) (q : BinNums.positive).

    Definition Rq : Type := tuple (F q) n.

    Definition zero : Rq := repeat (F.of_Z _ 0) n.
    Definition one : Rq :=
      from_list_default (F.of_Z _ 0) n (F.of_Z q 1 :: List.repeat (F.of_Z _ 0) (n-1)).
    Definition opp : Rq -> Rq := map F.opp.
    Definition add : Rq -> Rq -> Rq := map2 F.add.
    Definition sub : Rq -> Rq -> Rq := fun p q => add p (opp q).
    Definition scmul : F q -> Rq -> Rq := fun x => map (F.mul x).
    (* TODO : define tuple fold_right *)
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => List.fold_right scmul q (to_list n p).
    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Admitted.

    Section with_bytestream.
      Context (stream byte : Type)
              (byte0 : byte)
              (get_byte : stream -> nat -> byte)
              (make_byte : tuple bool 8 -> byte)
              (get_bit : byte -> nat -> bool)
              (splice_stream :
                 stream -> forall (start len : nat), stream).
      Context (splice_stream_correct :
                 forall s start len i,
                   (i < len)%nat ->
                   get_byte (splice_stream s start len) i
                   = get_byte s (i+start)).
      Let byte_array := tuple byte.
      Let bit_array := tuple bool.
      Let nth_byte {l} (B : byte_array l) i := nth_default byte0 i B.
      Let nth_bit {l} (B : bit_array l) i := nth_default false i B.

      Definition bytes_to_bits {l} (B : byte_array l)
        : bit_array (8*l) :=
        Tuple.flat_map (fun b => map (get_bit b) (Tuple.seq 0 8)) B.
      Definition bits_to_bytes {lx8} l (B : bit_array lx8)
        : byte_array l :=
        map (fun i => make_byte
                        (map (fun j => nth_bit B (i*8+j))
                             (Tuple.seq 0 8)))
                        (Tuple.seq 0 l).

    (* Equivalent to \sum_{j=0}^{len-1} in_bits_{j} *)
      Definition sum_bits {n} start len (B : bit_array n) :=
        fold_right
          (fun j => Z.add (Z.b2z (nth_bit B (start + j))))
          0 (seq 0 len).

      (* Algorithm 2 *)
      (* NOTE : The output is not meant to represent the input, just
    preserve the input's randomness. *)
      Definition CBD_sample (eta : nat) (B : byte_array (64*eta)) :=
        let B' := bytes_to_bits B in
        map (fun i =>
               let a := sum_bits (2*i*eta) eta B' in
               let b := sum_bits (2*i*eta+eta) eta B' in
               F.of_Z q (a - b))
            (Tuple.seq 0 n).
    End with_bytestream.
  End PolynomialRing.
End PolynomialRing.

Module KyberSpec.
  Import PolynomialRing.
  Section KyberSpec.
    (* Parameters about polynomial rings *)
    Context (n : nat) (q log2q : positive).
    Context (Zq_NTT : Type).
    Let Rq := Rq n q.
    Let Rq_NTT := tuple (Zq_NTT) n.
    Context (NTT : Rq -> Rq_NTT) (NTT_inv : Rq_NTT -> Rq).
    Context (freeze : Zq_NTT -> F (2^log2q)). (* modular reduction *)

    (* Parameters about bytestreams *)
    Context (stream byte : Type)
            (byte0 : byte)
            (get_byte : stream -> nat -> byte)
            (make_byte : tuple bool 8 -> byte)
            (bytes_to_stream : forall n, tuple byte n -> stream)
            (stream_to_bytes : forall n, stream -> tuple byte n)
            (get_bit : byte -> nat -> bool)
            (splice_stream :
               stream -> forall (start len : nat), stream).
    Context (nat_to_byte : nat -> byte).
    Let byte_array := tuple byte.
    Let bit_array := tuple bool.
    Let nth_bit {l} (B : bit_array l) i := nth_default false i B.
    Let CBD_sample n q := CBD_sample n q byte get_bit.
    Let matrix T n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)

    (* Kyber parameters *)
    Context (parse : stream -> Rq_NTT). (* Algorithm 1 *) (* TODO *)
    Context (k eta : nat)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : stream -> stream) (* "extendable output function" *)
            (PRF : byte_array 32 * byte -> stream) (* pseudorandom function *)
            (H : stream -> byte_array 32)
            (G : stream -> byte_array 32 * byte_array 32). (* hash function *)


    (* TODO *)
    Axiom matrix_mul :
      forall n m p,
        matrix Rq_NTT n m ->
        matrix Rq_NTT m p ->
        matrix Rq_NTT n p.
    Axiom matrix_transpose :
      forall {T} n m,
        tuple (tuple T n) m -> tuple (tuple T m) n.
    Axiom f_compress : forall q d, (F q) -> (F (2^d)).
    Axiom f_decompress : forall q d, (F (2^d)) -> (F q).
    Axiom polyvec_add :
      forall k,
        tuple Rq k -> tuple Rq k -> tuple Rq k.

    Section helpers.
      Definition split_array {T} n m {nm} (* nm = n * m *)
                 (d : T) (A : tuple T nm) : tuple (tuple T n) m :=
        map (fun i => map (fun j => nth_default d (i*m+j) A)
                          (Tuple.seq 0 n))
            (Tuple.seq 0 m).
      Definition bits_to_Z {n} (B : bit_array n) :=
        List.fold_right
          (fun i acc => acc + Z.shiftl (Z.b2z (nth_bit B i)) (Z.of_nat i))
          0 (seq 0 n).
      Definition bits_to_F m {n} (B : bit_array n) :=
        F.of_Z m (bits_to_Z B).
      Definition Z_to_bits (x : Z) n : bit_array n :=
        map (fun i => Z.testbit x (Z.of_nat i)) (Tuple.seq 0 n).
      Definition F_to_bits {m} (x : F m) n : bit_array n :=
        Z_to_bits (F.to_Z x) n.
    End helpers.
    Local Infix "||" := Tuple.concat.

    Section compression.
      Definition compress {k q} d
      : tuple (F q) k -> tuple (F (2^d)) k :=
        map (f_compress q d).
      Definition decompress {k} q {d}
        : tuple (F (2^d)) k -> tuple (F q) k :=
        map (f_decompress q d).
      Definition polyvec_compress {n m q} d
        : matrix (F q) n m -> matrix (F (2^d)) n m :=
        map (compress d).
      Definition polyvec_decompress {n m} q {d}
        : matrix (F (2^d)) n m -> matrix (F q) n m :=
        map (decompress q).
    End compression.

    Section encoding.
      Let bytes_to_bits {l} := @bytes_to_bits byte get_bit l.
      Let bits_to_bytes {l} := @bits_to_bytes byte make_byte l.

      Definition decode {l} (B : byte_array ((n/8)*Pos.to_nat l))
        : tuple (F (2^l)) n :=
        let B' := bytes_to_bits B in
        map (bits_to_F (2^l)) (split_array (Pos.to_nat l) n false B').

      Definition encode {l} (t : tuple (F (2^l)) n)
        : byte_array ((n/8) * Pos.to_nat l) :=
        bits_to_bytes _
          (Tuple.flat_map (fun x => F_to_bits x (Pos.to_nat l)) t).

      Definition polyvec_decode {k l}
                 (B : byte_array ((n/8)*Pos.to_nat l*k))
        : matrix (F (2^l)) k n :=
        map decode
            (split_array ((n/8)*Pos.to_nat l) k byte0 B).
      Definition polyvec_encode {k l}
                 (A : matrix (F (2^l)) k n)
        : byte_array ((n/8)*Pos.to_nat l*k) :=
        Tuple.flat_map encode A.
    End encoding.

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
      CBD_sample n q eta (stream_to_bytes _ (PRF (seed, nat_to_byte nonce))).
    Local Notation pksize := (n / 8 * Pos.to_nat dt * k + 32)%nat (only parsing).
    Local Notation sksize := (n / 8 * Pos.to_nat log2q * k)%nat (only parsing).
    Local Notation ciphertextsize := (n / 8 * Pos.to_nat du * k + n / 8 * Pos.to_nat dv * 1)%nat (only parsing).

    (* Algorithm 3 *)
    (* d should be chosen uniformly at random *)
    Definition KeyGen (d : byte_array 32)
      : byte_array pksize * byte_array sksize :=
      let '(rho, sigma) := G (bytes_to_stream _ d) in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (fun i => getnoise sigma i) (Tuple.seq 0 k) in
      let e := map (fun i => getnoise sigma i) (Tuple.seq k k) in
      let s' := map NTT s in
      let t := polyvec_add k (map NTT_inv (matrix_mul k k 1 A s')) e in
      let pk := Tuple.concat (polyvec_encode (polyvec_compress dt t)) rho in
      let sk := polyvec_encode (map (map freeze) s') in
      (pk, sk).

    Definition Enc (pk : byte_array pksize)
               (coins : byte_array 32) (msg : byte_array (n / 8 * Pos.to_nat 1))
      : byte_array ciphertextsize :=
      let t := polyvec_decompress q (polyvec_decode (Tuple.firstn _ pk)) in
      let rho := Tuple.skipn (n / 8 * Pos.to_nat dt * k) pk in
      let At := gen_at rho in
      let r := map (fun i => getnoise coins i) (Tuple.seq 0 k) in
      let e1 := map (fun i => getnoise coins i) (Tuple.seq k k) in
      let e2 := getnoise coins (2*k)%nat in
      let r' := map NTT r in
      let u := polyvec_add k (map NTT_inv (matrix_mul k k 1 At r')) e1 in
      let t' := map NTT t in
      let v :=
          polyvec_add 1
          (polyvec_add 1
            (NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k t') r'))
            e2)
          (decompress q (decode msg))
      in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      c1 || c2.

  End KyberSpec.
End KyberSpec.
