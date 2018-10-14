Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Tuple.
Local Open Scope Z_scope.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)

(* TODO: make an actual tuple-land definition *)
Definition tuple_seq start len := from_list_default 0%nat len (seq start len).

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
      Context (stream : Type)
              (testbit : stream -> nat -> bool)
              (splice_stream :
                 stream -> forall (start len : nat), stream).
      Context (splice_stream_correct :
                 forall s start len i,
                   (i < len)%nat ->
                   testbit (splice_stream s start len) i = testbit s (i+start)).

    (* Equivalent to \sum_{j=0}^{len-1} in_bits_{j} *)
      Definition count_ones_in_stream len (in_bits : stream) :=
        fold_right
          (fun j => Z.add (Z.b2z (testbit in_bits j)))
          0 (seq 0 len).

      (* Algorithm 2 *)
      (* NOTE : The output is not meant to represent the input, just
    preserve the input's randomness. *)
      Definition CBD_sample (eta : nat) (in_bits : stream) :=
        map (fun i =>
               let in1 := splice_stream in_bits (2*i*eta) eta in
               let in2 := splice_stream in_bits (2*i*eta+eta) eta in
               let a := count_ones_in_stream eta in1 in
               let b := count_ones_in_stream eta in2 in
               F.of_Z q (a - b))
            (tuple_seq 0 n).
    End with_bytestream.
  End PolynomialRing.
End PolynomialRing.

Module KyberSpec.
  Import PolynomialRing.
  Section KyberSpec.
    Context (n : nat) (q : positive).
    Context (Zq_NTT : Type).
    Let Rq := Rq n q.
    Let Rq_NTT := tuple (Zq_NTT) n.
    Context (NTT : Rq -> Rq_NTT) (NTT_inv : Rq_NTT -> Rq) (NTT_toZ : Rq_NTT -> Z).
    Context (freeze : Z -> Z). (* modular reduction *)
    Context (stream : Type)
            (testbit : stream -> nat -> bool)
            (lor : stream -> stream -> stream)
            (splice_stream :
               stream -> forall (start len : nat), stream).
    Context (parse : stream -> Rq_NTT). (* Algorithm 1 *) (* TODO *)
    Context (k eta : nat)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : stream -> stream) (* "extendable output function": input and output are both arbitrary-length byte strings *)
            (PRF : stream * stream -> stream) (* pseudorandom function: first input is 32 bytes, second is one byte, output is arbitrary length *)
            (Z_to_stream : Z -> stream)
            (H G : stream -> stream * stream). (* hash functions: inputs are arbitrary length and outputs are 32 bytes each *)
    Context (concat_stream : stream -> stream -> stream)
            (size : stream -> nat)
            (stream_to_Z : stream -> Z)
            (nil_stream : stream).

    Let nat_to_stream x := Z_to_stream (Z.of_nat x).
    Let CBD_sample n q := CBD_sample n q stream testbit splice_stream.
    Let matrix T n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)

    (* TODO *)
    Axiom matrix_mul :
      forall n m p,
        matrix Rq_NTT n m ->
        matrix Rq_NTT m p ->
        matrix Rq_NTT n p.
    Axiom matrix_transpose :
      forall {T} n m,
        tuple (tuple T n) m -> tuple (tuple T m) n.
    Axiom f_compress : forall q d, (F q) -> (F d).
    Axiom f_decompress : forall q d, (F d) -> (F q).
    Axiom polyvec_add :
      forall k,
        tuple Rq k -> tuple Rq k -> tuple Rq k.

    Definition compress {k q} d
      : tuple (F q) k -> tuple (F d) k :=
      map (f_compress q d).
    Definition decompress {k} q {d}
      : tuple (F d) k -> tuple (F q) k :=
      map (f_decompress q d).

    Definition polyvec_compress {n m q} d
      : matrix (F q) n m -> matrix (F d) n m :=
      map (compress d).
    Definition polyvec_decompress {n m} q {d}
      : matrix (F d) n m -> matrix (F q) n m :=
      map (decompress q).


    Definition split_stream n (x : stream) : list stream :=
      List.map (fun i => splice_stream x (i*n)%nat n) (seq 0 (size x / n)).
    Definition encode' {T k} (t2s : T -> stream) : tuple T k -> stream :=
      fun t => List.fold_right (fun x acc => concat_stream acc (t2s x)) nil_stream (to_list k t).
    Definition decode' {T k} nbits (* nbits = number of bits per element *)
               (s2t : stream -> T) : stream -> tuple T k :=
      fun b => map s2t (from_list_default nil_stream k (split_stream nbits b)).
    Let F_to_stream {m} (x : F m) := Z_to_stream (F.to_Z x).
    Let F_of_stream m (x : stream) := F.of_Z m (stream_to_Z x).
    Definition encode {l k} : tuple (F l) k -> stream :=
      encode' F_to_stream.
    Definition decode l k : stream -> tuple (F l) k :=
      decode' (Pos.to_nat l) (F_of_stream l).
    Definition polyvec_encode {n m l}
      : matrix (F l) n m -> stream :=
      encode' encode.
    Definition polyvec_decode m l
      : stream -> matrix (F l) m n :=
      decode' (n*Pos.to_nat l) (decode l n).

    (* Algorithm 3 *)
    (* d should be 32 (KYBER_SYMBYTES) bytes chosen uniformly at random *)
    Definition gen_matrix (seed : stream) (transposed : bool)
      : matrix Rq_NTT k k
      := map (fun i => map (fun j =>
                              let i := nat_to_stream i in
                              let j := nat_to_stream j in
                              let inp := if transposed
                                         then (lor (lor seed j) i)
                                         else (lor (lor seed i) j) in
                              parse (XOF inp)) (tuple_seq 0 k)) (tuple_seq 0 k).
    Definition gen_a := fun seed => gen_matrix seed false.
    Definition gen_at := fun seed => gen_matrix seed true.
    Definition getnoise (seed : stream) (nonce : nat) : Rq :=
      CBD_sample n q eta (PRF (seed, nat_to_stream nonce)).
    Definition KeyGen (d : stream) : stream * stream :=
      let '(rho, sigma) := G d in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (fun i => getnoise sigma i) (tuple_seq 0 k) in
      let e := map (fun i => getnoise sigma i) (tuple_seq k k) in
      let s' := map NTT s in
      let t := polyvec_add k (map NTT_inv (matrix_mul k k 1 A s')) e in
      let pk :=
          lor (polyvec_encode (polyvec_compress dt t)) rho in
      let sk := encode (map (fun x => F.of_Z q (freeze (NTT_toZ x))) s') in
      (pk, sk).

    Definition Enc (pk coins : stream) (msg : Z) : stream :=
      let t := polyvec_decompress q (polyvec_decode k dt pk) in
      let rho := stream_to_Z pk + ((dt * Z.of_nat k * Z.of_nat n) / 8) in
      let At := gen_at (Z_to_stream rho) in
      let r := map (fun i => getnoise coins i) (tuple_seq 0 k) in
      let e1 := map (fun i => getnoise coins i) (tuple_seq k k) in
      let e2 := getnoise coins (2*k)%nat in
      let r' := map NTT r in
      let u := polyvec_add k (map NTT_inv (matrix_mul k k 1 At r')) e1 in
      let t' := map NTT t in
      let v :=
          polyvec_add 1
          (polyvec_add 1
            (NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k t') r'))
            e2)
          (decode q n (F_to_stream (f_decompress q dt (F.of_Z dt msg))))
      in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      lor c1 c2.

  End KyberSpec.
End KyberSpec.
