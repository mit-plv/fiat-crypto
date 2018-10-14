Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Tuple.
Local Open Scope Z_scope.

Print Ring.
Locate ring.
Check @ring.
SearchAbout field.
Locate F.
Check @F.
(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)

(* TODO: make an actual tuple definition *)
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

    (* TODO : abstract byte-stream type with testbit and split *)

    (* Equivalent to \sum_{j=0}^{len-1} in_bits_{start_index+j} *)
    Definition count_ones_in_range in_bits start_index len :=
      fold_right
        (fun j => Z.add (Z.b2z (Z.testbit in_bits (Z.of_nat j))))
        0 (seq start_index len).

    (* Algorithm 2 *)
    (* NOTE : The output is not meant to represent the input, just
    preserve the input's randomness. *)
    Definition CBD_sample (eta : nat) (in_bits : Z) :=
      map (fun i =>
             let a := count_ones_in_range in_bits (2*i*eta) eta in
             let b := count_ones_in_range in_bits ((2*i*eta)+eta) eta in
             F.of_Z q (a - b))
          (tuple_seq 0 n).
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
    Context (parse : Z -> Rq_NTT). (* Algorithm 1 *) (* TODO *)
    Context (freeze : Z -> Z). (* modular reduction *)
    Context (k eta : nat)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : Z -> Z) (* "extendable output function": input and output are both arbitrary-length byte strings *)
            (PRF : Z * Z -> Z) (* pseudorandom function: first input is 32 bytes, second is one byte, output is arbitrary length *)
            (H G : Z -> Z * Z). (* hash functions: inputs are arbitrary length and outputs are 32 bytes each *)

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


    (* TODO : ZUtil *)
    Definition concat_bits x y : Z :=
      let nbits := if (x =? 1) then 1 else Z.log2_up x in
      Z.lor x (Z.shiftl y nbits).
    Definition select_bits start len x : Z :=
      Z.lor x (Z.shiftl (Z.ones len) start).
    (* number of bits in x should be divisible by n *)
    Definition split_bits n (x : Z) : list Z :=
      List.map (fun i => select_bits (Z.of_nat i*n) n x) (seq 0 (Z.to_nat (Z.log2_up x / n))).
    Definition encode' {T k} (t2z : T -> Z) : tuple T k -> Z :=
      fun t => List.fold_right (fun x acc => concat_bits acc (t2z x)) 0 (to_list k t).
    Definition decode' {T k} nbits (* nbits = number of bits per element *)
               (z2t : Z -> T) : Z -> tuple T k :=
      fun b => map z2t (from_list_default 0 k (split_bits nbits b)).
    Definition encode {l k} : tuple (F l) k -> Z :=
      encode' F.to_Z.
    Definition decode l k : Z -> tuple (F l) k :=
      decode' l (F.of_Z l).
    Definition polyvec_encode {n m l}
      : matrix (F l) n m -> Z :=
      encode' encode.
    Definition polyvec_decode m l
      : Z -> matrix (F l) m n :=
      decode' (Z.of_nat n*l) (decode l n).


    (* Algorithm 3 *)
    (* d should be 32 (KYBER_SYMBYTES) bytes chosen uniformly at random *)
    Definition gen_matrix (seed : Z) (transposed : bool)
      : matrix Rq_NTT k k
      := map (fun i => map (fun j =>
                              let i := Z.of_nat i in
                              let j := Z.of_nat j in
                              let inp := if transposed
                                         then (Z.lor (Z.lor seed j) i)
                                         else (Z.lor (Z.lor seed i) j) in
                              parse (XOF inp)) (tuple_seq 0 k)) (tuple_seq 0 k).
    Definition gen_a := fun seed => gen_matrix seed false.
    Definition gen_at := fun seed => gen_matrix seed true.
    Definition getnoise (seed nonce : Z) : Rq :=
      CBD_sample n q eta (PRF (seed, nonce)).
    Definition KeyGen (d : Z) : Z * Z :=
      let '(rho, sigma) := G d in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (fun i => getnoise sigma (Z.of_nat i)) (tuple_seq 0 k) in
      let e := map (fun i => getnoise sigma (Z.of_nat i)) (tuple_seq k k) in
      let s' := map NTT s in
      let t := polyvec_add k (map NTT_inv (matrix_mul k k 1 A s')) e in
      let pk :=
          Z.lor (polyvec_encode (polyvec_compress dt t)) rho in
      let sk := encode (map (fun x => F.of_Z q (freeze (NTT_toZ x))) s') in
      (pk, sk).

    Definition Enc (pk msg coins : Z) : Z :=
      let t := polyvec_decompress q (polyvec_decode k dt pk) in
      let rho := pk + ((dt * Z.of_nat k * Z.of_nat n) / 8) in
      let At := gen_at rho in
      let r := map (fun i => getnoise coins (Z.of_nat i)) (tuple_seq 0 k) in
      let e1 := map (fun i => getnoise coins (Z.of_nat i)) (tuple_seq k k) in
      let e2 := getnoise coins (2*Z.of_nat k) in
      let r' := map NTT r in
      let u := polyvec_add k (map NTT_inv (matrix_mul k k 1 At r')) e1 in
      let t' := map NTT t in
      let v :=
          polyvec_add 1
          (polyvec_add 1
            (NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k t') r'))
            e2)
          (decode q n (F.to_Z (f_decompress q dt (F.of_Z dt msg))))
      in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      Z.lor c1 c2.

  End KyberSpec.
End KyberSpec.
