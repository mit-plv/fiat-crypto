Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
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

  Definition on_tuple_default {A B} (f : list A -> list B) {n m} (d : B) (xs : tuple A n) :=
    from_list_default d m (f (to_list n xs)).

  Lemma on_tuple_default_eq A B f n m d H xs :
    @on_tuple_default A B f n m d xs = on_tuple f H xs.
  Proof.
    cbv [on_tuple on_tuple_default].
    erewrite <-from_list_default_eq.
    reflexivity.
  Qed.
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
    (* TODO : this definition is wrong *)
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => List.fold_right scmul q (to_list n p).
    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Admitted.

    Section with_bytestream.
      Context (stream byte : Type)
              (byte0 : byte)
              (make_byte : tuple bool 8 -> byte)
              (get_bit : byte -> nat -> bool).
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

      Definition compress (d : positive) : Rq -> tuple (F (2 ^ d)) n :=
        map (fun x : F q => F.of_Z _ ((Z.shiftl (F.to_Z x) d + (q / 2)) / q)).
      Definition decompress {d : positive} : tuple (F (2 ^ d)) n -> Rq :=
        map (fun x : F (2 ^ d) => F.of_Z _ (Z.shiftr (F.to_Z x * q + 2^(d-1)) d)).

    (* Equivalent to \sum_{j=0}^{len-1} in_bits_{j} *)
      Definition sum_bits {n} start len (B : bit_array n) :=
        fold_right
          (fun j => Z.add (Z.b2z (nth_bit B (start + j))))
          0 (seq 0 len).

      (* Algorithm 2 *)
      (* NOTE : The output is not meant to represent the input, just
    preserve the input's randomness. *)
      Definition CBD_sample (eta : nat) (B : byte_array (64*eta)) : Rq :=
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
  Import Tuple.
  Section KyberSpec.
    Context (Rq Rq_NTT : Type).
    Context {Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul}
            (Rqring : @ring Rq Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul).
    Context {Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul}
            (Rq_NTTring : @ring Rq_NTT Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul).
    Context (NTT : Rq -> Rq_NTT) (NTT_inv : Rq_NTT -> Rq).

    (* Parameters about bytestreams *)
    Context (stream byte : Type)
            (byte0 : byte)
            (get_byte : stream -> nat -> byte)
            (make_byte : tuple bool 8 -> byte)
            (bytes_to_stream : forall n, tuple byte n -> stream)
            (stream_to_bytes : forall n, stream -> tuple byte n)
            (get_bit : byte -> nat -> bool).
    Context (nat_to_byte : nat -> byte).
    Let byte_array := tuple byte.
    Let bit_array := tuple bool.
    Let nth_bit {l} (B : bit_array l) i := nth_default false i B.

    (* Kyber parameters *)
    Context (parse : stream -> Rq_NTT). (* Algorithm 1 *) (* TODO *)
    Context (k eta n : nat) (q log2q : positive)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : stream -> stream) (* "extendable output function" *)
            (PRF : byte_array 32 * byte -> stream) (* pseudorandom function *)
            (H : stream -> byte_array 32)
            (G : stream -> byte_array 32 * byte_array 32). (* hash function *)

    Context (CBD_sample : byte_array (64*eta) -> Rq).
    Context (NTT_of_F :tuple (F (2^log2q)) n -> Rq_NTT) (NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n).
    Context (compress : forall d, Rq -> tuple (F (2^d)) n) (decompress : forall {d}, tuple (F (2^d)) n -> Rq).
    Arguments decompress {_}.

    (* TODO : relocate? *)
    Let matrix T n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)
    Definition matrix_get {T n m} (d : T) (A : matrix T n m) (i j : nat) : T :=
      nth_default d j (nth_default (repeat d m) i A).
    Definition matrix_mul n m p
               (A : matrix Rq_NTT n m)
               (B : matrix Rq_NTT m p) : matrix Rq_NTT n p :=
      map (fun j =>
             map (fun i =>
                    fold_right
                      (fun k acc => Rq_NTTadd acc
                                              (Rq_NTTmul (matrix_get Rq_NTTzero A i k)
                                                         (matrix_get Rq_NTTzero B k j)))
                      Rq_NTTzero
                      (List.seq 0 m))
                 (seq 0 p))
          (seq 0 n).
    Definition matrix_transpose n m (A : matrix Rq_NTT n m) : matrix Rq_NTT m n :=
      map (fun j => map (fun i => matrix_get Rq_NTTzero A j i) (seq 0 n)) (seq 0 m).

    Definition pksize := (n / 8 * Pos.to_nat dt * k + 32)%nat.
    Definition sksize := (n / 8 * Pos.to_nat log2q * k)%nat.
    Definition ciphertextsize := (n / 8 * Pos.to_nat du * k + n / 8 * Pos.to_nat dv * 1)%nat.
    Definition msgsize := (n / 8 * Pos.to_nat 1)%nat.
    Local Hint Transparent pksize sksize ciphertextsize msgsize.
    Local Infix "||" := concat.

    Section helpers.
      Definition split_array {T} n m {nm} (* nm = n * m *)
                 (d : T) (A : tuple T nm) : tuple (tuple T n) m :=
        map (fun i => map (fun j => nth_default d (i*m+j) A)
                          (seq 0 n))
            (seq 0 m).
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
      Definition polyvec_add {k} : tuple Rq k -> tuple Rq k -> tuple Rq k :=
        map2 Rqadd.
    End helpers.
    Local Arguments polyvec_add {_} _ _.
    Local Infix "+" := polyvec_add : polyvec_scope.
    Delimit Scope polyvec_scope with poly.

    Section compression.
      Definition polyvec_compress {m} d
        : tuple Rq m -> matrix (F (2^d)) m n :=
        map (compress d).
      Definition polyvec_decompress {m d}
        : matrix (F (2^d)) m n -> tuple Rq m :=
        map (decompress).
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
          (flat_map (fun x => F_to_bits x (Pos.to_nat l)) t).

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
      let v := (tTr + e2 + (decompress (decode msg)))%poly in
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
      let m := encode (compress 1 (Rqsub v sTu)) in
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
  Axiom NTT : PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen (PolynomialRing.Rq n q)
                         Rq_NTT
                         (PolynomialRing.add n q)
                         Rq_NTTzero
                         Rq_NTTadd
                         Rq_NTTmul
                         NTT
                         NTT_inv
                         stream
                         byte
                         id
                         bytes_to_stream
                         stream_to_bytes
                         nat_to_byte
                         parse
                         k eta n log2q dt XOF PRF G
                         (PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      Rq_NTTzero
                      Rq_NTTadd
                      Rq_NTTmul
                      NTT
                      NTT_inv
                      stream
                      byte
                      byte0
                      id
                      bytes_to_stream
                      stream_to_bytes
                      get_bit
                      nat_to_byte
                      parse
                      k eta n dt du dv XOF PRF
                      (PolynomialRing.CBD_sample n q byte get_bit eta)
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      Rq_NTTzero
                      Rq_NTTadd
                      Rq_NTTmul
                      NTT
                      NTT_inv
                      byte
                      byte0
                      id
                      get_bit
                      k n log2q du dv
                      NTT_of_F
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
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

  Definition Rq_NTT := PolynomialRing.Rq n q.
  Definition NTT (x : PolynomialRing.Rq n q) : Rq_NTT := x.
  Definition NTT_inv (x : Rq_NTT) : PolynomialRing.Rq n q := x.
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
 
  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen (PolynomialRing.Rq n q)
                         Rq_NTT
                         (PolynomialRing.add n q)
                         (PolynomialRing.zero n q)
                         (PolynomialRing.add n q)
                         (PolynomialRing.mul n q)
                         NTT
                         NTT_inv
                         stream
                         byte
                         id
                         bytes_to_stream
                         stream_to_bytes
                         nat_to_byte
                         parse
                         k eta n log2q dt XOF PRF G
                         (PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      (PolynomialRing.zero n q)
                      (PolynomialRing.add n q)
                      (PolynomialRing.mul n q)
                      NTT
                      NTT_inv
                      stream
                      byte
                      byte0
                      id
                      bytes_to_stream
                      stream_to_bytes
                      get_bit
                      nat_to_byte
                      parse
                      k eta n dt du dv XOF PRF
                      (PolynomialRing.CBD_sample n q byte get_bit eta)
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      (PolynomialRing.zero n q)
                      (PolynomialRing.add n q)
                      (PolynomialRing.mul n q)
                      NTT
                      NTT_inv
                      byte
                      byte0
                      id
                      get_bit
                      k n log2q du dv
                      NTT_of_F
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      sk c.

  Local Notation "subst! v 'for' x 'in' e" := (match v with x => e end) (at level 200).
  Derive encode SuchThat
         (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 x,
             (*
             subst! (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9
          , x10, x11, x12, x13, x14, x15, x16, x17, x18, x19
          , x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
          , x30, x31) for x in *)
             (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9
          , x10, x11, x12, x13, x14, x15, x16, x17, x18, x19
          , x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
          , x30, x31) = x -> 
               encode x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 = @KyberSpec.encode byte id n 1 x) As encode_eq.
  Proof.
    intros. subst x.
    cbv - [PolynomialRing.bits_to_bytes byte Tuple.flat_map KyberSpec.F_to_bits Tuple.flat_map F id].
    cbv [Tuple.flat_map].
    rewrite <-Tuple.on_tuple_default_eq with (d:=false).
    cbn - [Z.testbit].
    cbv - [F byte] in encode.
    exact eq_refl.
  Qed.

  Local Ltac decode_simpl :=
    cbv - [map F KyberSpec.split_array PolynomialRing.bytes_to_bits get_bit KyberSpec.bits_to_F];
    cbv [PolynomialRing.bytes_to_bits Tuple.flat_map];
    rewrite <-Tuple.on_tuple_default_eq with (d:= false);
    cbv [map map' Tuple.seq seq from_list_default from_list_default'];
    cbn [fst snd];
    cbv [KyberSpec.split_array KyberSpec.bits_to_F];
    cbn - [F F.of_Z Z.shiftl Z.add get_bit].

  Derive decode1 SuchThat
         (forall c0 c1 c2 c3 c,
             (c0, c1, c2, c3) = c ->
             decode1 c0 c1 c2 c3 = @KyberSpec.decode byte get_bit n 1 c) As decode1_eq.
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
             = @KyberSpec.decode byte get_bit n 3 c) As decode3_eq.
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
             = @KyberSpec.decode byte get_bit n 5 c) As decode5_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  Derive Dec' SuchThat
         (forall sk0 sk1 sk2 sk3 sk4 sk5 sk6 sk7 sk8 sk9 sk10 sk11
                 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
                 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : byte,
             subst! (sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11) for sk in
             subst! (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23) for c in
               Dec' (sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11) (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23)
               = Dec sk c) As Dec'_correct.
  Proof.
    intros.
    cbv [Dec KyberSpec.Dec].
    cbv - [byte] in Dec'.
    cbv [KyberSpec.polyvec_encode].
    erewrite <-encode_eq.
    2 : {
    cbv [KyberSpec.polyvec_decode KyberSpec.polyvec_decompress].
    cbv [Nat.div Pos.to_nat du dv k n log2q Nat.divmod fst Pos.iter_op Nat.add Nat.mul].
    cbv [Pos.pow Pos.iter Pos.mul].
    cbv [KyberSpec.bits_to_F KyberSpec.bits_to_Z KyberSpec.F_to_bits KyberSpec.split_array].
    cbv [PolynomialRing.bytes_to_bits PolynomialRing.bits_to_bytes].
    cbv [PolynomialRing.Rq PolynomialRing.add PolynomialRing.mul PolynomialRing.zero].
    cbv [Tuple.skipn Tuple.firstn Tuple.seq Tuple.flat_map].
    rewrite <-!Tuple.on_tuple_default_eq with (d:=byte0).
    cbn [seq].
    cbn [from_list_default from_list_default'].
    cbn [map map' fst snd].
    cbv [Tuple.on_tuple_default].
    remember (@to_list (F q)) as X.
    cbn - [KyberSpec.decode byte byte0 NTT NTT_of_F KyberSpec.matrix_transpose F F.of_Z KyberSpec.matrix_mul Rq_NTT repeat map2 PolynomialRing.scmul PolynomialRing.decompress PolynomialRing.compress fold_right].
    subst X.

    erewrite <-decode1_eq by reflexivity.
    erewrite <-decode3_eq by reflexivity.
    erewrite <-decode5_eq by reflexivity.

    cbv [decode5 decode1].
    cbv [PolynomialRing.decompress].
    cbn - [decode3 NTT_of_F KyberSpec.matrix_transpose map2 PolynomialRing.compress Z.shiftr Z.shiftl F F.of_Z Z.b2z get_bit to_list].
    rewrite !F.to_Z_of_Z.
    autorewrite with zsimplify_fast.
    change (Z.shiftr 1 1) with 0.
    change (Z.shiftr 16 5) with 0.
 
    cbv [NTT].

    cbv [decode3].
    cbv [NTT_of_F].
    cbn [n map map' fst snd].
    cbv [log2q].
    rewrite !F.to_Z_of_Z.
    rewrite Z.mod_0_l.

    cbv [KyberSpec.matrix_transpose].
    cbv [Tuple.seq seq from_list_default from_list_default'].
    cbv [KyberSpec.matrix_get map map' nth_default hd hd'].
    cbv [to_list to_list'].
    cbv [KyberSpec.matrix_mul].
    cbv [Tuple.seq seq from_list_default from_list_default'].
    cbv [repeat append].
    cbv [KyberSpec.matrix_get map map' nth_default hd hd' to_list to_list' fold_right].

    cbv [PolynomialRing.scmul].
    unfold map at 30 31 32.
  (* TODO : it might make sense to change all the F (2 ^ l)  things to words, and change bytes also to words. *)
  Abort.
    
End Kyber32.