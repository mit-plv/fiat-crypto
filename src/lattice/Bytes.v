Require Import Crypto.Util.Tuple.

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
