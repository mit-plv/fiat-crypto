Require Import Bedrock.Word.
Import BinNums PArith.BinPos NArith.BinNat NArith.Ndigits.

Definition wordUn (f : N -> N) {sz : nat} (x : word sz) :=
	NToWord sz (f (wordToN x)).
Definition wshr {l} n := @wordUn (fun x => N.shiftr x n) l.
Lemma wshr_test : (wordToN (wshr 3 (NToWord 32 (128- 19)))) = 13%N.
	reflexivity.
Qed.

Module WordBoundsExamples.
  Definition u31 := word 31.
  Definition U31 := NToWord 31.
  Definition u64 := word 64.
  Definition U64 := NToWord 64.

	Definition c2  : u64 := NToWord _  2.
	Definition c19_31 : u31 := NToWord _ 19.
	Definition c19 : u64 := NToWord _ 19.
	Definition c38 : u64 := NToWord _ 38.
	Definition t25_31 : u31 := NToWord _ (Npos (2^25)).
	Definition t26_31 : u31 := NToWord _ (Npos (2^26)).
	Definition t25 : u64 := NToWord _ (Npos (2^25)).
	Definition t26 : u64 := NToWord _ (Npos (2^26)).
	Definition t27 : u64 := NToWord _ (Npos (2^26)).
	Definition m25 : u64 := t25^-(NToWord _ 1).
	Definition m26 : u64 := t26^-(NToWord _ 1).
	Definition r25 (hSk hk:u64) : (u64 * u64) := (hSk ^+ wshr 25 hk, wand m25 hk).
	Definition r26 (hSk hk:u64) : (u64 * u64) := (hSk ^+ wshr 26 hk, wand m26 hk).
	Definition r25mod (hSk hk:u64) : (u64 * u64) := (hSk ^+ c19^*wshr 25 hk, wand m25 hk).

	Lemma simple_add_rep : forall (a b c d:N),
		(a < Npos(2^29) -> b < Npos(2^29) -> c < Npos(2^29) -> d < Npos(2^29))%N ->
		wordToN(U31 a ^+ U31 b ^+ U31 c ^+ U31 d) = (a + b + c + d)%N.
	Admitted.

	Lemma simple_add_bound : forall (a b c d:u64),
		a < t25 -> b < t25 -> c < t25 -> d < t25 ->
		(a ^+ b ^+ c ^+ d) < t27.
	Admitted.

  (* the bounds can as well be stated in N if the _rep lemma works.
  I am not sure whether it is a better idea to propagate the bounds in word or
  in N, though -- proving rep requires propagating bounds for the subexpressions.
  *)

	Lemma simple_linear_rep : forall (a b:N), (a < Npos(2^25) + Npos(2^26) -> b < Npos(2^25))%N -> 
		wordToN((U31 a)^*c19_31 ^+ U31 b) = (a*19 + b)%N.
	Admitted.

	Lemma simple_linear_bound : forall (a b:u31), a < t25_31 ^+ t26_31 -> b < t25_31 -> 
		a^*c19_31 ^+ b < (NToWord _ 1946157056). (* (2**26+2**25)*19 + 2**25 = 1946157056 *)
	Admitted.

	Lemma simple_mul_carry_rep : forall (a b c:N), (a < Npos(2^26) -> b < Npos(2^26) -> c < Npos(2^26))%N ->
		wordToN(wshr 26 (U64 a ^* U64 b) ^+ U64 c) = ((a*b)/(2^26) + c)%N.
  Admitted.

	Lemma simple_mul_carry_bound : forall (a b c:u64), a < t26 -> b < t26 -> c < t26 ->
		wshr 26 (a ^* b) ^+ c < t27.
	Admitted.

	Lemma simple_mul_reduce_rep : forall (a b c:N), (a < Npos(2^26) -> b < Npos(2^26))%N ->
		wordToN(wand m26 (U64 a ^* U64 b)) = ((a*b) mod (2^26) + c)%N.
  Admitted.

	Lemma sandy2x_bound : forall
		(* this example is transcribed by hand from <https://eprint.iacr.org/2015/943.pdf> section 2.2.
			 it is very representative of the bounds check / absence-of-overflow proofs we actually
			 want to do. However, given its size, presence of transcription errors is totally plausible.
       A corresponding _rep proof will also necessary.*)
		(f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : u64)
		(g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : u64),
  	f0 < t26 -> g0 < t26 ->
  	f1 < t25 -> g1 < t25 ->
  	f2 < t26 -> g2 < t26 ->
  	f3 < t25 -> g3 < t25 ->
  	f4 < t26 -> g4 < t26 ->
  	f5 < t25 -> g5 < t25 ->
  	f6 < t26 -> g6 < t26 ->
  	f7 < t25 -> g7 < t25 ->
  	f8 < t26 -> g8 < t26 ->
  	f9 < t25 -> g9 < t25 ->

		let h0 := f0^*g0 ^+ c38^*f1^*g9 ^+ c19^*f2^*g8 ^+  c38^*f3^*g7 ^+ c19^*f4^*g6 ^+ c38^*f5^*g5 ^+ c19^*f6^*g4 ^+ c38^*f7^*g3 ^+ c19^*f8^*g2 ^+ c38^*f9^*g1 in
		let h1 := f0^*g1 ^+      f1^*g0 ^+ c19^*f2^*g9 ^+  c19^*f3^*g8 ^+ c19^*f4^*g7 ^+ c19^*f5^*g6 ^+ c19^*f6^*g5 ^+ c19^*f7^*g4 ^+ c19^*f8^*g3 ^+ c19^*f9^*g2 in
		let h2 := f0^*g2 ^+ c2^* f1^*g1 ^+      f2^*g0 ^+  c38^*f3^*g9 ^+ c19^*f4^*g8 ^+ c38^*f5^*g7 ^+ c19^*f6^*g6 ^+ c38^*f7^*g5 ^+ c19^*f8^*g4 ^+ c38^*f9^*g3 in
		let h3 := f0^*g3 ^+      f1^*g2 ^+      f2^*g1 ^+       f3^*g0 ^+ c19^*f4^*g9 ^+ c19^*f5^*g8 ^+ c19^*f6^*g7 ^+ c19^*f7^*g6 ^+ c19^*f8^*g5 ^+ c19^*f9^*g4 in
		let h4 := f0^*g4 ^+ c2^* f1^*g3 ^+      f2^*g2 ^+  c2^* f3^*g1 ^+      f4^*g0 ^+ c38^*f5^*g9 ^+ c19^*f6^*g8 ^+ c38^*f7^*g7 ^+ c19^*f8^*g6 ^+ c38^*f9^*g5 in
		let h5 := f0^*g5 ^+      f1^*g4 ^+      f2^*g3 ^+       f3^*g2 ^+      f4^*g1 ^+      f5^*g0 ^+ c19^*f6^*g9 ^+ c19^*f7^*g8 ^+ c19^*f8^*g7 ^+ c19^*f9^*g6 in
		let h6 := f0^*g6 ^+ c2^* f1^*g5 ^+      f2^*g4 ^+  c2^* f3^*g3 ^+      f4^*g2 ^+ c2^* f5^*g1 ^+      f6^*g0 ^+ c38^*f7^*g9 ^+ c19^*f8^*g8 ^+ c38^*f9^*g7 in
		let h7 := f0^*g7 ^+      f1^*g6 ^+      f2^*g5 ^+       f3^*g4 ^+      f4^*g3 ^+      f5^*g2 ^+      f6^*g1 ^+      f7^*g0 ^+ c19^*f8^*g9 ^+ c19^*f9^*g8 in
		let h8 := f0^*g8 ^+ c2^* f1^*g7 ^+      f2^*g6 ^+  c2^* f3^*g5 ^+      f4^*g4 ^+ c2^* f5^*g3 ^+      f6^*g2 ^+ c2^* f7^*g1 ^+      f8^*g0 ^+ c38^*f9^*g9 in
		let h9 := f0^*g9 ^+      f1^*g8 ^+      f2^*g7 ^+       f3^*g6 ^+      f4^*g5 ^+      f5^*g4 ^+      f6^*g3 ^+      f7^*g2 ^+      f8^*g1 ^+      f9^*g0 in
		
		let (h1_1, h0_1) := r26 h1 h0 in
		let (h2_1, h1_2) := r25 h2 h1_1 in
		let (h3_1, h2_2) := r26 h3 h2_1 in
		let (h4_1, h3_2) := r25 h4 h3_1 in

		let (h6_1, h5_1) := r25 h6 h5 in
		let (h7_1, h6_2) := r26 h7 h6_1 in
		let (h8_1, h7_2) := r25 h8 h7_1 in
		let (h9_1, h8_2) := r26 h9 h8_1 in
		let (h0_2, h9_2) := r25mod h0_1 h9_1 in
		let (h1_3, h0_2) := r26 h1_2 h0_1 in

		let (h5_2, h4_2) := r26 h5_1 h4_1 in
		let (h6_2, h5_3) := r25 h6_1 h5_2 in

  	h0_2 < t26 /\
  	h1_3 < t27 /\
  	h2_2 < t26 /\
  	h3_2 < t25 /\
  	h4_2 < t26 /\
  	h5_3 < t25 /\
  	h6_2 < t27 /\
  	h7_2 < t25 /\
  	h8_2 < t26 /\
  	h9_2 < t25.
	Admitted.
End WordBoundsExamples.
