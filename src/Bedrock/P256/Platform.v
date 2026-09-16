Require Import Bedrock.P256.Specs.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.

Import bedrock2.Syntax bedrock2.NotationsCustomEntry
LittleEndianList
ZArith.BinInt
BinInt BinNat Init.Byte
PrimeFieldTheorems ModInv
micromega.Lia
coqutil.Byte
Lists.List micromega.Lia
Jacobian
Coq.Strings.String Coq.Lists.List
ProgramLogic WeakestPrecondition
ProgramLogic.Coercions
OfListWord Separation SeparationLogic
letexists
BasicC64Semantics
ListIndexNotations
SepAutoArray
symmetry
PeanoNat micromega.Lia
Tactics
UniquePose
micromega.Lia Word.Properties.

Import ListIndexNotations.
Local Open Scope list_index_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Import (notations) coqutil.Map.Memory.
Import bedrock2.wsize.

Definition br_value_barrier := func! (a) ~> a {
  /*skip*/ (* insert appropriate incantation for compilers that optimize values *)
}.

Definition br_declassify := func! (a) ~> a {
  /*skip*/ (* insert appropriate incantation for ctgrind *)
}.

Definition br_broadcast_odd := func! (x) ~> y {
  unpack! x = br_value_barrier(x&$1);
  y = -x
}.

Definition br_broadcast_negative := func! (x) ~> y {
  y = x.>>$wmask;
  unpack! y = br_value_barrier(y)
}.

Definition br_broadcast_nonzero := func! (x) ~> y {
  unpack! y = br_broadcast_negative(x | -x)
}.

Lemma value_barrier_ok : program_logic_goal_for_function! br_value_barrier.
Proof. cbv [spec_of_value_barrier]; repeat straightline. Qed.

Lemma br_declassify_ok : program_logic_goal_for_function! br_declassify.
Proof. cbv [spec_of_br_declassify]; repeat straightline. Qed.

Lemma br_broadcast_odd_ok : program_logic_goal_for_function! br_broadcast_odd.
Proof.
  cbv [spec_of_br_broadcast_odd].
  repeat straightline.
  straightline_call; repeat straightline.
  subst x0 y.
  try rewrite Zmod.sub_0_l.
  cbv [word.broadcast]; apply f_equal.
  apply Zmod.unsigned_inj.
  rewrite bits.unsigned_and, !bits.unsigned_of_Z.
  change (1 mod 2 ^ 64) with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small (Z.b2z _)) by (case Z.odd; cbn; lia).
  rewrite <-Z.bit0_mod, Z.bit0_odd; trivial.
Qed.

Lemma br_broadcast_negative_ok : program_logic_goal_for_function! br_broadcast_negative.
Proof.
  cbv [spec_of_br_broadcast_negative].
  repeat straightline.
  straightline_call; repeat straightline.
  subst y.
  rewrite <-bits.testbit_sign by lia.
  setoid_rewrite eval_wmask'.
  setoid_rewrite word.srs_msb; trivial.
  all: lia.
Qed.

Lemma br_broadcast_nonzero_ok : program_logic_goal_for_function! br_broadcast_nonzero.
Proof.
  cbv [spec_of_br_broadcast_nonzero].
  repeat straightline.
  straightline_call; repeat straightline.
  apply f_equal, Bool.eq_true_iff_eq; rewrite Bool.negb_true_iff, Z.eqb_neq, <-word.nz_signed.
  try rewrite Zmod.sub_0_l.
  rewrite <-bits.testbit_sign, bits.unsigned_or, Z.lor_spec, !bits.testbit_sign by lia.
  case Z.ltb_spec; intros; cbn [orb]; try lia.
  setoid_rewrite word.signed_opp_nowrap; intuition ZnWords.ZnWords.
Qed.


Definition br_cmov := func! (c, vnz, vz) ~> r {
  unpack! m = br_broadcast_nonzero(c);
  r = m & vnz | ~m & vz
}.

Lemma br_cmov_ok : program_logic_goal_for_function! br_cmov.
Proof.
  cbv [spec_of_br_cmov].
  repeat (straightline || straightline_call).
  subst r x; cbn [Semantics.interp_op1] in *.
  pose proof (bits.unsigned_range vz width_nonneg).
  pose proof (bits.unsigned_range vnz width_nonneg).
  case Z.eqb_spec; intros; unfold word.broadcast in *; cbn [Z.b2z negb].
  all : apply Zmod.unsigned_inj;
    repeat rewrite ?bits.unsigned_or, bits.unsigned_and, ?Zmod.unsigned_opp, ?bits.unsigned_not, ?Zmod.unsigned_0, ?(bits.unsigned_1 (n:=64) ltac:(lia)).
  all : apply Z.bits_inj'; intros i Hi;
    repeat rewrite <-?Z.land_ones, ?Z.land_spec, ?Z.lor_spec, ?Z.ldiff_spec, ?Z.testbit_ones, ?Z.lnot_spec, ?Z.testbit_0_l by try ZnWords.ZnWords.
  all: repeat (((case Z.ltb_spec; [|]; intros)||(case Z.leb_spec; [|]; intros)); rewrite
      ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r,
      ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
      ?Z.testbit_0_l, ?(Z.bits_m1 : forall n, 0 <= n -> Z.testbit (-1) n = true), ?Z.testbit_neg_r, ?Z.testbit_high
    by intuition (idtac;
         match goal with
         | H : ?x < ?y^?a |- ?x < ?y^?b =>
             apply (Z.lt_le_trans _ (y^a)), Z.pow_le_mono_r; lia
         | _ => lia
         end);
    cbn [negb]; trivial; try lia).
Qed.

Definition br_abs := func! (k, sign_mask) ~> r {
  (* Alternatively we could have called br_cmov. *)
  r = (k ^ sign_mask) + (sign_mask & $1)
}.

#[local] Ltac div_mod_lia := rewrite <-?Zmod.smod_unsigned, ?word.smodulo_pow2 in *;
      PreOmega.Z.to_euclidean_division_equations; lia.

Lemma opp_sub_opp_add n m : - n - m = - (n + m). Proof. lia. Qed.

Lemma br_abs_ok : program_logic_goal_for_function! br_abs.
Proof.
  cbv [spec_of_br_abs]. repeat straightline.

  subst r.
  pose proof (bits.unsigned_range k width_nonneg).
  destruct (Z.abs_spec (Zmod.signed k)) as [[? ->] | [? ->]].
    { repeat (rewrite ?H, ?word.unsigned_add_nowrap, ?unsigned_xor_nowrap,
      ?bits.unsigned_and, ?bits.unsigned_of_Z_small,
      ?bits.unsigned_xor, ?Z.land_0_l, ?Z.lxor_0_r;
      try (lia || ZnWords.ZnWords); try (case Z.ltb_spec; intros)).
      div_mod_lia. }
    { repeat rewrite ?H, ?word.unsigned_add_nowrap, ?unsigned_xor_nowrap,
      ?bits.unsigned_and, ?bits.unsigned_of_Z_small,
      ?bits.unsigned_xor, ?Hsign, ?Z.land_ones; try (lia || ZnWords.ZnWords);
      try (case Z.ltb_spec; intros); try div_mod_lia.
      all: rewrite Z.land_comm, Z.land_ones_low by (lia || cbv; trivial).
      all: rewrite Z.lxor_comm, <-bits.unsigned_m1, <-bits.unsigned_xor, word.xor_m1_l, bits.unsigned_not', Z.ones_equiv by lia.
      all: div_mod_lia. }
Qed.

Definition br_memset := func! (p_d, v, n) {
  while n {
    store1(p_d, v);
    p_d = p_d+$1;
    n = n-$1
  }
}.

Definition br_memcxor := func! (p_d, p_s, n, m) {
  while n {
    store1(p_d, load1(p_d) ^ (m & load1(p_s)));
    p_d = p_d+$1;
    n = n-$1
  }
}.


Lemma br_memset_ok : program_logic_goal_for_function! br_memset.
Admitted.

Lemma br_memcxor_ok : program_logic_goal_for_function! br_memcxor.
Admitted.
