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
Word.Interface OfListWord Separation SeparationLogic
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

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

Local Definition wmask : expr.expr := bedrock_expr:((-$1>>$27)&$63).
Local Definition wsize : expr.expr := bedrock_expr:($wmask+$1).

Import Map.Interface. (* Coercions *)
Local Lemma eval_wmask (m : mem) (l : locals) : Semantics.eval_expr m l wmask = Some (word.of_Z 63).
Proof. cbn. reflexivity. Qed.
Local Lemma eval_wmask' : (word.and (word.sru (word.opp (word.of_Z 1)) (word.of_Z 27)) (word.of_Z 63)) = word.of_Z 63 :> word.
Proof. reflexivity. Qed.
Local Lemma eval_wsize (m : mem) (l : locals) : Semantics.eval_expr m l wsize = Some (word.of_Z 64).
Proof. cbn. reflexivity. Qed.
Local Lemma eval_wsize' : (word.and (word.sru (word.opp (word.of_Z 1)) (word.of_Z 27)) (word.of_Z 63).+1) = $64 :> word.
Proof. reflexivity. Qed.


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
  try rewrite word.sub_0_l.
  cbv [word.broadcast]; apply f_equal.
  apply word.unsigned_inj, Z.bits_inj'; intros i Hi.
  rewrite word.unsigned_and, !word.unsigned_of_Z, !word.testbit_wrap.
  f_equal. f_equal. change (word.wrap 1) with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite <-Z.bit0_mod, Z.bit0_odd; trivial.
Qed.

Lemma br_broadcast_negative_ok : program_logic_goal_for_function! br_broadcast_negative.
Proof.
  cbv [spec_of_br_broadcast_negative].
  repeat straightline.
  straightline_call; repeat straightline.
  subst y.
  rewrite word.signed_lts, <-word.testbit_msb.
  setoid_rewrite eval_wmask'.
  setoid_rewrite word.srs_msb; trivial.
Qed.

Lemma br_broadcast_nonzero_ok : program_logic_goal_for_function! br_broadcast_nonzero.
Proof.
  cbv [spec_of_br_broadcast_nonzero].
  repeat straightline.
  straightline_call; repeat straightline.
  apply f_equal, Bool.eq_true_iff_eq; rewrite Bool.negb_true_iff, Z.eqb_neq, <-word.nz_signed.
  try rewrite word.sub_0_l.
  rewrite word.signed_lts, word.signed_of_Z_nowrap by lia.
  rewrite <-word.testbit_msb, word.unsigned_or_nowrap, Z.lor_spec, !word.testbit_msb.
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
  pose proof word.unsigned_range vz.
  pose proof word.unsigned_range vnz.
  case Z.eqb_spec; intros; unfold word.broadcast in *; cbn [Z.b2z negb].
  all : apply word.unsigned_inj;
    repeat rewrite ?word.unsigned_or, word.unsigned_and, ?word.unsigned_opp, ?word.unsigned_not, ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; cbv [word.wrap].
  all : apply Z.bits_inj'; intros i Hi;
    repeat rewrite <-?Z.land_ones, ?Z.land_spec, ?Z.lor_spec, ?Z.testbit_ones, ?Z.lnot_spec, ?Z.testbit_0_l by try ZnWords.ZnWords.
  all: repeat (((case Z.ltb_spec; [|]; intros)||(case Z.leb_spec; [|]; intros)); rewrite
      ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r, 
      ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
      ?Z.testbit_0_l, ?prove_Zeq_bitwise.testbit_minus1, ?Z.testbit_neg_r, ?Z.testbit_high
    by intuition (idtac;
         match goal with
         | H : ?x < ?y^?a |- ?x < ?y^?b =>
             apply (Z.lt_le_trans _ (y^a)), Z.pow_le_mono_r; lia
         | _ => lia
         end);
    cbn [negb]; trivial; try lia).
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


Lemma br_memcpy_ok : program_logic_goal_for_function! br_memcpy.
Proof.
  cbv [spec_of_br_memcpy].
  repeat (straightline || straightline_call); intuition eauto; try ecancel_assumption; trivial.
Qed.

Lemma br_memset_ok : program_logic_goal_for_function! br_memset.
Admitted.

Lemma br_memcxor_ok : program_logic_goal_for_function! br_memcxor.
Admitted.
