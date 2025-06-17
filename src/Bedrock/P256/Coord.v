Require Import coqutil.Datatypes.List Coq.Lists.List.
Require Import Bedrock.P256.Specs.
Require Import Bedrock.P256.Platform.

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
micromega.Lia Word.Properties
coqutil.Tactics.Tactics.

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


Definition p256_coord_nonzero := func! (p_x) ~> nz {
  unpack! nz = br_broadcast_nonzero(load(p_x) | load(p_x.+$8) | load(p_x.+$8.+$8) | load(p_x.+$8.+$8.+$8))
}.

Definition p256_coord_sub := func!(out, x, y) {
  unpack! t0, borrow = full_sub(load(x),          load(y),          $0);
  unpack! t1, borrow = full_sub(load(x+$8),       load(y+$8),       borrow);
  unpack! t2, borrow = full_sub(load(x+$8+$8),    load(y+$8+$8),    borrow);
  unpack! t3, borrow = full_sub(load(x+$8+$8+$8), load(y+$8+$8+$8), borrow);
  unpack! mask = br_value_barrier(-borrow);
  unpack! r0, carry = full_add(t0, mask,                       $0);
  unpack! r1, carry = full_add(t1, mask & $0xffffffff,         carry);
  unpack! r2, carry = full_add(t2, $0,                         carry);
  unpack! r3, carry = full_add(t3, mask & $0xffffffff00000001, carry);
  store(out,          r0);
  store(out+$8,       r1);
  store(out+$8+$8,    r2);
  store(out+$8+$8+$8, r3)
}.

Definition u256_shr := func!(p_out, p_x, n) {
  x0 = load(p_x); x1 = load(p_x+$8); x2 = load(p_x+$8+$8); x3 = load(p_x+$8+$8+$8);
  unpack! y0 = shrd(x0, x1, n);
  unpack! y1 = shrd(x1, x2, n);
  unpack! y2 = shrd(x2, x3, n);
  y3 = x3 >> n;
  store(p_out, y0); store(p_out+$8, y1); store(p_out+$8+$8, y2); store(p_out+$8+$8+$8, y3)
}.

Definition u256_set_p256_minushalf_conditional := func!(p_out, mask) {
  mh0 = -$1; mh1 = mh0>>$33; mh2 = mh0<<$63; mh3 = mh0<<$32>>$1; (* minus one half modulo p256 *)
  store(p_out,          mask&mh0);
  store(p_out+$8,       mask&mh1);
  store(p_out+$8+$8,    mask&mh2);
  store(p_out+$8+$8+$8, mask&mh3)
}.

Definition p256_coord_add := func!(p_out, p_x, p_y) {
  unpack! t0, carry = full_add(load(p_x),          load(p_y),          $0);
  unpack! t1, carry = full_add(load(p_x+$8),       load(p_y+$8),       carry);
  unpack! t2, carry = full_add(load(p_x+$8+$8),    load(p_y+$8+$8),    carry);
  unpack! t3, carry = full_add(load(p_x+$8+$8+$8), load(p_y+$8+$8+$8), carry);
  unpack! r0, borrow = full_sub(t0, $0xffffffffffffffff, $0);
  unpack! r1, borrow = full_sub(t1, $0xffffffff,         borrow);
  unpack! r2, borrow = full_sub(t2, $0,                  borrow);
  unpack! r3, borrow = full_sub(t3, $0xffffffff00000001, borrow);
  unpack! r4, borrow = full_sub(carry, $0, borrow);
  unpack! r0 = br_cmov(borrow, t0, r0);
  unpack! r1 = br_cmov(borrow, t1, r1);
  unpack! r2 = br_cmov(borrow, t2, r2);
  unpack! r3 = br_cmov(borrow, t3, r3);
  store(p_out,          r0);
  store(p_out+$8,       r1);
  store(p_out+$8+$8,    r2);
  store(p_out+$8+$8+$8, r3)
}.


Import String List bedrock2.ToCString Macros.WithBaseName.
Local Open Scope string_scope. Local Open Scope list_scope.

Definition coord64 := &[,
 shrd.shrd;
 p256_coord_add;
 p256_coord_sub;
 p256_coord_nonzero;
 u256_shr;
 u256_set_p256_minushalf_conditional
 ].

From Coq Require Import String List.
Compute String.concat LF (List.map (fun f => "static inline "++ c_func f) coord64)%string.

Local Ltac length_tac :=
  repeat rewrite
    ?length_coord, ?length_point,
    ?app_length, ?firstn_length, ?skipn_length, ?length_le_split, ?length_nil,
    ?Nat.min_l
    by (trivial; lia); trivial; lia.

Import BasicC64Semantics.

Lemma fiat_coord_nonzero_ok : program_logic_goal_for_function! p256_coord_nonzero.
Proof.
  cbv [spec_of_p256_coord_nonzero];
  repeat straightline.

  rename H0 into Hm.
  cbv [coord.to_bytes] in *.
  set (x * coord.R)%F as xR in *.
  do 4 (
    rewrite <-(firstn_skipn 8 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.sub in Hm; set (le_split 8 _) in Hm);
  rewrite List.le_split_0_l in Hm.
  simpl Z.mul in *; simpl Z.add in *.
  subst l0 l1 l2 l3.

  repeat (seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm length_tac).
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac.
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac.
  rewrite ?le_combine_split, ?Z.shiftr_div_pow2 in Hm by length_tac.
  simpl Z.of_nat in *.
  simpl Z.mul in *.

  repeat (straightline || straightline_call).
  clear Hm.

  subst x1. f_equal. f_equal. apply Bool.eq_true_iff_eq.
  rewrite Z.eqb_eq, F.eqb_eq.
  rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff by exact _.
  rewrite !word.lor_0_iff, !word.zero_of_Z_iff, !Zdiv.Zmod_mod by exact _.

  rewrite coord.zero_iff; fold xR.
  rewrite F.zero_iff_to_Z.
  pose proof F.to_Z_range xR eq_refl as range.
  clearbody xR; clear x; set (F.to_Z xR) as x in *; clearbody x.
  clear -range.
  Time PreOmega.Z.to_euclidean_division_equations.
  cbv [p256] in *.
  lia.
Qed.

Import shrd.
Lemma u256_shr_ok : program_logic_goal_for_function! u256_shr.
Proof.
  cbv [spec_of_u256_shr].
  straightline; repeat straightline_cleanup.
  cbv [coord.to_bytes] in *.
  let domem Hm :=
  do 4 (
    rewrite <-(firstn_skipn 8 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.sub in Hm; set (le_split 8 _) in Hm) in
  domem H2.
  rewrite <-(firstn_skipn 8 out), <-(firstn_skipn 8 out[_:]), <-(firstn_skipn 8 out[_:][_:]), ?skipn_skipn, ?firstn_skipn in H3.
  subst l l0 l1 l2.

  let domem Hm :=
  repeat seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm length_tac;
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac;
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac;
  rewrite ?le_combine_split in Hm by lia 
  in domem H2; domem H3.

  simpl Z.of_nat in *; simpl Z.mul in *; simpl Z.add in *; simpl Nat.add in *.
  progress repeat (straightline || straightline_call); try ZnWords.ZnWords.

  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in H14.
  change (Memory.bytes_per access_size.word) with 8%nat in H14.
  do 3 seprewrite_in_by (@Array.list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  revert H14;
  eassert ((_ ++ _) = _) as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj; rewrite ?app_length, ?length_le_combine, ?length_le_split; trivial.
  rewrite !le_combine_app, !le_combine_split, ?length_le_split; change (2^(8%nat*8)) with (2^64).
  rewrite ?Z.mod_small by (cbv [p256] in *; ZnWords.ZnWords).
  subst y3; rewrite word.unsigned_sru_nowrap, Z.shiftr_div_pow2  by ZnWords.ZnWords.
  subst x3 x2 x1 x0.
  progress rewrite ?word.unsigned_of_Z in *; cbv [word.wrap] in *; rewrite <-?Z.land_ones in * by lia.
  pose proof word.unsigned_range n.
  DestructHead.destruct_head' @and.
  simpl Z.mul.
  all : rewrite ?H11, ?H12, ?H13.
  Import bitblast.
  all : apply Z.bits_inj'; intros i Hi;
  repeat rewrite <-?Z.shiftr_div_pow2, ?Z.land_spec, ?Z.lor_spec, ?Z.shiftr_spec', ?Z.shiftl_spec', ?Z.testbit_ones by try ZnWords.ZnWords.
  all: repeat (rewrite
      ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r, 
      ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
      ?Z.testbit_0_l, ?Z.testbit_neg_r, ?Z.testbit_high
    by intuition (idtac;
         match goal with
         | H : ?x < ?y^?a |- ?x < ?y^?b =>
             apply (Z.lt_le_trans _ (y^a)), Z.pow_le_mono_r; lia
         | _ => lia
         end);
    cbn [negb]; trivial; try lia
 || ((case Z.ltb_spec; [|]; intros)||(case Z.leb_spec; [|]; intros))).
    all:f_equal; try lia.
Qed.


Import full_sub full_add.
Local Existing Instances spec_of_full_sub spec_of_full_add.

Import Specs.

Lemma p256_coord_sub_nonmont_ok :
  let '_ := spec_of_p256_coord_sub_nonmont in
  program_logic_goal_for_function! p256_coord_sub.
Proof.
  cbv [spec_of_p256_coord_sub_nonmont].
  straightline; repeat straightline_cleanup.
  cbv [coord.to_bytes] in *.
  let domem Hm :=
  do 4 (
    rewrite <-(firstn_skipn 8 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.sub in Hm; set (le_split 8 _) in Hm) in
  domem H8; domem H9.
  rewrite <-(firstn_skipn 8 out), <-(firstn_skipn 8 out[_:]), <-(firstn_skipn 8 out[_:][_:]), ?skipn_skipn, ?firstn_skipn in H10.
  subst l l0 l1 l2 l3 l4 l5 l6.
  rewrite ?length_le_split in *.

  let domem Hm :=
  repeat seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm length_tac;
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac;
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac;
  rewrite ?le_combine_split, ?Z.shiftr_div_pow2 in Hm by lia 
  in domem H8; domem H9; domem H10.

  simpl Z.of_nat in *; simpl Z.mul in *; simpl Z.add in *; simpl Nat.add in *.
  repeat (straightline || straightline_call); try ZnWords.ZnWords.

  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in H23.
  change (Memory.bytes_per access_size.word) with 8%nat in H23.
  repeat seprewrite_in_by (@Array.list_word_at_app_of_adjacent_eq) H23 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  rewrite <-?app_assoc in H23.
  revert H23;
  eassert ((_ ++ _) = _) as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj; rewrite ?app_length, ?length_le_combine, ?length_le_split; trivial.
  rewrite !le_combine_app, !le_combine_split, ?length_le_split; change (2^(8%nat*8)) with (2^64).
  pose proof F.to_Z_range ((x - y)) eq_refl.
  rewrite ?Z.mod_small by (cbv [p256] in *; ZnWords.ZnWords).

  pose proof F.to_Z_range x eq_refl.
  pose proof F.to_Z_range y eq_refl.
  rewrite F.to_Z_sub.
  rewrite ?word.unsigned_of_Z in *; cbv [word.wrap] in *; rewrite ?Zdiv.Zmod_mod in *.

  cbv [Semantics.interp_op1] in *.
  assert (x9 = word.of_Z 0 /\ F.to_Z y <= F.to_Z x
        \/x9 = word.of_Z 1 /\ F.to_Z x < F.to_Z y) as [ [-> ?]|[-> ?]] by
      (rewrite <-!word.unsigned_inj_iff; cbv [p256] in *; ZnWords.ZnWords).
  { rewrite ?Z.add_0_r in *; cbv [p256] in *. ZnWords.ZnWords. }
  rewrite <-(Z.mod_add _ 1), Z.mod_small by (cbv [p256] in *; ZnWords.ZnWords).
  rewrite word.and_m1_l, ?word.unsigned_of_Z_nowrap in * by lia.
  cbv [p256] in *; ZnWords.ZnWords.
Qed.

Import DestructHead.
Lemma p256_coord_sub_ok : program_logic_goal_for_function! p256_coord_sub.
Proof.
  cbv [program_logic_goal_for spec_of_p256_coord_sub ]; intros; destruct_head' @and; destruct_head' @ex.
  eapply WeakestPreconditionProperties.Proper_call; [|unshelve (eapply p256_coord_sub_nonmont_ok; trivial)]; cycle 1.
  { exact (F.mul x coord.R). } { exact (F.mul y coord.R). } { shelve. } { exact out. }
  { repeat intro; intuition eauto using ex_intro with nocore. }
  repeat intro; destruct_head' @and.
  cbv [coord.to_bytes] in *; ssplit; trivial.
  enough ((x-y)*coord.R = x*coord.R - y*coord.R)%F as -> by eauto.
  ring.
Qed.


Definition spec_of_p256_coord_add_nonmont : spec_of "p256_coord_add" :=
  fnspec! "p256_coord_add" p_out p_x p_y / out (x y : F p256) R,
  { requires t m := m =*> (le_split 32 x)$@p_x /\ m =*> (le_split 32 y)$@p_y /\ m =* out$@p_out * R /\ length out = 32%nat;
    ensures t' m := t' = t /\ m =* (le_split 32 (x+y)%F)$@p_out * R }.

Lemma p256_coord_add_nonmont_ok :
  let '_ := spec_of_p256_coord_add_nonmont in
  program_logic_goal_for_function! p256_coord_add.
Proof.
  straightline; repeat straightline_cleanup.
  clear H H0 H1. clear H3 H4 H5 H6.
  clear H8; rename H12 into H8.
  clear H9; rename H13 into H9.
  clear H10; rename H14 into H10.

  cbv [coord.to_bytes] in *.
  let domem Hm :=
  do 4 (
    rewrite <-(firstn_skipn 8 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.add in Hm; set (le_split 8 _) in Hm) in
  domem H8; domem H9.
  rewrite <-(firstn_skipn 8 out), <-(firstn_skipn 8 out[_:]), <-(firstn_skipn 8 out[_:][_:]), ?skipn_skipn, ?firstn_skipn in H10.
  subst l l0 l1 l2 l3 l4 l5 l6.
  rewrite ?length_le_split in *.

  let domem Hm :=
  repeat seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm length_tac;
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac;
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac;
  rewrite ?le_combine_split, ?Z.shiftr_div_pow2 in Hm by lia 
  in domem H8; domem H9; domem H10.

  simpl Z.of_nat in *; simpl Z.mul in *; simpl Z.add in *; simpl Nat.add in *.
  repeat (straightline || straightline_call); try ZnWords.ZnWords.

  rename H18 into H23.
  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in H23.
  change (Memory.bytes_per access_size.word) with 8%nat in H23.
  repeat seprewrite_in_by (@Array.list_word_at_app_of_adjacent_eq) H23 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  rewrite <-?app_assoc in H23.
  revert H23; eassert ((_ ++ _) = _)%list as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj; rewrite ?app_length, ?length_le_combine, ?length_le_split; trivial.
  rewrite !le_combine_app, !le_combine_split, ?length_le_split; change (2^(8%nat*8)) with (2^64).
  pose proof F.to_Z_range ((x + y)) eq_refl.
  rewrite ?Z.mod_small by (cbv [p256] in *; ZnWords.ZnWords).

  pose proof F.to_Z_range x eq_refl.
  pose proof F.to_Z_range y eq_refl.
  rewrite F.to_Z_add.
  rewrite ?word.unsigned_of_Z in *; cbv [word.wrap] in *; rewrite ?Zdiv.Zmod_mod, ?Z.mod_0_l, ?Z.add_0_r, ?Z.sub_0_r in * by (clear; lia).

  destruct Z.eqb eqn:Hborrow in *; [apply Z.eqb_eq in Hborrow|apply Z.eqb_neq in Hborrow]; repeat straightline.
  { rewrite <-(Z.mod_add _ (-1)) by inversion 1; rewrite Z.mod_small; cbv [p256] in *; ZnWords.ZnWords. }
  { rewrite Z.mod_small; cbv [p256] in *; try ZnWords.ZnWords. }
Qed.

Lemma p256_coord_add_ok : program_logic_goal_for_function! p256_coord_add.
Proof.
  cbv [program_logic_goal_for spec_of_p256_coord_add ]; intros; destruct_head' @and; destruct_head' @ex.
  eapply WeakestPreconditionProperties.Proper_call; [|unshelve (eapply p256_coord_add_nonmont_ok; trivial)]; cycle 1.
  { exact (F.mul x coord.R). } { exact (F.mul y coord.R). } { shelve. } { exact out. }
  { repeat intro; intuition eauto using ex_intro with nocore. }
  repeat intro.
  cbv [coord.to_bytes] in *.
  assert ((x+y)*coord.R = x*coord.R + y*coord.R)%F as -> by ring; eauto.
Qed.

Lemma u256_set_p256_minushalf_conditional_ok : program_logic_goal_for_function! u256_set_p256_minushalf_conditional.
Proof.
  cbv [spec_of_p256_coord_set_minushalf_conditional].
  straightline; repeat straightline_cleanup.
  rename H into Hm.
   
  rewrite <-(firstn_skipn 8 out), <-(firstn_skipn 8 out[_:]), <-(firstn_skipn 8 out[_:][_:]), ?skipn_skipn, ?firstn_skipn in Hm.
  repeat seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm length_tac.
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac.
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac.
  simpl Z.of_nat in *.

  repeat straightline; ssplit; trivial.

  (* postcondition *)

  clear Hm; rename H3 into Hm.
  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in Hm.
  progress change (Memory.bytes_per access_size.word) with 8%nat in Hm.
  repeat seprewrite_in_by (@Array.list_word_at_app_of_adjacent_eq) Hm ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).

  revert Hm; eassert ((_ ++ _) = _)%list as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj. { length_tac. } 
  subst v v0 v1 v2 mask mh0 mh1 mh2 mh3.
  case b; Decidable.vm_decide.
Qed.
