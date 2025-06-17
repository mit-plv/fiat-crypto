Require Import coqutil.Datatypes.List Coq.Lists.List.
Require Import Bedrock.P256.Specs.
Require Import Bedrock.P256.Platform.
Import bedrock2.NotationsCustomEntry Specs.NotationsCustomEntry.
Import bedrock2Examples.shrd.

Definition p256_coord_nonzero := func! (p_x) ~> nz {
  nz = load(p_x) | load(p_x.+$4) | load(p_x.+$4.+$4) | load(p_x.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4.+$4.+$4);
  unpack! nz = br_broadcast_nonzero(nz)
}.

(*
Definition p256_coord_sub := func!(out, x, y) {
  unpack! t0, borrow = full_sub(load(x),          load(y),          $0);
  unpack! t1, borrow = full_sub(load(x+$4),       load(y+$4),       borrow);
  unpack! t2, borrow = full_sub(load(x+$4+$4),    load(y+$4+$4),    borrow);
  unpack! t3, borrow = full_sub(load(x+$4+$4+$4), load(y+$4+$4+$4), borrow);
  unpack! t4, borrow = full_sub(load(x+$4+$4+$4+$4), load(y+$4+$4+$4+$4), borrow);
  unpack! t5, borrow = full_sub(load(x+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4), borrow);
  unpack! t6, borrow = full_sub(load(x+$4+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4+$4), borrow);
  unpack! t7, borrow = full_sub(load(x+$4+$4+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4+$4+$4), borrow);
  unpack! mask = br_value_barrier(-borrow);
  unpack! r0, carry = full_add(t0, mask,   $0);
  unpack! r1, carry = full_add(t1, mask,   carry);
  unpack! r2, carry = full_add(t2, mask,   carry);
  unpack! r3, carry = full_add(t3, $0,     carry);
  unpack! r4, carry = full_add(t4, $0,     carry);
  unpack! r5, carry = full_add(t5, $0,     carry);
  unpack! r6, carry = full_add(t6, borrow, carry);
  unpack! r7, carry = full_add(t7, mask,   carry);
  store(out,          r0);
  store(out+$4,       r1);
  store(out+$4+$4,    r2);
  store(out+$4+$4+$4, r3);
  store(out+$4+$4+$4+$4,          r4);
  store(out+$4+$4+$4+$4+$4,       r5);
  store(out+$4+$4+$4+$4+$4+$4,    r6);
  store(out+$4+$4+$4+$4+$4+$4+$4, r7)
}.
*)

Definition u256_shr := func!(p_out, p_x, n) {
  x0 = load(p_x);
  x1 = load(p_x+$4);
  x2 = load(p_x+$4+$4);
  x3 = load(p_x+$4+$4+$4);
  x4 = load(p_x+$4+$4+$4+$4);
  x5 = load(p_x+$4+$4+$4+$4+$4);
  x6 = load(p_x+$4+$4+$4+$4+$4+$4);
  x7 = load(p_x+$4+$4+$4+$4+$4+$4+$4);
  unpack! y0 = shrd(x0, x1, n);
  unpack! y1 = shrd(x1, x2, n);
  unpack! y2 = shrd(x2, x3, n);
  unpack! y3 = shrd(x3, x4, n);
  unpack! y4 = shrd(x4, x5, n);
  unpack! y5 = shrd(x5, x6, n);
  unpack! y6 = shrd(x6, x7, n);
  y7 = x7 >> n;
  store(p_out, y0);
  store(p_out+$4, y1);
  store(p_out+$4+$4, y2);
  store(p_out+$4+$4+$4, y3);
  store(p_out+$4+$4+$4+$4, y4);
  store(p_out+$4+$4+$4+$4+$4, y5);
  store(p_out+$4+$4+$4+$4+$4+$4, y6);
  store(p_out+$4+$4+$4+$4+$4+$4+$4, y7)
}.

Definition u256_set_p256_minushalf_conditional := func!(p_out, mask) {
  mh0 = -$1; mh1 = mh0; mh2 = mh0>>$1; mh3 = $0; mh4 = $0; mh5 = $1<<$31; mh6 = mh5; mh7 = mh2;
  store(p_out,          mask&mh0);
  store(p_out+$4,       mask&mh1);
  store(p_out+$4+$4,    mask&mh2);
  store(p_out+$4+$4+$4, mask&mh3);
  store(p_out+$4+$4+$4+$4,          mask&mh4);
  store(p_out+$4+$4+$4+$4+$4,       mask&mh5);
  store(p_out+$4+$4+$4+$4+$4+$4,    mask&mh6);
  store(p_out+$4+$4+$4+$4+$4+$4+$4, mask&mh7)
}.

Import String List bedrock2.ToCString Macros.WithBaseName.
Local Open Scope string_scope. Local Open Scope list_scope.

Definition coord32 := &[,
 shrd;
 p256_coord_nonzero;
 u256_shr;
 u256_set_p256_minushalf_conditional
 ].

From Coq Require Import String List.
Compute String.concat LF (List.map (fun f => "static inline "++ c_func f) coord32)%string.

From bedrock2 Require Import BasicC32Semantics.

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
Word.Interface OfListWord Separation SeparationLogic SeparationMemory
letexists
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

Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Local Ltac length_tac :=
  repeat rewrite
    ?length_coord, ?length_point,
    ?app_length, ?firstn_length, ?skipn_length, ?length_le_split, ?length_nil,
    ?Nat.min_l
    by (trivial; lia); trivial; lia.


Lemma fiat_coord_nonzero_ok : program_logic_goal_for_function! p256_coord_nonzero.
Proof.
  cbv [spec_of_p256_coord_nonzero];
  repeat straightline.

  rename H0 into Hm.
  cbv [coord.to_bytes] in *.
  set (x * coord.R)%F as xR in *.
  do 8 (
    rewrite <-(firstn_skipn 4 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.sub in Hm; set (le_split 4 _) in Hm);
  rewrite List.le_split_0_l in Hm.
  simpl Z.mul in *; simpl Z.add in *.
  subst l0 l1 l2 l3 l4 l5 l6 l7.

  repeat (seprewrite_in_by (@sep_eq_of_list_word_at_app) Hm length_tac).
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
  subst nz nz'0 nz'1 nz'2 v.
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
  straightline.
  clear H2 H3 H4 H5.
  repeat straightline_cleanup.

  cbv [coord.to_bytes] in *.
  let domem Hm :=
  do 8 (
    rewrite <-(firstn_skipn 4 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia;
    simpl Nat.min in Hm; simpl Nat.sub in Hm; set (le_split 4 _) in Hm) in
  domem H2.
  rewrite <-(firstn_skipn 4 out), <-(firstn_skipn 4 out[_:]), <-(firstn_skipn 4 out[_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:][_:][_:]),
    ?skipn_skipn, ?firstn_skipn in H3.
  subst l l0 l1 l2 l3 l4 l5 l6.

  let domem Hm :=
  repeat seprewrite_in_by (@sep_eq_of_list_word_at_app) Hm length_tac;
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac;
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac;
  rewrite ?le_combine_split in Hm by lia 
  in domem H2; domem H3.

  simpl Z.of_nat in *; simpl Z.mul in *; simpl Z.add in *; simpl Nat.add in *.
  progress repeat (straightline || straightline_call); try ZnWords.ZnWords.

  rename H14 into H14'; rename H22 into H14.
  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in H14.
  repeat seprewrite_in_by ptsto_bytes_iff_eq_of_list_word_at H14 ltac:(try rewrite ?length_le_split, ?Scalars.bytes_per_width_bytes_per_word; cbv [Memory.bytes_per_word]; try ZnWords.ZnWords).
  rewrite ?Scalars.bytes_per_width_bytes_per_word in H14.
  progress change (Memory.bytes_per access_size.word) with 4%nat in H14.
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  seprewrite_in_by (@list_word_at_app_of_adjacent_eq) H14 ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  rewrite <-?app_assoc in H14.
  revert H14;
  eassert ((_ ++ _) = _) as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj; rewrite ?app_length, ?length_le_combine, ?length_le_split; trivial.
  rewrite !le_combine_app, !le_combine_split, ?length_le_split; change (2^(8%nat*8)) with (2^64).
  rewrite ?Z.mod_small by (cbv [p256] in *; ZnWords.ZnWords).
  subst y7; rewrite word.unsigned_sru_nowrap, Z.shiftr_div_pow2  by ZnWords.ZnWords.
  subst x7 x6 x5 x4 x3 x2 x1 x0.
  progress rewrite ?word.unsigned_of_Z in *; cbv [word.wrap] in *; rewrite <-?Z.land_ones in * by lia.
  pose proof word.unsigned_range n.
  DestructHead.destruct_head' @and.
  simpl Z.mul.
  all : rewrite !H11, !H12, !H13, !H14', !H15, !H16, !H17.
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
  all: try (f_equal; lia).
Qed.

Lemma u256_set_p256_minushalf_conditional_ok : program_logic_goal_for_function! u256_set_p256_minushalf_conditional.
Proof.
  cbv [spec_of_p256_coord_set_minushalf_conditional].
  straightline; repeat straightline_cleanup.
  rename H into Hm.
   
  rewrite <-(firstn_skipn 4 out), <-(firstn_skipn 4 out[_:]), <-(firstn_skipn 4 out[_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:][_:]),
         <-(firstn_skipn 4 out[_:][_:][_:][_:][_:][_:]),
    ?skipn_skipn, ?firstn_skipn in Hm.
  repeat seprewrite_in_by (@sep_eq_of_list_word_at_app) Hm length_tac.
  repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm length_tac.
  repeat seprewrite_in_by @Scalars.scalar_of_bytes Hm length_tac.
  simpl Z.of_nat in *.

  repeat straightline; ssplit; trivial.

  (* postcondition *)

  clear Hm; rename H7 into Hm.
  cbv [Scalars.scalar Scalars.truncated_word Scalars.truncated_scalar] in Hm.
  repeat seprewrite_in_by ptsto_bytes_iff_eq_of_list_word_at Hm ltac:(try rewrite ?length_le_split, ?Scalars.bytes_per_width_bytes_per_word; cbv [Memory.bytes_per_word]; try ZnWords.ZnWords).
  rewrite ?HList.tuple.to_list_of_list, ?Scalars.bytes_per_width_bytes_per_word in Hm.
  change (Memory.bytes_per access_size.word) with 4%nat in Hm.
  repeat seprewrite_in_by (@list_word_at_app_of_adjacent_eq) Hm ltac:(rewrite ?app_length, ?length_le_split, ?length_nil; try ZnWords.ZnWords).
  rewrite <-?app_assoc in Hm.
  simpl Nat.add in Hm.

  revert Hm; eassert ((_ ++ _) = _)%list as ->; [|intros;ecancel_assumption].
  eapply le_combine_inj. { length_tac. } 
  repeat match goal with x := _ |- _ => subst x end.
  case b; Decidable.vm_decide.
Qed.
