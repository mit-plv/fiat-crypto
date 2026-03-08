Require Import ZArith Psatz Coq.Lists.List.
From bedrock2 Require Import NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Require Import Bedrock.P256.Specs.
From bedrock2 Require Import WeakestPrecondition ProgramLogic.
From bedrock2 Require Import Map.SeparationLogic Array Scalars.
From coqutil Require Import Byte Word.Naive Word.Interface Word.LittleEndianList.
Require Import coqutil.Z.PushPullMod.
Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia.
From coqutil Require Import Tactics.Tactics Word.Properties Datatypes.List.
Require Import bedrock2.BasicC64Semantics.
From bedrock2Examples Require Import full_sub.
From coqutil Require Import Byte.

Import ProgramLogic.Coercions.
Set Printing Coercions.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ctime_ltu :=
  func! (a, b) ~> r {
    unpack! _d, r = br_full_sub(a, b, $0);
    unpack! r = br_value_barrier(r)
  }.

Definition index_bits :=
  func! (p_input, nbits, i, w) ~> r {
    idx = i >> $3; (* index = i/8 *)
    a = load1(p_input + idx);
    b = $0;
    if idx + $1 < (nbits + $7) >> $3 {
      b = load1(p_input + idx + $1)
    };
    s = a + (b << $8);
    t = s >> (i & $7); (* offset = i%8 *)
    r = t & (($1 << w) - $1)
  }.

(* Limb size (nonzero). *)
Local Notation w := 5.

Definition limbs_unpack :=
  func! (p_output, p_input, nbits) {
    i = $0;
    while i < nbits {
      unpack! r = index_bits(p_input, nbits, i, $w);
      store1(p_output, r); p_output = p_output + $1;
      i = i + $w;
      $(cmd.unset "r")
    }
  }.

Definition signed_recode_carry :=
  func! (p_limbs, ci, n) ~> ci {
      while n {
        x = load1(p_limbs) + ci;
        unpack! ci = ctime_ltu($(2^(w - 1)), x);
        unpack! x = br_cmov(ci, x - $(2^w), x);
        store1(p_limbs, x); p_limbs = p_limbs + $1;
        n = n - $1;
        $(cmd.unset "x")
      }
    }.

Definition signed_recode :=
  func! (p_limbs, n) {
    unpack! _c = signed_recode_carry(p_limbs, $0, n)
  }.

(* TODO: Should we put all the positional defs and lemmas somewhere? *)
Definition positional B := fold_right (fun a s => a + (B)*s) 0.

Lemma positional_nil B :
  positional B nil = 0.
Proof. reflexivity. Qed.

Lemma positional_cons B h t :
  positional B (h :: t) = h + B*(positional B t).
Proof. reflexivity. Qed.

Definition positional_bytes B l :=
  positional B (map byte.unsigned l).

Definition positional_signed_bytes B l :=
  positional B (map byte.signed l).

Lemma positional_bytes_cons B h t :
  positional_bytes B (h :: t) = byte.unsigned h + B*(positional_bytes B t).
Proof. constructor. Qed.

Local Notation bytearray := (Array.array ptsto (word.of_Z 1)).

#[export] Instance spec_of_ctime_ltu : spec_of "ctime_ltu" :=
  fnspec! "ctime_ltu" a b ~> r,
  { requires t m := True;
    ensures T M :=
      M = m /\ T = t /\
      word.unsigned r < 2 /\
      r = if word.ltu a b then word.of_Z 1 else word.of_Z 0
  }.

#[export] Instance spec_of_index_bits : spec_of "index_bits" :=
  fnspec! "index_bits" (p_input nbits i w : word) / input ~> r,
    { requires t m :=
        m =*> bytearray p_input input /\
        8 * (length input - 1) < nbits <= 8 * length input /\
        le_combine input < 2^nbits /\
        i < nbits /\
        0 <= w <= 8 /\
        nbits + 7 <= (word.of_Z (-1) : word);
      ensures T M :=
        M = m /\
        T = t /\
        r = le_combine input / 2^i mod 2^w :>Z
    }.

#[export] Instance spec_of_limbs_unpack : spec_of "limbs_unpack" :=
  fnspec! "limbs_unpack" (p_output p_input nbits : word) / output input R,
    { requires t m :=
        m =* bytearray p_output output * bytearray p_input input * R /\
        8 * (length input - 1) < nbits <= 8 * length input /\
        w * (length output - 1) < nbits <= w * length output /\
        le_combine input < 2^nbits /\
        nbits + 7 <= (word.of_Z (-1) : word);
      ensures T M := exists OUTPUT,
        M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
        length output = length OUTPUT /\
        T = t /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
        le_combine input = positional_bytes (2^w) OUTPUT
    }.

#[export] Instance spec_of_signed_recode_carry : spec_of "signed_recode_carry" :=
  fnspec! "signed_recode_carry" (p_limbs ci n : word) / limbs R ~> CO,
    { requires t m :=
        m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\
        0 <= ci <= 1;
      ensures T M := exists LIMBS,
        M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
        T = t /\
        positional_signed_bytes (2^w) LIMBS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) limbs /\
        Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS /\
        0 <= CO <= 1
    }.

#[export] Instance spec_of_signed_recode : spec_of "signed_recode" :=
  fnspec! "signed_recode" (p_limbs n : word) / limbs R,
  { requires t m :=
      m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\
      2 * (positional_bytes (2^w) limbs) < 2^(w*n) /\
      -2^(w*n) <= positional (2^w) (repeat (-2^w + 2) (Z.to_nat n));
    ensures T M := exists LIMBS,
      M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
      T = t /\
      positional_signed_bytes (2^w) LIMBS = positional_bytes (2^w) limbs /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS
  }.

Lemma ctime_ltu_ok : program_logic_goal_for_function! ctime_ltu.
Proof.
  repeat straightline.
  straightline_call.
  { ZnWords. }
  repeat straightline.
  straightline_call.
  { trivial. }
  repeat straightline.
  destruct (word.ltu_spec a b); split; ZnWords.
Qed.

Lemma bytearray_load_of_sep addr (addr' : word) n (values : list byte) R m
  (Hsep : (sep (bytearray addr values) R m))
  (_ : addr' = (word.add addr (word.of_Z (Z.of_nat n))))
  (_ : (n < length values)%nat) :
  Memory.load access_size.one m addr' =
  Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n))).
Proof.
  rewrite nth_default_eq.
  rewrite <-(firstn_nth_skipn _ _ values Byte.x00 H0) in Hsep.
  do 2 seprewrite_in @bytearray_append Hsep.
  seprewrite_in @array_cons Hsep.
  seprewrite_in @array_nil Hsep.
  rewrite length_firstn, min_l, <-H in Hsep by lia.
  eapply load_one_of_sep.
  ecancel_assumption.
Qed.

Lemma bytearray_load_of_sep' (addr addr': word) (values : list byte) R m :
  (sep (bytearray addr values) R m) ->
  let offset := word.unsigned (word.sub addr' addr) in
    (let n := Z.to_nat offset in (n < length values)%nat ->
    Memory.load access_size.one m addr' =
    Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n)))).
Proof.
  intros.
  eapply bytearray_load_of_sep; eauto.
  subst offset n.
  rewrite Z2Nat.id by apply word.unsigned_range.
  rewrite word.of_Z_unsigned.
  ring.
Qed.

#[local] Ltac bitwise_setup k :=
  apply Z.bits_inj'; intros k **;
  repeat rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.testbit_mod_pow2, ?bitblast.Z.div_pow2_bits' by ZnWords.

#[local] Ltac bitwise_solve solver :=
  repeat match goal with |- context _g[Z.ltb ?a ?b] => progress (
    case (Z.ltb_spec a b) as [];
    repeat rewrite ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.andb_false_l, ?Bool.andb_false_r,
                   ?Bool.orb_true_l, ?Bool.orb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r;
    try solve [solver])
  end.

Lemma index_bits_ok : program_logic_goal_for_function! index_bits.
Proof.
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  (* First byte load. *)
  eexists _.
  split. {
    eapply bytearray_load_of_sep'; eauto.
    ZnWords. }
  repeat straightline.
  (* Second byte load. *)
  eexists _.
  split.
  { repeat straightline. }
  split; intro cond; repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  { eexists _.
    split.
    { eapply bytearray_load_of_sep'; eauto.
      revert cond.
      case word.ltu_spec; intros; ZnWords. }
    repeat straightline.
    subst r t s v b.
    (* Subtraction in address computation. *)
    rewrite <-word.add_assoc, !word.word_sub_add_l_same_l.
    repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru, ?word.unsigned_add, ?word.unsigned_sub, ?word.unsigned_slu; try ZnWords.
    { rewrite !word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite (Z.mod_small 1) by lia.
      change (7 mod 2^64) with (Z.ones 3).
      rewrite Z.land_ones by lia.
      set (nth_default Byte.x00 input (Z.to_nat (word.unsigned idx))) as b1.
      set (nth_default Byte.x00 input (Z.to_nat ((word.unsigned idx + 1) mod 2 ^ 64))) as b2.
      assert (1 <= 2^w <= 2^8) by (split; [ZnWords | apply Z.pow_le_mono_r; lia]).
      assert ((Z.shiftl 1 (word.unsigned w) mod 2 ^ 64 - 1) mod 2 ^ 64 = Z.ones (word.unsigned w)) as ->.
      { rewrite Z.shiftl_1_l.
        (rewrite_strat (bottomup Z.mod_small)); try lia.
        rewrite Z.ones_equiv, Z.sub_1_r.
        reflexivity. }
      set (word.unsigned i mod 2 ^ 3).
      set ((le_combine input / 2 ^ word.unsigned i) mod 2 ^ word.unsigned w).
      pose proof byte.unsigned_range b1.
      pose proof byte.unsigned_range b2.
      (rewrite_strat (bottomup Z.mod_small)); rewrite ?Z.shiftr_div_pow2; try ZnWords.
      { rewrite Z.land_ones by ZnWords.
        rewrite Z.shiftl_mul_pow2 by lia.
        epose proof nth_default_le_split
          (Z.to_nat (word.unsigned idx))
          (length input) (le_combine input)
          ltac:(ZnWords) Byte.x00 as Hb1.
        rewrite split_le_combine in Hb1.
        subst b1.
        rewrite Hb1.
        clear Hb1.
        revert cond.
        case word.ltu_spec;
        repeat rewrite ?word.unsigned_add, ?word.unsigned_and, ?word.unsigned_sru, ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0 by ZnWords;
        intros Hcond **; try lia.
        unfold word.wrap in Hcond.
        repeat rewrite word.unsigned_of_Z_nowrap in Hcond by lia.
        epose proof nth_default_le_split
          (Z.to_nat ((word.unsigned idx + 1) mod 2 ^ 64))
          (length input) (le_combine input)
          ltac:(ZnWords) Byte.x00 as Hb2.
        rewrite split_le_combine in Hb2.
        subst b2.
        rewrite Hb2.
        clear Hb2.
        assert ((word.unsigned idx + 1) mod 2 ^ 64 = word.unsigned idx + 1) as -> by ZnWords.
        rewrite !Z2Nat.id by ZnWords.
        rewrite !byte.unsigned_of_Z.
        rewrite !Z.shiftr_div_pow2 by ZnWords.
        unfold byte.wrap.
        subst z0 z.
        set (le_combine input).
        assert(
          (z / 2 ^ (8 * word.unsigned idx)) mod 2 ^ 8 + (z / 2 ^ (8 * (word.unsigned idx + 1))) mod 2 ^ 8 * 2 ^ 8 =
          z / 2 ^ (8 * word.unsigned idx) mod 2 ^ 16
        ) as ->.
        { rewrite <-Z.shiftl_mul_pow2 by lia.
          rewrite <-bitblast.Z.or_to_plus.
          { bitwise_setup k.
            bitwise_solve ltac:(
              (reflexivity) ||
              (lia) ||
              (assert (k - 8 + 8 * (word.unsigned idx + 1) = k + 8 * word.unsigned idx) as -> by ZnWords;
              rewrite <-?Z.lor_spec, ?Z.lor_diag;
              reflexivity)
            ). }
          bitwise_setup k.
          bitwise_solve ltac:(
            (lia) ||
            (rewrite Z.testbit_0_l; reflexivity)
          ). }
        assert (word.unsigned idx = i / 2 ^ 3) as -> by ZnWords.
        assert (z = z mod 2^nbits) as ->.
        { rewrite Z.mod_small; trivial.
          pose proof le_combine_bound input.
          ZnWords. }
        bitwise_setup k.
        assert (k + i mod 2 ^ 3 + 8 * (i / 2 ^ 3) = k + i) as -> by ZnWords.
        bitwise_solve ltac:(
          (reflexivity) ||
          (Z.to_euclidean_division_equations; nia) ||
          (lia)
        ). }
      rewrite Z.shiftl_mul_pow2 by lia.
      Z.to_euclidean_division_equations; nia. }
    rewrite word.unsigned_of_Z_nowrap by lia.
    change (7) with (Z.ones 3).
    rewrite Z.land_ones by lia.
    ZnWords. }
  subst r t s b.
  (* Subtraction in address computation. *)
  rewrite word.word_sub_add_l_same_l.
  repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru, ?word.unsigned_add, ?word.unsigned_sub, ?word.unsigned_slu; try ZnWords.
  { rewrite !word.unsigned_of_Z.
    cbv [word.wrap].
    rewrite (Z.mod_small 0), (Z.mod_small 1) by lia.
    rewrite Z.add_0_r, Zmod_mod.
    change (7 mod 2^64) with (Z.ones 3).
    rewrite Z.land_ones by lia.
    set (nth_default Byte.x00 input (Z.to_nat (word.unsigned idx))) as b.
    assert (1 <= 2^w <= 2^8) by (split; [ZnWords | apply Z.pow_le_mono_r; lia]).
    assert ((Z.shiftl 1 (word.unsigned w) mod 2 ^ 64 - 1) mod 2 ^ 64 = Z.ones (word.unsigned w)) as ->.
    { rewrite Z.shiftl_1_l.
      (rewrite_strat (bottomup Z.mod_small)); try lia.
      rewrite Z.ones_equiv, Z.sub_1_r.
      reflexivity. }
    set (word.unsigned i mod 2 ^ 3).
    set ((le_combine input / 2 ^ word.unsigned i) mod 2 ^ word.unsigned w).
    pose proof byte.unsigned_range b.
    (rewrite_strat (bottomup Z.mod_small)); rewrite ?Z.shiftr_div_pow2; try ZnWords.
    { rewrite Z.land_ones by ZnWords.
      epose proof nth_default_le_split
        (Z.to_nat (word.unsigned idx))
        (length input) (le_combine input)
        ltac:(ZnWords) Byte.x00 as Hb.
      rewrite split_le_combine in Hb.
      subst b.
      rewrite Hb.
      clear Hb.
      rewrite Z2Nat.id by ZnWords.
      rewrite byte.unsigned_of_Z.
      rewrite Z.shiftr_div_pow2 by ZnWords.
      unfold byte.wrap.
      subst z0 z.
      set (le_combine input).
      assert (word.unsigned idx = i / 2 ^ 3) as -> by ZnWords.
      revert cond.
      case word.ltu_spec;
      repeat rewrite ?word.unsigned_add, ?word.unsigned_and, ?word.unsigned_sru, ?word.unsigned_of_Z_1 by ZnWords;
      intros Hcond **; try lia.
      unfold word.wrap in Hcond.
      repeat rewrite word.unsigned_of_Z_nowrap in Hcond by lia.
      assert (z = z mod 2^nbits) as ->.
      { rewrite Z.mod_small; trivial.
        pose proof le_combine_bound input.
        ZnWords. }
      bitwise_setup k.
      assert (k + i mod 2 ^ 3 + 8 * (i / 2 ^ 3) = k + i) as -> by ZnWords.
      bitwise_solve ltac:(
        (reflexivity) ||
        (Z.to_euclidean_division_equations; nia) ||
        (exfalso; ZnWords)
      ). }
    { pose proof Z.mod_bound_pos i (2 ^ 3) ltac:(ZnWords) ltac:(lia).
      Z.to_euclidean_division_equations; nia. } }
  rewrite word.unsigned_of_Z_nowrap by lia.
  change (7) with (Z.ones 3).
  rewrite Z.land_ones by lia.
  ZnWords.
Qed.

Lemma limbs_unpack_ok : program_logic_goal_for_function! limbs_unpack.
Proof.
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                   HList.polymorphic_list.nil))
    (* program variables *) (["p_output";"p_input";"nbits";"i"] : list String.string))
    (fun v output R t m p_output p_input nbits_ i => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned i /\
      nbits_ = nbits /\ (* input = inside loop *)
      m =* bytearray p_output output * bytearray p_input input * R /\
      8 * (length input - 1) < nbits <= 8 * length input /\
      w * (length output - 1) < nbits - i <= w * length output /\
      le_combine input < 2^nbits /\
      nbits + w <= (word.of_Z (-1) : word))
    (fun            T M P_OUTPUT P_INPUT NBITS I => (* postcondition *)
      exists OUTPUT,
      M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
      length output = length OUTPUT /\
      T = t /\
      p_input = P_INPUT /\
      nbits = NBITS /\ (* inside loop = output *)
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
      le_combine input / 2^i = positional_bytes (2^w) OUTPUT))
    (fun n m => m < n <= nbits + w) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.gt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; try ZnWords. }
  { repeat straightline; subst br.
    { revert H7.
      case word.ltu_spec; intros;
      rewrite word.unsigned_of_Z_nowrap in H8 by ZnWords; try lia.
      straightline_call. (* call index_bits *)
      { ssplit; try (eexists _; ecancel_assumption); trivial; ZnWords. }
      repeat straightline.
      clear dependent output; rename x into output.
      destruct output as [| out0 output_rest].
      { (* Empty list case. *)
        rewrite List.length_nil in *.
        lia. }
      cbn [bytearray] in * |-.
      repeat straightline.
      eexists _, _, _.
      repeat straightline.
      { cbn [length] in *.
        ssplit; try ecancel_assumption; trivial; ZnWords. }
      split.
      { (* loop test *)
        ZnWords. }
      repeat straightline.
      eexists (_ :: _).
      ssplit; try (cbn [bytearray]; ecancel_assumption); trivial.
      { rewrite !length_cons. ZnWords. }
      { (* Forall bound on output. *)
        apply Forall_cons.
        { rewrite H19.
          rewrite word.unsigned_of_Z_nowrap by ZnWords.
          rewrite byte.unsigned_of_Z.
          cbv [byte.wrap].
          rewrite Z.mod_small; ZnWords. }
        assumption. }
      rewrite positional_bytes_cons.
      rewrite <-H21, H19.
      subst i.
      rewrite word.unsigned_of_Z_nowrap by ZnWords.
      rewrite word.unsigned_add_nowrap by ZnWords.
      rewrite word.unsigned_of_Z_nowrap by ZnWords.
      rewrite byte.unsigned_of_Z.
      cbv [byte.wrap].
      rewrite Z.mod_small by ZnWords.
      rewrite Z.pow_add_r by ZnWords.
      rewrite <-Z.div_div by ZnWords.
      rewrite Z.add_comm.
      rewrite <-Z.div_mod by ZnWords.
      reflexivity. }
    (* base case *)
    eexists x.
    ssplit; try ecancel_assumption; auto;
    revert H7;
    case word.ltu_spec; intros;
    rewrite word.unsigned_of_Z_nowrap in H8 by ZnWords;
    try discriminate;
    assert (length x = 0%nat) by ZnWords;
    rewrite length_zero_iff_nil in *;
    subst x.
    { apply Forall_nil. }
    cbv [positional_bytes positional map fold_right].
    assert (2 ^ word.unsigned nbits <= 2 ^ word.unsigned x4) by (apply Z.pow_le_mono_r; ZnWords).
    assert (le_combine input < 2 ^ word.unsigned x4) by ZnWords.
    apply Z.div_small.
    split; [apply le_combine_bound | trivial]. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
  subst i.
  rewrite word.unsigned_of_Z_0, Z.pow_0_r, Z.div_1_r in H13.
  assumption.
Qed.

Lemma signed_recode_carry_ok : program_logic_goal_for_function! signed_recode_carry.
Proof.
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                   HList.polymorphic_list.nil))
    (* program variables *) (["p_limbs";"ci";"n"] : list String.string))
    (fun v limbs R t m p_limbs ci n => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned n /\
      m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\ 0 <= ci <= 1)
    (fun           T M P_LIMBS (CO : word) N => T = t /\ (* postcondition *)
      exists LIMBS,
      M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
      positional_signed_bytes (2^w) LIMBS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) limbs /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS /\ 0 <= CO <= 1))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.lt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; trivial. }
  { repeat straightline.
    { clear dependent limbs; rename x into limbs.
      (* Take the first element from the limbs list. *)
      destruct limbs as [| w0 limbs_rest].
      { rewrite List.length_nil in *; lia. }
      { cbn [array] in * |-.
        repeat straightline.
        (* call ctime_lt *)
        straightline_call.
        { apply Forall_inv in H9. ZnWords. }
        repeat straightline.
        (* call br_cmov *)
        straightline_call; trivial. clear H12.
        repeat straightline.
        exists limbs_rest; eexists _; exists (v - 1).
        repeat straightline.
        { ssplit.
          { ZnWords. }
          { ecancel_assumption. }
          { subst n.
            rewrite word.unsigned_sub_nowrap;
            rewrite word.unsigned_of_Z_1;
            rewrite <-H8;
            rewrite List.length_cons;
            lia. }
          { inversion H9. trivial. }
          all: subst x; case word.ltu_spec; ZnWords. }
        { split.
          { lia. }
          { repeat straightline.
            eexists (_ :: _).
            ssplit.
            { cbn [array].
              ecancel_assumption. }
            { rewrite length_cons; ZnWords. }
            {
              cbn [positional_signed_bytes positional_bytes positional map fold_right].
              cbv [x4 x].
              case word.ltu_spec; intros; case Z.eqb_spec; intros; try ZnWords;
              revert H13; cbv[x positional_signed_bytes positional_bytes];
              case word.ltu_spec; intros; try ZnWords;
              [
                rewrite word.unsigned_of_Z_1, (Z.add_comm 1), <-Z.sub_move_r in H17 |
                rewrite word.unsigned_of_Z_0, Z.add_0_l in H17
              ];
              rewrite <-H17; cbv[v0] in *;
              rewrite !Z.pow_mul_r by lia;
              apply Z.sub_move_0_r;
              set (positional (2 ^ w) (map byte.signed x8)).

              (* TODO: ring_simplify stalls Qed so we perform some manual simplifications. *)
              {
                assert (
                  (2 ^ w) * (z + (2 ^ w) ^ word.unsigned n * word.unsigned x6 - 1) =
                  (2 ^ w) * z + (2 ^ w) * (2 ^ w) ^ word.unsigned n * word.unsigned x6 - 2 ^ w
                ) as -> by lia.
                set ((2 ^ w) * z) as cancel.
                set (byte.signed (byte.of_Z (word.unsigned (word.sub (word.add (word.of_Z (byte.unsigned w0)) x2) (word.of_Z _))))).
                assert (
                  z0 + cancel + (2 ^ w) ^ word.unsigned x3 * word.unsigned x6 - (word.unsigned x2 + (byte.unsigned w0 + (cancel + (2 ^ w) * (2 ^ w) ^ word.unsigned n * word.unsigned x6 - 2 ^ w))) =
                  z0 + (2 ^ w) ^ word.unsigned x3 * word.unsigned x6 - (2 ^ w) * word.unsigned x6 * (2 ^ w) ^ word.unsigned n - word.unsigned x2 - byte.unsigned w0 + 2 ^ w
                ) as -> by lia.
                shelve.
              }
              {
                assert (
                  (2 ^ w) * (z + (2 ^ w) ^ word.unsigned n * word.unsigned x6) =
                  (2 ^ w) * z + (2 ^ w) * (2 ^ w) ^ word.unsigned n * word.unsigned x6
                ) as -> by lia.
                set ((2 ^ w) * z) as cancel.
                set (byte.signed (byte.of_Z (word.unsigned (word.add (word.of_Z (byte.unsigned w0)) x2)))).
                assert (
                  z0 + cancel + (2 ^ w) ^ word.unsigned x3 * word.unsigned x6 - (word.unsigned x2 + (byte.unsigned w0 + (cancel + (2 ^ w) * (2 ^ w) ^ word.unsigned n * word.unsigned x6))) =
                  z0 + (2 ^ w) ^ word.unsigned x3 * word.unsigned x6 - (2 ^ w) * word.unsigned x6 * (2 ^ w) ^ word.unsigned n - word.unsigned x2 - byte.unsigned w0
                ) as -> by lia.
                shelve.
              }

              Unshelve.
              { subst z0.
                set (word.of_Z (byte.unsigned w0)) as b0.
                assert (word.unsigned (word.sub (word.add b0 x2) (word.of_Z _)) = word.wrap (b0 + x2 - 2 ^ w)) as -> by ZnWords.
                cbv [byte.signed].
                rewrite byte.unsigned_of_Z, byte.swrap_wrap, word.byte_swrap_word_wrap by lia.
                cbv [byte.swrap word.swrap].
                subst b0.
                rewrite word.unsigned_of_Z_nowrap by (pose proof byte.unsigned_range w0; lia).
                rewrite Z.mod_small by (inversion H9; ZnWords).
                ring_simplify.
                subst n.
                rewrite word.unsigned_sub_nowrap by ZnWords.
                rewrite <-H8; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Z.pow_succ_r by lia.
                assert (
                  (Z.succ (Z.of_nat (length limbs_rest)) - word.unsigned (word.of_Z 1)) =
                  (Z.of_nat (length limbs_rest))
                ) as -> by ZnWords.
                ZnWords. }
              { subst z0.
                cbv [byte.signed].
                rewrite byte.unsigned_of_Z, byte.swrap_wrap.
                rewrite word.unsigned_add_nowrap.
                { cbv [byte.swrap word.swrap].
                  rewrite Z.mod_small by (inversion H9; ZnWords).
                  ring_simplify.
                  subst n.
                  rewrite word.unsigned_sub_nowrap by ZnWords.
                  rewrite <-H8; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Z.pow_succ_r by lia.
                  assert (
                    (Z.succ (Z.of_nat (length limbs_rest)) - word.unsigned (word.of_Z 1)) =
                    (Z.of_nat (length limbs_rest))
                  ) as -> by ZnWords.
                  rewrite word.unsigned_of_Z.
                  cbv [word.wrap].
                  rewrite Z.mod_small by (inversion H9; ZnWords).
                  ZnWords. }
                rewrite word.unsigned_of_Z.
                cbv [word.wrap].
                pose proof byte.unsigned_range w0.
                ZnWords. } }
            { constructor.
              { cbv [x4 x].
                case word.ltu_spec; intros; case Z.eqb_spec; intros; try ZnWords; inversion H9; cbv [v0] in *;
                set (word.of_Z (byte.unsigned w0)) as b0;
                [
                  assert (word.unsigned (word.sub (word.add b0 x2) (word.of_Z _)) = word.wrap (b0 + x2 - 2 ^ w)) as -> by ZnWords |
                  assert (word.unsigned (word.add b0 x2) = word.wrap (b0 + x2)) as -> by ZnWords
                ];
                cbv [byte.signed];
                rewrite byte.unsigned_of_Z, byte.swrap_wrap, word.byte_swrap_word_wrap by lia;
                cbv [byte.swrap word.swrap];
                subst b0;
                rewrite word.unsigned_of_Z_nowrap by (pose proof byte.unsigned_range w0; lia);
                rewrite Z.mod_small by lia; ZnWords. }
              trivial. }
            { trivial. }
            { trivial. } } } } }
    { (*base case*)
      assert (length x = 0%nat) by ZnWords.
      rewrite length_zero_iff_nil in *.
      subst x.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      cbn [positional_signed_bytes positional_bytes positional List.map fold_right].
      rewrite H6, Z.mul_0_r.
      lia. } }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma positional_bounded (l : list Z) L U :
  let n := length l in
  Forall (fun b => (L <= 2*b <= U)) l ->
  positional (2^w) (List.repeat L n) <= 2 * (positional (2^w) l) <= positional (2^w) (List.repeat U n).
Proof.
  induction 1.
  { subst n.
    rewrite length_nil, ?positional_nil.
    lia. }
  { subst n.
    rewrite length_cons, positional_cons.
    cbn [repeat].
    rewrite ?positional_cons.
    cbv [id] in *.
    lia. }
Qed.

Lemma signed_recode_ok : program_logic_goal_for_function! signed_recode.
Proof.
  repeat straightline.
  straightline_call. (* call signed_recode_carry *)
  { ssplit; try ecancel_assumption; trivial; ZnWords. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
  assert (word.unsigned x <> 1).
  { intros Hx.
    rewrite word.unsigned_of_Z_0, Z.add_0_l, Hx, Z.mul_1_r in H9.
    epose proof positional_bounded (map byte.signed x0) (- 2 ^ w + 2) (2 ^ w) ltac:(apply Forall_map; assumption).
    rewrite length_map in H5.
    progress fold (positional_signed_bytes (2 ^ w) x0) in H5.
    assert (2*positional_signed_bytes (2 ^ w) x0 < -2^(w*n)) by lia.
    assert (positional (2 ^ w) (repeat (- 2 ^ w + 2) (length x0)) < -2 ^ (w * n)) by lia.
    rewrite <-H7, Nat2Z.id in H4.
    rewrite <-H7 in H13.
    lia. }
  ZnWords.
Qed.
