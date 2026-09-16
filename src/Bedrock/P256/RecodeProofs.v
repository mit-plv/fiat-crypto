Require Import ZArith.ZArith Lia Lists.List.
From coqutil Require Import
  Byte
  Word.LittleEndianList
  Word.Properties
  Tactics.Tactics
  Datatypes.List.

From bedrock2 Require Import
  NotationsCustomEntry
  WeakestPrecondition
  ProgramLogic
  Map.SeparationLogic
  Array
  Scalars
  Syntax
  ZnWords
  BasicC64Semantics.

Require Import Bedrock.P256.Specs Bedrock.P256.RecodeSpecs.
From bedrock2Examples Require Import full_sub.

Import BinInt String ListNotations.
Import ProgramLogic.Coercions.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.

#[local] Notation bytearray := (Array.array ptsto (bits.of_Z _ 1)).

(* Limb size (nonzero). *)
#[local] Notation w := 5.

Lemma ctime_ltu_ok : program_logic_goal_for_function! ctime_ltu.
Proof.
  repeat straightline.
  straightline_call.
  { ZnWords. }
  repeat straightline.
  straightline_call.
  { trivial. }
  repeat straightline.
  case Z.ltb_spec; split; ZnWords.
Qed.

Lemma bytearray_load_of_sep addr (addr' : word) n (values : list byte) R m
  (Hsep : (sep (bytearray addr values) R m))
  (Haddr : addr' = (Zmod.add addr (bits.of_Z _ (Z.of_nat n))))
  (Hlength : (n < length values)) :
  Memory.load access_size.one m addr' =
  Some (bits.of_Z _ (byte.unsigned (nth_default Byte.x00 values n))).
Proof.
  rewrite nth_default_eq.
  rewrite <-(firstn_nth_skipn _ n values Byte.x00) in Hsep by lia.
  do 2 seprewrite_in @bytearray_append Hsep.
  seprewrite_in @array_cons Hsep.
  seprewrite_in @array_nil Hsep.
  rewrite length_firstn, min_l, <-Haddr in Hsep by lia.
  eapply load_one_of_sep.
  ecancel_assumption.
Qed.

Lemma bytearray_load_of_sep' (addr addr': word) (values : list byte) R m :
  (sep (bytearray addr values) R m) ->
  let offset := Zmod.unsigned (Zmod.sub addr' addr) in
    (let n := Z.to_nat offset in (n < length values) ->
    Memory.load access_size.one m addr' =
    Some (bits.of_Z _ (byte.unsigned (nth_default Byte.x00 values n)))).
Proof.
  intros.
  eapply bytearray_load_of_sep; eauto.
  subst offset n.
  rewrite Z2Nat.id by apply (bits.unsigned_range _ width_nonneg).
  rewrite Zmod.of_Z_unsigned.
  ring.
Qed.

Lemma extract_limb_at_bit_zify a b (i : word) :
  0 <= a < 2^8 ->
  0 <= b < 2^8 ->
  Zmod.unsigned (Zmod.and
    (Zmod.sru (Zmod.or (bits.of_Z 64 a) (Zmod.slu (bits.of_Z 64 b) (Zmod.unsigned (bits.of_Z 64 8) mod 2 ^ Z.log2 64)))
      (Zmod.unsigned (Zmod.and i (bits.of_Z 64 7)) mod 2 ^ Z.log2 64))
    (Zmod.sub (Zmod.slu (bits.of_Z 64 1) (Zmod.unsigned (bits.of_Z 64 w) mod 2 ^ Z.log2 64)) (bits.of_Z 64 1))) =
  Z.land ((Z.shiftr (Z.lor a (Z.shiftl b 8)) (Z.land (Zmod.unsigned i) (Z.ones 3)))) (Z.ones w).
Proof.
  intros.
  rewrite !shamt_of_Z_small by lia.
  rewrite !bits.unsigned_and, !bits.unsigned_of_Z_small by lia.
  change 7 with (Z.ones 3); rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small (_ mod 2 ^ 3))
    by (change (2 ^ Z.log2 64) with 64; pose proof Z.mod_pos_bound (Zmod.unsigned i) (2 ^ 3) ltac:(lia); lia).
  rewrite Zmod.unsigned_sru, bits.unsigned_or, !Zmod.unsigned_slu, !bits.unsigned_of_Z_small
    by (try apply Z.mod_pos_bound; lia).
  rewrite word.unsigned_sub_nowrap
    by (try exact width_pos; rewrite ?Zmod.unsigned_slu, ?bits.unsigned_of_Z_small; cbn; lia).
  rewrite ?Zmod.unsigned_slu, ?bits.unsigned_of_Z_small by lia.
  rewrite (Z.mod_small (Z.shiftl b 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change (Z.shiftl 1 5 mod 2 ^ 64 - 1) with (Z.ones 5).
  rewrite Z.land_ones by lia; reflexivity.
Qed.


Lemma bytelist_extract_two num i b1 b2:
  let idx := i / 8  in
  b1 = (nth_default Byte.x00 num (Z.to_nat idx)) ->
  b2 = (nth_default Byte.x00 num (S (Z.to_nat (idx)))) ->
  0 <= i < length num * 8 ->
  Z.land ((Z.shiftr (Z.lor (byte.unsigned b1) (Z.shiftl (byte.unsigned b2) 8)) (Z.land i (Z.ones 3)))) (Z.ones w) =
  (LittleEndianList.le_combine num / 2 ^ i) mod 2 ^ w.
Proof.
  intros ? Hb1 Hb2. intros.

  rewrite (Z.land_ones _ 3) by lia.
  replace (i mod 2^3) with (i - idx*8) by ZnWords.

  replace (LittleEndianList.le_combine num) with
      (LittleEndianList.le_combine
        ((firstn (Z.to_nat (idx)) num) ++ [b1] ++ [b2] ++ (skipn (S (S (Z.to_nat (idx)))) num)));cycle 1.
  { rewrite Hb1, Hb2, !nth_default_eq, app_assoc.
    rewrite firstn_nth by ZnWords.
    destruct (Nat.eq_dec (S (Z.to_nat idx)) ((length num))) as [Hlength|?].
    { rewrite <- (le_combine_snoc_0 num).
      f_equal.
      rewrite List.skipn_all, nth_overflow by lia.
      rewrite Hlength, firstn_all, app_nil_r.
      reflexivity. }
    { f_equal. rewrite firstn_nth_skipn by ZnWords. reflexivity. }}
  repeat rewrite LittleEndianList.le_combine_app.
  rewrite <-(byte.wrap_unsigned b1), <-(byte.wrap_unsigned b2); cbv [byte.wrap].

  rewrite le_combine_firstn, ?le_combine_1.
  rewrite !length_cons, !length_nil, firstn_length_le, Z2Nat.id by ZnWords.

  rewrite <-(byte.wrap_unsigned b1), <-(byte.wrap_unsigned b2); cbv [byte.wrap].

  apply Z.bits_inj'; intros.
  repeat rewrite
    <-?Z.shiftr_div_pow2, ?Z.testbit_mod_pow2,
    ?bitblast.Z.shiftr_spec', ?bitblast.Z.shiftl_spec', ?Z.land_spec, ?Z.lor_spec,
    ?Z.testbit_mod_pow2, ?Z.testbit_ones_nonneg
    by (lia || ZnWords).

  repeat (trivial; case Z.ltb_spec; intros; try lia;
    repeat rewrite
      ?Z.add_sub_assoc,
      ?Bool.andb_true_r, ?Bool.andb_true_l,
      ?Bool.andb_false_r, ?Bool.andb_false_l,
      ?Bool.orb_true_r, ?Bool.orb_true_l,
      ?Bool.orb_false_r, ?Bool.orb_false_l;
    repeat match goal with |- context [Z.testbit ?a ?b] => rewrite (Z.testbit_neg_r a b) by ZnWords end).
Qed.

Lemma extract_limb_at_bit_ok : program_logic_goal_for_function! extract_limb_at_bit.
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
      case Z.ltb_spec; intros; ZnWords. }
    repeat straightline.
    subst r t s v b.
    revert cond; case Z.ltb_spec; intros; [|ZnWords].

    rewrite extract_limb_at_bit_zify by apply byte.unsigned_range.

    erewrite bytelist_extract_two; [reflexivity | | | ZnWords ].
    all: repeat f_equal; ZnWords.
  }
  subst r t s b.
  revert cond; case Z.ltb_spec; intros cond ?; [ZnWords|].

  rewrite extract_limb_at_bit_zify by (try apply byte.unsigned_range; lia).

  replace 0 with (byte.unsigned Byte.x00).
  erewrite bytelist_extract_two; [reflexivity | | | ZnWords ].
  { repeat f_equal; try ZnWords. }

  rewrite nth_default_eq, nth_overflow.
  { reflexivity. }
  ZnWords.
Qed.

Lemma decompose_to_limbs_ok : program_logic_goal_for_function! decompose_to_limbs.
Proof.
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                   HList.polymorphic_list.nil))
    (* program variables *) (["p_output";"p_input";"total_bits";"i"] : list String.string))
    (fun v output R t m p_output p_input total_bits_ i => PrimitivePair.pair.mk (* precondition *)
      (v = Zmod.unsigned i /\
      total_bits_ = total_bits /\ (* input = inside loop *)
      m =* bytearray p_output output * bytearray p_input input * R /\
      8 * (length input - 1) < total_bits <= 8 * length input /\
      w * (length output - 1) < total_bits - i <= w * length output /\
      le_combine input < 2^total_bits /\
      total_bits + w <= bits.of_Z 64 (-1))
    (fun            T M P_OUTPUT P_INPUT TOTAL_BITS I => (* postcondition *)
      exists OUTPUT,
      M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
      length output = length OUTPUT /\
      T = t /\
      p_input = P_INPUT /\
      total_bits = TOTAL_BITS /\ (* inside loop = output *)
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
      le_combine input / 2^i = positional_bytes (2^w) OUTPUT))
    (fun n m => m < n <= total_bits + w) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.gt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; try ZnWords. }
  { intros v output_ R_ t_ m_ p_output_ p_input_ total_bits_ i_.
    repeat straightline; subst br.
    { destruct (Z.ltb_spec i_ total_bits);
      rewrite ?bits.unsigned_of_Z_small, ?bits.unsigned_1, ?Zmod.unsigned_0 in * by ZnWords; try lia.
      straightline_call. (* call extract_limb_at_bit *)
      { ssplit; try (eexists _; ecancel_assumption); trivial; ZnWords. }
      repeat straightline.
      destruct output_ as [| out0 output_rest].
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
        { match goal with H: ?x = _ |- context [?x] => rewrite H end.
          rewrite byte.unsigned_of_Z.
          cbv [byte.wrap].
          rewrite Z.mod_small; ZnWords. }
        assumption. }
      rewrite positional_bytes_cons.
      match goal with H: _ = ?x |- context [?x] => rewrite <-H end.
      match goal with H: ?x = _ |- context [?x] => rewrite H end.
      subst i.
      rewrite word.unsigned_add_nowrap, bits.unsigned_of_Z_small by ZnWords.
      rewrite byte.unsigned_of_Z.
      cbv [byte.wrap].
      rewrite Z.mod_small, Z.pow_add_r, <-Z.div_div, Z.add_comm, <-Z.div_mod by ZnWords.
      reflexivity. }
    (* base case *)
    eexists output_.
    destruct (Z.ltb_spec i_ total_bits);
    rewrite ?bits.unsigned_of_Z_small, ?bits.unsigned_1, ?Zmod.unsigned_0 in * by ZnWords; try lia.
    ssplit; try ecancel_assumption; trivial;
    assert (length output_ = 0%nat) by ZnWords;
    rewrite length_zero_iff_nil in *;
    subst output_.
    { apply Forall_nil. }
    cbn [positional_bytes positional map fold_right].
    assert (2 ^ Zmod.unsigned total_bits <= 2 ^ Zmod.unsigned i_) by (apply Z.pow_le_mono_r; ZnWords).
    assert (le_combine input < 2 ^ Zmod.unsigned i_) by ZnWords.
    apply Z.div_small.
    split; [apply le_combine_bound | trivial]. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
  subst i.
  match goal with H: _ = ?x |- context [?x] => rewrite <-H end.
  cbn. apply Z.div_1_r.
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
      (v = Zmod.unsigned n /\
      m =* bytearray p_limbs limbs * R /\ length limbs = Zmod.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\ 0 <= ci <= 1)
    (fun           T M P_LIMBS (CO : word) N => T = t /\ (* postcondition *)
      exists LIMBS,
      M =* bytearray p_limbs LIMBS * R /\ length LIMBS = Zmod.unsigned n :>Z /\
      positional_signed_bytes (2^w) LIMBS + 2^(w*n)*CO = Zmod.unsigned ci + positional_bytes (2^w) limbs /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS /\ 0 <= CO <= 1))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.lt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; trivial. }
  { clear dependent limbs.
    intros v limbs R_ t_ m_ p_limbs_ ci_ n_.
    repeat straightline.
    { (* Take the first element from the limbs list. *)
      destruct limbs as [| w0 limbs_rest].
      { rewrite List.length_nil in *; lia. }
      { cbn [array] in * |-.
        repeat straightline.
        (* call ctime_lt *)
        straightline_call.
        { match goal with H: Forall _ _ |- _ => apply Forall_inv in H end.
          ZnWords. }
        repeat straightline.
        (* call br_cmov *)
        straightline_call; trivial.
        repeat straightline.
        exists limbs_rest; eexists _; exists (v - 1).
        repeat straightline.
        { ssplit.
          { ZnWords. }
          { ecancel_assumption. }
          { subst n.
            rewrite word.unsigned_sub_nowrap, bits.unsigned_1;
            rewrite List.length_cons in *;
            try ZnWords. }
          { match goal with H: Forall _ _ |- _ => inversion H end; trivial. }
          all: subst x; case Z.ltb_spec; ZnWords. }
        { split.
          { lia. }
          { repeat straightline.
            eexists (_ :: _).
            ssplit.
            { cbn [array].
              ecancel_assumption. }
            { rewrite length_cons; ZnWords. }
            {
              match goal with H: context[positional_signed_bytes] |- _ => revert H end.
              unfold positional_signed_bytes, positional_bytes.
              rewrite Zeq_plus_swap.
              cbn [map positional fold_right]. intros ->.
              rewrite Z.mul_sub_distr_l.

              subst n.
              rewrite <- !Z.add_assoc, <- Z.sub_sub_distr, Z.add_sub_assoc, <- Z.sub_0_r.
              f_equal.
              2:{ rewrite word.unsigned_sub_nowrap, bits.unsigned_1, Z.mul_assoc, <- Z.pow_add_r by ZnWords.
                rewrite Zeq_minus; [trivial|].
                do 2 f_equal. lia. }

              cbv [x0 x v0 byte.signed].
              match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
              case Z.ltb_spec; case Z.eqb_spec; [ZnWords | | | ZnWords];
              repeat rewrite ?Zmod.unsigned_0, ?Zmod.unsigned_0, ?word.unsigned_sub_nowrap,
                ?Zmod.unsigned_sub, ?word.unsigned_add_nowrap, ?byte.unsigned_of_Z, ?byte.swrap_wrap by ZnWords; intros.
              { rewrite word.byte_swrap_word_wrap by ZnWords.
                cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
              { cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
            }
            { constructor.
              { cbv [x0 x v0].
                match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
                case Z.ltb_spec; case Z.eqb_spec;
                repeat rewrite ?Zmod.unsigned_0, ?Zmod.unsigned_0, ?word.unsigned_sub_nowrap,
                ?word.unsigned_add_nowrap, ?Zmod.unsigned_sub, ?bits.unsigned_of_Z_small by ZnWords;
                intros; try ZnWords; unfold byte.signed; rewrite byte.unsigned_of_Z, byte.swrap_wrap;
                rewrite ?word.byte_swrap_word_wrap by lia;
                cbv [byte.swrap]; rewrite Z.mod_small; try ZnWords. }
                assumption. }
            all: lia. } } } }
    { assert (length limbs = 0%nat) by ZnWords.
      rewrite length_zero_iff_nil in *.
      subst limbs.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      cbn [positional_signed_bytes positional_bytes positional List.map fold_right].
      match goal with H: ?x = _ |- context [?x] => rewrite H end.
      lia. }
  }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma positional_bound (l : list Z) L U :
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
  assert (Zmod.unsigned x <> 1).
  { intros Hx.
    rewrite Zmod.unsigned_0, Z.add_0_l, Hx, Z.mul_1_r in *.
    epose proof positional_bound (map byte.signed x0) (- 2 ^ w + 2) (2 ^ w) ltac:(apply Forall_map; assumption).
    rewrite length_map in *.
    progress fold (positional_signed_bytes (2 ^ w) x0) in *.
    assert (2*positional_signed_bytes (2 ^ w) x0 < -2^(w*n)) by lia.
    assert (positional (2 ^ w) (repeat (- 2 ^ w + 2) (length x0)) < -2 ^ (w * n)) by lia.
    match goal with H: _ = Zmod.unsigned n |- _ => rewrite <-H in * end.
    rewrite Nat2Z.id in *.
    lia. }
  ZnWords.
Qed.
