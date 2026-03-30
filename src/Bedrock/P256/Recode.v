Require Import ZArith.ZArith Lia Lists.List.
From coqutil Require Import
  Byte
  Word.Naive
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

Require Import Bedrock.P256.Specs.
From bedrock2Examples Require Import full_sub.

Import BinInt String ListNotations.
Import ProgramLogic.Coercions.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.

Definition ctime_ltu :=
  func! (a, b) ~> r {
    unpack! _d, r = br_full_sub(a, b, $0);
    unpack! r = br_value_barrier(r)
  }.

(* Limb size (nonzero). *)
#[local] Notation w := 5.

Definition extract_limb_at_bit :=
  func! (p_input, total_bits, i) ~> r {
    idx = i >> $3; (* index = i/8 *)
    a = load1(p_input + idx);
    b = $0;
    if idx + $1 < (total_bits + $7) >> $3 {
      b = load1(p_input + idx + $1)
    };
    s = a + (b << $8);
    t = s >> (i & $7); (* offset = i%8 *)
    r = t & (($1 << $w) - $1)
  }.

Definition decompose_to_limbs :=
  func! (p_output, p_input, total_bits) {
    i = $0;
    while i < total_bits {
      unpack! r = extract_limb_at_bit(p_input, total_bits, i);
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

Section WithBase.
Context (B : Z).
Definition positional := fold_right (fun a s => a + (B)*s) 0.

Lemma positional_nil :
  positional nil = 0.
Proof. reflexivity. Qed.

Lemma positional_cons h t :
  positional (h :: t) = h + B*(positional t).
Proof. reflexivity. Qed.

Definition positional_bytes l :=
  positional (map byte.unsigned l).

Definition positional_signed_bytes l :=
  positional (map byte.signed l).

Lemma positional_bytes_cons h t :
  positional_bytes (h :: t) = byte.unsigned h + B*(positional_bytes t).
Proof. constructor. Qed.
End WithBase.

#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).

#[export] Instance spec_of_ctime_ltu : spec_of "ctime_ltu" :=
  fnspec! "ctime_ltu" a b ~> r,
  { requires t m := True;
    ensures T M :=
      M = m /\ T = t /\
      word.unsigned r < 2 /\
      r = if word.ltu a b then word.of_Z 1 else word.of_Z 0
  }.

#[export] Instance spec_of_extract_limb_at_bit : spec_of "extract_limb_at_bit" :=
  fnspec! "extract_limb_at_bit" (p_input total_bits i : word) / input ~> r,
    { requires t m :=
        m =*> bytearray p_input input /\
        8 * (length input - 1) < total_bits <= 8 * length input /\
        le_combine input < 2^total_bits /\
        i < total_bits /\
        total_bits + 7 <= (word.of_Z (-1) : word);
      ensures T M :=
        M = m /\
        T = t /\
        r = le_combine input / 2^i mod 2^w :>Z
    }.

#[export] Instance spec_of_decompose_to_limbs : spec_of "decompose_to_limbs" :=
  fnspec! "decompose_to_limbs" (p_output p_input total_bits : word) / output input R,
    { requires t m :=
        m =* bytearray p_output output * bytearray p_input input * R /\
        8 * (length input - 1) < total_bits <= 8 * length input /\
        w * (length output - 1) < total_bits <= w * length output /\
        le_combine input < 2^total_bits /\
        total_bits + 7 <= (word.of_Z (-1) : word);
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
  case word.ltu_spec; split; ZnWords.
Qed.

Lemma bytearray_load_of_sep addr (addr' : word) n (values : list byte) R m
  (Hsep : (sep (bytearray addr values) R m))
  (Haddr : addr' = (word.add addr (word.of_Z (Z.of_nat n))))
  (Hlength : (n < length values)%nat) :
  Memory.load access_size.one m addr' =
  Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n))).
Proof.
  rewrite nth_default_eq.
  rewrite <-(firstn_nth_skipn _ _ values Byte.x00 Hlength) in Hsep.
  do 2 seprewrite_in @bytearray_append Hsep.
  seprewrite_in @array_cons Hsep.
  seprewrite_in @array_nil Hsep.
  rewrite length_firstn, min_l, <-Haddr in Hsep by lia.
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


Lemma extract_limb_at_bit_zify a b i :
  0 <= a < 2^8 ->
  0 <= b < 2^8 ->
  word.unsigned (word.and
    (word.sru (word.add (word.of_Z a) (word.slu (word.of_Z b) (word.of_Z 8))) (word.and i (word.of_Z 7)))
    (word.sub (word.slu (word.of_Z 1) (word.of_Z w)) (word.of_Z 1))) =
  ((a + (b * 2^8)) / 2^((word.unsigned i) mod 8)) mod (2^w).
Proof.
  intros.
  assert (1 <= 2^w <= 2^8) by (split; [lia | apply Z.pow_le_mono_r; lia]).
  pose proof Naive.word64_ok.
  repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?word.unsigned_add_nowrap,
    ?word.unsigned_sub_nowrap, ?word.unsigned_slu, ?Z.shiftl_1_l,
    ?word.unsigned_of_Z_nowrap; try lia; try ZnWords.
  all: (change (7) with (Z.ones 3); rewrite Z.land_ones by lia).
  2: ZnWords.

  assert ((word.wrap (2 ^ w) - 1) = Z.ones w) as ->.
      { rewrite Z.ones_equiv, Z.sub_1_r.
        ZnWords. }
  rewrite !Z.shiftr_div_pow2, Z.land_ones, Z.shiftl_mul_pow2 by ZnWords.
  cbv [word.wrap]. rewrite (Z.mod_small (b * 2^8)) by ZnWords.
  reflexivity.
Qed.

Lemma bytelist_extract_two num i b1 b2 w:
  let idx := i / 8  in
  let offset := i mod 8 in
  b1 = (nth_default Byte.x00 num (Z.to_nat idx)) ->
  b2 = (nth_default Byte.x00 num (S (Z.to_nat (idx)))) ->
  0 <= w <= 8 ->
  0 <= i < length num * 8 ->
  (Z.of_bytes num / 2 ^ i) mod 2 ^ w =
      ((byte.unsigned b1 + byte.unsigned  b2 * 2 ^ 8) / 2 ^ offset) mod 2 ^ w.
Proof.
  intros ? ? Hb1 Hb2. intros.

  assert (i = 8 * idx + offset) as Hi. {
    subst idx offset. apply Z_div_mod_eq_full.
  } rewrite Hi.

  pose proof (Z.mod_pos_bound i 8 ltac:(lia)).
  rewrite Z.pow_add_r, <- Z.div_div by lia.

  replace (Z.of_bytes num) with
      (Z.of_bytes ((firstn (Z.to_nat (idx)) num) ++ [b1] ++ [b2] ++ (skipn (S (S (Z.to_nat (idx)))) num))).
  2: { rewrite Hb1, Hb2, !nth_default_eq, app_assoc.
    rewrite firstn_nth by lia.
    destruct (Nat.eq_dec (S (Z.to_nat idx)) ((length num))) as [Hlength|?].
    { rewrite <- (le_combine_snoc_0 num).
      f_equal.
      rewrite List.skipn_all, nth_overflow by lia.
      rewrite Hlength, firstn_all, app_nil_r.
      reflexivity. }
    { f_equal. rewrite firstn_nth_skipn by lia. reflexivity. }}

  repeat rewrite Specs.le_combine_app.
  rewrite !length_cons, !length_nil, firstn_length_le, Z2Nat.id by lia.

  (* The lower part is zero because it's devided by something bigger. *)
  pose proof (le_combine_bound (firstn (Z.to_nat idx) num)) as Hb. revert Hb.
  rewrite !firstn_length_le, !Z2Nat.id by lia.
  rewrite !(Z.mul_comm idx 8). rewrite !Div.Z.div_add' by lia. intros.
  rewrite (Z.div_small _ (2 ^ (8 * idx))) by lia.

  (* The higher part is zero because it's too big for any remains afters the modulo. *)
  rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc.
  rewrite <- Z.pow_add_r by lia.
  replace (2 ^ (Z.of_nat 1 * 8 + Z.of_nat 1 * 8)) with (2^offset * 2^(16-offset)). 2: {
    rewrite <- Z.pow_add_r; f_equal; lia.
  }
  rewrite <- !Z.mul_assoc, !Z.add_assoc.
  rewrite Div.Z.div_add' by lia.
  assert ((16 - offset) > w) by lia.
  replace (2 ^ (16 - offset)) with (2^w * 2^(16-offset-w)). 2: {
    rewrite <- Z.pow_add_r; f_equal; lia.
  }
  rewrite <- Z.mul_assoc.
  rewrite Modulo.Z.mod_add'_full.

  rewrite !le_combine_1. do 2 f_equal. lia.
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
      case word.ltu_spec; intros; ZnWords. }
    repeat straightline.
    subst r t s v b.
    revert cond; case word.ltu_spec; intros; [|ZnWords].

    rewrite extract_limb_at_bit_zify by apply byte.unsigned_range.

    erewrite bytelist_extract_two; [| reflexivity | reflexivity | lia | ZnWords ].

    rewrite <-word.add_assoc, !word.word_sub_add_l_same_l.
    subst idx.
    repeat rewrite ?word.unsigned_sru, ?word.unsigned_add, ?word.unsigned_of_Z_nowrap by ZnWords.

    repeat f_equal; ZnWords.
  }
  subst r t s b.
  revert cond; case word.ltu_spec; intros cond ?; [ZnWords|].

  rewrite extract_limb_at_bit_zify by (try apply byte.unsigned_range; lia).

  erewrite bytelist_extract_two; [| reflexivity | reflexivity | lia | ZnWords].

  subst idx.
  repeat f_equal. { ZnWords. }

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
      (v = word.unsigned i /\
      total_bits_ = total_bits /\ (* input = inside loop *)
      m =* bytearray p_output output * bytearray p_input input * R /\
      8 * (length input - 1) < total_bits <= 8 * length input /\
      w * (length output - 1) < total_bits - i <= w * length output /\
      le_combine input < 2^total_bits /\
      total_bits + w <= (word.of_Z (-1) : word))
    (fun            T M P_OUTPUT P_INPUT total_bits I => (* postcondition *)
      exists OUTPUT,
      M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
      length output = length OUTPUT /\
      T = t /\
      p_input = P_INPUT /\
      total_bits = total_bits /\ (* inside loop = output *)
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
    { destruct (word.ltu_spec i_ total_bits);
      rewrite word.unsigned_of_Z_nowrap in * by ZnWords; try lia.
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
      rewrite word.unsigned_add_nowrap, word.unsigned_of_Z_nowrap by ZnWords.
      rewrite byte.unsigned_of_Z.
      cbv [byte.wrap].
      rewrite Z.mod_small, Z.pow_add_r, <-Z.div_div, Z.add_comm, <-Z.div_mod by ZnWords.
      reflexivity. }
    (* base case *)
    eexists output_.
    destruct (word.ltu_spec i_ total_bits);
    rewrite word.unsigned_of_Z_nowrap in * by ZnWords; try lia.
    ssplit; try ecancel_assumption; trivial;
    assert (length output_ = 0%nat) by ZnWords;
    rewrite length_zero_iff_nil in *;
    subst output_.
    { apply Forall_nil. }
    cbn [positional_bytes positional map fold_right].
    assert (2 ^ word.unsigned total_bits <= 2 ^ word.unsigned i_) by (apply Z.pow_le_mono_r; ZnWords).
    assert (le_combine input < 2 ^ word.unsigned i_) by ZnWords.
    apply Z.div_small.
    split; [apply le_combine_bound | trivial]. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
  subst i.
  match goal with H: _ = ?x |- context [?x] => rewrite <-H end.
  rewrite word.unsigned_of_Z_0, Z.pow_0_r, Z.div_1_r.
  reflexivity.
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
            rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_1;
            rewrite List.length_cons in *;
            try ZnWords. }
          { match goal with H: Forall _ _ |- _ => inversion H end; trivial. }
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
              match goal with H: context[positional_signed_bytes] |- _ => revert H end.
              unfold positional_signed_bytes, positional_bytes.
              rewrite Zeq_plus_swap.
              cbn [map positional fold_right]. intros ->.
              rewrite Z.mul_sub_distr_l.

              subst n.
              rewrite <- !Z.add_assoc, <- Z.sub_sub_distr, Z.add_sub_assoc, <- Z.sub_0_r.
              f_equal.
              2:{ rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_1, Z.mul_assoc, <- Z.pow_add_r by ZnWords.
                rewrite Zeq_minus; [trivial|].
                do 2 f_equal. lia. }

              cbv [x0 x v0 byte.signed].
              match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
              case word.ltu_spec; case Z.eqb_spec; [ZnWords | | | ZnWords];
              repeat rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_0, ?word.unsigned_sub_nowrap,
                ?word.unsigned_sub, ?word.unsigned_add_nowrap, ?byte.unsigned_of_Z, ?byte.swrap_wrap by ZnWords; intros.
              { rewrite word.byte_swrap_word_wrap by ZnWords.
                cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
              { cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
            }
            { constructor.
              { cbv [x0 x v0].
                match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
                case word.ltu_spec; case Z.eqb_spec;
                repeat rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_0, ?word.unsigned_sub_nowrap,
                ?word.unsigned_add_nowrap, ?word.unsigned_sub, ?word.unsigned_of_Z_nowrap by ZnWords;
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
    rewrite word.unsigned_of_Z_0, Z.add_0_l, Hx, Z.mul_1_r in *.
    epose proof positional_bounded (map byte.signed x0) (- 2 ^ w + 2) (2 ^ w) ltac:(apply Forall_map; assumption).
    rewrite length_map in *.
    progress fold (positional_signed_bytes (2 ^ w) x0) in *.
    assert (2*positional_signed_bytes (2 ^ w) x0 < -2^(w*n)) by lia.
    assert (positional (2 ^ w) (repeat (- 2 ^ w + 2) (length x0)) < -2 ^ (w * n)) by lia.
    match goal with H: _ = word.unsigned n |- _ => rewrite <-H in * end.
    rewrite Nat2Z.id in *.
    lia. }
  ZnWords.
Qed.
