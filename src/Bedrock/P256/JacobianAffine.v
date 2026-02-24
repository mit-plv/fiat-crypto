Require Import coqutil.Datatypes.List Coq.Lists.List.
Require Import Bedrock.P256.Specs.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Import Curves.Weierstrass.P256.

Import bedrock2.Syntax bedrock2.NotationsCustomEntry
LittleEndianList
Crypto.Util.ZUtil.Modulo Zdiv ZArith BinInt
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

Import Zbool. (*compat 8.20*)
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


Import Coq.micromega.Lia.
Import coqutil.Tactics.Tactics.


Definition fe_set_1 := func! (o) {
  o0 = $1; o1 = $0xffffffff00000000; o2 = -$1; o3 = $0xfffffffe;
  store(o, o0); store(o+$8, o1); store(o+$16, o2); store(o+$24, o3)
}.

Definition p256_point_add_affine_nz_nz_neq := func! (p_out, p_P, p_Q) ~> ok {
  stackalloc 32 as z1z1;
  stackalloc 32 as u2;
  stackalloc 32 as h;
  stackalloc 32 as s2;
  stackalloc 32 as r;
  stackalloc 32 as Hsqr;
  stackalloc 32 as Hcub;

  p256_coord_sqr(z1z1, p_P.+$32.+$32);
  p256_coord_mul(u2, p_Q, z1z1);
  p256_coord_sub(h, u2, p_P);
  p256_coord_mul(s2, p_P.+$32.+$32, z1z1);
  p256_coord_mul(p_out.+$32.+$32, h, p_P.+$32.+$32);
  p256_coord_mul(s2, s2, p_Q.+$32);
  p256_coord_sub(r, s2, p_P.+$32);
  p256_coord_sqr(Hsqr, h);
  p256_coord_sqr(p_out, r);
  p256_coord_mul(Hcub, Hsqr, h);
  p256_coord_mul(u2, p_P, Hsqr);

  unpack! different_x = p256_coord_nonzero(Hcub);
  unpack! different_y = p256_coord_nonzero(p_out);
  unpack! ok = br_value_barrier(different_x | different_y);

  p256_coord_sub(p_out, p_out, Hcub);
  p256_coord_sub(p_out, p_out, u2);
  p256_coord_sub(p_out, p_out, u2);
  p256_coord_sub(h, u2, p_out);
  p256_coord_mul(s2, Hcub, p_P.+$32);
  p256_coord_mul(h, h, r);
  p256_coord_sub(p_out.+$32, h, s2)
}.

Local Ltac length_tac_rewrites :=
  repeat rewrite
    ?length_coord, ?length_point,
    ?app_length, ?firstn_length, ?skipn_length, ?length_le_split, ?length_nil,
    ?Nat.min_l in *
    by (trivial; lia).
Local Ltac length_tac := repeat straightline_cleanup;length_tac_rewrites; trivial; lia.

Local Ltac clear_nongoal_sephyps :=
  repeat match reverse goal with
  | H : (_ * _)%sep ?m |- _ =>
      tryif match goal with |- context[m] => idtac end
      then try rename H into Hm
      else clear H; try clear m
  | m : Interface.map.rep |- _ => clear m
  end.

Local Ltac clear_nonsymex_sephyps :=
  tryif
  match goal with
  | |- Semantics.call _ _ _ _ _ _ => idtac
  | |- cmd _ _ _ _ _ _ => idtac
  | |- expr _ _ _ _ => idtac
  | |- dexpr _ _ _ _ => idtac
  | |- load _ _ _ _ => idtac
  | |- store _ _ _ _ _ => idtac
  | |- Memory.load _ _ _ = _ => idtac
  end
  then clear_nongoal_sephyps else idtac.

Local Ltac symex_call := (straightline_call; ssplit; [ solve [
      repeat match goal with
      | |- True => exact I
      | |- exists _, _ => letexists
      | |- _ _ => ecancel_assumption
      | |- _ => length_tac
      end
    ] ..  | repeat straightline_cleanup; straightline; repeat straightline_cleanup; clear_nonsymex_sephyps; repeat straightline]).

Lemma p256_point_add_affine_nz_nz_neq_ok : program_logic_goal_for_function! p256_point_add_affine_nz_nz_neq.
Proof.
  cbv [spec_of_p256_point_add_affine_nz_nz_neq of_affine].
  straightline; repeat straightline_cleanup.
  destruct P as (((x1 & y1) & z1) & p1), (Jacobian.of_affine Q) as (((x2 & y2) & z2) & p2) eqn:HeqQ;
    cbv [proj1_sig proj2_sig fst snd point.to_bytes] in * |-.
  match goal with H : _ m |- context[m] => rename H into Hm end.

  rewrite <-(firstn_skipn 32 out) in Hm.
  rewrite <-(firstn_skipn 32 (skipn _ out)) in Hm.
  progress repeat seprewrite_in_by Array.sep_eq_of_list_word_at_app Hm length_tac.

  repeat straightline. clear_nonsymex_sephyps.
  repeat seprewrite_in_by Array.array1_iff_eq_of_list_word_at Hm ltac:(Lia.lia).
  progress change (Z.of_nat 32) with 32 in *.

  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  symex_call.
  clear_nongoal_sephyps.

  (* stackdealloc *)
  progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm ltac:(rewrite ?length_coord; Lia.lia).
  progress repeat match type of Hm with context [Array.array ptsto _ _ (coord.to_bytes ?x)] =>
    unique pose proof (length_coord x) end.
  repeat straightline. clear_nongoal_sephyps.
  progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) Hm ltac:(rewrite ?length_coord; Lia.lia).
  length_tac_rewrites.

  (* postcondition *)

  cbv [proj1_sig proj2_sig fst snd point.to_bytes ].
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_Q)(p_Q.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_Q)(p_Q.+32.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_P)(p_P.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_P)(p_P.+32.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_out)(p_out.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  seprewrite_in_by (Array.list_word_at_app_of_adjacent_eq(p_out)(p_out.+32.+32)) Hm ltac:(length_tac_rewrites; listZnWords).
  eexists; ssplit.
  { use_sep_assumption. cancel. repeat ecancel_step. Morphisms.f_equiv. }
  { length_tac. }
  clear Hm.

  intros.
  cbv [affine_point.iszero] in *.
  destruct Q as ([[]|[]]&?) in HeqQ, H59; [|contradiction]; apply (f_equal (@proj1_sig _ _)) in HeqQ;
      cbv [of_affine Jacobian.of_affine Jacobian.of_affine_impl fst snd Jacobian.eq proj1_sig] in HeqQ; Prod.inversion_prod; subst.

  case (Properties.word.eqb_spec x3 $0); subst x3; rewrite word.lor_0_iff; [right|left]; split; trivial.
  { subst x x0.
    rewrite !word.broadcast_0_iff in *.
    rewrite !Bool.negb_false_iff, !F.eqb_eq in *.
    cbv [of_affine Jacobian.of_affine fst snd Jacobian.eq Jacobian.iszero proj1_sig] in *.
    case H60 as [Hx Hy].
    case Decidable.dec; intros; try contradiction; split; [apply Hierarchy.one_neq_zero|].
    rewrite Hierarchy.commutative in Hx.
    rewrite <-!F.pow_succ_r in Hx, Hy; simpl N.succ in Hx, Hy.
    rewrite F.pow_0_iff, Ring.sub_zero_iff in Hx, Hy by (lia||exact _).
    rewrite ?F.pow_3_r, ?F.pow_2_r in Hx.
    rewrite ?F.pow_3_r, ?F.pow_2_r in Hy.
    split; Field.fsatz. }
  { unshelve eexists ?[pfPneqQ].
    { intros HX; cbv [Jacobian.eq Jacobian.iszero of_affine Jacobian.of_affine Jacobian.of_affine_impl proj1_sig fst snd] in H59, H60, HX.
      destruct Decidable.dec in HX; try contradiction; case HX as (Hz&Hx&Hy).
      apply H60. subst x x0.
      rewrite !word.broadcast_0_iff in *.
      rewrite !Bool.negb_false_iff, !F.eqb_eq.
      rewrite ?F.pow_3_r, ?F.pow_2_r, ?Hx, ?Hy, ?(proj2 (Ring.sub_zero_iff _ _)); ssplit; Field.fsatz. }
    cbv [Jacobian.add_inequal_nz_nz Jacobian.add_inequal_impl of_affine Jacobian.of_affine Jacobian.of_affine_impl proj1_sig fst snd point.to_bytes]; cbn [fst snd proj1_sig].
    rewrite ?app_assoc, ?F.pow_3_r, ?F.pow_2_r; repeat (ring || f_equal). }
Qed.


Definition p256_point_add_affinenz_conditional_vartime_if_doubling := func! (p_out, p_P, p_Q, c) {
  unpack! zeroP = p256_point_iszero(p_P);
  unpack! nzQ = br_broadcast_nonzero(c);
  zeroQ = ~nzQ;
  stackalloc (3*32) as p_tmp;
  unpack! ok = p256_point_add_affine_nz_nz_neq(p_tmp, p_P, p_Q);
  unpack! ok = br_declassify(zeroP | zeroQ | ok);
  stackalloc (3*32) as p_buf;
  br_memset(p_buf, $0, $3*$32);
  br_memcxor(p_buf, p_tmp,  $3*$32,     ~zeroP & ~zeroQ);
  br_memcxor(p_buf, p_P,    $3*$32,     ~zeroP &  zeroQ);
  br_memcxor(p_buf, p_Q,    $3*$32,      zeroP & ~zeroQ);
  if !ok { p256_point_double(p_buf, p_P) };
  br_memcpy(p_out, p_buf, $(3*32))
}.

From bedrock2Examples Require Import memcpy.

Lemma p256_point_add_affinenz_conditional_vartime_if_doubling_ok : program_logic_goal_for_function! p256_point_add_affinenz_conditional_vartime_if_doubling.
Proof.
  cbv [spec_of_p256_point_add_affinenz_conditional_vartime_if_doubling].
  repeat straightline.
  match goal with H : _ m |- context[m] => rename H into Hm end.

  straightline_call; repeat straightline. (*iszero*)
  { letexists. ecancel_assumption. }
  straightline_call; repeat straightline. (*broadcast*)
  (* stackalloc *)
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) Hm ltac:(lia).
  straightline_call; ssplit. (*add*)
  { ecancel_assumption. }
  { rewrite length_point; lia. }
  repeat straightline.
  straightline_call; repeat straightline (* br_declassify *).
  (* stackalloc *)
  clear_nonsymex_sephyps.
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) Hm ltac:(lia).
  straightline_call; ssplit. (* memset *)
  { ecancel_assumption. }
  { ZnWords.ZnWords. }
  repeat straightline.
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite H17, length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }
  clear_nonsymex_sephyps.
  progress rewrite ?word.unsigned_mul_nowrap, ?word.unsigned_of_Z_nowrap in * by ZnWords.ZnWords.

assert (word__and_broadcast : forall a b, word.and (word.broadcast a) (word.broadcast b) = word.broadcast (andb a b)). {
  clear; intros a b; case a, b; cbv [word.broadcast]; trivial.
}

  cbv [affine_point.iszero] in *; subst zeroQ.
  subst x x0 x3.
  cbn [Semantics.interp_op1] in *; rewrite ?word.not_broadcast, ?word__and_broadcast, ?Bool.negb_involutive in *.

  letexists; ssplit; repeat straightline; subst v (* if ok *).
  { straightline_call; repeat straightline; ssplit (* memcpy *).
    { ecancel_assumption. }
    { rewrite H10, length_point; trivial. }
    { trivial. }
    { clear; ZnWords.ZnWords. }
    clear_nongoal_sephyps.
    (* stackdealloc *)
    progress repeat seprewrite_in_by (symmetry! (Array.array1_iff_eq_of_list_word_at a)) Hm ltac:(length_tac_rewrites; listZnWords).
    progress repeat seprewrite_in_by (symmetry! (Array.array1_iff_eq_of_list_word_at a0)) Hm ltac:(length_tac_rewrites; listZnWords).
    assert (Datatypes.length x6 = 96%nat) by (length_tac_rewrites; listZnWords).
    assert (Datatypes.length x2 = 96%nat) by (length_tac_rewrites; listZnWords).
    repeat straightline; clear_nongoal_sephyps.

    rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff in H16 by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in H16.
    destruct (iszero P) eqn:HP in *; (destruct (word.eqb_spec c2 (word.of_Z 0)) as [|HQ] in *; [subst c2|]);
      repeat (cbn [Z.eqb negb andb] in *; rewrite ?Z.eqb_refl in *; rewrite ?(proj2 (Z.eqb_neq _ _)) in * by ZnWords.ZnWords;
        match goal with
           | H : word.broadcast false = word.of_Z 0 -> _ |- _ => specialize (H eq_refl)
           | H : word.broadcast true = word.of_Z (-1) -> _ |- _ => specialize (H eq_refl)
           end); subst; rewrite ?Byte.map_xor_0_l in * by (rewrite ?length_point; ZnWords.ZnWords).
    { (* 0 + 0 *)
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      eexists (exist _ (0,0,0)%F I); split.
      { use_sep_assumption; cancel. reflexivity. }
      rewrite Jacobian.eq_iff, HP; reflexivity. }
    { (* 0 + Q *)
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      eexists; split. { ecancel_assumption. }
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HP.
      symmetry.
      eapply Hierarchy.left_identity. }
    { (* P + 0 *)
      eexists; split. { ecancel_assumption. } reflexivity. }
    { (* nz + nz' *)
      (* Decidable.dec_iff? *)
      cbv [iszero] in HP, HQ; case Decidable.dec in HP; try congruence.
      destruct (H18 ltac:(trivial) ltac:(intros HX; specialize (H11 HX); congruence)) as [ [_ (?&HE)] |]; [|intuition fail].
      repeat straightline_cleanup.
      eexists; split; [ecancel_assumption|].
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, Jacobian.to_affine_add_inequal_nz_nz; trivial; [reflexivity|].
      rewrite Jacobian.iszero_iff, Jacobian.to_affine_of_affine.
      destruct Q as ([(?&?)|[]]&?); intuition idtac.
    } }
  { (* if !ok *)
    rewrite <-word.unsigned_of_Z_0, word.unsigned_inj_iff in * by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in *.
    DestructHead.destruct_head' @and; subst.
    rewrite ?word.not_broadcast, ?word__and_broadcast, ?Bool.negb_involutive, ?word.broadcast_0_iff, ?Z.eqb_neq, ?word.unsigned_of_Z_0 in *.

    straightline_call; repeat straightline.
    { split. { ecancel_assumption. } { length_tac. } }
    straightline_call; repeat straightline; ssplit (* memcpy *).
    { ecancel_assumption. }
    { rewrite H10, length_point; trivial. }
    { trivial. }
    { clear; ZnWords.ZnWords. }
    repeat straightline.
    (* stackdealloc *)
    clear_nongoal_sephyps.
    progress repeat seprewrite_in_by (symmetry! (Array.array1_iff_eq_of_list_word_at a)) Hm ltac:(length_tac_rewrites; listZnWords).
    progress repeat seprewrite_in_by (symmetry! (Array.array1_iff_eq_of_list_word_at a0)) Hm ltac:(length_tac_rewrites; listZnWords).
    assert (Datatypes.length x6 = 96%nat) by (length_tac_rewrites; listZnWords).
    assert (Datatypes.length ((to_bytes (Jacobian.double_minus_3 eq_refl P))) = 96%nat) by (length_tac_rewrites; listZnWords).
    repeat straightline; clear_nongoal_sephyps.

    eexists; ssplit. { ecancel_assumption. }
    destruct (word.eqb_spec c2 (word.of_Z 0)); [subst; rewrite ?word.unsigned_of_Z_0 in *; contradiction|].
    rewrite <-Jacobian.double_minus_3_eq_double.
    rewrite Jacobian.eq_iff, Jacobian.to_affine_double, Jacobian.to_affine_add; Morphisms.f_equiv.
    enough (Jacobian.eq P Q) as -> by reflexivity.

    cbv [iszero] in *; case Decidable.dec in *; try congruence.
    destruct (H18 ltac:(trivial) ltac:(intros HX; specialize (H11 HX); congruence)) as [ [? (?&HE)] |]; [congruence|intuition fail]. }
Qed.


Definition sc_halve := func!(y, x) {
  unpack! m = br_value_barrier(-(load(x)&$1)); (* is x odd? *)
  mh0 = $0x79dce5617e3192a8; mh1 = $0xde737d56d38bcf42; mh2 = $0x7fffffffffffffff; mh3 = $0x7fffffff80000000; (* minus one half modulo l *)
  stackalloc 32 as mmh; (* maybe minus half *)
  store(mmh, m&mh0); store(mmh+$8, m&mh1); store(mmh+$16, m&mh2); store(mmh+$24, m&mh3);
  y0 = load(y); y1 = load(y+$8); y2 = load(y+$16); y3 = load(y+$24);
  unpack! y0 = shrd_64(y0, y1, $1);
  unpack! y1 = shrd_64(y1, y2, $1);
  unpack! y2 = shrd_64(y2, y3, $1);
  y3 = y3 >> $1;
  store(y, y0); store(y+$8, y1); store(y+$16, y2); store(y+$24, y3);
  sc_sub(y, y, mmh)
}.

Definition sc_sub := func!(out, x, y) {
  unpack! x1, x2 = sbb64($0, load(x), load(y));
  unpack! x3, x4 = sbb64(x2, load(x+$8), load(y+$8));
  unpack! x5, x6 = sbb64(x4, load(x+$16), load(y+$16));
  unpack! x7, x8 = sbb64(x6, load(x+$24), load(y+$24));
  x9 = -x8;
  unpack! x10, x11 = adc64($0, x1, x9 & $0xf3b9cac2fc632551);
  unpack! x12, x13 = adc64(x11, x3, x9 & $0xbce6faada7179e84);
  unpack! x14, x15 = adc64(x13, x5, x9);
  unpack! x16, x17 = adc64(x15, x7, x9 << $32);
  x17 = x17+$0;
  store(out, x10);
  store(out+$8, x12);
  store(out+$16, x14);
  store(out+$24, x16)
}.
