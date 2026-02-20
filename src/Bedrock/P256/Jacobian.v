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

Definition p256_point_iszero := func! (p_P) ~> z {
  unpack! nz = p256_coord_nonzero(p_P.+$32.+$32);
  z = ~nz
}.


Lemma p256_point_iszero_ok : program_logic_goal_for_function! p256_point_iszero.
Proof.
  cbv [spec_of_fiat_p256_point_iszero].
  repeat straightline.

  rename H0 into Hm.
  cbv [point.to_bytes] in *.
  repeat seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm ltac:(rewrite ?app_length, ?length_coord; trivial; try lia).
  simpl Z.of_nat in *.

  straightline_call; [eexists; ecancel_assumption|]; repeat straightline.

  subst z x0.
  setoid_rewrite word.not_broadcast; rewrite Bool.negb_involutive; trivial.
Qed.

Definition p256_coord_halve := func!(y, x) {
  stackalloc 32 as mmh;
  unpack! m = br_broadcast_odd(load(x));
  u256_set_p256_minushalf_conditional(mmh, m);
  u256_shr(y, x, $1);
  p256_coord_sub(y, y, mmh)
}.


Local Ltac length_tac :=
  repeat rewrite
    ?length_coord, ?length_point,
    ?app_length, ?firstn_length, ?skipn_length, ?length_le_split, ?length_nil,
    ?Nat.min_l
    by (trivial; lia); trivial; lia.

Lemma p256_coord_halve_ok :
  let '_ := spec_of_p256_coord_sub_nonmont in
  program_logic_goal_for_function! p256_coord_halve.
Proof.
  cbv [spec_of_p256_coord_halve].
  straightline; repeat straightline_cleanup.

  pose proof (conj H3 H4) as Hm; clear H4 H3; pattern m in Hm.
  progress change (?P m) with (id P m) in Hm.
  repeat straightline.
  eapply sep_and_l_fwd in Hm; case Hm as [Hm Hm'].

  letexists; split.
  { cbn. repeat straightline. eexists; split; [|reflexivity].
    cbv [coord.to_bytes] in Hm.
    rewrite <-(firstn_skipn 8 (le_split _ _)), List.firstn_le_split, skipn_le_split, ?Z.shiftr_shiftr in Hm by lia.
    seprewrite_in_by (@Array.sep_eq_of_list_word_at_app) Hm ltac:(rewrite ?length_le_split; trivial; lia).
    seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) Hm ltac:(rewrite ?length_le_split; lia).
    seprewrite_in_by @Scalars.scalar_of_bytes Hm ltac:(rewrite ?length_le_split; lia).
    rewrite le_combine_split in Hm.
    repeat straightline. }

  straightline_call; [eexists; ecancel_assumption|]; repeat straightline.

  seprewrite_in_by Array.array1_iff_eq_of_list_word_at Hm0 ltac:(Lia.lia).

  straightline_call; ssplit; [ ecancel_assumption | trivial | exact eq_refl | ].
  repeat straightline.

  eapply sep_and_r_fwd in H10; case H10 as [Hm3 Hm3'].

  straightline_call; ssplit.
  { eexists. cbv [coord.to_bytes] in *. ecancel_assumption. }
  { cbv [coord.to_bytes] in *. ecancel_assumption. }
  { trivial. }
  { eapply F.to_Z_range, eq_refl. }
  { etransitivity; try eapply F.to_Z_range; eapply eq_refl. }
  { ZnWords.ZnWords. }

  repeat straightline.
  rewrite ?Z.pow_1_r in *.

  set (Z.odd _) as b in *.

  eapply WeakestPreconditionProperties.Proper_call; cycle -1;
  [ eapply H2 | .. | intros ? ? ? ?]; ssplit.
  { eexists.
    use_sep_assumption; cancel.
    cancel_seps_at_indices 0%nat 0%nat; [|cancel].

    instantiate (1:=F.of_Z _ (F.to_Z (x*coord.R)%F / 2)).
    rewrite F.to_Z_of_Z, Z.mod_small; trivial.
    specialize (F.to_Z_range (x*coord.R) eq_refl); clear; PreOmega.Z.to_euclidean_division_equations; lia. }
  { eexists. use_sep_assumption. cancel.
    cancel_seps_at_indices 1%nat 0%nat. { exact eq_refl. }
    cancel. }
  { ecancel_assumption. }
  { length_tac. }

  repeat straightline.

  (* stackdealloc *)
  progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H12 length_tac.
  progress repeat match type of H12 with context [Array.array ptsto _ _ (le_split 32 ?x)] =>
    unique pose proof (length_le_split 32 x) end.
  progress repeat straightline.
  progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H12 length_tac.

  (* postcondition *)
  use_sep_assumption.
  cancel.
  cancel_seps_at_indices 0%nat 0%nat; [|cancel].
  f_equal.
  f_equal.
  subst x2 b.
  cbv [coord.to_bytes F.div].
  progress Morphisms.f_equiv; [].
  progress Morphisms.f_equiv; [].
  transitivity (x * coord.R * F.inv (1 + 1))%F; [|ring].
  set (x*coord.R)%F as xR; set (F.inv (1 + 1)) as i2.

  (* NOTE: back-and-forth rewrite between Z.modulo and Z.odd *)
  rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Zmod_mod, Zdiv.Zodd_mod, Z.mod_mod_divide by (apply Divide.Z.divide_pow_le with (n:=1); lia).
  symmetry; rewrite <-(F.of_Z_to_Z xR) at 1; rewrite (Z.div_mod xR 2) at 1 by lia.
  rewrite Div.Z.div_sub_mod_exact, Zdiv.Zmod_odd by lia.

  assert (F.of_Z p256 2 * i2 = F.one)%F as Hi2 by (cbv [i2]; clear; Decidable.vm_decide).
  case Z.odd; cbn [Z.eqb Pos.eqb Zeq_bool Z.compare Pos.compare Pos.compare_cont]; rewrite ?F.of_Z_add, ?F.of_Z_mul; fold (@F.zero p256); fold (@F.one p256); try ring [Hi2].
Qed.

Definition p256_point_add_nz_nz_neq := func! (p_out, p_P, p_Q) ~> ok {
  stackalloc 32 as z1z1;
  stackalloc 32 as z2z2;
  stackalloc 32 as u1;
  stackalloc 32 as u2;
  stackalloc 32 as h;
  stackalloc 32 as s1;
  stackalloc 32 as s2;
  stackalloc 32 as r;
  stackalloc 32 as Hsqr;
  stackalloc 32 as Hcub;
  p256_coord_sqr(z1z1, p_P.+$32.+$32);
  p256_coord_mul(u2, p_Q, z1z1);
  p256_coord_sqr(z2z2, p_Q.+$32.+$32);
  p256_coord_mul(u1, p_P, z2z2);
  p256_coord_sub(h, u2, u1);
  p256_coord_mul(s2, p_P.+$32.+$32, z1z1);
  p256_coord_mul(p_out.+$32.+$32, h, p_P.+$32.+$32);
  p256_coord_mul(p_out.+$32.+$32, p_out.+$32.+$32, p_Q.+$32.+$32);
  p256_coord_mul(s2, s2, p_Q.+$32);
  p256_coord_mul(s1, p_Q.+$32.+$32, z2z2);
  p256_coord_mul(s1, s1, p_P.+$32);
  p256_coord_sub(r, s2, s1);
  p256_coord_sqr(Hsqr, h);
  p256_coord_sqr(p_out, r);
  p256_coord_mul(Hcub, Hsqr, h);
  p256_coord_mul(u2, u1, Hsqr);

  unpack! different_x = p256_coord_nonzero(Hcub);
  unpack! different_y = p256_coord_nonzero(p_out);
  unpack! ok = br_value_barrier(different_x | different_y);

  p256_coord_sub(p_out, p_out, Hcub);
  p256_coord_sub(p_out, p_out, u2);
  p256_coord_sub(p_out, p_out, u2);
  p256_coord_sub(h, u2, p_out);
  p256_coord_mul(s2, Hcub, s1);
  p256_coord_mul(h, h, r);
  p256_coord_sub(p_out.+$32, h, s2)
}.

Lemma p256_point_add_nz_nz_neq_ok : program_logic_goal_for_function! p256_point_add_nz_nz_neq.
Proof.
  cbv [spec_of_p256_point_add_nz_nz_neq].
  straightline; repeat straightline_cleanup.
  destruct P as (((x1 & y1) & z1) & p1),  Q as (((x2 & y2) & z2) & p2);
    cbv [proj1_sig proj2_sig fst snd point.to_bytes] in * |-.
  repeat seprewrite_in_by Array.sep_eq_of_list_word_at_app H25
     ltac:(rewrite ?app_length, ?length_coord; trivial; try Lia.lia).

  repeat straightline.
  repeat seprewrite_in_by Array.array1_iff_eq_of_list_word_at H25 ltac:(Lia.lia).

  rewrite <-(firstn_skipn 32 out) in H25.
  rewrite <-(firstn_skipn 32 (SeparationLogic.skipn _ out)) in H25. (* WHY does this need to be SeparationLogic. ? *)
  rewrite ?skipn_skipn in H25.
rewrite ?app_length, ?length_coord in *.
  repeat seprewrite_in_by Array.sep_eq_of_list_word_at_app H25 (* WHY does first rewrite take 0.1s? *)
    ltac:(repeat rewrite ?app_length, ?firstn_length, ?skipn_length, ?Nat.min_l; try Lia.lia; trivial).

  progress change (Z.of_nat 32) with 32 in *.

  (* WHY does skipn get unfolded below without this?
   *) repeat (set (List.skipn  _ _) in H25 || set (List.firstn  _ _) in H25).

  repeat (straightline_call; ssplit;
    [ solve [repeat match goal with
      | |- True => exact I
      | |- exists _, _ => letexists
      | |- _ => subst l10 l11 l12; progress rewrite ?length_coord, ?firstn_length, ?skipn_length; Lia.lia
      | _ => ecancel_assumption
      end] ..
    | repeat straightline ]).

  (* stackdealloc *)
  progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H93 ltac:(rewrite ?length_coord; Lia.lia).
  progress repeat match type of H93 with context [Array.array ptsto _ _ (coord.to_bytes ?x)] =>
    unique pose proof (length_coord x) end.
  repeat straightline.
  progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H93 ltac:(rewrite ?length_coord; Lia.lia).

  (* postcondition *)
  eexists; ssplit.
  {
    cbv [proj1_sig proj2_sig fst snd point.to_bytes].
    repeat seprewrite_in_by Array.list_word_at_app_of_adjacent_eq H93 ltac:(rewrite ?length_coord; listZnWords).
    (* other direction: repeat seprewrite_by Array.sep_eq_of_list_word_at_app ltac:(rewrite ?length_coord, ?app_length; trivial; try Lia.lia). *)
    ecancel_assumption. }
  { rewrite ?app_length, ?length_point, ?length_coord; trivial. }

  case (Properties.word.eqb_spec x3 $0); subst x3; rewrite word.lor_0_iff; [right|left]; split; trivial.
  { case H121 as [Hx Hy].
    subst x x0.
    rewrite !word.broadcast_0_iff in *.
    rewrite !Bool.negb_false_iff, !F.eqb_eq in *.
    cbv [fst snd Jacobian.eq Jacobian.iszero proj1_sig] in *.
    case Decidable.dec; intros; try contradiction; split; trivial.
    rewrite Hierarchy.commutative in Hx.
    rewrite <-!F.pow_succ_r in Hx, Hy; simpl N.succ in Hx, Hy.
    rewrite F.pow_0_iff, Ring.sub_zero_iff in Hx, Hy by (lia||exact _).
    rewrite ?F.pow_3_r, ?F.pow_2_r in Hx.
    rewrite ?F.pow_3_r, ?F.pow_2_r in Hy.
    split; Field.fsatz. }
  { unshelve eexists ?[pfPneqQ].
    { intros HX; cbv [Jacobian.eq Jacobian.iszero proj1_sig fst snd] in H122, H123, HX.
      destruct Decidable.dec in HX; try contradiction; case HX as (Hz&Hx&Hy).
      apply H121. subst x x0.
      rewrite !word.broadcast_0_iff in *.
      rewrite !Bool.negb_false_iff, !F.eqb_eq.
      rewrite ?F.pow_3_r, ?F.pow_2_r, ?Hx, ?Hy, ?(proj2 (Ring.sub_zero_iff _ _)); ssplit; Field.fsatz. }
    cbv [Jacobian.add_inequal_nz_nz point.to_bytes]; cbn [fst snd proj1_sig].
    rewrite ?F.pow_3_r, ?F.pow_2_r.
    trivial. }
Qed.

Import coqutil.Tactics.Tactics.

Definition p256_point_add_vartime_if_doubling := func!(p_out, p_P, p_Q) {
  unpack! zeroP = p256_point_iszero(p_P);
  unpack! zeroQ = p256_point_iszero(p_Q);
  stackalloc (3*32) as p_tmp;
  unpack! ok = p256_point_add_nz_nz_neq(p_tmp, p_P, p_Q);
  unpack! ok = br_declassify(zeroP | zeroQ | ok);
  stackalloc (3*32) as p_sel;
  br_memset(p_sel, $0, $(3*32));
  br_memcxor(p_sel, p_tmp, $(3*32), ~zeroP & ~zeroQ);
  br_memcxor(p_sel, p_P,   $(3*32), ~zeroP &  zeroQ);
  br_memcxor(p_sel, p_Q,   $(3*32),  zeroP & ~zeroQ);
  if !ok { p256_point_double(p_sel, p_P) };
  br_memcpy(p_out, p_sel, $(3*32))
}.

Import memcpy.
Lemma p256_point_add_vartime_if_doubling_ok : program_logic_goal_for_function! p256_point_add_vartime_if_doubling.
Proof.
  cbv [spec_of_p256_point_add_vartime_if_doubling].
  repeat straightline.
  straightline_call; repeat straightline. (*iszero*)
  { letexists. ecancel_assumption. }
  straightline_call; repeat straightline. (*iszero*)
  { letexists. ecancel_assumption. }
  (* stackalloc *)
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H9 ltac:(lia).
  straightline_call; ssplit. (*add*)
  { ecancel_assumption. }
  { rewrite length_point; lia. }
  repeat straightline.
  straightline_call; repeat straightline (* br_declassify *).
  (* stackalloc *)
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H17 ltac:(lia).
  straightline_call; ssplit. (* memset *)
  { ecancel_assumption. }
  { ZnWords.ZnWords. }
  repeat straightline.
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite H18, length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }

  rewrite ?word.and_xorm1_l, ?word.and_xorm1_r in *.

  subst x x0 x3.
  letexists; ssplit; repeat straightline; subst v (* if ok *).
  { straightline_call; repeat straightline; ssplit (* memcpy *).
    { ecancel_assumption. }
    { rewrite H10, length_point; trivial. }
    { trivial. }
    { clear; ZnWords.ZnWords. }
    repeat straightline.
    (* stackdealloc *)
    progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H42 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).
    progress repeat match type of H42 with context [Array.array ptsto _ _ (point.to_bytes ?x)] =>
    unique pose proof (length_point x) end.
    assert (Datatypes.length x6 = 96%nat) by ZnWords.ZnWords.
    repeat straightline.
    progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H42 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).

    rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff in H27 by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in H27.
    destruct (iszero P) eqn:HP, (iszero Q) eqn:HQ in *; try intuition discriminate;
      repeat match goal with
             | H : _ = _ -> _ |- _ => specialize (H eq_refl)
             | H : ?x = ?y -> _ |- _ => assert (x = y -> False) as _ by inversion 1; clear H
             end;
      subst x4; subst x5; subst x6;
      rewrite ?Byte.map_xor_0_l in * by (rewrite ?length_point; ZnWords.ZnWords).
    { (* 0 + 0 *)
      eexists (exist _ (0,0,0)%F I); split.
      { use_sep_assumption; cancel. reflexivity. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      apply Decidable.dec_bool, Jacobian.iszero_iff in HQ.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HP, HQ.
      exact I. }
    { (* 0 + Q *)
      eexists; split. { ecancel_assumption. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HP.
Import Curves.Weierstrass.AffineProofs.
      symmetry.
      eapply Hierarchy.left_identity. }
    { (* P + 0 *)
      eexists; split. { ecancel_assumption. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HQ.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HQ.
      symmetry.
      unshelve eapply Hierarchy.right_identity. }
    { (* nz + nz' *)
      rewrite <-Bool.not_true_iff_false in HP, HQ.
      (* Decidable.dec_iff? *)
      cbv [iszero] in HP, HQ; case Decidable.dec in HP; case Decidable.dec in HQ; try congruence.
      destruct (H19 ltac:(trivial) ltac:(trivial)) as [HE|]; [|intuition fail].
      case HE as [_ (?&HE)].
      repeat straightline_cleanup.
      eexists; split; [ecancel_assumption|].
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, Jacobian.to_affine_add_inequal_nz_nz; trivial; reflexivity. } }
  { (* if !ok *)
    rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff in H27 by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in H27.
    case H27 as ((HP&HQ)&->); rewrite ?HP, ?HQ in *;
      repeat match goal with
             | H : _ = _ -> _ |- _ => specialize (H eq_refl)
             | H : ?x = ?y -> _ |- _ => assert (x = y -> False) as _ by inversion 1; clear H
             end;
      subst x4; subst x5; subst x6;
      rewrite ?Byte.map_xor_0_l in * by (rewrite ?length_point; ZnWords.ZnWords).
    rewrite <-Bool.not_true_iff_false in HP, HQ.
    cbv [iszero] in HP, HQ; case Decidable.dec in HP; case Decidable.dec in HQ; try congruence.
    case (H19 ltac:(trivial) ltac:(trivial)) as [[HE ?]|[? HE]]; [case (HE eq_refl)|].

    straightline_call; repeat straightline.
    { split. { ecancel_assumption. }
      rewrite ?map_length, ?combine_length, ?repeat_length.
      rewrite H18, length_point. clear; ZnWords.ZnWords. }

    straightline_call; repeat straightline; ssplit (* memcpy *).
    { ecancel_assumption. }
    { rewrite H10, length_point; trivial. }
    { trivial. }
    { clear; ZnWords.ZnWords. }
    repeat straightline.
    (* stackdealloc *)
    progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H31 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).
    progress repeat match type of H31 with context [Array.array ptsto _ _ (point.to_bytes ?x)] =>
    unique pose proof (length_point x) end.
    repeat straightline.
    progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H31 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).

    eexists; ssplit. { ecancel_assumption. }
    rewrite <-HE, <-Jacobian.double_minus_3_eq_double.
    rewrite Jacobian.eq_iff, Jacobian.to_affine_double, Jacobian.to_affine_add.
    reflexivity. }
Qed.

Definition p256_point_double := func!(out, in1) {
  stackalloc 32 as D;
  stackalloc 32 as A;
  stackalloc 32 as tmp;
  p256_coord_add(D, in1.+$32, in1.+$32);
  p256_coord_sqr(tmp, in1.+$32.+$32);
  p256_coord_sqr(D, D);
  p256_coord_mul(out.+$32.+$32, in1.+$32.+$32, in1.+$32);
  p256_coord_add(out.+$32.+$32, out.+$32.+$32, out.+$32.+$32);
  p256_coord_add(A, in1, tmp);
  p256_coord_sub(tmp, in1, tmp);
  { stackalloc 32 as t2; p256_coord_add(t2, tmp, tmp); p256_coord_add(tmp, t2, tmp) };
  p256_coord_sqr(out.+$32, D);
  p256_coord_mul(A, A, tmp);
  p256_coord_mul(D, D, in1);
  p256_coord_sqr(out, A);
  p256_coord_add(tmp, D, D);
  p256_coord_sub(out, out, tmp);
  p256_coord_sub(D, D, out);
  p256_coord_mul(D, D, A);
  p256_coord_halve(out.+$32, out.+$32);
  p256_coord_sub(out.+$32, D, out.+$32)
}.

Lemma p256_point_double_ok : program_logic_goal_for_function! p256_point_double.
Proof.
  cbv [spec_of_p256_point_double].
  straightline; repeat straightline_cleanup.
  destruct P as (((x1 & y1) & z1) & p1);
    cbv [proj1_sig proj2_sig fst snd point.to_bytes] in * |-.
  progress repeat seprewrite_in_by Array.sep_eq_of_list_word_at_app H18
     ltac:(rewrite ?app_length, ?length_coord; trivial; try Lia.lia).

  repeat straightline.
  repeat seprewrite_in_by Array.array1_iff_eq_of_list_word_at H18 ltac:(Lia.lia).

  rewrite <-(firstn_skipn 32 out) in H18.
  rewrite <-(firstn_skipn 32 (skipn _ out)) in H18.
  rewrite !skipn_skipn in H18.
rewrite ?app_length, ?length_coord in *.
  progress repeat seprewrite_in_by Array.sep_eq_of_list_word_at_app H18
    ltac:(repeat rewrite ?app_length, ?firstn_length, ?skipn_length, ?Nat.min_l; try Lia.lia; trivial).

  progress change (Z.of_nat 32) with 32 in *.

  progress repeat (set (List.skipn  _ _) in H18 || set (List.firstn  _ _) in H18).

  progress repeat (straightline_call; ssplit;
    [ solve [repeat match goal with
      | |- True => exact I
      | |- exists _, _ => letexists
      | |- _ =>
          repeat match goal with x := _ : list _ |- _ => subst x end;
          progress rewrite ?length_coord, ?firstn_length, ?skipn_length; lia
      | _ => ecancel_assumption
      end] ..
    | repeat straightline ]).

  (* stackalloc *)
  repeat seprewrite_in_by Array.array1_iff_eq_of_list_word_at H42 ltac:(Lia.lia).

  progress repeat (straightline_call; ssplit;
    [ solve [repeat match goal with
      | |- True => exact I
      | |- exists _, _ => letexists
      | |- _ =>
          repeat match goal with x := _ : list _ |- _ => subst x end;
          progress rewrite ?length_coord, ?firstn_length, ?skipn_length; lia
      | _ => ecancel_assumption
      end] ..
    | repeat straightline ]).

  (* stackdealloc *)
  progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H50 ltac:(rewrite ?length_coord; Lia.lia).
  progress repeat match type of H50 with context [Array.array ptsto _ _ (coord.to_bytes ?x)] =>
    unique pose proof (length_coord x) end.
  repeat straightline.
  progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H50 ltac:(rewrite ?length_coord; Lia.lia).

  progress repeat (straightline_call; ssplit;
    [ solve [repeat match goal with
      | |- True => exact I
      | |- exists _, _ => letexists
      | |- _ =>
          repeat match goal with x := _ : list _ |- _ => subst x end;
          progress rewrite ?length_coord, ?firstn_length, ?skipn_length; lia
      | _ => ecancel_assumption
      end] ..
    | repeat straightline ]).

  (* stackdealloc *)
  progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H69 ltac:(rewrite ?length_coord; Lia.lia).
  progress repeat match type of H69 with context [Array.array ptsto _ _ (coord.to_bytes ?x)] =>
    unique pose proof (length_coord x) end.
  repeat straightline.
  progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H69 ltac:(rewrite ?length_coord; Lia.lia).

  (* postcondition *)

  cbv [proj1_sig proj2_sig fst snd point.to_bytes Jacobian.double_minus_3 Jacobian.double_minus3_impl Jacobian.Fsquare Jacobian.Ftriple Jacobian.Fhalve ].
  progress repeat seprewrite_in_by Array.list_word_at_app_of_adjacent_eq H69 ltac:(rewrite ?length_coord; listZnWords).
  rewrite ?F.pow_3_r, ?F.pow_2_r in H69.
  ecancel_assumption.
Qed.

Import BinInt. Local Open Scope Z_scope.

Definition fe_set_1 := func! (o) {
  o0 = $1; o1 = $0xffffffff00000000; o2 = -$1; o3 = $0xfffffffe;
  store(o, o0); store(o+$8, o1); store(o+$16, o2); store(o+$24, o3)
}.

Definition p256_point_add_affine_nz_nz_neq := func! (out, in1, in2) ~> ok {
  stackalloc 32 as z1z1;
  stackalloc 32 as u2;
  stackalloc 32 as h;
  stackalloc 32 as s2;
  stackalloc 32 as r;
  stackalloc 32 as Hsqr;
  stackalloc 32 as Hcub;

  p256_coord_sqr(z1z1, in1.+$32.+$32);
  p256_coord_mul(u2, in2, z1z1);
  p256_coord_sub(h, u2, in1);
  p256_coord_mul(s2, in1.+$32.+$32, z1z1);
  p256_coord_mul(out.+$32.+$32, h, in1.+$32.+$32);
  p256_coord_mul(s2, s2, in2.+$32);
  p256_coord_sub(r, s2, in1.+$32);
  p256_coord_sqr(Hsqr, h);
  p256_coord_sqr(out, r);
  p256_coord_mul(Hcub, Hsqr, h);
  p256_coord_mul(u2, in1, Hsqr);

  unpack! different_x = p256_coord_nonzero(Hcub);
  unpack! different_y = p256_coord_nonzero(out);
  unpack! ok = br_value_barrier(different_x | different_y);

  p256_coord_sub(out, out, Hcub);
  p256_coord_sub(out, out, u2);
  p256_coord_sub(out, out, u2);
  p256_coord_sub(h, u2, out);
  p256_coord_mul(s2, Hcub, in1.+$32);
  p256_coord_mul(h, h, r);
  p256_coord_sub(out.+$32, h, s2)
}.

Definition p256_point_add_affine_conditional := func! (out, in1, in2, c) {
  unpack! p1zero = p256_point_iszero(in1.+$32.+$32);
  unpack! p2zero = constant_time_is_zero_w(c);
  stackalloc (3*32) as p_out;
  unpack! ok = p256_point_add_affine_nz_nz_neq(p_out, in1, in2);
  unpack! ok = br_declassify(p1zero | p2zero | ok);
  stackalloc (3*32) as t;
  br_memset(t, $0, $3*$32);
  memcxor(t, p_out,  $3*$32,     ~p1zero & ~p2zero);
  memcxor(t, in1,    $3*$32,     ~p1zero &  p2zero);
  memcxor(t, in2,    $3*$32,      p1zero & ~p2zero);
  if !ok { p256_point_double(t, in1) };
  br_memcpy(out, t, $(3*32))
}.

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
