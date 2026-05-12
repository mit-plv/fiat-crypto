From coqutil Require Import
  Byte
  Datatypes.List
  Macros.symmetry
  OfListWord
  Tactics
  Tactics.Tactics
  Word.Interface
  Word.Properties.

From bedrock2 Require Import
  BasicC64Semantics
  NotationsCustomEntry
  ProgramLogic
  SepAutoArray
  Separation
  SeparationLogic
  Syntax
  WeakestPrecondition
  wsize
  ZnWords.

From bedrock2Examples Require Import
  memcpy.

From Crypto Require Import
  Arithmetic.Signed
  Curves.Weierstrass.Affine
  Curves.Weierstrass.AffineProofs
  Curves.Weierstrass.Jacobian.Jacobian
  ListUtil
  ModInv
  PrimeFieldTheorems
  Spec.WeierstrassCurve
  Util.ZUtil.Modulo
  ZArith
  Curves.Weierstrass.P256. (* Overrides W.mul for scalarmult. *)

From Crypto.Bedrock.P256 Require Import
  Jacobian
  PrecomputedMultiples
  RecodeProofs
  RecodeSpecs
  Specs.

Require Import
  BinInt
  BinNat
  Coq.Lists.List
  Init.Byte
  micromega.Lia
  Zdiv.

Import ProgramLogic.Coercions.

Import Coq.Lists.List.ListNotations.
Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Import LittleEndianList.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.
#[local] Open Scope list_scope.

Existing Instance AffineProofs.W.commutative_group.

#[local] Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

#[local] Notation sizeof_point := 96%nat.
#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).
#[local] Notation pointarray := (Array.array (fun (p : word.rep) (Q : point) =>
  ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat sizeof_point))).
(* w is limb size (nonzero). *)
#[local] Notation w := 5.
(* Is it helpful that these ar nat? *)
#[local] Notation num_bits := 256%nat.
#[local] Notation num_limbs := 52%nat. (* log2 p256_group_order / w + 1*)

(* Loads the byte at address p_b interpreted as signed integer. *)
Definition load1_sext :=
  func! (p_b) ~> r {
    r = (load1(p_b) << ($wsize - $8)) .>> ($wsize - $8)
  }.

(* Computes 2^n * P. *)
Definition p256_mul_by_pow2 :=
  func! (p_P, n) {
    while n {
      stackalloc sizeof_point as p_dP; (* Temporary point dP. *)
      p256_point_double(p_dP, p_P); (* dP = [2]P *)
      br_memcpy(p_P, p_dP, $sizeof_point); (* P = dP *)
      n = n - $1;
      $(cmd.unset "p_dP")
    }
  }.

(* Computes k*P for a signed recoded scalar k. *)
Definition p256_point_mul_signed :=
  func! (p_out, p_sscalar, p_P) {
    stackalloc (sizeof_point * 17) as p_table;
    p256_precompute_multiples(p_table, p_P); (* Precompute multiples [k]P for k \in [0, 16].*)
    p256_point_set_zero(p_out); (* Set result point to identity. *)
    i = $0;
    while ($num_limbs - i) {
      stackalloc sizeof_point as p_kP; (* Temporary point kP = [k]P. *)
      stackalloc sizeof_point as p_tmp; (* Temporary point for addition. *)
      p256_mul_by_pow2(p_out, $w); (* OUT = [2^w]OUT *)
      unpack! k = load1_sext(p_sscalar + ($num_limbs - i - $1)); (* k is the next recoded signed scalar limb. *)
      p256_get_multiple(p_kP, p_table, k); (* kP = [k]P *)
      p256_point_add_vartime_if_doubling(p_tmp, p_out, p_kP); (* TMP = OUT + kP *)
      br_memcpy(p_out, p_tmp, $sizeof_point); (* OUT = TMP *)
      i = i + $1;
      $(cmd.unset "k");
      $(cmd.unset "p_kP");
      $(cmd.unset "p_tmp")
    }
  }.

(* Align helpers. *)
Definition align_mask x mask := Z.land (x + mask) (Z.lnot mask).
Definition align x a := align_mask x (a - 1).

#[local] Abbreviation to_affine := Jacobian.Jacobian.to_affine.
#[local] Abbreviation of_affine := Jacobian.Jacobian.of_affine.

Definition p256_point_mul :=
  func! (p_out, p_scalar, p_P) {
    stackalloc (align num_limbs 8) as p_sscalar; (* Space for limbs of unpacked and recoded scalar. *)
    decompose_to_limbs(p_sscalar, p_scalar, $num_bits); (* Unpack scalar into unsigned w-bit limbs. *)
    signed_recode(p_sscalar, $num_limbs); (* Recode scalar into signed w-bit limbs. *)
    p256_point_mul_signed(p_out, p_sscalar, p_P) (* Multiply using signed multiplication. *)
  }.

#[export] Instance spec_of_load1_sext : spec_of "load1_sext" :=
  fnspec! "load1_sext" p_b / b R ~> r,
  { requires t m :=
    m =* ptsto p_b b * R;
    ensures T M :=
    M =* ptsto p_b b * R /\ T = t /\
    word.signed r = byte.signed b
  }.

#[export] Instance spec_of_p256_mul_by_pow2 : spec_of "p256_mul_by_pow2" :=
  fnspec! "p256_mul_by_pow2" p_P n / (P : point) R,
  { requires t m :=
    m =* P$@p_P * R;
    ensures T M := exists (Q : point),
    M =* Q$@p_P * R /\
    W.eq (to_affine Q) (W.mul (2^n) (to_affine P)) /\
    T = t
  }.

#[export] Instance spec_of_p256_point_mul_signed : spec_of "p256_point_mul_signed" :=
  fnspec! "p256_point_mul_signed" (p_out p_sscalar p_P : word) / out sscalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
    length out = length P /\ length sscalar = num_limbs /\
    0 < positional_signed_bytes (2^w) sscalar < p256_group_order /\
    Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) sscalar;
    ensures T M := exists (Q : point) (* Q = [sscalar]P *),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      W.eq (to_affine Q) (W.mul (positional_signed_bytes (2^w) sscalar) (to_affine P)) /\
      T = t
  }.

#[export] Instance spec_of_p256_point_mul : spec_of "p256_point_mul" :=
  fnspec! "p256_point_mul" (p_out p_scalar p_P : word) / out scalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_scalar scalar * P$@p_P * R /\
    length out = length P /\
    8 * (length scalar - 1) < num_bits <= 8 * length scalar /\
    0 < Z.of_bytes scalar < p256_group_order;
    ensures T M := exists (Q : point) (* Q = [scalar]P *),
      M =* Q$@p_out * bytearray p_scalar scalar * P$@p_P * R /\
      W.eq (to_affine Q) (W.mul (Z.of_bytes scalar) (to_affine P)) /\
      T = t
  }.

Lemma load1_sext_ok : program_logic_goal_for_function! load1_sext.
Proof.
  repeat straightline.
  ssplit; try ecancel_assumption; trivial.
  cbv [r Semantics.interp_op1].
  rewrite eval_wsize'.
  rewrite <-word.ring_morph_sub.
  rewrite word.signed_srs_nowrap by ZnWords.
  rewrite word.signed_eq_swrap_unsigned.
  rewrite word.unsigned_slu_shamtZ by lia.
  rewrite ?word.unsigned_of_Z_nowrap by (pose proof byte.unsigned_range b; lia).
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  cbv [byte.signed word.wrap byte.swrap word.swrap].
  PreOmega.Z.div_mod_to_equations.
  lia.
Qed.

#[local] Ltac hyp_containing a := match goal with H : context[a] |- _ => H end.

#[local] Ltac ensure_map m := lazymatch type of m with | @Interface.map.rep _ _ _ => true | _ => false end.
#[local] Ltac newest_memory_hyp := match goal with | H: ?G ?m |- _ =>
    match (ensure_map m) with true => H | false => fail end end.

Local Ltac subst_weq :=
  repeat match goal with |- context [?P] =>
    match goal with H : W.eq P _ |- _ =>
      rewrite H
    end
  end.

Lemma p256_mul_by_pow2_ok : program_logic_goal_for_function! p256_mul_by_pow2.
Proof.
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil))
    (* program variables *) (["p_P";"n"] : list String.string))
    (fun v (P : point) R t m p_P n => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned n /\
      m =* P$@p_P * R)
    (fun                 T M P_P N => (* postcondition *)
      exists (Q : point),
      M =* Q$@p_P * R /\
      p_P = P_P /\
      W.eq (to_affine Q) (W.mul (2^n) (to_affine P)) /\
      T = t))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { apply Z.lt_wf. }
  { (* Base case. *)
    repeat straightline.
    ecancel_assumption. }
  { intros ? ?kP ? ? ? ? ?power.
     repeat straightline.
    (* Induction case. *)
    { straightline_call. (* call p256_point_double *)
      { split.
        { seprewrite_in_by Array.array1_iff_eq_of_list_word_at ltac:(newest_memory_hyp) ltac:(lia).
          ecancel_assumption. }
        { rewrite length_point; trivial. } }
      repeat straightline.
      straightline_call. (* call br_memcpy *)
      { ssplit; try ecancel_assumption.
        { rewrite length_point; trivial. }
        { rewrite length_point; trivial. }
        ZnWords. }
      repeat straightline.
      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a) ltac:(newest_memory_hyp) ltac:(rewrite length_point; lia).
      pose proof (length_point (Jacobian.Jacobian.double_minus_3 eq_refl kP)).
      repeat straightline.
      eexists _, _, (word.unsigned n).
      repeat straightline.
      { ecancel_assumption. }
      split.
      { ZnWords. }
      repeat straightline.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      subst_weq.
      subst n.
      rewrite word.unsigned_sub, word.unsigned_of_Z_nowrap by lia.
      cbv [word.wrap].
      rewrite Z.mod_small by ZnWords.
      rewrite <-Jacobian.double_minus_3_eq_double.
      rewrite Jacobian.to_affine_double.
      rewrite <-ScalarMult.scalarmult_2_l.
      rewrite ScalarMult.scalarmult_assoc.
      assert (2 * 2 ^ (word.unsigned power - 1) = 2 ^ word.unsigned power) as ->.
      { rewrite <-Z.pow_succ_r by ZnWords.
        f_equal.
        lia. }
      reflexivity. }
    (* Post condition. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.
    etransitivity.
    { symmetry. exact (ScalarMult.scalarmult_1_l (eq:=W.eq) (to_affine kP)). }
    Morphisms.f_equiv.
    rewrite <- (Z.pow_0_r 2). f_equal. lia. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

(* Needed for pointarray deallocation. *)
Lemma pointarray_iff_eq_bytearray (a : word) (bs : list point)
  : Lift1Prop.iff1 (pointarray a bs) (bytearray a (flat_map to_bytes bs)).
Proof.
  generalize a. induction bs.
  { reflexivity. }
  { intros.
    etransitivity. { apply Array.array_cons. }
    symmetry. etransitivity. { rewrite ListUtil.List.flat_map_cons. apply Array.array_append. }
    rewrite <-(Array.array1_iff_eq_of_list_word_at _) by (rewrite length_point; lia).
    cancel. cbv [seps].
    symmetry.
    etransitivity. { apply IHbs. }
    Morphisms.f_equiv. }
Qed.

Lemma p256_point_mul_signed_ok :
  (* Use the alternative spec for p256_point_add_vartime_if_doubling. *)
  let _ := spec_of_p256_point_add_constant_time in
  program_logic_goal_for_function! p256_point_mul_signed.
Proof.
  repeat straightline.
  straightline_call. (* call p256_precompute_multiples *)
  { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a) ltac:(newest_memory_hyp) ltac:(lia).
    ssplit; try ecancel_assumption; trivial. }
  repeat straightline.
  straightline_call. (* call p256_point_set_zero *)
  { ssplit; try ecancel_assumption; trivial. }
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil))))
    (* program variables *) (["p_out";"p_sscalar";"p_P";"p_table";"i"] : list String.string))
    (fun (v:nat) processed_limbs remaining_limbs (curr_out : point) R t m p_out p_sscalar p_P p_table i => PrimitivePair.pair.mk
        (sscalar = remaining_limbs ++ processed_limbs /\
        length processed_limbs = i :> Z /\
        W.eq (to_affine curr_out)
            (W.mul (positional_signed_bytes (2^w) processed_limbs)(to_affine P)) /\
        m =* curr_out$@p_out * bytearray p_sscalar remaining_limbs *
            bytearray (word.add p_sscalar (word.of_Z(length remaining_limbs))) processed_limbs * P$@p_P *
            pointarray p_table x * R /\
        v = i :> Z)
    (fun T M P_OUT P_SSCALAR P_P P_TABLE I =>
      exists (Q : point),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * pointarray p_table x * R /\
      W.eq (to_affine Q)
           (W.add
            (W.mul (2^(w*(length remaining_limbs))) (to_affine curr_out))
            (W.mul (positional_signed_bytes (2^w) remaining_limbs) (to_affine P))) /\
      T = t))
    (fun n m => (m < n <= length sscalar)%nat)
    _ _ _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { apply PeanoNat.Nat.gt_wf. }
  { (* Base case. *)
    repeat straightline. ssplit.
    2: { rewrite length_nil. ZnWords. }
    { rewrite app_nil_r. reflexivity. }
    { cbn [positional_signed_bytes positional fold_right map].
      rewrite Jacobian.to_affine_of_affine.
      rewrite ScalarMult.scalarmult_0_l.
      reflexivity. }
    { seprewrite @Array.array_nil. ecancel_assumption. }
    { rewrite Znat.Z2Nat.id; [exact eq_refl|ZnWords]. } }

  (* Postcondition of the function holds after the loop. *)
  2: {
    repeat straightline.
    seprewrite_in pointarray_iff_eq_bytearray ltac:(newest_memory_hyp).
    assert (length (flat_map to_bytes x) = (17*sizeof_point)%nat).
    { rewrite (flat_map_constant_length (c := sizeof_point)) by trivial.
      rewrite <-(length_map to_affine).
      erewrite Forall2_length by eassumption.
      trivial. }
    repeat straightline.
    eexists _.
    ssplit; try ecancel_assumption; try exact eq_refl.
    subst_weq.
    rewrite Jacobian.to_affine_of_affine.
    rewrite ScalarMult.scalarmult_zero_r.
    rewrite Hierarchy.left_identity.
    reflexivity.
  }

  (* Loop *)
  intros ?v ?processed_limbs ?remaining_limbs ?curr_out ?R ?t ?m ?p_out ?p_sscalar ?p_P ?p_table ?i.
  repeat straightline.

  (* Loop postcondition holds after the final iteration. *)
  2: {
    eexists _.
    ssplit; trivial.
    { subst sscalar.
      seprewrite @Array.array_append.
      use_sep_assumption. cancel.
      cancel_seps_at_indices 0%nat 1%nat. { reflexivity. }
      Morphisms.f_equiv. do 3 f_equal. ZnWords.
    }
    assert (length processed_limbs = length sscalar) by ZnWords.
    destruct remaining_limbs. 2: { subst sscalar. rewrite length_app, length_cons in *. lia. }
    subst_weq.
    cbn [positional_signed_bytes positional List.map fold_right].
    rewrite ScalarMult.scalarmult_0_l.
    rewrite Hierarchy.right_identity.
    rewrite Z.mul_0_r, Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity.
  }

  rename a0 into p_kP.
  straightline_call. (* call p256_mul_by_pow2 *)
  { ecancel_assumption. }
  repeat straightline.
  rename x0 into shifted_cur_out.

  subst sscalar.
  match goal with H: Forall _ _ |- _ => rename H into HForall end.
  apply Forall_app in HForall. destruct HForall as (HForallRem&HForallProc).

  assert ((length remaining_limbs + length processed_limbs = num_limbs)%nat).
  { rewrite <- length_app. assumption. }
  assert (length processed_limbs < num_limbs)%nat by ZnWords.
  assert (length remaining_limbs > 0) by ZnWords.

  (* Split out the last element of remaining_limbs, this is the limb we will use. *)
  let H := ltac:(newest_memory_hyp) in rename H into Hmem.
  destruct (length remaining_limbs) as [| new_remaining_limbs] eqn:Hrem; try lia.
  set (nth_default "000"%byte remaining_limbs new_remaining_limbs) as cur_limb in *.
  assert (remaining_limbs = firstn new_remaining_limbs remaining_limbs ++ [cur_limb]) as Hremsplit. {
    rewrite <- (ListUtil.List.firstn_all remaining_limbs) at 1.
    rewrite Hrem at 1.
    erewrite ListUtil.firstn_succ by lia.
    reflexivity. }
  rewrite Hremsplit in Hmem by lia.
  seprewrite_in @Array.array_append Hmem.
  seprewrite_in @Array.array_cons Hmem.
  rewrite length_firstn in Hmem.

  straightline_call. (* call load1_sext *)
  { use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat. { f_equal. ZnWords. } ecancel. }
  repeat straightline.
  rename x0 into k.

  straightline_call. (* call p256_get_multiple *)
  { split; [|split; [|split; [|split]]].
    4: eassumption.
    { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at p_kP) ltac:(newest_memory_hyp) ltac:(lia).
      ecancel_assumption. }
    { rewrite length_point. ZnWords. }
    { rewrite <-(length_map to_affine).
      erewrite Forall2_length by eassumption.
      trivial. }
    { let H := ltac:(hyp_containing (word.signed k)) in rewrite H.
      apply Forall_nth_default.
      { eapply Forall_impl. 2: apply HForallRem.
        intros ? Hbounds. clear -Hbounds. cbv [id] in Hbounds. lia. }
      clear. cbv. split; reflexivity. } }
  repeat straightline.
  rename x0 into kP.

  straightline_call. (* call p256_point_add_vartime_if_doubling *)
  { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a3) ltac:(newest_memory_hyp) ltac:(lia).
    ssplit; try ecancel_assumption; trivial.
    intros Hnotbothzero.
    subst_weq.
    rewrite ScalarMult.scalarmult_assoc.
    rewrite Z.mul_comm, word.unsigned_of_Z_nowrap by lia.
    rewrite p256_mul_mod_n. 2: {
      intros HPzero. apply Hnotbothzero.
      subst_weq.
      rewrite !ScalarMult.scalarmult_zero_r. split; reflexivity.
    }
    unfold positional_signed_bytes in *.
    let H := ltac:(hyp_containing (Logic.eq (word.signed k))) in rewrite H.
    apply (fixed_window_no_doubling') with (xs := (firstn new_remaining_limbs (map byte.signed remaining_limbs))); unfold p256_group_order in *.
    all: try ZnWords.
    { apply Forall_firstn. apply Forall_map. apply HForallRem. }
    { apply Forall_map. apply HForallProc. }
    { apply Forall_nth_default. { apply HForallRem. }  clear. cbn. lia. }
    { intros [?N1 ?N2].
      match goal with H: ~ (_ /\ _) |- _ => apply H end; split.
      { subst_weq. unfold positional.
        rewrite N2.
        rewrite ScalarMult.scalarmult_0_l, ScalarMult.scalarmult_zero_r.
        reflexivity. }
      { subst_weq.
        let H := ltac:(hyp_containing (Logic.eq (word.signed k))) in rewrite H.
        rewrite N1.
        apply ScalarMult.scalarmult_0_l. } }
    { rewrite ListUtil.app_cons_app_app.
      rewrite firstn_map. erewrite <- map_nil by reflexivity. rewrite <- map_cons. rewrite <- map_app.
      rewrite <- Hremsplit. rewrite <- map_app.
      unfold positional in *. lia. } }
  repeat straightline.
  rename x0 into curr_out_new.

  straightline_call. (* call br_memcpy *)
  { ssplit; try ecancel_assumption; trivial.
    ZnWords. }
  repeat straightline.

  (* Deallocate stack. *)
  seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ p_kP)
      ltac:(newest_memory_hyp) ltac:(rewrite length_point; lia).
  assert (length (to_bytes kP) = sizeof_point) by (rewrite length_point; trivial).
  seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a3)
      ltac:(newest_memory_hyp) ltac:(rewrite length_point; lia).
  assert (length (to_bytes curr_out_new) = sizeof_point%nat) by (rewrite length_point; trivial).

  (* Repeat straighline hangs here so we do it in steps. *)
  do 2 straightline_stackdealloc.
  eexists _, _, _, _, _.
  split.
  { repeat straightline. }
  repeat straightline. (* TODO pslit more globally, give the nth element a name*)
  eexists (cur_limb :: processed_limbs), (firstn new_remaining_limbs remaining_limbs), _, _, _.
  repeat straightline.
  { ssplit.
    { rewrite ListUtil.app_cons_app_app. rewrite Hremsplit at 1. reflexivity. }
    { subst i. listZnWords. }
    all: cycle 1.
    { seprewrite @Array.array_cons. seprewrite_in @Array.array_nil ltac:(newest_memory_hyp).
      rewrite length_firstn.
      use_sep_assumption. cancel.
      cancel_seps_at_indices 0%nat 2%nat; [reflexivity|].
      cancel_seps_at_indices 0%nat 0%nat. { f_equal. ZnWords. }
      cancel_seps_at_indices 0%nat 0%nat. { f_equal. ZnWords. }
      ecancel. }
    { subst i. rewrite Znat.Z2Nat.id; [exact eq_refl|ZnWords]. }
    { let H := ltac:(hyp_containing (add shifted_cur_out kP)) in rewrite H.
      rewrite Jacobian.to_affine_add.
      subst_weq.
      let H := ltac:(hyp_containing (Logic.eq (word.signed k))) in rewrite H.
      subst i.
      rewrite ScalarMult.scalarmult_assoc.
      rewrite <-ScalarMult.scalarmult_add_l.
      rewrite word.unsigned_of_Z_nowrap by lia.
      cbv [positional_signed_bytes].
      Morphisms.f_equiv.
      rewrite map_cons.
      rewrite positional_cons.
      lia. } }
  split.
  { ZnWords. }
  (* Postcondition propagates. *)
  repeat straightline.
  eexists _.
  ssplit; trivial.
  { ecancel_assumption. }
  subst_weq.
  let H := ltac:(hyp_containing (Jacobian.eq curr_out_new)) in rewrite H.
  rewrite Jacobian.to_affine_add.
  subst_weq.
  rewrite word.unsigned_of_Z_nowrap by lia.
  let H := ltac:(hyp_containing (Logic.eq (word.signed k))) in rewrite H.
  subst i.
  repeat rewrite ?ScalarMult.scalarmult_assoc, <-?ScalarMult.scalarmult_add_l.
  Morphisms.f_equiv.
  rewrite (Z.pow_mul_r 2 w _) by lia.
  rewrite Z.mul_add_distr_r.
  rewrite <- !Z.add_assoc. f_equal.
  { rewrite <-Z.mul_assoc.
    f_equal.
    rewrite Z.pow_mul_r by lia.
    rewrite Pow.Z.pow_mul_base by ZnWords.
    f_equal. rewrite length_firstn.
    ZnWords. }
  cbv [positional_signed_bytes].
  rewrite Hremsplit at 3. rewrite map_app.
  rewrite positional_app. rewrite length_map.
  cbn. lia.
Qed.

Lemma p256_point_mul_ok : program_logic_goal_for_function! p256_point_mul.
Proof.
  repeat straightline.
  (* Split stack into space for sscalar and padding. *)
  let H:= ltac:(newest_memory_hyp) in
    rewrite <-(firstn_skipn num_limbs stack) in H;
  set (sscalar := ListDef.firstn num_limbs stack) in H;
  set (padding := ListDef.skipn num_limbs stack) in H;
  seprewrite_in Array.bytearray_append H.
  assert (length sscalar = num_limbs) as Hsscalar.
  { unfold sscalar.
    rewrite length_firstn.
    lia. }
  rewrite Hsscalar in *.
  set (word.add a (word.of_Z (Z.of_nat _))) in *.
  straightline_call. (* call limbs_unpack *)
  { (* Solve limbs_unpack assumptions. *)
    ssplit; try ecancel_assumption; try ZnWords.
    rewrite word.unsigned_of_Z_nowrap by lia.
    cbv [p256_group_order] in *.
    lia. }
  repeat straightline.
  straightline_call. (* call recode_wrap *)
  { (* Solve recode_wrap assumptions. *)
    ssplit; try ecancel_assumption; trivial.
    { ZnWords. }
    { let H := (hyp_containing (le_combine scalar)) in rewrite H.
      rewrite word.unsigned_of_Z_nowrap by lia.
      cbv [p256_group_order] in *.
      lia. }
    { Decidable.vm_decide. } }
  repeat straightline.
  straightline_call. (* call p256_point_mul_signed *)
  { ssplit; try ecancel_assumption; trivial; try ZnWords. }
  repeat straightline.
  (* Restore stack by combining scalar and padding. *)
  seprewrite_in_by (Array.bytearray_index_merge x0 padding) ltac:(newest_memory_hyp) ZnWords.
  assert (length (x0 ++ padding) = 56%nat).
  { rewrite length_app.
    cbv [padding].
    rewrite length_skipn.
    ZnWords. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
  subst_weq.
  Morphisms.f_equiv.
  etransitivity. { eassumption. }
  assumption.
Qed.
