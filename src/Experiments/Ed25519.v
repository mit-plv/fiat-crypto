Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.MxDHRepChange. Import MxDH.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NUtil.
Require Crypto.Specific.GF25519.
Require Crypto.Specific.GF25519Bounded.
Require Crypto.Specific.SC25519.
Require Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Crypto.Encoding.PointEncoding.
Require Crypto.Util.IterAssocOp.
Import Morphisms.
Import NPeano.

Local Coercion GF25519BoundedCommon.word64ToZ : GF25519BoundedCommon.word64 >-> Z.
Local Coercion GF25519BoundedCommon.proj1_fe25519 : GF25519BoundedCommon.fe25519 >-> GF25519.fe25519.
Local Set Printing Coercions.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Context {SHA512: forall n : nat, Word.word n -> Word.word 512}.

(* MOVE : pre-Specific, same level as other fe operations *)
Definition feSign (f :  GF25519BoundedCommon.fe25519) : bool :=
  let x := GF25519Bounded.freeze f in
  let '(x9, x8, x7, x6, x5, x4, x3, x2, x1, x0) := (x : GF25519.fe25519) in
  BinInt.Z.testbit x0 0.

Section Constants.
  Import GF25519BoundedCommon.
  Definition a' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode a.
  Definition a : GF25519BoundedCommon.fe25519 :=
    Eval cbv [a' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize a').
  Definition d' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode d.
  Definition d : GF25519BoundedCommon.fe25519 :=
    Eval cbv [d' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize d').
  Definition twice_d' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in (GF25519Bounded.add d d).
  Definition twice_d : GF25519BoundedCommon.fe25519 :=
    Eval cbv [twice_d' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize twice_d').
End Constants.

Lemma phi_a : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.a) a.
Proof. reflexivity. Qed.
Lemma phi_d : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.d) d.
Proof. vm_decide_no_check. Qed.

Definition Erep := (@ExtendedCoordinates.Extended.point
         GF25519BoundedCommon.fe25519
         GF25519BoundedCommon.eq
         GF25519BoundedCommon.zero
         GF25519BoundedCommon.one
         GF25519Bounded.add
         GF25519Bounded.mul
         GF25519BoundedCommon.div
         a
         d
      ).

Local Existing Instance GF25519.homomorphism_F25519_encode.
Local Existing Instance GF25519.homomorphism_F25519_decode.
(* MOVE : mostly pre-Specific. TODO : narrow down which properties can
be proven generically and which need to be computed, then maybe create
a tactic to do the computed ones *)
Local Instance twedprm_ERep :
  @CompleteEdwardsCurve.E.twisted_edwards_params
   GF25519BoundedCommon.fe25519 GF25519BoundedCommon.eq
   GF25519BoundedCommon.zero GF25519BoundedCommon.one
   GF25519Bounded.add GF25519Bounded.mul a d.
Proof.
  constructor; try vm_decide.
  { destruct CompleteEdwardsCurve.E.square_a as [sqrt_a H].
    exists (GF25519BoundedCommon.encode sqrt_a).
    transitivity (GF25519BoundedCommon.encode Spec.Ed25519.a); [ rewrite <- H | vm_decide ].
    rewrite <- Algebra.Ring.homomorphism_mul; reflexivity. }
  { intros x H.
    pose proof (CompleteEdwardsCurve.E.nonsquare_d (GF25519BoundedCommon.decode x)) as ns_d.
    apply ns_d; clear ns_d.
    transitivity (GF25519BoundedCommon.decode d); [ rewrite <- H | vm_decide ].
    rewrite <- Algebra.Ring.homomorphism_mul; reflexivity. }
Qed.

Definition coord_to_extended (xy : GF25519BoundedCommon.fe25519 * GF25519BoundedCommon.fe25519) pf :=
  ExtendedCoordinates.Extended.from_twisted
    (field := GF25519Bounded.field25519) (prm :=twedprm_ERep)
    (exist Pre.onCurve xy pf).

Definition extended_to_coord (P : Erep) : (GF25519BoundedCommon.fe25519 * GF25519BoundedCommon.fe25519) :=
  CompleteEdwardsCurve.E.coordinates (ExtendedCoordinates.Extended.to_twisted P (field:=GF25519Bounded.field25519)).

Lemma encode_eq_iff :  forall x y : ModularArithmetic.F.F GF25519.modulus,
                    GF25519BoundedCommon.eq
                      (GF25519BoundedCommon.encode x)
                      (GF25519BoundedCommon.encode y) <->  x = y.
Proof.
  intros.
  cbv [GF25519BoundedCommon.eq GF25519BoundedCommon.encode ModularBaseSystem.eq].
  rewrite !GF25519BoundedCommon.proj1_fe25519_exist_fe25519, !ModularBaseSystemProofs.encode_rep.
  reflexivity.
Qed.

Definition EToRep :=
  PointEncoding.point_phi
    (Kfield := GF25519Bounded.field25519)
    (phi_homomorphism := GF25519Bounded.homomorphism_F25519_encode)
    (Kpoint := Erep)
    (phi_a := phi_a)
    (phi_d := phi_d)
    (Kcoord_to_point := ExtendedCoordinates.Extended.from_twisted (prm := twedprm_ERep) (field := GF25519Bounded.field25519)).

Definition ZNWord sz x := Word.NToWord sz (BinInt.Z.to_N x).
Definition WordNZ {sz} (w : Word.word sz) := BinInt.Z.of_N (Word.wordToN w).

Definition SRep := SC25519.SRep.
Definition S2Rep := SC25519.S2Rep.

Lemma eq_a_minus1 : GF25519BoundedCommon.eq a (GF25519Bounded.opp GF25519BoundedCommon.one).
Proof. vm_decide. Qed.

Definition ErepAdd :=
  (@ExtendedCoordinates.Extended.add _ _ _ _ _ _ _ _ _ _
                                     a d GF25519Bounded.field25519 twedprm_ERep _
                                     eq_a_minus1 twice_d (eq_refl _)
                                     _ (fun _ _ => reflexivity _)).

Local Coercion Z.of_nat : nat >-> Z.
Definition ERepSel : bool -> Erep -> Erep -> Erep := fun b x y => if b then y else x.

Local Existing Instance ExtendedCoordinates.Extended.extended_group.
(* TODO : automate this? *)
Local Instance Ahomom :
      @Algebra.Monoid.is_homomorphism E
           CompleteEdwardsCurveTheorems.E.eq
           CompleteEdwardsCurve.E.add Erep
           (ExtendedCoordinates.Extended.eq
              (field := GF25519Bounded.field25519)) ErepAdd EToRep.
Proof.
  eapply (Algebra.Group.is_homomorphism_compose
           (Hphi := CompleteEdwardsCurveTheorems.E.lift_homomorphism
                (field := PrimeFieldTheorems.F.field_modulo GF25519.modulus)
                (Ha := phi_a) (Hd := phi_d)
                (Kprm := twedprm_ERep)
                (point_phi := CompleteEdwardsCurveTheorems.E.ref_phi
                                (Ha := phi_a) (Hd := phi_d)
                                (fieldK := GF25519Bounded.field25519))
                (fieldK := GF25519Bounded.field25519))
           (Hphi' :=  ExtendedCoordinates.Extended.homomorphism_from_twisted)).
  cbv [EToRep PointEncoding.point_phi].
  reflexivity.
  Grab Existential Variables.
  cbv [CompleteEdwardsCurveTheorems.E.eq].
  intros.
  match goal with |- @Tuple.fieldwise _ _ ?n ?R _ _ =>
                  let A := fresh "H" in
                  assert (Equivalence R) as A by (exact _);
                    pose proof (@Tuple.Equivalence_fieldwise _ R A n)
  end.
  reflexivity.
Qed.

(* TODO : automate *)
Lemma ERep_eq_E P Q :
      ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519)
      (EToRep P) (EToRep Q)
      -> CompleteEdwardsCurveTheorems.E.eq P Q.
Proof.
  destruct P as [[] HP], Q as [[] HQ].
  cbv [ExtendedCoordinates.Extended.eq EToRep PointEncoding.point_phi CompleteEdwardsCurveTheorems.E.ref_phi CompleteEdwardsCurveTheorems.E.eq CompleteEdwardsCurve.E.coordinates
                                       ExtendedCoordinates.Extended.coordinates
                                       ExtendedCoordinates.Extended.to_twisted
                                       ExtendedCoordinates.Extended.from_twisted
                                       GF25519BoundedCommon.eq ModularBaseSystem.eq
  Tuple.fieldwise Tuple.fieldwise' fst snd proj1_sig].
  intro H.
  rewrite !GF25519Bounded.mul_correct, !GF25519Bounded.inv_correct, !GF25519BoundedCommon.proj1_fe25519_encode in *.
  rewrite !Algebra.Ring.homomorphism_mul in H.
  pose proof (Algebra.Field.homomorphism_multiplicative_inverse (H:=GF25519.field25519)) as Hinv;
    rewrite Hinv in H by vm_decide; clear Hinv.
  let e := constr:((ModularBaseSystem.decode (GF25519BoundedCommon.proj1_fe25519 GF25519BoundedCommon.one))) in
  set e as xe; assert (Hone:xe = ModularArithmetic.F.one) by vm_decide; subst xe; rewrite Hone in *; clear Hone.
  rewrite <-!(Algebra.field_div_definition(inv:=ModularArithmetic.F.inv)) in H.
  rewrite !(Algebra.Field.div_one(one:=ModularArithmetic.F.one)) in H.
  pose proof ModularBaseSystemProofs.encode_rep as Hencode;
    unfold ModularBaseSystem.rep in Hencode; rewrite !Hencode in H.
  assumption.
Qed.

Section SRepERepMul.
  Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
  Import Coq.NArith.NArith Coq.PArith.BinPosDef.
  Import Coq.Numbers.Natural.Peano.NPeano.
  Import Crypto.Algebra.
  Import Crypto.Util.IterAssocOp.

  Let ll := Eval vm_compute in (BinInt.Z.to_nat (BinInt.Z.log2_up l)).
  Definition SRepERepMul : SRep -> Erep -> Erep := fun x =>
    IterAssocOp.iter_op
      (op:=ErepAdd)
      (id:=ExtendedCoordinates.Extended.zero(field:=GF25519Bounded.field25519)(prm:=twedprm_ERep))
      (fun i => N.testbit_nat (Z.to_N x) i)
      (sel:=ERepSel)
      ll
  .

  (* TODO : automate *)
  Lemma SRepERepMul_correct n P :
    ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519)
                                    (EToRep (CompleteEdwardsCurve.E.mul (n mod (Z.to_nat l))%nat P))
                                    (SRepERepMul (S2Rep (ModularArithmetic.F.of_nat l n)) (EToRep P)).
  Proof.
    rewrite ScalarMult.scalarmult_ext.
    unfold SRepERepMul.
    etransitivity; [|symmetry; eapply iter_op_correct].
    3: intros; reflexivity.
    2: intros; reflexivity.
    { etransitivity.
      apply (@Group.homomorphism_scalarmult _ _ _ _ _ _ _ _ _ _ _ _ EToRep Ahomom ScalarMult.scalarmult_ref _ ScalarMult.scalarmult_ref _ _ _).
      unfold S2Rep, SC25519.S2Rep, ModularArithmetic.F.of_nat.
      apply (_ : Proper (_ ==> _ ==> _) ScalarMult.scalarmult_ref); [ | reflexivity ].
      rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
      apply Nat2Z.inj_iff.
      rewrite N_nat_Z, Z2N.id by (refine (proj1 (Zdiv.Z_mod_lt _ _ _)); vm_decide).
      rewrite Zdiv.mod_Zmod by (intro Hx; inversion Hx);
      rewrite Z2Nat.id by vm_decide; reflexivity. }
    { (* this could be made a lemma with some effort *)
      unfold S2Rep, SC25519.S2Rep, ModularArithmetic.F.of_nat;
        rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
      destruct (Z.mod_pos_bound (Z.of_nat n) l) as [Hl Hu];
        try (eauto || vm_decide); [].
      generalize dependent (Z.of_nat n mod l)%Z; intros; [].
      apply Z2N.inj_lt in Hu; try (eauto || vm_decide); [];
        apply Z2N.inj_le in Hl; try (eauto || vm_decide); [].
      clear Hl; generalize dependent (Z.to_N z); intro x; intros.
      rewrite N.size_nat_equiv.
      destruct (dec (x = 0%N)); subst; try vm_decide; [];
        rewrite N.size_log2 by assumption.
      rewrite N2Nat.inj_succ; assert (N.to_nat (N.log2 x) < ll); try omega.
      change ll with (N.to_nat (N.of_nat ll)).
      apply Nomega.Nlt_out; eapply N.le_lt_trans.
      eapply N.log2_le_mono; eapply N.lt_succ_r.
      rewrite N.succ_pred; try eassumption.
      vm_decide.
      vm_compute. reflexivity. }
  Qed.

  Definition NERepMul : N -> Erep -> Erep := fun x =>
    IterAssocOp.iter_op
      (op:=ErepAdd)
      (id:=ExtendedCoordinates.Extended.zero(field:=GF25519Bounded.field25519)(prm:=twedprm_ERep))
      (N.testbit_nat x)
      (sel:=ERepSel)
      ll
  .
  Lemma NERepMul_correct n P :
    (N.size_nat (N.of_nat n) <= ll) ->
    ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519)
                                    (EToRep (CompleteEdwardsCurve.E.mul n P))
                                    (NERepMul (N.of_nat n) (EToRep P)).
  Proof.
    rewrite ScalarMult.scalarmult_ext.
    unfold NERepMul.
    etransitivity; [|symmetry; eapply iter_op_correct].
    3: intros; reflexivity.
    2: intros; reflexivity.
    { rewrite Nat2N.id.
      apply (@Group.homomorphism_scalarmult _ _ _ _ _ _ _ _ _ _ _ _ EToRep Ahomom ScalarMult.scalarmult_ref _ ScalarMult.scalarmult_ref _ _ _). }
    { assumption. }
  Qed.
End SRepERepMul.

(* TODO : figure out if and where to move this *)
Lemma nth_default_freeze_input_bound_compat : forall i,
  (nth_default 0 PseudoMersenneBaseParams.limb_widths i <
   GF25519.freeze_input_bound)%Z.
Proof.
  pose proof GF25519.freezePreconditions25519.
  intros.
  destruct (lt_dec i (length PseudoMersenneBaseParams.limb_widths)).
  { apply ModularBaseSystemProofs.B_compat.
    rewrite nth_default_eq.
    auto using nth_In. }
  { rewrite nth_default_out_of_bounds by omega.
    cbv; congruence. }
Qed.

(* TODO : This is directly implied by other lemmas and should be
easier. I'd say automate it, but given that the basesystem stuff is in
flux maybe we should leave it for now and then do a complete rewrite
later. *)
Lemma minrep_freeze : forall x,
            Pow2Base.bounded
              PseudoMersenneBaseParams.limb_widths
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width
                    (ModularBaseSystem.encode x))) /\
            ModularBaseSystemList.ge_modulus
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width
                    (ModularBaseSystem.encode x))) =
            0%Z.
Proof.
    pose proof GF25519.freezePreconditions25519.
    intros.
    match goal with
      |- appcontext [ModularBaseSystem.freeze _ ?x] =>
      pose proof (ModularBaseSystemProofs.minimal_rep_freeze x) as Hminrep end.
    match type of Hminrep with ?P -> _ => assert P end.
    { intros i ?.
      let A := fresh "H" in
      pose proof (ModularBaseSystemProofs.bounded_encode x) as A;
          rewrite Pow2BaseProofs.bounded_iff in A; specialize (A i).
      split; [ omega | ].
      eapply Z.lt_le_trans; [ solve [intuition eauto] | ].
      match goal with |- appcontext [if ?a then _ else _] => destruct a end.
      { apply Z.pow_le_mono_r; try omega.
        apply Z.lt_le_incl.
        apply nth_default_freeze_input_bound_compat. }
      { transitivity (2 ^ (Z.pred GF25519.freeze_input_bound))%Z.
          { apply Z.pow_le_mono; try omega.
            apply Z.lt_le_pred.
            apply nth_default_freeze_input_bound_compat. }
          { rewrite Z.shiftr_div_pow2 by (auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg).
          rewrite <- Z.pow_sub_r by (try omega; split; auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg, Z.lt_le_incl, nth_default_freeze_input_bound_compat).
          replace (2 ^ GF25519.freeze_input_bound)%Z
            with (2 ^ (Z.pred GF25519.freeze_input_bound + 1))%Z
            by (f_equal; omega).
          rewrite Z.pow_add_r by (omega || (cbv; congruence)).
          rewrite <-Zplus_diag_eq_mult_2.
          match goal with |- (?a <= ?a + ?b - ?c)%Z =>
                          assert (c <= b)%Z; [ | omega ] end.
          apply Z.pow_le_mono; try omega.
          rewrite <-Z.sub_1_r.
          apply Z.sub_le_mono_l.
          replace 1%Z with (Z.succ 0) by reflexivity.
          rewrite Z.le_succ_l.
          apply PseudoMersenneBaseParams.limb_widths_pos.
          rewrite nth_default_eq; apply nth_In.
          omega. } } }
    { apply Hminrep. assumption. }
Qed.

Lemma convert_freezes: forall x,
  (ModularBaseSystemList.freeze GF25519.int_width
       (Tuple.to_list
          (length PseudoMersenneBaseParams.limb_widths) x)) =
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width x)).
Proof.
  cbv [ModularBaseSystem.freeze].
  intros.
  rewrite Tuple.to_list_from_list.
  reflexivity.
Qed.
Ltac to_MBSfreeze H :=
  rewrite GF25519.freeze_correct in H;
  rewrite ModularBaseSystemOpt.freeze_opt_correct in H
    by (rewrite ?Tuple.length_to_list; reflexivity);
  erewrite convert_freezes,  Tuple.from_list_default_eq, Tuple.from_list_to_list in H.

Lemma bounded_freeze : forall x,
  Pow2Base.bounded
         PseudoMersenneBaseParams.limb_widths
         (ModularBaseSystemList.freeze
            GF25519.int_width
            (Tuple.to_list
               (length
                  PseudoMersenneBaseParams.limb_widths)
               (ModularBaseSystem.encode x))).
Proof.
  intro.
  rewrite convert_freezes.
  pose proof (minrep_freeze x).
  intuition assumption.
Qed.

Lemma ge_modulus_freeze : forall x,
  ModularBaseSystemList.ge_modulus
         (ModularBaseSystemList.freeze
            GF25519.int_width
            (Tuple.to_list
               (length
                  PseudoMersenneBaseParams.limb_widths)
               (ModularBaseSystem.encode x))) = 0%Z.
Proof.
  intro.
  rewrite convert_freezes.
  pose proof (minrep_freeze x).
  intuition assumption.
Qed.


(* TODO : automate *)
Lemma initial_bounds : forall x n,
  n < length PseudoMersenneBaseParams.limb_widths ->
  (0 <=
   nth_default 0
     (Tuple.to_list (length PseudoMersenneBaseParams.limb_widths)
        (GF25519BoundedCommon.proj1_fe25519 x)) n <
   2 ^ GF25519.freeze_input_bound -
   (if eq_nat_dec n 0%nat
    then 0
    else
     Z.shiftr (2 ^ GF25519.freeze_input_bound)
       (nth_default 0 PseudoMersenneBaseParams.limb_widths
                    (pred n))))%Z.
Proof.
  intros.
  cbv [GF25519BoundedCommon.fe25519] in *.
  repeat match goal with p : (_ * _)%type |- _ => destruct p end.
  cbv [GF25519BoundedCommon.proj1_fe25519].
  cbv [GF25519BoundedCommon.fe25519WToZ
         GF25519BoundedCommon.proj1_fe25519W
         PseudoMersenneBaseParams.limb_widths
         GF25519.params25519 length
         Tuple.to_list Tuple.to_list' nth_default] in *.
  repeat match goal with
         | [ |- appcontext[nth_error _ ?n] ]
           => is_var n; destruct n; simpl @nth_error; cbv beta iota
         end;
    simpl in *; unfold Z.pow_pos; simpl; try omega;
      match goal with
        |- appcontext [GF25519BoundedCommon.proj_word ?b] =>
        let A := fresh "H" in
        pose proof (@GF25519BoundedCommon.word_bounded _ _ b) as A;
          rewrite Bool.andb_true_iff in A; destruct A end;
      rewrite !Z.leb_le in *;
      omega.
Qed.

(* TODO : automate (after moving feSign) *)
Lemma feSign_correct : forall x,
  PointEncoding.sign x = feSign (GF25519BoundedCommon.encode x).
Proof.
  cbv [PointEncoding.sign feSign].
  intros.
  rewrite GF25519Bounded.freeze_correct.
  rewrite GF25519BoundedCommon.proj1_fe25519_encode.
  match goal with |- appcontext [GF25519.freeze ?x] =>
                  remember (GF25519.freeze x) end.
  transitivity (Z.testbit (nth_default 0%Z (Tuple.to_list 10 f) 0) 0).
  Focus 2. {
  cbv [GF25519.fe25519] in *.
  repeat match goal with p : (_ * _)%type |- _ => destruct p end.
  simpl. reflexivity. } Unfocus.

  rewrite !Z.bit0_odd.
  rewrite <-@Pow2BaseProofs.parity_decode with (limb_widths := PseudoMersenneBaseParams.limb_widths) by (auto using PseudoMersenneBaseParamProofs.limb_widths_nonneg, Tuple.length_to_list; cbv; congruence).
  pose proof GF25519.freezePreconditions25519.
  match goal with H : _ = GF25519.freeze ?u |- _ =>
                  let A := fresh "H" in let B := fresh "H" in
                  pose proof (ModularBaseSystemProofs.freeze_rep u x) as A;
                    match type of A with ?P -> _ => assert P as B by apply ModularBaseSystemProofs.encode_rep end;
                    specialize (A B); clear B
  end.
  to_MBSfreeze Heqf.
  rewrite <-Heqf in *.
  cbv [ModularBaseSystem.rep ModularBaseSystem.decode ModularBaseSystemList.decode] in *.
  rewrite <-H0.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
  rewrite Z.mod_small; [ reflexivity | ].
  pose proof (minrep_freeze x).
  apply ModularBaseSystemListProofs.ge_modulus_spec;
    try solve [inversion H; auto using Tuple.length_to_list];
    subst f; intuition auto.
  Grab Existential Variables.
  apply Tuple.length_to_list.
Qed.

(* MOVE : to wherever feSign goes*)
Local Instance Proper_feSign : Proper (GF25519BoundedCommon.eq ==> eq) feSign.
Proof.
  repeat intro; cbv [feSign].
  rewrite !GF25519Bounded.freeze_correct.
  repeat match goal with |- appcontext[GF25519.freeze ?x] =>
                         remember (GF25519.freeze x) end.
  assert (Tuple.fieldwise (n := 10) eq f f0).
  { pose proof GF25519.freezePreconditions25519.
    match goal with H1 : _ = GF25519.freeze ?u,
                    H2 : _ = GF25519.freeze ?v |- _ =>
    let A := fresh "H" in
    let HP := fresh "H" in
    let HQ := fresh "H" in
        pose proof (ModularBaseSystemProofs.freeze_canonical
                      (freeze_pre := GF25519.freezePreconditions25519) u v _ _ eq_refl eq_refl);
        match type of A with ?P -> ?Q -> _ =>
                            assert P as HP by apply initial_bounds;
                                assert Q as HQ by apply initial_bounds end;
        specialize (A HP HQ); clear HP HQ end.
    cbv [ModularBaseSystem.eq] in *.
    to_MBSfreeze Heqf0.
    to_MBSfreeze Heqf.
    subst.
    apply H1.
    cbv [GF25519BoundedCommon.eq ModularBaseSystem.eq] in *.
    auto. }
  { cbv [GF25519.fe25519 ] in *.
    repeat match goal with p : (_ * _)%type |- _ => destruct p end.
    cbv [Tuple.fieldwise Tuple.fieldwise' fst snd] in *.
    intuition congruence. }
  Grab Existential Variables.
  rewrite Tuple.length_to_list; reflexivity.
  rewrite Tuple.length_to_list; reflexivity.
Qed.

(* MOVE : pre-Specific *)
Lemma Proper_pack :
  Proper (Tuple.fieldwise (n := length PseudoMersenneBaseParams.limb_widths) eq ==>
                          Tuple.fieldwise (n := length GF25519.wire_widths) eq) GF25519.pack.
Proof.
  repeat intro.
  cbv [PseudoMersenneBaseParams.limb_widths GF25519.params25519 length] in *.
  cbv [Tuple.tuple] in *.
  repeat match goal with
         | p : Tuple.tuple' Z (S ?n) |- _ => destruct p
         | p : Tuple.tuple' Z 0 |- _ => cbv [Tuple.tuple'] in p
         end.
  cbv [GF25519.pack].
  cbv [GF25519.wire_widths length Tuple.fieldwise Tuple.fieldwise' fst snd] in *;
    intuition subst; reflexivity.
Qed.

Lemma ext_eq_correct : forall p q : Erep,
  ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519) p q <->
  Tuple.fieldwise (n := 2) GF25519BoundedCommon.eq (extended_to_coord p) (extended_to_coord q).
Proof.
  cbv [extended_to_coord]; intros.
  cbv [ExtendedCoordinates.Extended.eq].
  match goal with |- _ <-> Tuple.fieldwise _
                                           (CompleteEdwardsCurve.E.coordinates ?x)
                                           (CompleteEdwardsCurve.E.coordinates ?y) =>
                  pose proof (CompleteEdwardsCurveTheorems.E.Proper_coordinates
                                (field := GF25519Bounded.field25519) (a := a) (d := d) x y)
  end.
  tauto.
Qed.

Definition SRepEnc : SRep -> Word.word b := (fun x => Word.NToWord _ (Z.to_N x)).

(* TODO : automate? *)
Local Instance Proper_SRepERepMul : Proper (SC25519.SRepEq ==> ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519) ==> ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519)) SRepERepMul.
  unfold SRepERepMul, SC25519.SRepEq.
  repeat intro.
  eapply IterAssocOp.Proper_iter_op.
  { eapply @ExtendedCoordinates.Extended.Proper_add. }
  { reflexivity. }
  { repeat intro; subst; reflexivity. }
  { unfold ERepSel; repeat intro; break_match; solve [ discriminate | eauto ]. }
  { reflexivity. }
  { assumption. }
Qed.

Lemma SRepEnc_correct : forall x : ModularArithmetic.F.F l, Senc x = SRepEnc (S2Rep x).
  unfold SRepEnc, Senc, Fencode; intros; f_equal.
Qed.

Section ConstantPoints.
  Import GF25519BoundedCommon.
  Let proj1_sig_ERepB' := Eval vm_compute in proj1_sig (EToRep B).
  Let tmap4 := Eval compute in @Tuple.map 4. Arguments tmap4 {_ _} _ _.
  Let proj1_sig_ERepB := Eval cbv [tmap4 proj1_sig_ERepB' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (tmap4 fe25519_word64ize proj1_sig_ERepB').
  Let proj1_sig_ERepB_correct : proj1_sig_ERepB = proj1_sig (EToRep B).
  Proof. vm_cast_no_check (eq_refl proj1_sig_ERepB). Qed.

  Definition ERepB : Erep.
    exists (eta4 proj1_sig_ERepB).
    cbv [GF25519BoundedCommon.eq ModularBaseSystem.eq Pre.onCurve].
    vm_decide_no_check.
  Defined.

  Lemma ERepB_correct : ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519) ERepB (EToRep B).
    generalize proj1_sig_ERepB_correct as H; destruct (EToRep B) as [B ?] in |- *.
    cbv [proj1_sig] in |- *. intro. subst B.
    vm_decide.
  Qed.
End ConstantPoints.

Lemma B_order_l : CompleteEdwardsCurveTheorems.E.eq
              (CompleteEdwardsCurve.E.mul (Z.to_nat l) B)
              CompleteEdwardsCurve.E.zero.
Proof.
  apply ERep_eq_E.
  rewrite NERepMul_correct; rewrite (Z_nat_N l).
  2:vm_decide.
  apply dec_bool.
  vm_cast_no_check (eq_refl true).
(* Time Qed. (* Finished transaction in 1646.167 secs (1645.753u,0.339s) (successful) *) *)
Admitted.

Axiom ERepEnc : Erep -> Word.word b.
Axiom ERepEnc_correct : (forall P : E, Eenc P = ERepEnc (EToRep P)).
Axiom Proper_ERepEnc : Proper (ExtendedCoordinates.Extended.eq ==> eq) ERepEnc.

Definition sign := @EdDSARepChange.sign E
         (@CompleteEdwardsCurveTheorems.E.eq Fq (@eq Fq) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.add q) (@ModularArithmetic.F.mul q) Spec.Ed25519.a Spec.Ed25519.d)
         (@CompleteEdwardsCurve.E.add Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params)
         (@CompleteEdwardsCurve.E.zero Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params)
         (@CompleteEdwardsCurveTheorems.E.opp Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0)
            (@ModularArithmetic.F.one q) (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q)
            (@ModularArithmetic.F.sub q) (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q)
            (@ModularArithmetic.F.div q) Spec.Ed25519.a Spec.Ed25519.d (@PrimeFieldTheorems.F.field_modulo q prime_q)
            (@ModularArithmeticTheorems.F.eq_dec q))
         (@CompleteEdwardsCurve.E.mul Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params) b SHA512 c n l B Eenc Senc (@ed25519 SHA512 B_order_l ) Erep ERepEnc SRep SC25519.SRepDecModL
         SRepERepMul SRepEnc SC25519.SRepAdd SC25519.SRepMul ERepB SC25519.SRepDecModLShort.

Let sign_correct : forall pk sk {mlen} (msg:Word.word mlen), sign pk sk _ msg = EdDSA.sign pk sk msg :=
  @sign_correct
      (* E := *) E
      (* Eeq := *) CompleteEdwardsCurveTheorems.E.eq
      (* Eadd := *) CompleteEdwardsCurve.E.add
      (* Ezero := *) CompleteEdwardsCurve.E.zero
      (* Eopp := *) CompleteEdwardsCurveTheorems.E.opp
      (* EscalarMult := *) CompleteEdwardsCurve.E.mul
      (* b := *) b
      (* H := *) SHA512
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) (ed25519 B_order_l)
      (* Erep := *) Erep
      (* ErepEq := *) ExtendedCoordinates.Extended.eq
      (* ErepAdd := *) ErepAdd
      (* ErepId := *) ExtendedCoordinates.Extended.zero
      (* ErepOpp := *) ExtendedCoordinates.Extended.opp
      (* Agroup := *) ExtendedCoordinates.Extended.extended_group
      (* EToRep := *) EToRep
      (* Ahomom := *) Ahomom
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) ERepEnc_correct
      (* Proper_ERepEnc := *) Proper_ERepEnc
      (* SRep := *) SRep
      (* SRepEq := *) SC25519.SRepEq (*(Tuple.fieldwise Logic.eq)*)
      (* H0 := *) SC25519.SRepEquiv (* Tuple.Equivalence_fieldwise*)
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) SC25519.SRepDecModL
      (* SRepDecModL_correct := *) SC25519.SRepDecModL_Correct
      (* SRepERepMul := *) SRepERepMul
      (* SRepERepMul_correct := *) SRepERepMul_correct
      (* Proper_SRepERepMul := *) Proper_SRepERepMul
      (* SRepEnc := *) _
      (* SRepEnc_correct := *) SRepEnc_correct
      (* Proper_SRepEnc := *) _
      (* SRepAdd := *) SC25519.SRepAdd
      (* SRepAdd_correct := *) SC25519.SRepAdd_Correct
      (* Proper_SRepAdd := *) SC25519.SRepAdd_Proper
      (* SRepMul := *) SC25519.SRepMul
      (* SRepMul_correct := *) SC25519.SRepMul_Correct
      (* Proper_SRepMul := *) SC25519.SRepMul_Proper
      (* ErepB := *) ERepB
      (* ErepB_correct := *) ERepB_correct
      (* SRepDecModLShort := *) SC25519.SRepDecModLShort
      (* SRepDecModLShort_correct := *) SC25519.SRepDecModLShort_Correct
.
Definition Fsqrt_minus1 := Eval vm_compute in ModularBaseSystem.decode (GF25519.sqrt_m1).
Definition Fsqrt := PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1.

(* MOVE : maybe make a Pre file for these bound_check things? *)
Lemma bound_check_255_helper x y : (0 <= x)%Z -> (BinInt.Z.to_nat x < 2^y <-> (x < 2^(Z.of_nat y))%Z).
Proof.
  intros.
  rewrite <-(Znat.Nat2Z.id 2) at 1.
  rewrite ZUtil.Z.pow_Z2N_Zpow by omega.
  rewrite <- Znat.Z2Nat.inj_lt by auto with zarith.
  reflexivity.
Qed.
Lemma bound_check255 : BinInt.Z.to_nat GF25519.modulus < 2^255.
Proof.
  apply bound_check_255_helper; vm_compute; intuition congruence.
Qed.

Lemma bound_check256 : BinInt.Z.to_nat GF25519.modulus < 2^256.
Proof.
  apply bound_check_255_helper; vm_compute; intuition congruence.
Qed.

Definition Edec := (@PointEncodingPre.point_dec
               _ eq
               ModularArithmetic.F.zero
               ModularArithmetic.F.one
               ModularArithmetic.F.opp
               ModularArithmetic.F.add
               ModularArithmetic.F.sub
               ModularArithmetic.F.mul
               ModularArithmetic.F.div
               _
               Spec.Ed25519.a
               Spec.Ed25519.d
               _
               Fsqrt
               (PointEncoding.Fencoding
                  (two_lt_m := GF25519.modulus_gt_2)
                  (bound_check := bound_check255))
               Spec.Ed25519.sign).

(* MOVE : pre-Specific (general SC files?) *)
Definition Sdec : Word.word b -> option (ModularArithmetic.F.F l) :=
 fun w =>
 let z := (BinIntDef.Z.of_N (Word.wordToN w)) in
 if ZArith_dec.Z_lt_dec z l
 then Some (ModularArithmetic.F.of_Z l z) else None.

(* MOVE: same place as Sdec *)
Lemma eq_enc_S_iff : forall (n_ : Word.word b) (n : ModularArithmetic.F.F l),
 Senc n = n_ <-> Sdec n_ = Some n.
Proof.
  assert (0 < Ed25519.l)%Z as l_pos by (cbv; congruence).
  intros.
  pose proof (ModularArithmeticTheorems.F.to_Z_range n l_pos).
  unfold Senc, Fencode, Sdec; intros;
    split; break_match; intros; inversion_option; subst; f_equal;
  repeat match goal with
         | |- _ => rewrite !WordUtil.wordToN_NToWord_idempotent in *
             by (apply N.ZToN_NPow2_lt; split; try omega; eapply Z.lt_le_trans;
                 [ intuition eassumption | ]; cbv; congruence)
         | |- _ => rewrite WordUtil.NToWord_wordToN
         | |- _ => rewrite Z2N.id in * by omega
         | |- _ => rewrite N2Z.id in * by omega
         | |- _ => rewrite Z.mod_small by (split; try omega; apply N2Z.is_nonneg)
         | |- _ => rewrite ModularArithmeticTheorems.F.of_Z_to_Z in *
         | |- _ => rewrite @ModularArithmeticTheorems.F.to_Z_of_Z in *
         | |- _ => reflexivity
         | |- _ => omega
         end.
Qed.

(* MOVE : same place as Sdec *)
Definition SRepDec : Word.word b -> option SRep := fun w => option_map ModularArithmetic.F.to_Z (Sdec w).

(* MOVE : same place as Sdec *)
Lemma SRepDec_correct : forall w : Word.word b,
 @Option.option_eq SRep SC25519.SRepEq
   (@option_map (ModularArithmetic.F.F l) SRep S2Rep (Sdec w))
   (SRepDec w).
Proof.
  unfold SRepDec, S2Rep, SC25519.S2Rep; intros; reflexivity.
Qed.

Lemma extended_to_coord_from_twisted: forall pt,
  Tuple.fieldwise (n := 2) GF25519BoundedCommon.eq
     (extended_to_coord (ExtendedCoordinates.Extended.from_twisted pt))
      (CompleteEdwardsCurve.E.coordinates pt).
Proof.
  intros; cbv [extended_to_coord].
  rewrite ExtendedCoordinates.Extended.to_twisted_from_twisted.
  reflexivity.
Qed.

Lemma Fsqrt_minus1_correct :
 ModularArithmetic.F.mul Fsqrt_minus1 Fsqrt_minus1 =
 ModularArithmetic.F.opp
   (ModularArithmetic.F.of_Z GF25519.modulus 1).
Proof.
  replace (Fsqrt_minus1) with (ModularBaseSystem.decode (GF25519.sqrt_m1)) by reflexivity.
  rewrite <-ModularBaseSystemProofs.carry_mul_rep by reflexivity.
  rewrite <-ModularBaseSystemOpt.carry_mul_opt_correct
    with (k_ := GF25519.k_) (c_ := GF25519.c_) by reflexivity.
  rewrite <-GF25519.mul_correct.
  apply GF25519.sqrt_m1_correct.
Qed.

Section bounded_by_from_is_bounded.
  Local Arguments Z.sub !_ !_.
  Local Arguments Z.pow_pos !_ !_ / .
  (* TODO : automate?*)
  Lemma bounded_by_from_is_bounded
    : forall x, GF25519BoundedCommon.is_bounded x = true
                -> ModularBaseSystemProofs.bounded_by
                     x
                     (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
  Proof.
    intros x H.
    pose proof (GF25519BoundedCommon.is_bounded_to_nth_default _ H) as H'; clear H.
    unfold ModularBaseSystemProofs.bounded_by.
    intros n pf; specialize (H' n pf).
    match goal with
    | [ H : (0 <= ?y <= _)%Z |- (0 <= ?x < _)%Z ]
      => change y with x in H; generalize dependent x
    end.
    intros ? H'.
    split; [ omega | ].
    eapply Z.le_lt_trans; [ exact (proj2 H') | ].
    unfold ModularBaseSystemProofs.freeze_input_bounds, nth_default, GF25519.freeze_input_bound; simpl in *.
    repeat match goal with
           | [ |- context[nth_error _ ?n] ]
             => is_var n; destruct n; simpl
           end;
      try (vm_compute; reflexivity);
      try omega.
  Qed.
End bounded_by_from_is_bounded.

Lemma bounded_by_encode_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (ModularBaseSystem.encode x)
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
Proof.
  intros; apply bounded_by_from_is_bounded, GF25519BoundedCommon.encode_bounded.
Qed.

Lemma bounded_by_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (GF25519BoundedCommon.fe25519WToZ (GF25519BoundedCommon.proj1_fe25519W x))
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
Proof.
  intros; apply bounded_by_from_is_bounded, GF25519BoundedCommon.is_bounded_proj1_fe25519.
Qed.

Local Ltac prove_bounded_by :=
  repeat match goal with
         | [ |- ModularBaseSystemProofs.bounded_by _ _ ]
           => apply bounded_by_from_is_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.mulW (_, _))) = true ]
           => apply GF25519Bounded.mulW_correct_and_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.mulW_noinline (_, _))) = true ]
           => apply GF25519Bounded.mulW_correct_and_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.powW _ _)) = true ]
           => apply GF25519Bounded.powW_correct_and_bounded
         | [ |- context[GF25519BoundedCommon.fe25519WToZ (GF25519BoundedCommon.fe25519ZToW _)] ]
           => rewrite GF25519BoundedCommon.fe25519WToZ_ZToW
         | [ |- GF25519BoundedCommon.is_bounded (ModularBaseSystem.encode _) = true ]
           => apply GF25519BoundedCommon.encode_bounded
         end.

(* TODO : automate, make intermediate lemmas? This seems like it should not be so much pain *)
Lemma sqrt_correct' : forall x,
        GF25519BoundedCommon.eq
          (GF25519BoundedCommon.encode
             (PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1 (GF25519BoundedCommon.decode x)))
          (GF25519Bounded.sqrt x).
Proof.
  intros.
  cbv [GF25519BoundedCommon.eq].
  rewrite GF25519Bounded.sqrt_correct.
  cbv [GF25519Bounded.GF25519sqrt].
  cbv [LetIn.Let_In].
  repeat match goal with (* needed on Coq 8.4, should be the only default everywhere *)
           |- context[GF25519BoundedCommon.proj1_fe25519 (GF25519BoundedCommon.encode ?x)] =>
           rewrite (GF25519BoundedCommon.proj1_fe25519_encode x)
         end.
  rewrite GF25519.sqrt_correct, ModularBaseSystemOpt.sqrt_5mod8_opt_correct by reflexivity.
  cbv [ModularBaseSystem.eq].
  rewrite ModularBaseSystemProofs.encode_rep.
  symmetry.
  eapply @ModularBaseSystemProofs.sqrt_5mod8_correct;
    eauto using GF25519.freezePreconditions25519, ModularBaseSystemProofs.encode_rep, bounded_by_freeze, bounded_by_encode_freeze; prove_bounded_by; eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519;
      cbv [HList.hlistP HList.hlistP'] in *;
      repeat apply conj;
      [ reflexivity |
        try lazymatch goal with
    | |- appcontext[GF25519Bounded.powW ?a ?ch] =>
      let A := fresh "H" in
      destruct (GF25519Bounded.powW_correct_and_bounded ch a) as [A ?];
      [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW;
        hnf;
          solve [eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519]
        | cbv [Tuple.map List.map Tuple.on_tuple Tuple.from_list' Tuple.from_list Tuple.to_list Tuple.to_list'] in *;
          rewrite A;
          rewrite GF25519.pow_correct, ModularBaseSystemOpt.pow_opt_correct
            by reflexivity]
      end..].
  (*{ lazymatch goal with
    | |- appcontext[GF25519Bounded.powW ?a ?ch] =>
      let A := fresh "H" in
      destruct (GF25519Bounded.powW_correct_and_bounded ch a) as [A ?];
        [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW;
          hnf;
          solve [eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519]
        | cbv [Tuple.map List.map Tuple.on_tuple Tuple.from_list' Tuple.from_list Tuple.to_list Tuple.to_list'] in *;
          move A at bottom;
          rewrite A, !GF25519.pow_correct
            by reflexivity(*
          rewrite GF25519.pow_correct, ModularBaseSystemOpt.pow_opt_correct
            by reflexivity*)]
    end.
    About GF25519.pow_correct.

    cbv [GF25519BoundedCommon.is_bounded fst snd GF25519BoundedCommon.is_bounded_gen].

    cbv [Tuple.map2 Tuple.on_tuple2 Tuple.to_list GF25519.length_fe25519 Tuple.to_list' map2 GF25519BoundedCommon.bounds].
    rewrite ModularBaseSystemOpt.pow_opt_correct.
    rewrite GF25519.pow_correct.
    rewrite H.
    .
    SearchAbout GF25519Bounded.mulW.
    Set Printing Coercions.
    rewrite H.

    [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW by (eapply GF25519BoundedCommon.is_bounded_proj1_fe25519); reflexivity | ].
  unfold GF25519Bounded.mulW_noinline.
  match goal with
  | |- appcontext[GF25519Bounded.mulW ?a ?b] =>
    let A := fresh "H" in
    destruct (GF25519Bounded.mulW_correct_and_bounded a b) as [A ?];
      [ auto | auto | rewrite A]
  end.
  rewrite GF25519.mul_correct, ModularBaseSystemOpt.carry_mul_opt_correct by reflexivity.
  rewrite !H.
  rewrite GF25519.pow_correct.
  cbv [ModularBaseSystem.eq].
  rewrite ModularBaseSystemProofs.carry_mul_rep by reflexivity.
  rewrite ModularBaseSystemProofs.mul_rep by reflexivity.
  apply f_equal2;
  rewrite ModularBaseSystemOpt.pow_opt_correct; reflexivity.*)
Admitted.

(* TODO : move to GF25519BoundedCommon *)
Module GF25519BoundedCommon.
  Lemma decode_encode x: GF25519BoundedCommon.decode (GF25519BoundedCommon.encode x) = x.
  Proof.
    unfold GF25519BoundedCommon.encode, GF25519BoundedCommon.decode.
    rewrite GF25519BoundedCommon.proj1_fe25519_exist_fe25519.
    erewrite ModularBaseSystemProofs.rep_decode; eauto using ModularBaseSystemProofs.encode_rep.
  Qed.
End GF25519BoundedCommon.

Lemma sqrt_correct : forall x : ModularArithmetic.F.F q,
        GF25519BoundedCommon.eq
          (GF25519BoundedCommon.encode
             (PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1 x))
          (GF25519Bounded.sqrt (GF25519BoundedCommon.encode x)).
Proof.
  intros. pose proof sqrt_correct' (GF25519BoundedCommon.encode x) as H.
  rewrite GF25519BoundedCommon.decode_encode in H; exact H.
Qed.

Local Instance Proper_sqrt :
  Proper (GF25519BoundedCommon.eq ==> GF25519BoundedCommon.eq) GF25519Bounded.sqrt.
Proof.
  intros x y Hxy.
  rewrite <-(sqrt_correct' x); symmetry; rewrite <-(sqrt_correct' y); symmetry.
  eapply f_equal. eapply f_equal. eapply f_equal. rewrite Hxy. reflexivity.
Qed.

Lemma eq_enc_E_iff : forall (P_ : Word.word b) (P : E),
 Eenc P = P_ <->
 Option.option_eq CompleteEdwardsCurveTheorems.E.eq (Edec P_) (Some P).
Proof.
  cbv [Eenc].
  eapply (@PointEncoding.encode_point_decode_point_iff (b-1)); try (exact iff_equivalence || exact curve_params); [].
  intros.
  apply (@PrimeFieldTheorems.F.sqrt_5mod8_correct GF25519.modulus _ eq_refl Fsqrt_minus1 Fsqrt_minus1_correct).
  eexists.
  symmetry; eassumption.
Qed.

Axiom ERepDec : Word.word b -> option Erep.
Axiom ERepDec_correct : forall w : Word.word b,
 option_eq ExtendedCoordinates.Extended.eq (ERepDec w) (option_map EToRep (Edec w)).

Definition verify := @verify E b SHA512 B Erep ErepAdd
         (@ExtendedCoordinates.Extended.opp GF25519BoundedCommon.fe25519
            GF25519BoundedCommon.eq GF25519BoundedCommon.zero
            GF25519BoundedCommon.one GF25519Bounded.opp GF25519Bounded.add
            GF25519Bounded.sub GF25519Bounded.mul GF25519Bounded.inv
            GF25519BoundedCommon.div a d GF25519Bounded.field25519 twedprm_ERep
            (fun x y : GF25519BoundedCommon.fe25519 =>
             @ModularArithmeticTheorems.F.eq_dec GF25519.modulus
               (@ModularBaseSystem.decode GF25519.modulus GF25519.params25519
                  (GF25519BoundedCommon.proj1_fe25519 x))
               (@ModularBaseSystem.decode GF25519.modulus GF25519.params25519
                  (GF25519BoundedCommon.proj1_fe25519 y)))) EToRep ERepEnc ERepDec
         SRep SC25519.SRepDecModL SRepERepMul SRepDec.

Let verify_correct :
  forall {mlen : nat} (msg : Word.word mlen) (pk : Word.word b)
  (sig : Word.word (b + b)), verify _ msg pk sig = true <-> EdDSA.valid msg pk sig :=
  @verify_correct
      (* E := *) E
      (* Eeq := *) CompleteEdwardsCurveTheorems.E.eq
      (* Eadd := *) CompleteEdwardsCurve.E.add
      (* Ezero := *) CompleteEdwardsCurve.E.zero
      (* Eopp := *) CompleteEdwardsCurveTheorems.E.opp
      (* EscalarMult := *) CompleteEdwardsCurve.E.mul
      (* b := *) b
      (* H := *) SHA512
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) (ed25519 B_order_l)
      (* Proper_Eenc := *) (PointEncoding.Proper_encode_point (b:=b-1))
      (* Edec := *) Edec
      (* eq_enc_E_iff := *) eq_enc_E_iff
      (* Sdec := *) Sdec
      (* eq_enc_S_iff := *) eq_enc_S_iff
      (* Erep := *) Erep
      (* ErepEq := *) ExtendedCoordinates.Extended.eq
      (* ErepAdd := *) ErepAdd
      (* ErepId := *) ExtendedCoordinates.Extended.zero
      (* ErepOpp := *) ExtendedCoordinates.Extended.opp
      (* Agroup := *) ExtendedCoordinates.Extended.extended_group
      (* EToRep := *) EToRep
      (* Ahomom := *) Ahomom
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) ERepEnc_correct
      (* Proper_ERepEnc := *) Proper_ERepEnc
      (* ERepDec := *) ERepDec
      (* ERepDec_correct := *) ERepDec_correct
      (* SRep := *) SRep (*(Tuple.tuple (Word.word 32) 8)*)
      (* SRepEq := *) SC25519.SRepEq (* (Tuple.fieldwise Logic.eq)*)
      (* H0 := *) SC25519.SRepEquiv (* Tuple.Equivalence_fieldwise*)
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) SC25519.SRepDecModL
      (* SRepDecModL_correct := *) SC25519.SRepDecModL_Correct
      (* SRepERepMul := *) SRepERepMul
      (* SRepERepMul_correct := *) SRepERepMul_correct
      (* Proper_SRepERepMul := *) _
      (* SRepDec := *) SRepDec
      (* SRepDec_correct := *) SRepDec_correct
.

(* TODO : make a new file for the stuff below *)

Lemma Fhomom_inv_zero :
  GF25519BoundedCommon.eq
    (GF25519BoundedCommon.encode
       (@ModularArithmetic.F.inv GF25519.modulus
                                 (ModularArithmetic.F.of_Z GF25519.modulus 0)))
    (GF25519Bounded.inv GF25519BoundedCommon.zero).
Proof.
  vm_decide_no_check.
Qed.

Import ModularArithmetic.
Module Spec.
  Module X25519.
    Definition a : F q := F.of_Z _ 486662.
    Definition a24 : F q := ((a - F.of_Z _ 2) / F.of_Z _ 4)%F.
  End X25519.
End Spec.

Section X25519Constants.
  Import GF25519BoundedCommon.
  Definition a24' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode Spec.X25519.a24.
  Definition a24 : GF25519BoundedCommon.fe25519 :=
    Eval cbv [a24' GF25519BoundedCommon.fe25519_word64ize GF25519BoundedCommon.word64ize andb GF25519BoundedCommon.opt.word64ToZ GF25519BoundedCommon.opt.word64ize GF25519BoundedCommon.opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (GF25519BoundedCommon.fe25519_word64ize a24').
  Lemma a24_correct : GF25519BoundedCommon.eq
                        (GF25519BoundedCommon.encode Spec.X25519.a24)
                        (a24).
  Proof. vm_decide_no_check. Qed.
End X25519Constants.

Definition x25519 (n:N) (x:GF25519BoundedCommon.fe25519) : GF25519BoundedCommon.fe25519 :=
  @MxDH.montladder GF25519BoundedCommon.fe25519 GF25519BoundedCommon.zero
                   GF25519BoundedCommon.one GF25519Bounded.add GF25519Bounded.sub
                   GF25519Bounded.mul GF25519Bounded.inv a24
                   (fun (H : bool)
                        (H0
                           H1 : GF25519BoundedCommon.fe25519 * GF25519BoundedCommon.fe25519)
                    => if H then (H1, H0) else (H0, H1)) 255 (N.testbit_nat n) x.

Definition x25519_correct' n x :
  GF25519BoundedCommon.eq
    (GF25519BoundedCommon.encode (MxDH.montladder 255 (N.testbit_nat n) x))
    (MxDH.montladder 255 (N.testbit_nat n) (GF25519BoundedCommon.encode x)) :=
  MxDHRepChange
      (field:=PrimeFieldTheorems.F.field_modulo GF25519.modulus)
      (impl_field:=GF25519Bounded.field25519)
      (homomorphism_inv_zero:=Fhomom_inv_zero)
      (homomorphism_a24:=a24_correct)
      (Fcswap_correct:= fun _ _ _ => (reflexivity _))
      (Kcswap_correct:= fun _ _ _ => (reflexivity _))
      (tb2_correct:=fun _ => (reflexivity _))
      255 _.

Let three_correct := (@x25519_correct', @sign_correct, @verify_correct).
Print Assumptions three_correct.
(* [B_order_l] is proven above in this file, just replace Admitted with Qed, start the build and wait for a couple of hours *)
(* [prime_q] and [prime_l] have been proven in Coq exactly as stated here, see <https://github.com/andres-erbsen/safecurves-primes> for the (lengthy) proofs *)
(* [SHA512] is outside the scope of this project, but its type is satisfied by [(fun n bits => Word.wzero 512)] *)
Definition __check_SHA512_type := [(fun n bits => Word.wzero 512); SHA512].
