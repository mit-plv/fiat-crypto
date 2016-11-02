Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Option.
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

Context {H: forall n : nat, Word.word n -> Word.word (b + b)}.

Definition feSign (f :  GF25519BoundedCommon.fe25519) : bool :=
  let x := GF25519Bounded.freeze f in
  let '(x9, x8, x7, x6, x5, x4, x3, x2, x1, x0) := (x : GF25519.fe25519) in
  BinInt.Z.testbit x0 0.

Definition freezePre :
  @ModularBaseSystemProofs.FreezePreconditions
    GF25519.modulus GF25519.params25519 GF25519.int_width.
Proof.
  pose proof GF25519.freezePreconditions25519 as A.
  inversion A;  econstructor; eauto.
Defined.

Definition a : GF25519BoundedCommon.fe25519 :=
  Eval vm_compute in GF25519BoundedCommon.encode a.
Definition d : GF25519BoundedCommon.fe25519 :=
  Eval vm_compute in GF25519BoundedCommon.encode d.
Definition twice_d : GF25519BoundedCommon.fe25519 :=
  Eval vm_compute in (GF25519Bounded.add d d).
Lemma phi_a : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.a) a.
Proof. reflexivity. Qed.
Lemma phi_d : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.d) d.
Proof. vm_decide_no_check. Qed.

Let Erep := (@ExtendedCoordinates.Extended.point
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

Let EToRep :=
  PointEncoding.point_phi
    (Kfield := GF25519Bounded.field25519)
    (phi_homomorphism := GF25519Bounded.homomorphism_F25519_encode)
    (Kpoint := Erep)
    (phi_a := phi_a)
    (phi_d := phi_d)
    (Kcoord_to_point := ExtendedCoordinates.Extended.from_twisted (prm := twedprm_ERep) (field := GF25519Bounded.field25519)).

Let ZNWord sz x := Word.NToWord sz (BinInt.Z.to_N x).
Let WordNZ {sz} (w : Word.word sz) := BinInt.Z.of_N (Word.wordToN w).

(* TODO :
   GF25519.pack does most of the work here, but the spec currently talks
   about 256-bit words and [pack] makes a sequence of short (in this case
   32- and 31-bit) Zs. We should either automate this transformation or change
   the spec.
 *)

Definition feEnc (x : GF25519BoundedCommon.fe25519) : Word.word 255 :=
  let '(x7, x6, x5, x4, x3, x2, x1, x0) :=
      (GF25519BoundedCommon.proj1_wire_digits (GF25519Bounded.pack (GF25519Bounded.freeze x))) in
  Word.combine (ZNWord 32 x0)
    (Word.combine (ZNWord 32 x1)
      (Word.combine (ZNWord 32 x2)
        (Word.combine (ZNWord 32 x3)
          (Word.combine (ZNWord 32 x4)
            (Word.combine (ZNWord 32 x5)
              (Word.combine (ZNWord 32 x6) (ZNWord 31 x7))))))).
Check GF25519Bounded.unpack.
Print GF25519BoundedCommon.wire_digits.
Eval compute in GF25519.wire_widths.
Eval compute in (Tuple.from_list 8 GF25519.wire_widths _).

(** TODO(jadep or andreser, from jgross): Is the reversal on the words passed in correct? *)
Definition feDec (w : Word.word 255) : option GF25519BoundedCommon.fe25519 :=
  let w0 := Word.split1 32 _ w in
  let a0 := Word.split2 32 _ w in
  let w1 := Word.split1 32 _ a0 in
  let a1 := Word.split2 32 _ a0 in
  let w2 := Word.split1 32 _ a1 in
  let a2 := Word.split2 32 _ a1 in
  let w3 := Word.split1 32 _ a2 in
  let a3 := Word.split2 32 _ a2 in
  let w4 := Word.split1 32 _ a3 in
  let a4 := Word.split2 32 _ a3 in
  let w5 := Word.split1 32 _ a4 in
  let a5 := Word.split2 32 _ a4 in
  let w6 := Word.split1 32 _ a5 in
  let w7 := Word.split2 32 _ a5 in
  let result := (GF25519Bounded.unpack (GF25519BoundedCommon.word31_to_unbounded_word w7,
                                        GF25519BoundedCommon.word32_to_unbounded_word w6,
                                        GF25519BoundedCommon.word32_to_unbounded_word w5,
                                        GF25519BoundedCommon.word32_to_unbounded_word w4,
                                        GF25519BoundedCommon.word32_to_unbounded_word w3,
                                        GF25519BoundedCommon.word32_to_unbounded_word w2,
                                        GF25519BoundedCommon.word32_to_unbounded_word w1,
                                        GF25519BoundedCommon.word32_to_unbounded_word w0)) in
  if GF25519BoundedCommon.w64eqb (GF25519Bounded.ge_modulus result) (GF25519BoundedCommon.ZToWord64 1)
  then None else (Some result).

Let ERepEnc :=
  (PointEncoding.Kencode_point
         (Ksign := feSign)
         (Kenc := feEnc)
         (Kpoint := Erep)
         (Kpoint_to_coord :=  fun P => CompleteEdwardsCurve.E.coordinates
                                (ExtendedCoordinates.Extended.to_twisted P (field:=GF25519Bounded.field25519)))
  ).

Let SRep := SC25519.SRep.
Let S2Rep := SC25519.S2Rep.
(*Let SRep := Tuple.tuple (Word.word 32) 8.

Let S2Rep := fun (x : ModularArithmetic.F.F l) =>
               Tuple.map (ZNWord 32)
               (Tuple.from_list_default (BinInt.Z.of_nat 0) 8
                  (Pow2Base.encodeZ
                  (List.repeat (BinInt.Z.of_nat 32) 8)
                  (ModularArithmetic.F.to_Z x))).*)

Lemma eq_a_minus1 : GF25519BoundedCommon.eq a (GF25519Bounded.opp GF25519BoundedCommon.one).
Proof. vm_decide. Qed.

Let ErepAdd :=
  (@ExtendedCoordinates.Extended.add _ _ _ _ _ _ _ _ _ _
                                     a d GF25519Bounded.field25519 twedprm_ERep _
                                     eq_a_minus1 twice_d (eq_refl _) ).

Local Coercion Z.of_nat : nat >-> Z.
Let ERepSel : bool -> Erep -> Erep -> Erep := fun b x y => if b then y else x.

Local Existing Instance ExtendedCoordinates.Extended.extended_group.

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

Module N.
  Lemma size_le a b : (a <= b -> N.size a <= N.size b)%N.
  Proof.
    destruct (dec (a=0)%N), (dec (b=0)%N); subst; auto using N.le_0_l.
    { destruct a; auto. }
    { rewrite !N.size_log2 by assumption.
      rewrite <-N.succ_le_mono.
      apply N.log2_le_mono. }
  Qed.

  Lemma le_to_nat a b : (a <= b)%N <-> (N.to_nat a <= N.to_nat b)%nat.
  Proof.
    rewrite <-N.lt_succ_r.
    rewrite <-Nat.lt_succ_r.
    rewrite <-Nnat.N2Nat.inj_succ.
    rewrite <-NatUtil.Nat2N_inj_lt.
    rewrite !Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Lemma size_nat_le a b : (a <= b)%N -> (N.size_nat a <= N.size_nat b)%nat.
  Proof.
    rewrite !IterAssocOp.Nsize_nat_equiv.
    rewrite <-le_to_nat.
    apply size_le.
  Qed.
End N.

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
      rewrite Nsize_nat_equiv.
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

Lemma ZToN_NPow2_lt : forall z n, (0 <= z < 2 ^ Z.of_nat n)%Z ->
                                  (Z.to_N z < Word.Npow2 n)%N.
Proof.
  intros.
  apply WordUtil.bound_check_nat_N.
  apply Znat.Nat2Z.inj_lt.
  rewrite Znat.Z2Nat.id by omega.
  rewrite ZUtil.Z.pow_Zpow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  omega.
Qed.

Lemma combine_ZNWord : forall sz1 sz2 z1 z2,
  (0 <= Z.of_nat sz1)%Z ->
  (0 <= Z.of_nat sz2)%Z ->
  (0 <= z1 < 2 ^ (Z.of_nat sz1))%Z ->
  (0 <= z2 < 2 ^ (Z.of_nat sz2))%Z ->
  Word.combine (ZNWord sz1 z1) (ZNWord sz2 z2) =
    ZNWord (sz1 + sz2) (Z.lor z1 (Z.shiftl z2 sz1)).
Proof.
  cbv [ZNWord]; intros.
  rewrite !Word.NToWord_nat.
  match goal with |- ?a = _ => rewrite <- (Word.natToWord_wordToNat a) end.
  rewrite WordUtil.wordToNat_combine.
  rewrite !Word.wordToNat_natToWord_idempotent by (rewrite Nnat.N2Nat.id; auto using ZToN_NPow2_lt).
  f_equal.
  rewrite ZUtil.Z.lor_shiftl by auto.
  rewrite !Z_N_nat.
  rewrite Znat.Z2Nat.inj_add by (try apply Z.shiftl_nonneg; omega).
  f_equal.
  rewrite Z.shiftl_mul_pow2 by auto.
  rewrite Znat.Z2Nat.inj_mul by omega.
  rewrite <-ZUtil.Z.pow_Z2N_Zpow by omega.
  rewrite Nat.mul_comm.
  f_equal.
Qed.

Lemma nth_default_B_compat : forall i,
  (nth_default 0 PseudoMersenneBaseParams.limb_widths i <
   GF25519.int_width)%Z.
Proof.
    assert (@ModularBaseSystemProofs.FreezePreconditions
                 GF25519.modulus GF25519.params25519
                 GF25519.int_width) by
     (let A := fresh "H" in
            pose proof GF25519.freezePreconditions25519 as A;
            inversion A;  econstructor; eauto).
    intros.
    destruct (lt_dec i (length PseudoMersenneBaseParams.limb_widths)).
    { apply ModularBaseSystemProofs.B_compat.
      rewrite nth_default_eq.
      auto using nth_In. }
    { rewrite nth_default_out_of_bounds by omega.
      cbv; congruence. }
Qed.

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
    assert (@ModularBaseSystemProofs.FreezePreconditions
                 GF25519.modulus GF25519.params25519
                 GF25519.int_width)
      by (let A := fresh "H" in
            pose proof GF25519.freezePreconditions25519 as A;
            inversion A;  econstructor; eauto).
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
          apply Z.lt_le_incl, nth_default_B_compat. }
      { transitivity (2 ^ (Z.pred GF25519.int_width))%Z.
          { apply Z.pow_le_mono; try omega.
          apply Z.lt_le_pred.
          apply nth_default_B_compat. }
          { rewrite Z.shiftr_div_pow2 by (auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg).
          rewrite <- Z.pow_sub_r by (try omega; split; auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg, Z.lt_le_incl, nth_default_B_compat).
          replace (2 ^ GF25519.int_width)%Z
          with (2 ^ (Z.pred GF25519.int_width + 1))%Z by (f_equal; omega).
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

Lemma lor_shiftl_bounds : forall x y n m,
  (0 <= n)%Z -> (0 <= m)%Z ->
  (0 <= x < 2 ^ m)%Z ->
  (0 <= y < 2 ^ n)%Z ->
  (0 <= Z.lor y (Z.shiftl x n) < 2 ^ (n + m))%Z.
Proof.
  intros.
  apply ZUtil.Z.lor_range.
  { split; try omega.
    apply Z.lt_le_trans with (m := (2 ^ n)%Z); try omega.
    apply Z.pow_le_mono_r; omega. }
  { rewrite Z.shiftl_mul_pow2 by omega.
    rewrite Z.pow_add_r by omega.
    split; ZUtil.Z.zero_bounds.
    rewrite Z.mul_comm.
    apply Z.mul_lt_mono_pos_l; omega. }
Qed.

Lemma feEnc_correct : forall x,
    PointEncoding.Fencode x = feEnc (GF25519BoundedCommon.encode x).
Proof.
  cbv [feEnc PointEncoding.Fencode]; intros.
  rewrite GF25519Bounded.pack_correct, GF25519Bounded.freeze_correct.
  rewrite GF25519BoundedCommon.proj1_fe25519_encode.
  match goal with |- appcontext [GF25519.pack ?x] =>
                  remember (GF25519.pack x) end.
  transitivity (ZNWord 255 (Pow2Base.decode_bitwise GF25519.wire_widths (Tuple.to_list 8 w))).
  { cbv [ZNWord].
    do 2 apply f_equal.
    subst w.
    pose proof freezePre.
    match goal with
      |- appcontext [GF25519.freeze ?x ] =>
      let A := fresh "H" in
      pose proof (ModularBaseSystemProofs.freeze_decode x) as A end.
    pose proof (ge_modulus_freeze x); pose proof (bounded_freeze x).
    repeat match goal with
           | |- _ => rewrite Tuple.to_list_from_list
           | |- _ => progress cbv [ModularBaseSystem.pack ModularBaseSystemList.pack]
           | |- _ => progress rewrite ?GF25519.pack_correct, ?GF25519.freeze_correct,
             ?ModularBaseSystemOpt.pack_correct,
             ?ModularBaseSystemOpt.freeze_opt_correct by reflexivity
           | |- _ => rewrite Pow2BaseProofs.decode_bitwise_spec
               by (auto using Conversion.convert_bounded,
                   Conversion.length_convert; cbv [In GF25519.wire_widths];
                   intuition omega)
           | H : length ?ls = ?n |- appcontext [Tuple.from_list_default _ ?n ?ls] =>
               rewrite Tuple.from_list_default_eq with (pf := H)
           | |- appcontext [Tuple.from_list_default _ ?n ?ls] =>
               assert (length ls = n) by
               (rewrite ModularBaseSystemListProofs.length_freeze;
               try rewrite Tuple.length_to_list; reflexivity)
           | |- _ => rewrite <-Conversion.convert_correct by auto
           end.
      rewrite <-ModularBaseSystemProofs.Fdecode_decode_mod with (us := ModularBaseSystem.encode x) by apply ModularBaseSystemProofs.encode_rep.
      match goal with H : _ = ?b |- ?b = _ => rewrite <-H; clear H end.
      cbv [ModularBaseSystem.freeze].
      rewrite Tuple.to_list_from_list.
      rewrite Z.mod_small by (apply ModularBaseSystemListProofs.ge_modulus_spec; auto; cbv; congruence).
      f_equal. }
  { assert (Pow2Base.bounded GF25519.wire_widths (Tuple.to_list 8 w)).
    { subst w.
      rewrite GF25519.pack_correct, ModularBaseSystemOpt.pack_correct.
      cbv [ModularBaseSystem.pack ModularBaseSystemList.pack].
      rewrite Tuple.to_list_from_list.
      apply Conversion.convert_bounded. }
    { destruct w;
      repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
      cbv [Tuple.to_list Tuple.to_list'] in *.
      rewrite Pow2BaseProofs.bounded_iff in *.
      (* TODO : Is there a better way to do this? *)
      pose proof (H0 0).
      pose proof (H0 1).
      pose proof (H0 2).
      pose proof (H0 3).
      pose proof (H0 4).
      pose proof (H0 5).
      pose proof (H0 6).
      pose proof (H0 7).
      clear H0.
      cbv [GF25519.wire_widths nth_default nth_error value] in *.
      repeat rewrite combine_ZNWord by (rewrite ?Znat.Nat2Z.inj_add; simpl Z.of_nat; repeat apply lor_shiftl_bounds; omega).
      cbv - [ZNWord Z.lor Z.shiftl].
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.
      reflexivity. } }
Qed.

Lemma initial_bounds : forall x n,
  n < length PseudoMersenneBaseParams.limb_widths ->
  (0 <=
   nth_default 0
     (Tuple.to_list (length PseudoMersenneBaseParams.limb_widths)
        (GF25519BoundedCommon.proj1_fe25519 x)) n <
   2 ^ GF25519.int_width -
   (if eq_nat_dec n 0%nat
    then 0
    else
     Z.shiftr (2 ^ GF25519.int_width)
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
  pose proof freezePre.
  match goal with H : _ = GF25519.freeze ?u |- _ =>
                  let A := fresh "H" in let B := fresh "H" in
                  pose proof (ModularBaseSystemProofs.freeze_rep u x) as A;
                    match type of A with ?P -> _ => assert P as B by apply ModularBaseSystemProofs.encode_rep end;
                    specialize (A B); clear B
  end.
  to_MBSfreeze Heqf.
  rewrite <-Heqf in *.
  cbv [ModularBaseSystem.rep ModularBaseSystem.decode ModularBaseSystemList.decode] in *.
  rewrite <-H1.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
  rewrite Z.mod_small; [ reflexivity | ].
  pose proof (minrep_freeze x).
  apply ModularBaseSystemListProofs.ge_modulus_spec;
    try solve [inversion H0; auto using Tuple.length_to_list];
    subst f; intuition auto.
  Grab Existential Variables.
  apply Tuple.length_to_list.
Qed.


Local Instance Proper_feSign : Proper (GF25519BoundedCommon.eq ==> eq) feSign.
Proof.
  repeat intro; cbv [feSign].
  rewrite !GF25519Bounded.freeze_correct.
  repeat match goal with |- appcontext[GF25519.freeze ?x] =>
                         remember (GF25519.freeze x) end.
  assert (Tuple.fieldwise (n := 10) eq f f0).
  { pose proof freezePre.
    match goal with H1 : _ = GF25519.freeze ?u,
                    H2 : _ = GF25519.freeze ?v |- _ =>
    let A := fresh "H" in
    let HP := fresh "H" in
    let HQ := fresh "H" in
        pose proof (ModularBaseSystemProofs.freeze_canonical
                    (freeze_pre := freezePre) u v _ _ eq_refl eq_refl);
        match type of A with ?P -> ?Q -> _ =>
                            assert P as HP by apply initial_bounds;
                                assert Q as HQ by apply initial_bounds end;
        specialize (A HP HQ); clear HP HQ end.
    cbv [ModularBaseSystem.eq] in *.
    to_MBSfreeze Heqf0.
    to_MBSfreeze Heqf.
    subst.
    apply H2.
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

Lemma Proper_feEnc : Proper (GF25519BoundedCommon.eq ==> eq) feEnc.
Proof.
  pose proof freezePre.
  repeat intro; cbv [feEnc].
  rewrite !GF25519Bounded.pack_correct, !GF25519Bounded.freeze_correct.
  rewrite !GF25519.freeze_correct, !ModularBaseSystemOpt.freeze_opt_correct
    by (rewrite ?Tuple.length_to_list; reflexivity).
  cbv [GF25519BoundedCommon.eq ModularBaseSystem.eq] in *.
  match goal with
  H : ModularBaseSystem.decode ?x = ModularBaseSystem.decode ?y |- _ =>
  let A := fresh "H" in
  let HP := fresh "H" in
  let HQ := fresh "H" in
    pose proof (ModularBaseSystemProofs.freeze_canonical
                (freeze_pre := freezePre)  x y (ModularBaseSystem.decode x)
                (ModularBaseSystem.decode y) eq_refl eq_refl);
      match type of A with ?P -> ?Q -> _ =>
                           assert P as HP by apply initial_bounds;
                             assert Q as HQ by apply initial_bounds end;
      specialize (A HP HQ); clear HP HQ; apply A in H
  end.
  repeat match goal with |- appcontext [GF25519.pack ?x] => remember (GF25519.pack x) end.
  match goal with x : GF25519.wire_digits, y : GF25519.wire_digits |- _ =>
                  assert (Tuple.fieldwise (n := length GF25519.wire_widths) eq x y) as Heqxy end.
  { subst.
    rewrite !convert_freezes.
    erewrite !Tuple.from_list_default_eq.
    rewrite !Tuple.from_list_to_list.
    apply Proper_pack.
    assumption. }
  { cbv [length GF25519.wire_digits] in *.
    repeat match goal with p : (_ * _)%type |- _ => destruct p end.
    cbv [GF25519.wire_widths length Tuple.fieldwise Tuple.fieldwise' fst snd] in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
      subst; reflexivity. }
  Grab Existential Variables.
  rewrite Tuple.length_to_list; reflexivity.
  rewrite Tuple.length_to_list; reflexivity.
Qed.

Lemma ERepEnc_correct P : Eenc P = ERepEnc (EToRep P).
Proof.
  cbv [Eenc ERepEnc EToRep sign Fencode].
  transitivity (PointEncoding.encode_point (b := 255) P);
    [ | eapply (PointEncoding.Kencode_point_correct
           (Ksign_correct := feSign_correct)
           (Kenc_correct := feEnc_correct)
           (Proper_Ksign := Proper_feSign)
           (Proper_Kenc := Proper_feEnc))
    ].
  reflexivity.
  Grab Existential Variables.
  intros.
  eapply @CompleteEdwardsCurveTheorems.E.Proper_coordinates.
  { apply GF25519Bounded.field25519. }
  { exact _. }
  { apply ExtendedCoordinates.Extended.to_twisted_from_twisted. }
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

Let SRepEnc : SRep -> Word.word b := (fun x => Word.NToWord _ (Z.to_N x)).

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

(** TODO: How do we speed up vm_compute here?  I think it's spending most of it's time rechecking boundedness... *)
Definition ERepB_value := Eval vm_compute in (proj1_sig (EToRep B)).
Let ERepB : Erep.
  exists (eta4 ERepB_value).
  cbv [GF25519BoundedCommon.eq ModularBaseSystem.eq Pre.onCurve].
  vm_decide_no_check.
Defined.

Lemma ERepB_value_correct : ERepB_value = proj1_sig (EToRep B).
Proof. vm_cast_no_check (eq_refl ERepB_value). Qed.

Let ERepB_correct : ExtendedCoordinates.Extended.eq (field:=GF25519Bounded.field25519) ERepB (EToRep B).
  pose proof ERepB_value_correct; destruct (EToRep B).
  cbv [proj1_sig] in *; subst.
  vm_decide.
Qed.

Lemma B_order_l : CompleteEdwardsCurveTheorems.E.eq
              (CompleteEdwardsCurve.E.mul (Z.to_nat l) B)
              CompleteEdwardsCurve.E.zero.
Proof.
  apply ERep_eq_E.
  rewrite NERepMul_correct; rewrite (Z_nat_N l).
  2:vm_decide.
  apply dec_bool.
  vm_cast_no_check (eq_refl true).
Admitted.
(* Time Qed. (* Finished transaction in 1646.167 secs (1645.753u,0.339s) (successful) *) *)

Let sign := @EdDSARepChange.sign E
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
            Spec.Ed25519.d curve_params) b H c n l B Eenc Senc (@ed25519 H) Erep ERepEnc SRep SC25519.SRepDecModL
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
      (* H := *) H
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) ed25519
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
      (* Proper_ERepEnc := *) (PointEncoding.Proper_Kencode_point (Kpoint_eq_correct := ext_eq_correct) (Proper_Kenc := Proper_feEnc))
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

Let Edec := (@PointEncodingPre.point_dec
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

Let Sdec : Word.word b -> option (ModularArithmetic.F.F l) :=
 fun w =>
 let z := (BinIntDef.Z.of_N (Word.wordToN w)) in
 if ZArith_dec.Z_lt_dec z l
 then Some (ModularArithmetic.F.of_Z l z) else None.

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
             by (apply ZToN_NPow2_lt; split; try omega; eapply Z.lt_le_trans;
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

Let SRepDec : Word.word b -> option SRep := fun w => option_map ModularArithmetic.F.to_Z (Sdec w).

Lemma SRepDec_correct : forall w : Word.word b,
 @Option.option_eq SRep SC25519.SRepEq
   (@option_map (ModularArithmetic.F.F l) SRep S2Rep (Sdec w))
   (SRepDec w).
Proof.
  unfold SRepDec, S2Rep, SC25519.S2Rep; intros; reflexivity.
Qed.

Let ERepDec :=
    (@PointEncoding.Kdecode_point
         _
         GF25519BoundedCommon.fe25519
         GF25519BoundedCommon.eq
         GF25519BoundedCommon.zero
         GF25519BoundedCommon.one
         GF25519Bounded.opp
         GF25519Bounded.add
         GF25519Bounded.sub
         GF25519Bounded.mul
         GF25519BoundedCommon.div
         _ a d feSign
         _ (ExtendedCoordinates.Extended.from_twisted
              (field := GF25519Bounded.field25519)
              (prm := twedprm_ERep)
           )
         feDec GF25519Bounded.sqrt
    ).

Lemma extended_to_coord_from_twisted: forall pt,
  Tuple.fieldwise (n := 2) GF25519BoundedCommon.eq
     (extended_to_coord (ExtendedCoordinates.Extended.from_twisted pt))
      (CompleteEdwardsCurve.E.coordinates pt).
Proof.
  intros; cbv [extended_to_coord].
  rewrite ExtendedCoordinates.Extended.to_twisted_from_twisted.
  reflexivity.
Qed.

Local Instance Proper_sqrt :
  Proper (GF25519BoundedCommon.eq ==> GF25519BoundedCommon.eq) GF25519Bounded.sqrt.
Admitted.

Lemma WordNZ_split1 : forall {n m} w,
    Z.of_N (Word.wordToN (Word.split1 n m w)) = ZUtil.Z.pow2_mod (Z.of_N (Word.wordToN w)) n.
Admitted.

Lemma WordNZ_split2 : forall {n m} w,
    Z.of_N (Word.wordToN (Word.split2 n m w)) = Z.shiftr (Z.of_N (Word.wordToN w)) n.
Admitted.

Lemma WordNZ_range : forall {n} B w,
  (2 ^ Z.of_nat n <= B)%Z ->
  (0 <= Z.of_N (@Word.wordToN n w) < B)%Z.
Admitted.

Lemma WordNZ_range_mono : forall {n} m w,
  (Z.of_nat n <= m)%Z ->
  (0 <= Z.of_N (@Word.wordToN n w) < 2 ^ m)%Z.
Admitted.

(* TODO : move to ZUtil *)
Lemma pow2_mod_range : forall a n m,
  (n <= m)%Z ->
  (0 <= ZUtil.Z.pow2_mod a n < 2 ^ m)%Z.
Admitted.

(* TODO : move to ZUtil *)
Lemma shiftr_range : forall a n m,
  (0 <= a < 2 ^ (n + m))%Z ->
  (0 <= Z.shiftr a n < 2 ^ m)%Z.
Admitted.

Lemma feDec_correct : forall w : Word.word (pred b),
        option_eq GF25519BoundedCommon.eq
          (option_map GF25519BoundedCommon.encode
                      (PointEncoding.Fdecode w)) (feDec w).
Proof.
  intros; cbv [PointEncoding.Fdecode feDec].
  Print GF25519BoundedCommon.eq.
  rewrite <-GF25519BoundedCommon.word64eqb_Zeqb.
  rewrite GF25519Bounded.ge_modulus_correct.
  rewrite GF25519BoundedCommon.word64ToZ_ZToWord64 by
    (rewrite GF25519BoundedCommon.unfold_Pow2_64;
     cbv [GF25519BoundedCommon.Pow2_64]; omega).
  rewrite GF25519.ge_modulus_correct.
  rewrite ModularBaseSystemOpt.ge_modulus_opt_correct.
  match goal with
    |- appcontext [GF25519Bounded.unpack ?x] =>
    assert ((Z.of_N (Word.wordToN w)) = BaseSystem.decode (Pow2Base.base_from_limb_widths PseudoMersenneBaseParams.limb_widths) (Tuple.to_list 10 (GF25519BoundedCommon.proj1_fe25519 (GF25519Bounded.unpack x)))) end.
  {
    rewrite GF25519Bounded.unpack_correct.
  rewrite GF25519.unpack_correct, ModularBaseSystemOpt.unpack_correct.

  cbv [GF25519BoundedCommon.proj1_wire_digits
       GF25519BoundedCommon.wire_digitsWToZ
       GF25519BoundedCommon.proj1_wire_digitsW
       GF25519BoundedCommon.app_wire_digits
       HList.mapt HList.mapt'
       length GF25519.wire_widths
       fst snd
      ].

  cbv [GF25519BoundedCommon.proj_word
       GF25519BoundedCommon.word31_to_unbounded_word
       GF25519BoundedCommon.word32_to_unbounded_word
       GF25519BoundedCommon.word_to_unbounded_word
       GF25519BoundedCommon.Build_bounded_word
       GF25519BoundedCommon.Build_bounded_word'
      ].
  rewrite !GF25519BoundedCommon.word64ToZ_ZToWord64 by
    (rewrite GF25519BoundedCommon.unfold_Pow2_64;
     cbv [GF25519BoundedCommon.Pow2_64];
     apply WordNZ_range; cbv; congruence).
  rewrite !WordNZ_split1.
  rewrite !WordNZ_split2.
  simpl Z.of_nat.
  cbv [ModularBaseSystem.eq].
  match goal with
    |- appcontext [@ModularBaseSystem.unpack _ _ ?ls _ _ ?t] =>
    assert (Pow2Base.bounded ls (Tuple.to_list (length ls) t)) end.
  { cbv [Pow2Base.bounded length].
    intros.
    destruct (lt_dec i 8).
    { cbv [Tuple.to_list Tuple.to_list' fst snd].
        assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by omega.
        repeat match goal with H : (_ \/ _)%type |- _ => destruct H; subst end;
        cbv [nth_default nth_error value]; try (apply pow2_mod_range; omega).
            repeat apply shiftr_range; apply WordNZ_range_mono; cbv;
            congruence. }
    { rewrite !nth_default_out_of_bounds
        by (rewrite ?Tuple.length_to_list; cbv [length]; omega).
      rewrite Z.pow_0_r. omega. } }
  cbv [ModularBaseSystem.unpack ModularBaseSystemList.unpack].
  rewrite Tuple.to_list_from_list.
  rewrite <-Conversion.convert_correct by (auto || rewrite Tuple.to_list; reflexivity).
  rewrite <-Pow2BaseProofs.decode_bitwise_spec by (auto || cbv [In]; intuition omega).
  cbv [Tuple.to_list Tuple.to_list' length fst snd Pow2Base.decode_bitwise Pow2Base.decode_bitwise' nth_default nth_error ].
  clear.
  apply Z.bits_inj'.
  intros.
  rewrite Z.shiftl_0_l.
  rewrite Z.lor_0_r.
  repeat match goal with |- appcontext[@Word.wordToN (?x + ?y) w] =>
                  change (@Word.wordToN (x + y) w) with (@Word.wordToN (pred b) w) end.
  assert (
      0 <= n < 32 \/
      32 <= n < 64 \/
      64 <= n < 96 \/
      96 <= n < 128 \/
      128 <= n < 160 \/
      160 <= n < 192 \/
      192 <= n < 224 \/
      224 <= n < 256 \/
      256 <= n)%Z by omega.
  repeat match goal with H : (_ \/ _)%type |- _ => destruct H; subst end;
  repeat match goal with
         | |- _ => rewrite Z.lor_spec
         | |- _ => rewrite Z.shiftl_spec by omega
         | |- _ => rewrite Z.shiftr_spec by omega
         | |- _ => rewrite Z.testbit_neg_r by omega
         | |- _ => rewrite ZUtil.Z.testbit_pow2_mod by omega;
                     VerdiTactics.break_if; try omega
         end;
  repeat match goal with
        | |- _ = (false || _)%bool => rewrite Bool.orb_false_l
        | |- ?x = (?x || ?y)%bool => replace y with false;
            [ rewrite Bool.orb_false_r; reflexivity | ]
        | |- false = (?x || ?y)%bool => replace y with false;
            [ rewrite Bool.orb_false_r;
                replace x with false; [ reflexivity | ]
            | ]
        | |- false = Z.testbit _ _ =>
            rewrite Z.testbit_neg_r by omega; reflexivity
        | |- Z.testbit ?w ?n = Z.testbit ?w ?m =>
          replace m with n by omega; reflexivity
        | |- Z.testbit ?w ?n = (Z.testbit ?w ?m || _)%bool =>
          replace m with n by omega
         end;
  admit. (* TODO(jadep): there are goal left here on 8.4 *)
  }
  match goal with
    |- option_eq _ (option_map _ (if Z_lt_dec ?a ?b then Some _ else None)) (if (?X =? 1)%Z then None else Some _) =>
    assert ((a < b)%Z <-> X = 0%Z) end.
  {
    rewrite ModularBaseSystemListProofs.ge_modulus_spec;
      [ | cbv; congruence | rewrite Tuple.length_to_list; reflexivity | ].
    Focus 2. {
      rewrite GF25519Bounded.unpack_correct.
      rewrite GF25519.unpack_correct, ModularBaseSystemOpt.unpack_correct.
      cbv [ModularBaseSystem.unpack].
      rewrite Tuple.to_list_from_list.
      cbv [ModularBaseSystemList.unpack].
      apply Conversion.convert_bounded.
    } Unfocus.
    rewrite <-H0.
    intuition; try omega.
    apply Znat.N2Z.is_nonneg.
  }

  do 2 VerdiTactics.break_if;
  [
  match goal with H: ?P, Hiff : ?P <-> ?x = 0%Z |- _ =>
                  let A := fresh "H" in
                  pose proof ((proj1 Hiff) H) as A;
                    rewrite A in *; discriminate
  end
  | | reflexivity |
  match goal with
    H: ~ ?P, Hiff : ?P <-> ModularBaseSystemList.ge_modulus ?x = 0%Z
    |- _ =>
    exfalso; apply H; apply Hiff;
    destruct (ModularBaseSystemListProofs.ge_modulus_01 x) as [Hgm | Hgm];
      rewrite Hgm in *; try discriminate; reflexivity
  end ].

  cbv [option_map option_eq].
  cbv [GF25519BoundedCommon.eq].
  rewrite GF25519BoundedCommon.proj1_fe25519_encode.
  cbv [ModularBaseSystem.eq].
  etransitivity.
  Focus 2. {
    cbv [ModularBaseSystem.decode ModularBaseSystemList.decode].
    cbv [length PseudoMersenneBaseParams.limb_widths GF25519.params25519] in H0 |- *.
    rewrite <-H0.
    reflexivity. } Unfocus.
  apply ModularBaseSystemProofs.encode_rep.

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

Lemma bounded_by_encode_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (ModularBaseSystem.encode x)
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.int_width)).
Proof.
Admitted.

Lemma bounded_by_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (GF25519BoundedCommon.fe25519WToZ x)
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.int_width)).
Admitted.

Lemma sqrt_correct : forall x : ModularArithmetic.F.F q,
        GF25519BoundedCommon.eq
          (GF25519BoundedCommon.encode
             (PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1 x))
          (GF25519Bounded.sqrt (GF25519BoundedCommon.encode x)).
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
    eauto using freezePre, ModularBaseSystemProofs.encode_rep, bounded_by_freeze, bounded_by_encode_freeze;
  match goal with
  | |- appcontext[GF25519Bounded.powW ?a ?ch] =>
    let A := fresh "H" in
    destruct (GF25519Bounded.powW_correct_and_bounded ch a) as [A ?];
      [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW;
        rewrite <-GF25519BoundedCommon.proj1_fe25519_encode;
        apply GF25519BoundedCommon.is_bounded_proj1_fe25519
      | rewrite A;
        rewrite GF25519.pow_correct, ModularBaseSystemOpt.pow_opt_correct
          by reflexivity]
  end;[ solve [f_equiv; apply GF25519BoundedCommon.fe25519WToZ_ZToW;
             rewrite <-GF25519BoundedCommon.proj1_fe25519_encode;
             apply GF25519BoundedCommon.is_bounded_proj1_fe25519] | ].
  match goal with
  | |- appcontext[GF25519Bounded.mulW ?a ?b] =>
    let A := fresh "H" in
    destruct (GF25519Bounded.mulW_correct_and_bounded a b) as [A ?];
      [ auto | auto | rewrite A]
  end.
  rewrite GF25519.mul_correct, ModularBaseSystemOpt.carry_mul_opt_correct by reflexivity.
  rewrite !H0.
  rewrite GF25519.pow_correct.
  cbv [ModularBaseSystem.eq].
  rewrite ModularBaseSystemProofs.carry_mul_rep by reflexivity.
  rewrite ModularBaseSystemProofs.mul_rep by reflexivity.
  apply f_equal2;
  rewrite ModularBaseSystemOpt.pow_opt_correct; reflexivity.
Qed.

Lemma ERepDec_correct : forall w : Word.word b,
    ERepDec w = @option_map E Erep EToRep (Edec w).
Proof.
  pose proof (@PointEncoding.Kdecode_point_correct
                (pred b) _ Spec.Ed25519.a Spec.Ed25519.d _
                GF25519.modulus_gt_2 bound_check255
                _ _ _ _ _ _ _ _ _ _ GF25519Bounded.field25519
                _ _ _ _ _ phi_a phi_d feSign feSign_correct _
                (ExtendedCoordinates.Extended.from_twisted
                  (field := GF25519Bounded.field25519)
                  (prm := twedprm_ERep))
                extended_to_coord
                extended_to_coord_from_twisted
                _ ext_eq_correct _ _ encode_eq_iff
                feDec GF25519Bounded.sqrt _ _ feDec_correct
                (@PrimeFieldTheorems.F.sqrt_5mod8 _ Fsqrt_minus1)
                sqrt_correct
             ).
  intros; specialize (H0 w).
  cbv [ERepDec Edec EToRep].
Admitted.

Lemma eq_enc_E_iff : forall (P_ : Word.word b) (P : E),
 Eenc P = P_ <->
 Option.option_eq CompleteEdwardsCurveTheorems.E.eq (Edec P_) (Some P).
Proof.
  cbv [Eenc].
  eapply @PointEncoding.encode_point_decode_point_iff; try (exact iff_equivalence || exact curve_params); [].
  intros.
  apply (@PrimeFieldTheorems.F.sqrt_5mod8_correct GF25519.modulus _ eq_refl Fsqrt_minus1 Fsqrt_minus1_correct).
  eexists.
  symmetry; eassumption.
Qed.

Let verify_correct :
  forall {mlen : nat} (msg : Word.word mlen) (pk : Word.word b)
  (sig : Word.word (b + b)), verify msg pk sig = true <-> EdDSA.valid msg pk sig :=
  @verify_correct
      (* E := *) E
      (* Eeq := *) CompleteEdwardsCurveTheorems.E.eq
      (* Eadd := *) CompleteEdwardsCurve.E.add
      (* Ezero := *) CompleteEdwardsCurve.E.zero
      (* Eopp := *) CompleteEdwardsCurveTheorems.E.opp
      (* EscalarMult := *) CompleteEdwardsCurve.E.mul
      (* b := *) b
      (* H := *) H
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) ed25519
      (* Proper_Eenc := *) PointEncoding.Proper_encode_point
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
      (* Proper_ERepEnc := *) (PointEncoding.Proper_Kencode_point (Kpoint_eq_correct := ext_eq_correct) (Proper_Kenc := Proper_feEnc))
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
Let both_correct := (@sign_correct, @verify_correct).
Print Assumptions both_correct.

(*** Extraction *)




Extraction Language Haskell.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction AccessOpaque.

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec    => "".
Extract Inlined Constant eq_rec_r  => "".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Bool, sumbool, Decidable *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive Bool.reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inlined Constant Bool.iff_reflect => "".
Extraction Inline Crypto.Util.Decidable.Decidable Crypto.Util.Decidable.dec.

(* Extract Inlined Constant Equality.bool_beq => *)
(*   "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     =>
  "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant xorb => "Data.Bits.xor".

(** Comparisons *)

Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].
Extract Inductive CompareSpecT => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     => "Data.List.genericLength".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** nat *)

Require Import Crypto.Experiments.ExtrHaskellNats.

(** positive *)
Require Import BinPos.

Extract Inductive positive => "Prelude.Integer" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> {- match_on_positive -}
                   if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))".

Extract Inlined Constant Pos.succ => "(1 Prelude.+)".
Extract Inlined Constant Pos.add => "(Prelude.+)".
Extract Inlined Constant Pos.mul => "(Prelude.*)".
Extract Inlined Constant Pos.pow => "(Prelude.^)".
Extract Inlined Constant Pos.max => "Prelude.max".
Extract Inlined Constant Pos.min => "Prelude.min".
Extract Inlined Constant Pos.gcd => "Prelude.gcd".
Extract Inlined Constant Pos.land => "(Data.Bits..&.)".
Extract Inlined Constant Pos.lor => "(Data.Bits..|.)".
Extract Inlined Constant Pos.compare => "Prelude.compare".
Extract Inlined Constant Pos.ltb => "(Prelude.<)".
Extract Inlined Constant Pos.leb => "(Prelude.<=)".
Extract Inlined Constant Pos.eq_dec => "(Prelude.==)".
Extract Inlined Constant Pos.eqb => "(Prelude.==)".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Pos.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Pos.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Pos.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Pos.pred => "(\n -> Prelude.max 1 (Prelude.pred n))".
Extract Constant Pos.sub => "(\n m -> Prelude.max 1 (n Prelude.- m))".

(** N *)

Extract Inlined Constant N.succ => "(1 Prelude.+)".
Extract Inlined Constant N.add => "(Prelude.+)".
Extract Inlined Constant N.mul => "(Prelude.*)".
Extract Inlined Constant N.pow => "(Prelude.^)".
Extract Inlined Constant N.max => "Prelude.max".
Extract Inlined Constant N.min => "Prelude.min".
Extract Inlined Constant N.gcd => "Prelude.gcd".
Extract Inlined Constant N.lcm => "Prelude.lcm".
Extract Inlined Constant N.land => "(Data.Bits..&.)".
Extract Inlined Constant N.lor => "(Data.Bits..|.)".
Extract Inlined Constant N.lxor => "Data.Bits.xor".
Extract Inlined Constant N.compare => "Prelude.compare".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.ltb => "(Prelude.<)".
Extract Inlined Constant N.leb => "(Prelude.<=)".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.odd => "Prelude.odd".
Extract Inlined Constant N.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant N.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant N.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant N.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant N.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant N.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant N.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant N.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive N => "Prelude.Integer" [ "0" "(\x -> x)" ]
  "(\fO fS n -> {- match_on_N -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

(** Z *)
Require Import ZArith.BinInt.

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> {- match_on_Z -}
                   if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))".

Extract Inlined Constant Z.succ => "(1 Prelude.+)".
Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.opp => "Prelude.negate".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.pow => "(Prelude.^)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z.lcm => "Prelude.lcm".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.pred => "Prelude.pred".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.lor => "(Data.Bits..|.)".
Extract Inlined Constant Z.lxor => "Data.Bits.xor".
Extract Inlined Constant Z.compare => "Prelude.compare".
Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.odd => "Prelude.odd".
Extract Inlined Constant Z.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Z.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Z.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Z.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Z.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

(** Conversions *)

Extract Inlined Constant Z.of_N => "".
Extract Inlined Constant Z.to_N => "".
Extract Inlined Constant N.to_nat => "".
Extract Inlined Constant N.of_nat => "".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extract Inlined Constant Z.abs_N => "Prelude.abs".
Extract Inlined Constant Z.abs_nat => "Prelude.abs".
Extract Inlined Constant Pos.pred_N => "Prelude.pred".
Extract Inlined Constant Pos.lxor => "Data.Bits.xor".

(** Word *)
(* do not annotate every bit of a word with the number of bits after it *)
Extraction Implicit Word.WS [ 2 ].
Extraction Implicit Word.whd [ 1 ].
Extraction Implicit Word.wtl [ 1 ].
Extraction Implicit Word.bitwp [ 2 ].
Extraction Implicit Word.wand [ 1 ].
Extraction Implicit Word.wor [ 1 ].
Extraction Implicit Word.wxor [ 1 ].
Extraction Implicit Word.wordToN [ 1 ].
Extraction Implicit Word.wordToNat [ 1 ].
Extraction Implicit Word.combine [ 1 3 ].
Extraction Implicit Word.split1 [ 2 ].
Extraction Implicit Word.split2 [ 2 ].
Extraction Implicit WordUtil.cast_word [1 2 3].
Extraction Implicit WordUtil.wfirstn [ 2 4 ].
Extract Inlined Constant WordUtil.cast_word => "".

(** Let_In *)
Extraction Inline LetIn.Let_In.

(* inlining, primarily to reduce polymorphism *)
Extraction Inline dec_eq_Z dec_eq_N dec_eq_sig_hprop.
Extraction Inline Erep SRep ZNWord WordNZ.
Extraction Inline GF25519BoundedCommon.fe25519.
Extraction Inline EdDSARepChange.sign EdDSARepChange.splitSecretPrngCurve.
Extraction Inline Crypto.Util.IterAssocOp.iter_op Crypto.Util.IterAssocOp.test_and_op.
Extraction Inline PointEncoding.Kencode_point.
Extraction Inline ExtendedCoordinates.Extended.point ExtendedCoordinates.Extended.coordinates ExtendedCoordinates.Extended.to_twisted  ExtendedCoordinates.Extended.from_twisted ExtendedCoordinates.Extended.add_coordinates ExtendedCoordinates.Extended.add ExtendedCoordinates.Extended.opp ExtendedCoordinates.Extended.zero. (* ExtendedCoordinates.Extended.zero could be precomputed *)
Extraction Inline CompleteEdwardsCurve.E.coordinates CompleteEdwardsCurve.E.zero.
Extraction Inline GF25519BoundedCommon.proj_word GF25519BoundedCommon.Build_bounded_word GF25519BoundedCommon.Build_bounded_word'.

(* Recursive Extraction sign. *)
  (* most of the code we want seems to be below [eq_dec1] and there is other stuff above that *)
  (* TODO: remove branching from [sRep] functions *)

(* fragment of output:

sign :: Word -> Word -> Prelude.Integer -> Word -> Word
sign pk sk mlen msg =
  let {
   sp = let {hsk = h b sk} in
        (,)
        (sRepDecModLShort
          (combine n (clearlow n c (wfirstn n ((Prelude.+) b b) hsk)) (Prelude.succ 0)
            (wones (Prelude.succ 0)))) (split2 b b hsk)}
  in
  let {r = sRepDecModL (h ((Prelude.+) b mlen) (combine b (Prelude.snd sp) mlen msg))} in
  let {r0 = sRepERepMul r eRepB} in
  combine b (eRepEnc r0) b
    (sRepEnc
      (sRepAdd r
        (sRepMul
          (sRepDecModL
            (h ((Prelude.+) b ((Prelude.+) b mlen))
              (combine b (eRepEnc r0) ((Prelude.+) b mlen) (combine b pk mlen msg)))) (Prelude.fst sp))))

sRepERepMul :: SRep0 -> Erep -> Erep
sRepERepMul sc a =
  Prelude.snd
    (funexp (\state ->
      case state of {
       (,) i acc ->
        let {acc2 = erepAdd acc acc} in
        let {acc2a = erepAdd a acc2} in
        (\fO fS n -> {- match_on_nat -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> (,) 0
          acc)
          (\i' -> (,) i'
          (eRepSel ((\w n -> Data.Bits.testBit w (Prelude.fromIntegral n)) sc (of_nat i')) acc2 acc2a))
          i}) ((,) ll
      (case  ((,) zero_ one_) of {
        (,) x y -> (,) ((,) ((,) x y) one_) (mul3 x y)})) ll)

erepAdd :: (Point0 Fe25519) -> (Point0 Fe25519) -> Point0 Fe25519
erepAdd p q =
  case  p of {
   (,) y t1 ->
    case y of {
     (,) y0 z1 ->
      case y0 of {
       (,) x1 y1 ->
        case  q of {
         (,) y2 t2 ->
          case y2 of {
           (,) y3 z2 ->
            case y3 of {
             (,) x2 y4 ->
              let {a = mul3 (sub2 y1 x1) (sub2 y4 x2)} in
              let {b0 = mul3 (add2 y1 x1) (add2 y4 x2)} in
              let {c0 = mul3 (mul3 t1 twice_d) t2} in
              let {d = mul3 z1 (add2 z2 z2)} in
              let {e = sub2 b0 a} in
              let {f = sub2 d c0} in
              let {g = add2 d c0} in
              let {h0 = add2 b0 a} in
              let {x3 = mul3 e f} in
              let {y5 = mul3 g h0} in
              let {t3 = mul3 e h0} in let {z3 = mul3 f g} in (,) ((,) ((,) x3 y5) z3) t3}}}}}}
*)
