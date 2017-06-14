Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Spec.EdDSA Bedrock.Word.
Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Algebra.Monoid Crypto.Algebra.Group Crypto.Algebra.ScalarMult.
Require Import Crypto.Util.Decidable Crypto.Util.Option.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option Crypto.Util.Logic Crypto.Util.Relations Crypto.Util.WordUtil Util.LetIn Util.NatUtil.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.PrimeFieldTheorems.
Import NPeano.

Import Notations.

Section EdDSA.
  Context `{prm:EdDSA}.
  Local Infix "==" := Eeq. Local Infix "+" := Eadd. Local Infix "*" := ZEmul.

  Local Notation valid := (@valid E Eeq Eadd ZEmul b H l B Eenc Senc).
  Lemma sign_valid : forall A_ sk {n} (M:word n), A_ = public sk -> valid M A_ (sign A_ sk M).
  Proof using Type.
    cbv [sign public Spec.EdDSA.valid]; intros; subst;
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => eapply conj
             | |- _ => reflexivity
             end.
    rewrite F.to_Z_of_Z, scalarmult_mod_order, scalarmult_add_l, cancel_left, scalarmult_mod_order, Z.mul_comm, scalarmult_assoc;
      try solve [ reflexivity
                | setoid_rewrite (*unify 0*) (Z2Nat.inj_iff _ 0); pose proof EdDSA_l_odd; omega
                | pose proof EdDSA_l_odd; omega
                | apply EdDSA_l_order_B
                | rewrite scalarmult_assoc, Z.mul_comm, <-scalarmult_assoc,
                  EdDSA_l_order_B, scalarmult_zero_r; reflexivity].
  Qed.

  Lemma solve_for_R_sig : forall s B R n A, { solution | s * B == R + n * A <-> R == solution }.
  Proof.
    eexists.
    set_evars.
    setoid_rewrite <-(symmetry_iff(R:=Eeq)) at 1.
    setoid_rewrite <-eq_r_opp_r_inv.
    setoid_rewrite <-scalarmult_opp_r.
    subst_evars.
    reflexivity.
  Defined.
  Definition solve_for_R := Eval cbv [proj2_sig solve_for_R_sig] in (fun s B R n A => proj2_sig (solve_for_R_sig s B R n A)).

  Context {Proper_Eenc : Proper (Eeq==>Logic.eq) Eenc}.
  Global Instance Proper_eq_Eenc ref : Proper (Eeq ==> iff) (fun P => Eenc P = ref).
  Proof using Proper_Eenc. intros ? ? Hx; rewrite Hx; reflexivity. Qed.

  Context {Edec:word b-> option E}   {eq_enc_E_iff: forall P_ P, Eenc P = P_ <-> option_eq Eeq (Edec P_) (Some P)}.
  Context {Sdec:word b-> option (F l)} {eq_enc_S_iff: forall n_ n, Senc n = n_ <-> Sdec n_ = Some n}.

  Local Infix "++" := combine.
  Definition verify'_sig : { verify | forall mlen (message:word mlen) (pk:word b) (sig:word (b+b)),
      verify mlen message pk sig = true <-> valid message pk sig }.
  Proof.
    eexists; intros mlen message pk sig; set_evars.
    unfold Spec.EdDSA.valid.
    setoid_rewrite solve_for_R.
    setoid_rewrite combine_eq_iff.
    setoid_rewrite and_comm at 4. setoid_rewrite and_assoc. repeat setoid_rewrite exists_and_indep_l.
    setoid_rewrite (and_rewrite_l Eenc (split1 b b sig)
                            (fun x y => x == _ * B + Z.of_nat (wordToNat (H _ (y ++ Eenc _ ++ message))) mod _ * Eopp _)); setoid_rewrite eq_enc_S_iff.
    setoid_rewrite (@exists_and_equiv_r _ _ _ _ _ _).
    setoid_rewrite <- (fun A => and_rewriteleft_l (fun x => x) (Eenc A) (fun pk EencA => exists a,
        Sdec (split2 b b sig) = Some a /\
        Eenc (_ * B + Z.of_nat (wordToNat (H (b + (b + mlen)) (split1 b b sig ++ EencA ++ message))) mod _ * Eopp A)
        = split1 b b sig)). setoid_rewrite (eq_enc_E_iff pk).
    setoid_rewrite <-weqb_true_iff.
    setoid_rewrite <-option_rect_false_returns_true_iff_eq.
    rewrite <-option_rect_false_returns_true_iff by
     (intros ? ? Hxy; unfold option_rect; break_match; rewrite <-?Hxy; reflexivity).

    subst_evars.
    eapply reflexivity.
  Defined.
  Definition verify' {mlen} (message:word mlen) (pk:word b) (sig:word (b+b)) : bool :=
    Eval cbv [proj1_sig verify'_sig] in proj1_sig verify'_sig mlen message pk sig.
  Lemma verify'_correct : forall {mlen} (message:word mlen) pk sig,
    verify' message pk sig = true <-> valid message pk sig.
  Proof using Type*. exact (proj2_sig verify'_sig). Qed.

  Section ChangeRep.
    Context {Erep ErepEq ErepAdd ErepId ErepOpp} {Agroup:@Algebra.Hierarchy.group Erep ErepEq ErepAdd ErepId ErepOpp}.
    Context {EToRep} {Ahomom:@is_homomorphism E Eeq Eadd Erep ErepEq ErepAdd EToRep}.

    Context {ERepEnc : Erep -> word b}
            {ERepEnc_correct : forall P:E, Eenc P = ERepEnc (EToRep P)}
            {Proper_ERepEnc:Proper (ErepEq==>Logic.eq) ERepEnc}.

    Context {ERepDec : word b -> option Erep}
            {ERepDec_correct : forall w, option_eq ErepEq (ERepDec w) (option_map EToRep (Edec w)) }.

    Context {SRep SRepEq} `{@Equivalence SRep SRepEq} {S2Rep:F l->SRep}.

    Context {SRepDecModL} {SRepDecModL_correct: forall (w:word (b+b)), SRepEq (S2Rep (F.of_Z _ (Z.of_nat (wordToNat w)))) (SRepDecModL w)}.

    Context {SRepERepMul:SRep->Erep->Erep}
            {SRepERepMul_correct:forall n P, ErepEq (EToRep ((n mod l)*P)) (SRepERepMul (S2Rep (F.of_Z _ n)) (EToRep P))}
            {Proper_SRepERepMul: Proper (SRepEq==>ErepEq==>ErepEq) SRepERepMul}.

    Context {SRepDec: word b -> option SRep}
            {SRepDec_correct : forall w, option_eq SRepEq (option_map S2Rep (Sdec w)) (SRepDec w)}.

    Definition verify_using_representation
               {mlen} (message:word mlen) (pk:word b) (sig:word (b+b))
               : { answer | answer = verify' message pk sig }.
    Proof.
      eexists.
      pose proof EdDSA_l_odd.
      cbv [verify'].

      etransitivity. Focus 2. {
        eapply Proper_option_rect_nd_changebody; [intro|reflexivity].
        eapply Proper_option_rect_nd_changebody; [intro|reflexivity].
        rewrite <-F.mod_to_Z by omega.
        repeat (
            rewrite ERepEnc_correct
            || rewrite homomorphism
            || rewrite homomorphism_id
            || rewrite (homomorphism_inv(INV:=Eopp)(inv:=ErepOpp)(eq:=ErepEq)(phi:=EToRep))
            || rewrite SRepERepMul_correct
            || rewrite SdecS_correct
            || rewrite SRepDecModL_correct
            || rewrite (@F.of_Z_to_Z _ _)
            || rewrite (@F.mod_to_Z _ _)
          ).
        reflexivity.
      } Unfocus.

      (* lazymatch goal with |- _ _ (option_rect _ ?some _ _) => idtac some end. *)
      setoid_rewrite (option_rect_option_map EToRep
           (fun s =>
            option_rect (fun _ : option _ => bool)
              (fun s0 =>
               weqb
                 (ERepEnc
                    (ErepAdd (SRepERepMul (_ s0) (EToRep B))
                       (SRepERepMul
                          (SRepDecModL
                             (H _ (split1 b b sig ++ pk ++ message)))
                          (ErepOpp (s))))) (split1 b b sig)) false
              (Sdec (split2 b b sig)))
           false).
      (* rewrite with a complicated proper instance for inline code .. *)
      etransitivity;
        [| eapply Proper_option_rect_nd_changevalue;
           [
           | reflexivity
           | eapply ERepDec_correct
           ];
           [ repeat match goal with
                    | |- _ => intro
                    | |- _ => eapply Proper_option_rect_nd_changebody
                    | |- ?R ?x ?x => reflexivity
                    | H : _ |- _ => rewrite H; reflexivity
                    end
           ]
        ].

      etransitivity. Focus 2. {
        eapply Proper_option_rect_nd_changebody; [intro|reflexivity].
        set_evars.
        setoid_rewrite (option_rect_option_map S2Rep
            (fun s0 =>
             weqb
               (ERepEnc
                  (ErepAdd (SRepERepMul (s0) (EToRep B))
                     (SRepERepMul
                        (SRepDecModL (H _ (split1 b b sig ++ pk ++ message)))
                        (ErepOpp _)))) (split1 b b sig))

                   false).
        subst_evars.

        eapply Proper_option_rect_nd_changevalue;
          [repeat intro; repeat f_equiv; eassumption|reflexivity|..].

        symmetry.
        eapply SRepDec_correct.
      } Unfocus.

      reflexivity.
    Defined.

    Definition verify {mlen} (msg:word mlen) pk sig :=
      Eval cbv beta iota delta [proj1_sig verify_using_representation] in
      proj1_sig (verify_using_representation msg pk sig).
    Lemma verify_correct {mlen} (msg:word mlen) pk sig : verify msg pk sig = true <-> valid msg pk sig.
    Proof using Type*.
      etransitivity; [|eapply (verify'_correct msg pk sig)].
      eapply iff_R_R_same_r, (proj2_sig (verify_using_representation _ _ _)).
    Qed.

    Context {SRepEnc : SRep -> word b}
            {SRepEnc_correct : forall x, Senc x = SRepEnc (S2Rep x)}
            {Proper_SRepEnc:Proper (SRepEq==>Logic.eq) SRepEnc}.
    Context {SRepAdd : SRep -> SRep -> SRep}
            {SRepAdd_correct : forall x y, SRepEq (S2Rep (x+y)%F) (SRepAdd (S2Rep x) (S2Rep y)) }
            {Proper_SRepAdd:Proper (SRepEq==>SRepEq==>SRepEq) SRepAdd}.
    Context {SRepMul : SRep -> SRep -> SRep}
            {SRepMul_correct : forall x y, SRepEq (S2Rep (x*y)%F) (SRepMul (S2Rep x) (S2Rep y)) }
            {Proper_SRepMul:Proper (SRepEq==>SRepEq==>SRepEq) SRepMul}.
    Context {ErepB:Erep} {ErepB_correct:ErepEq ErepB (EToRep B)}.

    Context {SRepDecModLShort} {SRepDecModLShort_correct: forall (w:word (n+1)), SRepEq (S2Rep (F.of_nat _ (wordToNat w))) (SRepDecModLShort w)}.

    (* We would ideally derive the optimized implementations from
    specifications using `setoid_rewrite`, but doing this without
    inlining let-bound subexpressions turned out to be quite messy in
    the current state of Coq: <https://github.com/mit-plv/fiat-crypto/issues/64> *)

    Let n_le_bpb : (n <= b+b)%nat. destruct prm. omega. Qed.

    (* TODO: change impl to basesystem *)
    Context (splitSecretPrngCurve : forall (sk:word b), SRep * word b).
    Context (splitSecretPrngCurve_correct : forall sk,
      let (s, r) := splitSecretPrngCurve sk in
      SRepEq s (S2Rep (F.of_Z l (curveKey sk))) /\ r = prngKey (H:=H) sk).

    Definition sign (pk sk : word b) {mlen} (msg:word mlen) :=
      dlet sp := splitSecretPrngCurve sk in
      dlet s := fst sp in
      dlet p := snd sp in
      dlet r := SRepDecModL (H _ (p ++ msg)) in
      dlet R := SRepERepMul r ErepB in
      dlet S := SRepAdd r (SRepMul (SRepDecModL (H _ (ERepEnc R ++ pk ++ msg))) s) in
      ERepEnc R ++ SRepEnc S. 

    Lemma Z_l_nonzero : Z.pos l <> 0%Z. discriminate. Qed.

    Lemma sign_correct (pk sk : word b) {mlen} (msg:word mlen)
               : sign pk sk msg = EdDSA.sign pk sk msg.
    Proof using Agroup Ahomom ERepEnc_correct ErepB_correct H0 Proper_ERepEnc Proper_SRepAdd Proper_SRepERepMul Proper_SRepEnc Proper_SRepMul SRepAdd_correct SRepDecModLShort_correct SRepDecModL_correct SRepERepMul_correct SRepEnc_correct SRepMul_correct splitSecretPrngCurve_correct.
      cbv [sign EdDSA.sign Let_In].

      let H := fresh "H" in
      pose proof (splitSecretPrngCurve_correct sk) as H;
        destruct (splitSecretPrngCurve sk);
        destruct H as [curveKey_correct prngKey_correct].

      repeat (
          reflexivity
          || rewrite ERepEnc_correct
          || rewrite SRepEnc_correct
          || rewrite SRepDecModL_correct
          || rewrite SRepERepMul_correct
          || rewrite (F.of_Z_add (m:=l))
          || rewrite (F.of_Z_mul (m:=l))
          || rewrite SRepAdd_correct
          || rewrite SRepMul_correct
          || rewrite ErepB_correct
          || rewrite <-prngKey_correct
          || rewrite <-curveKey_correct
          || eapply (f_equal2 (fun a b => a ++ b))
          || f_equiv
          || rewrite <-(scalarmult_mod_order l B Z_l_nonzero EdDSA_l_order_B), SRepERepMul_correct
        ).
    Qed.
  End ChangeRep.
End EdDSA.
