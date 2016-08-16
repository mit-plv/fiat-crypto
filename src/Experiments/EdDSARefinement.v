Require Import Crypto.Spec.EdDSA Bedrock.Word.
Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Algebra. Import Group ScalarMult.
Require Import Crypto.Util.Decidable Crypto.Util.Option Crypto.Util.Tactics.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Spec.ModularArithmetic Crypto.ModularArithmetic.PrimeFieldTheorems.

Module Import NotationsFor8485.
  Import NPeano Nat.
  Infix "mod" := modulo.
End NotationsFor8485.

(* TODO: move lemmas to better places *)
Lemma symmetry_iff {T} {R} {Rsym:@Symmetric T R} x y: R x y <-> R y x.
  intuition eauto using symmetry.
Qed.

Lemma combine_eq_iff {a b} (A:word a) (B:word b) C :
  combine A B = C <-> A = split1 a b C /\ B = split2 a b C.
Proof. intuition; subst; auto using split1_combine, split2_combine, combine_split. Qed.

Local Ltac logic :=
  repeat match goal with
         | |- _ => intro
         | H:exists _, _ |- _ => destruct H
         | H:_ /\ _ |- _ => destruct H
         | |- _ => solve [eauto]
         | |- _ => split
         end.
Lemma exists_and_indep_l {A B} P Q :
  (exists a b, P a /\ Q a b) <-> (exists a:A, P a /\ exists b:B, Q a b).
Proof. logic. Qed.

Lemma exists_and_indep_r {A B} P Q :
  (exists a b, Q a b /\ P a) <-> (exists a:A, P a /\ exists b:B, Q a b).
Proof. logic. Qed.

Lemma and_rewrite_l {A B} {RA RB} {Equivalence_RA:Equivalence RA} {Equivalence_RB:Equivalence RB}
      (f:A->B) ref P {Proper_P: Proper (RA==>RB==>iff) P} a
  : (RB (f a) ref /\ P a (f a)) <-> (RB (f a) ref /\ P a ref).
Proof.
  logic; match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
Qed.

Lemma and_rewriteleft_l {A B} {RA RB} {Equivalence_RA:Equivalence RA} {Equivalence_RB:Equivalence RB}
      (f:A->B) ref P {Proper_P: Proper (RA==>RB==>iff) P} a
  : (RB ref (f a) /\ P a (f a)) <-> (RB ref (f a) /\ P a ref).
Proof.
  logic; match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
Qed.

Lemma exists_and_equiv_r {A} {RA} {Equivalence_RA:Equivalence RA}
      P {Proper_P: Proper (RA==>iff) P} (ref:A)
  : (exists a, P a /\ RA a ref) <-> P ref.
Proof.
  logic; try match goal with [H:_|-_] => (rewrite H || rewrite <-H); assumption end.
  repeat (assumption||reflexivity||econstructor); assumption. (* WHY the last [assumption]?*)
Qed.

Global Instance Equivalence_option_eq {T} {R} {Equivalence_R:@Equivalence T R}
  : Equivalence (option_eq R).
Proof.
  split; cbv; repeat (break_match || intro || intuition congruence ||
                      solve [ reflexivity | symmetry; eassumption | etransitivity; eassumption ] ).
Qed.

Global Instance Proper_option_rect_nd_changebody
      {A B:Type} {a:option A} {RB:relation B}
  : Proper (pointwise_relation _ RB ==> RB ==> RB) (fun S N => option_rect (fun _ => B) S N a).
Proof. cbv; repeat (intro || break_match); intuition. Qed.

Global Instance Proper_option_rect_nd_changevalue
      {A B RA RB} some {Proper_some: Proper (RA==>RB) some}
  : Proper (RB ==> option_eq RA ==> RB) (@option_rect A (fun _ => B) some).
Proof. cbv; repeat (intro || break_match || f_equiv || intuition congruence). Qed.

Lemma option_rect_false_returns_true_iff {T} (f:T->bool) (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, o = Some s /\ f s = true.
Proof. unfold option_rect; break_match; logic; congruence. Qed.

Module F.
  Lemma to_nat_of_nat {m:Z} (n:nat) : F.to_nat (F.of_nat m n) = n mod (Z.to_nat m).
  Admitted.
  Lemma of_nat_to_nat {m:Z} x : F.of_nat m (F.to_nat x) = x.
  Admitted.
  Lemma of_nat_mod {m} (n:nat) : F.of_nat m (n mod (Z.to_nat m)) = F.of_nat m n.
  Admitted.
End F.

Section EdDSA.
  Context `{prm:EdDSA}.
  Local Infix "==" := Eeq. Local Infix "+" := Eadd. Local Infix "*" := EscalarMult.

  Local Notation valid := (@valid E Eeq Eadd EscalarMult b H l B Eenc Senc).
  Lemma sign_valid : forall A_ sk {n} (M:word n), A_ = public sk -> valid M A_ (sign A_ sk M).
  Proof.
    cbv [sign public Spec.EdDSA.valid]; intros; subst;
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => eapply conj
             | |- _ => reflexivity
             end.
    rewrite F.to_nat_of_nat, scalarmult_mod_order, scalarmult_add_l, cancel_left, scalarmult_mod_order, NPeano.Nat.mul_comm, scalarmult_assoc;
      try solve [ reflexivity
                | setoid_rewrite (*unify 0*) (Z2Nat.inj_iff _ 0); pose proof EdDSA_l_odd; omega
                | apply EdDSA_l_order_B
                | rewrite scalarmult_assoc, mult_comm, <-scalarmult_assoc,
                             EdDSA_l_order_B, scalarmult_zero_r; reflexivity ].
  Qed.

  (* TODO: prove in group *)
  Lemma eq_r_opp_r_inv : forall a b c, a == c + Eopp b <-> a + b == c. Admitted.

  Lemma solve_for_R_sig : forall s B R n A, { solution | s * B == R + n * A <-> R == solution }.
  Proof.
    eexists.
    set_evars.
    setoid_rewrite <-(symmetry_iff(R:=Eeq)) at 1.
    setoid_rewrite <-eq_r_opp_r_inv.
    setoid_rewrite opp_mul.
    subst_evars.
    reflexivity.
  Defined.
  Definition solve_for_R := Eval cbv [proj2_sig solve_for_R_sig] in (fun s B R n A => proj2_sig (solve_for_R_sig s B R n A)).

  Context {Proper_Eenc : Proper (Eeq==>Logic.eq) Eenc}.
  Global Instance Proper_eq_Eenc ref : Proper (Eeq ==> iff) (fun P => Eenc P = ref).
  Proof. intros ? ? Hx; rewrite Hx; reflexivity. Qed.

  Context {Edec:word b-> option E}   {eq_enc_E_iff: forall P_ P, Eenc P = P_ <-> Edec P_ = Some P}.
  Context {Sdec:word b-> option (F l)} {eq_enc_S_iff: forall n_ n, Senc n = n_ <-> Sdec n_ = Some n}.

  Local Infix "++" := combine.
  Definition verify_sig : { verify | forall mlen (message:word mlen) (pk:word b) (sig:word (b+b)),
      verify mlen message pk sig = true <-> valid message pk sig }.
  Proof.
    eexists; intros; set_evars.
    unfold Spec.EdDSA.valid.
    setoid_rewrite solve_for_R.
    setoid_rewrite combine_eq_iff.
    setoid_rewrite and_comm at 4. setoid_rewrite and_assoc. repeat setoid_rewrite exists_and_indep_l.
    setoid_rewrite (and_rewrite_l Eenc (split1 b b sig)
                            (fun x y => x == _ * B + wordToNat (H _ (y ++ Eenc _ ++ message)) mod _ * Eopp _)); setoid_rewrite eq_enc_S_iff.
    setoid_rewrite (@exists_and_equiv_r _ _ _ _ _ _).
    setoid_rewrite <- (fun A => and_rewriteleft_l (fun x => x) (Eenc A) (fun pk EencA => exists a,
        Sdec (split2 b b sig) = Some a /\
        Eenc (_ * B + wordToNat (H (b + (b + mlen)) (split1 b b sig ++ EencA ++ message)) mod _ * Eopp A)
        = split1 b b sig)); setoid_rewrite (eq_enc_E_iff pk).
    setoid_rewrite <-weqb_true_iff.
    repeat setoid_rewrite <-option_rect_false_returns_true_iff.

    subst_evars.
    (* TODO: generalize this higher order reflexivity *)
    match goal with
      |- ?f ?mlen ?msg ?pk ?sig = true <-> ?term = true
      => let term := eval pattern sig in term in
         let term := eval pattern pk in term in
         let term := eval pattern msg in term in
         let term := match term with
                       (fun msg => (fun pk => (fun sig => @?body msg pk sig) sig) pk) msg =>
                       body
                     end in
         let term := eval pattern mlen in term in
         let term := match term with
                       (fun mlen => @?body mlen) mlen => body
                     end in
         unify f term; reflexivity
    end.
  Defined.
  Definition verify {mlen} (message:word mlen) (pk:word b) (sig:word (b+b)) : bool :=
    Eval cbv [proj1_sig verify_sig] in proj1_sig verify_sig mlen message pk sig.
  Lemma verify_correct : forall {mlen} (message:word mlen) pk sig,
    verify message pk sig = true <-> valid message pk sig.
  Proof. exact (proj2_sig verify_sig). Qed.

  Section ChangeRep.
    Context {Erep ErepEq ErepAdd ErepId ErepOpp} {Agroup:@group Erep ErepEq ErepAdd ErepId ErepOpp}.
    Context {EToRep} {Ahomom:@is_homomorphism E Eeq Eadd Erep ErepEq ErepAdd EToRep}.

    Context {ERepEnc : Erep -> word b}
            {ERepEnc_correct : forall P:E, Eenc P = ERepEnc (EToRep P)}
            {Proper_ERepEnc:Proper (ErepEq==>Logic.eq) ERepEnc}.

    Context {ERepDec : word b -> option Erep}
            {ERepDec_correct : forall w, ERepDec w = option_map EToRep (Edec w) }.

    Context {SRep SRepEq} `{@Equivalence SRep SRepEq} {S2Rep:F l->SRep}.

    Context {SRepDecModL} {SRepDecModL_correct: forall (w:word (b+b)), SRepEq (S2Rep (F.of_nat _ (wordToNat w))) (SRepDecModL w)}.

    Context {SRepERepMul:SRep->Erep->Erep}
            {SRepERepMul_correct:forall n P, ErepEq (EToRep (n*P)) (SRepERepMul (S2Rep (F.of_nat _ n)) (EToRep P))}
            {Proper_SRepERepMul: Proper (SRepEq==>ErepEq==>ErepEq) SRepERepMul}.

    Context {SRepDec: word b -> option SRep}
            {SRepDec_correct : forall w, option_eq SRepEq (option_map S2Rep (Sdec w)) (SRepDec w)}.

    Definition verify_using_representation
               {mlen} (message:word mlen) (pk:word b) (sig:word (b+b))
               : { answer | answer = verify message pk sig }.
    Proof.
      eexists.
      cbv [verify].
      repeat (
          setoid_rewrite ERepEnc_correct
          || setoid_rewrite homomorphism
          || setoid_rewrite homomorphism_id
          || setoid_rewrite (homomorphism_inv(INV:=Eopp)(inv:=ErepOpp)(eq:=ErepEq)(phi:=EToRep))
          || setoid_rewrite SRepERepMul_correct
          || setoid_rewrite SdecS_correct
          || setoid_rewrite SRepDecModL_correct
          || setoid_rewrite F.of_nat_to_nat
          || setoid_rewrite F.of_nat_mod
        ).
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
       false); rewrite <-(ERepDec_correct pk).

        setoid_rewrite (option_rect_option_map S2Rep
(fun s0 =>
 weqb
   (ERepEnc
      (ErepAdd (SRepERepMul (s0) (EToRep B))
         (SRepERepMul
            (SRepDecModL (H _ (split1 b b sig ++ pk ++ message)))
            (ErepOpp _)))) (split1 b b sig))

       false).

        etransitivity. Focus 2. {
        eapply Proper_option_rect_nd_changebody; [intro|reflexivity..].
        etransitivity. Focus 2. {
        eapply Proper_option_rect_nd_changevalue; [ | reflexivity | ].
        { repeat intro; repeat f_equiv; eassumption. }
        { symmetry. eapply SRepDec_correct. }
        } Unfocus. reflexivity.
        } Unfocus.
        reflexivity.
    Defined.
  End ChangeRep.
End EdDSA.
