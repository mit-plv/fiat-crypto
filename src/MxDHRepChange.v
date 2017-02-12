Require Import Crypto.Spec.MxDH.
Require Import Crypto.Algebra Crypto.Algebra.Monoid Crypto.Algebra.Group Crypto.Algebra.Ring Crypto.Algebra.Field.
Require Import Crypto.Util.Tuple.

Section MxDHRepChange.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq} {Fcswap:bool->F*F->F*F->(F*F)*(F*F)} {Fa24:F} {tb1:nat->bool}.
  Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv} {impl_field:@Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv} {Keq_dec:Decidable.DecidableRel Keq} {Kcswap:bool->K*K->K*K->(K*K)*(K*K)} {Ka24:K} {tb2:nat->bool}.

  Context {FtoK} {homom:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                              K Keq Kone Kadd Kmul FtoK}.
  Context {homomorphism_inv_zero:Keq (FtoK (Finv Fzero)) (Kinv Kzero)}.
  Context {homomorphism_a24:Keq (FtoK Fa24) Ka24}.
  Context {Fcswap_correct:forall b x y, Fcswap b x y = if b then (y,x) else (x,y)}.
  Context {Kcswap_correct:forall b x y, Kcswap b x y = if b then (y,x) else (x,y)}.
  Context {tb2_correct:forall i, tb2 i = tb1 i}.

  (* TODO: move to algebra *)
  Lemma homomorphism_multiplicative_inverse_complete' x : Keq (FtoK (Finv x)) (Kinv (FtoK x)).
  Proof.
    eapply (homomorphism_multiplicative_inverse_complete).
    intro J; rewrite J. rewrite homomorphism_inv_zero, homomorphism_id.
    reflexivity.
  Qed.

  Ltac t :=
    let hom := match goal with H : is_homomorphism |- _ => H end in
    let mhom := constr:(@homomorphism_is_homomorphism _ _ _ _ _ _ _ _ _ _ _ hom) in
    repeat (
        rewrite (@homomorphism_id _ _ _ _ _ _ _ _ _ _ _ _ _ mhom) ||
        rewrite (@homomorphism_one _ _ _ _ _ _ _ _ _ _ _ hom) ||
        rewrite (@homomorphism_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hom) ||
        rewrite (@homomorphism_add _ _ _ _ _ _ _ _ _ _ _ hom) ||
        rewrite (@homomorphism_mul _ _ _ _ _ _ _ _ _ _ _ hom) ||
        rewrite homomorphism_a24 ||
        rewrite homomorphism_multiplicative_inverse_complete' ||
        reflexivity
      ).

  Import Crypto.Util.Tactics.
  Import List.
  Import Coq.Classes.Morphisms.

  Global Instance Proper_ladderstep :
    Proper (Keq ==> (fieldwise (n:=2) Keq) ==> fieldwise (n:=2) Keq ==> fieldwise (n:=2) (fieldwise (n:=2) Keq)) (@MxDH.ladderstep K Kadd Ksub Kmul Ka24).
  Proof.
    cbv [MxDH.ladderstep tuple tuple' fieldwise fieldwise' fst snd];
      repeat intro; destruct_head' prod; destruct_head' and; repeat split;
        repeat match goal with [H:Keq ?x ?y |- _ ] => rewrite !H; clear H x end; reflexivity.
  Qed.

  Lemma MxLadderstepRepChange u P Q Ku (Ku_correct:Keq (FtoK u) Ku):
    fieldwise (n:=2) (fieldwise (n:=2) Keq)
    ((Tuple.map (n:=2) (Tuple.map (n:=2) FtoK)) (@MxDH.ladderstep F Fadd Fsub Fmul Fa24 u P Q))
    (@MxDH.ladderstep K Kadd Ksub Kmul Ka24 Ku (Tuple.map (n:=2) FtoK P) (Tuple.map (n:=2) FtoK Q)).
  Proof.
    destruct P as [? ?], Q as [? ?]; cbv; repeat split; rewrite <-?Ku_correct; t.
  Qed.

  Let loopiter_sig F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb u :
    { loopiter | @MxDH.montladder F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb u =
      let '(_, _, _) := MxDH.downto _ _ loopiter in  _ } := exist _ _ eq_refl.
  Let loopiter F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb u :=
  Eval cbv [proj1_sig loopiter_sig] in (
    proj1_sig (loopiter_sig F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb u)).

  Let loopiter_phi s : ((K * K) * (K * K)) * bool :=
    (Tuple.map (n:=2) (Tuple.map (n:=2) FtoK) (fst s), snd s).

  Let loopiter_eq (a b: (((K * K) * (K * K)) * bool)) :=
    fieldwise (n:=2) (fieldwise (n:=2) Keq) (fst a) (fst b) /\ snd a = snd b.

  Local Instance Equivalence_loopiter_eq : Equivalence loopiter_eq.
  Proof.
    unfold loopiter_eq; split; repeat intro;
      intuition (reflexivity||symmetry;eauto||etransitivity;symmetry;eauto).
  Qed.

  Lemma MxLoopIterRepChange b Fu s i Ku (HKu:Keq (FtoK Fu) Ku) : loopiter_eq
    (loopiter_phi (loopiter F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb1 Fu s i))
    (loopiter K Kzero Kone Kadd Ksub Kmul Kinv Ka24 Kcswap b tb2 Ku (loopiter_phi s) i).
  Proof.
    destruct_head' prod; break_match.
    simpl.
    rewrite !Fcswap_correct, !Kcswap_correct, tb2_correct in *.
    break_match; cbv [loopiter_eq loopiter_phi fst snd]; split; try reflexivity;
      (etransitivity;[|etransitivity]; [ | eapply (MxLadderstepRepChange _ _ _ _ HKu) | ];
            match goal with Heqp:_ |- _ => rewrite <-Heqp; reflexivity end).
  Qed.

  Global Instance Proper_fold_left {A RA B RB} :
    Proper ((RA==>RB==>RA) ==> SetoidList.eqlistA RB ==> RA ==> RA) (@fold_left A B).
  Proof.
    intros ? ? ? ? ? Hl; induction Hl; repeat intro; [assumption|].
    simpl; cbv [Proper respectful] in *; eauto.
  Qed.

  Lemma proj_fold_left {A B L} R {Equivalence_R:@Equivalence B R} (proj:A->B) step step' {Proper_step':(R ==> eq ==> R)%signature step' step'} (xs:list L) init init' (H0:R (proj init) init') (Hproj:forall x i, R (proj (step x i)) (step' (proj x) i)) :
         R (proj (fold_left step xs init)) (fold_left step' xs init').
  Proof.
    generalize dependent init; generalize dependent init'.
    induction xs; [solve [eauto]|].
    repeat intro; simpl; rewrite IHxs by eauto.
    apply (_ : Proper ((R ==> eq ==> R) ==> SetoidList.eqlistA eq ==> R ==> R) (@fold_left _ _));
      try reflexivity;
      eapply Proper_step'; eauto.
  Qed.

  Global Instance Proper_downto {T R} {Equivalence_R:@Equivalence T R} :
    Proper (R ==> Logic.eq ==> (R==>Logic.eq==>R) ==> R) MxDH.downto.
  Proof.
    intros s0 s0' Hs0 n' n Hn'; subst n'; generalize dependent s0; generalize dependent s0'.
    induction n; repeat intro; [assumption|].
    unfold MxDH.downto; simpl.
    eapply Proper_fold_left; try eassumption; try reflexivity.
    cbv [Proper respectful] in *; eauto.
  Qed.

  Global Instance Proper_loopiter a b c :
   Proper (loopiter_eq ==> eq ==> loopiter_eq) (loopiter K Kzero Kone Kadd Ksub Kmul Kinv Ka24 Kcswap a b c).
  Proof.
    unfold loopiter; intros [? ?] [? ?] [[[] []] ?]; repeat intro ; cbv [fst snd] in * |-; subst.
    repeat VerdiTactics.break_match; subst; repeat (VerdiTactics.find_injection; intros; subst).
    split; [|reflexivity].
    etransitivity; [|etransitivity]; [ | eapply Proper_ladderstep | ];
      [eapply eq_subrelation; [ exact _ | symmetry; eassumption ]
      | reflexivity | |
      | eapply eq_subrelation; [exact _ | eassumption ] ];
      rewrite !Kcswap_correct in *;
      match goal with [H: (if ?b then _ else _) = _ |- _] => destruct b end;
      repeat (VerdiTactics.find_injection; intros; subst);
    split; simpl; eauto.
  Qed.

  Lemma MxDHRepChange b (x:F) :
    Keq
      (FtoK (@MxDH.montladder F Fzero Fone Fadd Fsub Fmul Finv Fa24 Fcswap b tb1 x))
      (@MxDH.montladder K Kzero Kone Kadd Ksub Kmul Kinv Ka24 Kcswap b tb2 (FtoK x)).
  Proof.
    cbv [MxDH.montladder].
    repeat break_match.
    assert (Hrel:loopiter_eq (loopiter_phi (p, p0, b0)) (p1, p3, b1)).
    {
      rewrite <-Heqp0; rewrite <-Heqp.
      unfold MxDH.downto.
      eapply (proj_fold_left (L:=nat) loopiter_eq loopiter_phi).
      { eapply @Proper_loopiter. }
      { cbv; repeat split; t. }
      { intros; eapply MxLoopIterRepChange; reflexivity. }
    }
    { destruct_head' prod; destruct Hrel as [[[] []] ?]; simpl in *; subst.
      rewrite !Fcswap_correct, !Kcswap_correct in *.
      match goal with [H: (if ?b then _ else _) = _ |- _] => destruct b end;
        repeat (VerdiTactics.find_injection; intros; subst);
        repeat match goal with [H: Keq (FtoK ?x) (?kx)|- _ ] => rewrite <- H end;
        t.
    }
    Grab Existential Variables.
    exact 0.
    exact 0.
  Qed.
End MxDHRepChange.
