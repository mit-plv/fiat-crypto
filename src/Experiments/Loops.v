Require Import Coq.Lists.List.
Require Import Lia. 
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.

Require Import Crypto.Util.CPSNotations.

Module Import core.
  Section Loops.
    Context {A B : Type} (body : A -> A + B).

    Fixpoint loop (fuel : nat) (s : A) {struct fuel} : A + B :=
      match fuel with
      | O => inl s
      | S fuel' =>
        let s := body s in
        match s with
        | inl a => loop fuel' a
        | inr b => inr b
        end
      end.

    Context (body_cps : A ~> A + B).

    Fixpoint loop_cps (fuel : nat) (s : A) {struct fuel} :~> A + B :=
      match fuel with
      | O => return (inl s)
                  | S fuel' =>
                    s <- body_cps s;
                      match s with
                      | inl a => loop_cps fuel' a
                      | inr b => return (inr b)
                      end
      end.

    Context (body_cps_ok : forall s {R} f, body_cps s R f = f (body s)).
    Lemma loop_cps_ok n s {R} f : loop_cps n s R f = f (loop n s).
    Proof.
      revert f; revert R; revert s; induction n; [reflexivity|]; cbn; intros.
      cbv [cpscall cpsreturn]; rewrite body_cps_ok;
        break_match; rewrite ?IHn; reflexivity.
    Qed.

    Context (body_cps2 : A -> forall {R}, (A -> R) -> (B -> R) -> R).
    Fixpoint loop_cps2 (fuel : nat) (s : A) {R} (timeout:A->R) (ret:B->R) {struct fuel} : R :=
      match fuel with
      | O => timeout s
      | S fuel' =>
        body_cps2 s R
                  (fun a => @loop_cps2 fuel' a R timeout ret)
                  (fun b => ret b)
      end.

    Context (body_cps2_ok : forall s {R} continue break,
                body_cps2 s R continue break =
                match body s with
                | inl a => continue a
                | inr b => break b
                end).
    Lemma loop_cps2_ok n s {R} (timeout ret : _ -> R) :
      @loop_cps2 n s R timeout ret =
      match loop n s with
      | inl a => timeout a
      | inr b => ret b
      end.
    Proof.
      revert ret; revert timeout; revert R; revert s;
        induction n; intros; cbn; [reflexivity|].
      rewrite body_cps2_ok.
      destruct (body s); [|reflexivity].
      rewrite IHn. reflexivity.
    Qed.

    Lemma loop_fuel_0 s : loop 0 s = inl s.
    Proof. reflexivity. Qed.

    Lemma loop_fuel_S_first n s : loop (S n) s =
                                  match body s with
                                  | inl a => loop n a
                                  | inr b => inr b
                                  end.
    Proof. reflexivity. Qed.

    Lemma loop_fuel_S_last n s : loop (S n) s =
                                 match loop n s with
                                 | inl a => body a
                                 | inr b => loop n s
                                 end.
    Proof.
      revert s; induction n; cbn; intros s.
      { break_match; reflexivity. }
      { destruct (body s); cbn; rewrite <-?IHn; reflexivity. }
    Qed.

    Lemma loop_fuel_S_stable n s b (H : loop n s = inr b) : loop (S n) s = inr b.
    Proof.
      revert H; revert b; revert s; induction n; intros ? ? H.
      { cbn [loop nat_rect] in H. congruence_sum. }
      { rewrite loop_fuel_S_last.
        break_match; congruence_sum; reflexivity. }
    Qed.

    Lemma loop_fuel_add_stable n m s b (H : loop n s = inr b) : loop (m+n) s = inr b.
    Proof.
      induction m; intros.
      { rewrite PeanoNat.Nat.add_0_l. assumption. }
      { rewrite PeanoNat.Nat.add_succ_l.
        erewrite loop_fuel_S_stable; eauto. }
    Qed.

    Lemma loop_fuel_irrelevant n m s bn bm
          (Hn : loop n s = inr bn)
          (Hm : loop m s = inr bm)
      : bn = bm.
    Proof.
      destruct (Compare_dec.le_le_S_dec n m) as [H|H];
        destruct (PeanoNat.Nat.le_exists_sub _ _ H) as [d [? _]]; subst.
      { erewrite loop_fuel_add_stable in Hm by eassumption; congruence. }
      { erewrite loop_fuel_add_stable in Hn.
        { congruence_sum. reflexivity. }
        { erewrite loop_fuel_S_stable by eassumption. congruence. } }
    Qed.

    Lemma by_invariant' (inv P:_->Prop) measure f s0
          (init : inv s0 /\ measure s0 < f)
          (step : forall s, inv s -> match body s with
                                     | inl s' => inv s' /\ measure s' < measure s
                                     | inr s' => P s'
                                     end)
      : match loop f s0 with
        | inl a => False
        | inr s => P s
        end.
    Proof.
      revert dependent s0; induction f; intros; destruct_head'_and.
      { exfalso; lia. }
      { rewrite loop_fuel_S_first.
        specialize (step s0 H); destruct (body s0); [|assumption].
        destruct step.
        exact (IHf a ltac:(split; (assumption || lia))). }
    Qed.

    Lemma by_invariant (inv P:_->Prop) measure f s0
          (init : inv s0 /\ measure s0 < f)
          (step : forall s, inv s -> match body s with
                                     | inl s' => inv s' /\ measure s' < measure s
                                     | inr s' => P s'
                                     end)
      : exists b, loop f s0 = inr b /\ P b.
    Proof.
      pose proof (by_invariant' inv P measure f s0);
        specialize_by assumption; break_match_hyps; [contradiction|eauto].
    Qed.

    (* Completeness proof *)

    Definition iterations_required fuel s : option nat :=
      nat_rect _ None
               (fun n r =>
                  match r with
                  | Some _ => r
                  | None =>
                    match loop (S n) s with
                    | inl a => None
                    | inr b => Some (S n)
                    end
                  end
               ) fuel.

    Lemma iterations_required_correct fuel s :
      (forall m, iterations_required fuel s = Some m ->
                 1 <= m <= fuel /\
                 exists b, forall n, (n < m -> exists a, loop n s = inl a) /\ (m <= n -> loop n s = inr b))
      /\
      (iterations_required fuel s = None -> forall n, n <= fuel -> exists a, loop n s = inl a).
    Proof.
      induction fuel; intros.
      { cbn. split; intros; inversion_option.
        replace n with 0 by lia. rewrite loop_fuel_0. eauto. }
      { change (iterations_required (S fuel) s)
          with (match iterations_required fuel s with
                | None => match loop (S fuel) s with
                          | inl _ => None
                          | inr _ => Some (S fuel)
                          end
                | Some _ => iterations_required fuel s
                end) in *.
        destruct (iterations_required fuel s) in *.
        { split; intros; inversion_option; subst.
          destruct (proj1 IHfuel _ eq_refl); split; [lia|assumption]. }
        { destruct (loop (S fuel) s) eqn:HSf; split; intros; inversion_option; subst.
          { intros. destruct (PeanoNat.Nat.eq_dec n (S fuel)); subst; eauto; [].
            assert (n <= fuel) by lia. eapply IHfuel; congruence. }
          { split; [lia|].
            exists b; intros; split; intros.
            { eapply IHfuel; congruence || lia. }
            { eapply PeanoNat.Nat.le_exists_sub in H; destruct H as [?[]]; subst.
              eauto using loop_fuel_add_stable. } } } }
    Qed.

    Lemma iterations_required_step fuel s s' n
          (Hs : iterations_required fuel s = Some n)
          (Hstep : body s = inl s')
      : exists n', iterations_required fuel s' = Some n' /\ n = S n'.
    Proof.
      eapply iterations_required_correct in Hs.
      destruct Hs as [Hn [b Hs]].
      destruct n as [|n]; [pose proof (proj2 (Hs 0) ltac:(lia)) as Hx; inversion Hx|].
      exists n; split; [|reflexivity].
      pose proof (proj2 (Hs (S n)) ltac:(lia)) as H.
      rewrite loop_fuel_S_first, Hstep in H.
      destruct (iterations_required fuel s') as [x|] eqn:Hs' in *; [f_equal|exfalso].
      { eapply iterations_required_correct in Hs'; destruct Hs' as [Hx Hs'].
        destruct Hs' as [b' Hs'].
        destruct (Compare_dec.le_lt_dec n x) as [Hc|Hc].
        { destruct (Compare_dec.le_lt_dec x n) as [Hc'|Hc']; try lia; [].
          destruct (proj1 (Hs' n) Hc'); congruence. }
        { destruct (proj1 (Hs (S x)) ltac:(lia)) as [? HX].
          rewrite loop_fuel_S_first, Hstep in HX.
          pose proof (proj2 (Hs' x) ltac:(lia)).
          congruence. } }
      { eapply iterations_required_correct in Hs'; [|exact (ltac:(lia) : n <= fuel)].
        destruct Hs'.
        congruence. }
    Qed.

    Lemma invariant_complete (P:_->Prop) f s0 b (H:loop f s0 = inr b) (HP:P b)
      : exists inv measure,
        (inv s0 /\ measure s0 < f)
        /\ forall s, inv s -> match body s with
                              | inl s' => inv s' /\ measure s' < measure s
                              | inr s' => P s'
                              end.
    Proof.
      set (measure f s :=
             match iterations_required f s with
             | None => 0
             | Some s => pred s
             end).
      exists (fun s => match loop (S (measure f s)) s with
                       | inl a => False
                       | inr r => r = b end).
      exists (measure f); split; [ |repeat match goal with |- _ /\ _ => split end..].
      { cbv [measure].
        destruct (iterations_required f s0) eqn:Hs0;
          eapply iterations_required_correct in Hs0;
          [ .. | exact (ltac:(lia):f <= f)]; [|destruct_head'_ex; congruence].
        destruct Hs0 as [? [? Hs0]].
        replace (S (Nat.pred n)) with n by lia.
        pose proof (proj2 (Hs0 n) ltac:(lia)) as HH; rewrite HH.
        split; [exact (loop_fuel_irrelevant _ _ _ _ _ HH H) | lia]. }
      { intros s Hinv; destruct (body s) as [s'|c] eqn:Hstep.
        { destruct (loop (S (measure f s)) s) eqn:Hs; [contradiction|subst].
          cbv [measure] in *.
          destruct (iterations_required f s) eqn:Hs' in *;
            [|rewrite loop_fuel_S_last in Hs; cbv in Hs; congruence].
          destruct (iterations_required_step _ _ s' _ Hs' Hstep) as [? [HA ?]]; subst.
          rewrite HA.
          destruct (proj1 (iterations_required_correct _ _) _ HA) as [? [? [? HE']]].
          pose proof (HE' ltac:(constructor)) as HE; clear HE'.
          split; [|lia].
          replace (S (Nat.pred (S x))) with (S x) in * by lia.
          rewrite loop_fuel_S_first, Hstep in Hs.
          replace (S (Nat.pred x)) with x in * by lia; rewrite HE.
          exact (loop_fuel_irrelevant _ _ _ _ _ HE Hs). }
        { destruct (loop (S (measure f s)) s) eqn:Hs; [contradiction|subst].
          assert (HH: loop 1 s = inr c) by (cbn; rewrite Hstep; reflexivity).
          rewrite (loop_fuel_irrelevant _ _ _ _ _ HH Hs); exact HP. } }
    Qed.

    Lemma invariant_iff f s0 P :
      (exists b, loop f s0 = inr b /\ P b)
      <->
      (exists inv measure,
          (inv s0 /\ measure s0 < f)
          /\ forall s, inv s -> match body s with
                                | inl s' => inv s' /\ measure s' < measure s
                                | inr s' => P s'
                                end).
    Proof.
      repeat (intros || split || destruct_head'_ex || destruct_head'_and);
        eauto using invariant_complete, by_invariant.
    Qed.
  End Loops.
End core.

Module default.
  Section Default.
    Context {A B} (default : B) (body : A -> A + B).
    Definition loop fuel s : B :=
      match loop body fuel s with
      | inl s => default
      | inr s => s
      end.

    Lemma by_invariant inv (P:_->Prop) measure f s0
          (init : inv s0 /\ measure s0 < f)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop f s0).
    Proof.
      edestruct (by_invariant body inv P measure f s0) as [x [HA HB]]; eauto; [].
      apply (f_equal (fun r : A + B => match r with inl s => default | inr s => s end)) in HA.
      cbv [loop]; break_match; congruence.
    Qed.
  End Default.
End default.

Module silent.
  Section Silent.
    Context {state} (body : state -> state + state).
    Definition loop fuel s : state :=
      match loop body fuel s with
      | inl s => s
      | inr s => s
      end.

    Lemma by_invariant inv (P:_->Prop) measure f s0
          (init : inv s0 /\ measure s0 < f)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop f s0).
    Proof.
      edestruct (by_invariant body inv P measure f s0) as [x [A B]]; eauto; [].
      apply (f_equal (fun r : state + state => match r with inl s => s | inr s => s end)) in A.
      cbv [loop]; break_match; congruence.
    Qed.
  End Silent.
End silent.

Module while.
  Section While.
    Context {state}
            (test : state -> bool)
            (body : state -> state).

    Fixpoint while f s :=
      match f with
      | O => s
      | S f =>
        if test s
        then while f (body s)
        else s
      end.

    Local Definition lbody := fun s => if test s then inl (body s) else inr s.

    Lemma eq_loop f s : while f s = silent.loop lbody f s.
    Proof.
      revert s; induction f; intros s; [reflexivity|].
      cbn; cbv [silent.loop lbody] in *.
      rewrite IHf.
      cbn; cbv [silent.loop lbody].
      break_match; reflexivity.
    Qed.

    Lemma by_invariant inv P measure f s0
          (init : inv s0 /\ measure s0 < f)
          (step : forall s, inv s -> if test s
                                     then inv (body s) /\ measure (body s) < measure s
                                     else P s)
      : P (while f s0).
    Proof.
      rewrite eq_loop.
      eapply silent.by_invariant; eauto; []; intros s H; cbv [lbody].
      specialize (step s H); destruct (test s); eauto.
    Qed.
    
    Context (body_cps : state ~> state).

    Fixpoint while_cps f s :~> state :=
      match f with
      | O => return s
      | S f =>
        if test s
        then s <- body_cps s; while_cps f s
        else return s
      end.

    Context (body_cps_ok : forall s {R} f, body_cps s R f = f (body s)).
    Lemma loop_cps_ok n s {R} f : while_cps n s R f = f (while n s).
    Proof.
      revert s; induction n; intros s; [reflexivity|].
      cbn; break_match;
        cbv [cpscall cpsreturn]; rewrite ?body_cps_ok, ?IHn; reflexivity.
    Qed.
  End While.
End while.
Notation while := while.while.

Definition for2 {state} (test : state -> bool) (increment body : state -> state)
  := while test (fun s => let s := body s in increment s). 

Definition for3 {state} init test increment body fuel :=
  @for2 state test increment body fuel init.