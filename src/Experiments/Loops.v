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

(* TODO: do we have these anywhere? 
Ltac forward H :=
  match type of H with
  | ?A -> ?B => let HA := fresh in assert A as HA; [|specialize(H HA)]
  end.
Ltac forward_by H t :=
  match type of H with
  | ?A -> ?B => let HA := fresh in assert A as HA by t; [|specialize(H HA)]
  end.
 *)

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
          (inv_init : inv s0 /\ measure s0 < f)
          (inv_continue : forall s s', body s = inl s' -> inv s -> inv s' /\ measure s' < measure s)
          (inv_break : forall s s', body s = inr s' -> inv s -> P s')
    : match loop f s0 with
      | inl a => False
      | inr s => P s
      end.
  Proof.
    revert dependent s0; induction f; intros; destruct_head'_and.
    { exfalso; lia. }
    { rewrite loop_fuel_S_first.
      destruct (body s0) eqn:Hs0a; [|solve [eauto] ].
      specialize (IHf a).
      destruct (inv_continue s0 a Hs0a ltac:(assumption)).
      specialize_by (split; (auto || lia)); auto. }
  Qed.

  Lemma by_invariant (inv P:_->Prop) measure f s0
          (inv_init : inv s0 /\ measure s0 < f)
          (inv_continue : forall s s', body s = inl s' -> inv s -> inv s' /\ measure s' < measure s)
          (inv_break : forall s s', body s = inr s' -> inv s -> P s')
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
          /\ (forall s s', body s = inl s' -> inv s -> inv s' /\ measure s' < measure s)
          /\ (forall s s', body s = inr s' -> inv s -> P s').
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
    { intros s s' Hstep Hinv.
      destruct (loop (S (measure f s)) s) eqn:Hs; [contradiction|subst].
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
    { intros s c Hstep Hinv.
      destruct (loop (S (measure f s)) s) eqn:Hs; [contradiction|subst].
      assert (HH: loop 1 s = inr c) by (cbn; rewrite Hstep; reflexivity).
      rewrite (loop_fuel_irrelevant _ _ _ _ _ HH Hs); exact HP. }
  Qed.

  Lemma invariant_iff f s0 P :
    (exists b, loop f s0 = inr b /\ P b)
    <->
    (exists inv measure,
        (inv s0 /\ measure s0 < f)
        /\ (forall s s', body s = inl s' -> inv s -> inv s' /\ measure s' < measure s)
        /\ (forall s s', body s = inr s' -> inv s -> P s')).
  Proof.
    repeat (intros || split || destruct_head'_ex || destruct_head'_and);
      eauto using invariant_complete, by_invariant.
  Qed.

  Lemma partial_by_invariant P inv f s0
        (inv_init : inv s0)
        (inv_continue : forall s s', body s = inl s' -> inv s -> inv s')
        (inv_break : forall s s', body s = inr s' -> inv s -> P s')
    : match loop f s0 with
      | inl a => inv a
      | inr s => P s
      end.
  Proof.
    induction f.
    { rewrite loop_fuel_0; auto. }
    { rewrite loop_fuel_S_last.
      destruct (loop f s0) eqn:Hn;
        [ destruct (body a) eqn:Ha; eauto | eauto ]. }
  Qed.

  Lemma by_invariant_inr P inv f s0 b (H : loop f s0 = inr b)
          (inv_init : inv s0)
          (inv_continue : forall s s', body s = inl s' -> inv s -> inv s')
          (inv_break : forall s s', body s = inr s' -> inv s -> P s')
      : P b.
  Proof.
    pose proof (partial_by_invariant P inv f s0) as HH.
    rewrite H in HH; eauto.
  Qed.

  Lemma by_invariant_inr_complete (P:_->Prop) f s0 b (Hf : loop f s0 = inr b) (H : P b) :
    exists (inv : A -> Prop),
      inv s0
      /\ (forall s s', body s = inl s' -> inv s -> inv s')
      /\ (forall s s', body s = inr s' -> inv s -> P s').
  Proof.
    exists (fun s => exists n, match loop n s0 with
                               | inl a => a = s
                               | _ => False end).
    repeat split.
    { exists 0. rewrite loop_fuel_0. reflexivity. }
    { intros s s' Hss' [n Hn]. exists (S n).
      destruct (loop n s0) eqn:Hn_; [|contradiction]; subst a; rename Hn_ into Hn.
      rewrite loop_fuel_S_last, Hn, Hss'. reflexivity. }
    { intros s s' Hss' [n Hn].
      destruct (loop n s0) eqn:Hn_; [|contradiction]; subst a; rename Hn_ into Hn.
      assert (loop (S n) s0 = inr s') as HH by
            (rewrite loop_fuel_S_last, Hn, Hss'; reflexivity).
      rewrite (loop_fuel_irrelevant _ _ _ _ _ HH Hf); assumption. }
  Qed.

  Lemma invariant_inr_iff P f s0 b (H : loop f s0 = inr b) :
      P b <->
      (exists (inv : A -> Prop),
          inv s0
          /\ (forall s s', body s = inl s' -> inv s -> inv s')
          /\ (forall s s', body s = inr s' -> inv s -> P s')).
  Proof.
    split.
    { intros; eapply by_invariant_inr_complete; eauto. }
    { intros [? [?[]]]; eapply by_invariant_inr; eauto. }
  Qed.
End Loops.

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
          (step : forall s s' : state,
              body s = inl s' -> inv s -> inv s' /\ measure s' < measure s)
          (fini: forall s s' : state, body s = inr s' -> inv s -> P s')
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

    Section AsLoop.
      Local Definition lbody := fun s => if test s then inl (body s) else inr s.

      Lemma eq_loop f s : while f s = sum_rect (fun _ => _) id id (loop lbody f s).
      Proof.
        revert s; induction f; intros s; [reflexivity|].
        { cbv [lbody sum_rect id] in *; cbn in *.
          rewrite IHf; break_innermost_match; reflexivity. }
      Qed.

      Lemma by_invariant inv P measure f s0
            (init : inv s0 /\ measure s0 < f)
            (step : forall s, if test s
                              then inv s -> inv (body s) /\ measure (body s) < measure s
                              else P (body s))
        : P (while f s0).
      Proof.
      Qed.
    End AsLoop.
  End While.
  Arguments by_invariant {_ _ _ _ _}.
End while.
Notation while := while.while.

Definition for2 {state} (test : state -> bool) (increment body : state -> state)
  := while test (fun s => increment (body s)). 

Definition for3 {state} init test increment body fuel :=
  @for2 state test increment body fuel init.
*)