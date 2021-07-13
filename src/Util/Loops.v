Require Import Coq.micromega.Lia.

Module Import core.
  Section Loops.
    Context {A B : Type} (body : A -> A + B).

    (* the fuel parameter is only present to allow defining a loop
    without proving its termination. The loop body does not have
    access to the amount of remaining fuel, and thus increasing fuel
    beyond termination cannot change the behavior. fuel counts full
    loops -- the one that executes "break" is not included *)

    Fixpoint loop (fuel : nat) (s : A) {struct fuel} : A + B :=
      let s := body s in
      match s with
      | inl a =>
        match fuel with
        | O => inl a
        | S fuel' => loop fuel' a
        end
      | inr b => inr b
      end.


    Context (body_cps : A -> forall T, (A + B -> T) -> T).

    Fixpoint loop_cps (fuel : nat) (s : A) {struct fuel} : forall T, (A + B -> T) -> T :=
      body_cps s _ (fun s =>
        match s with
        | inl a =>
          match fuel with
          | O => fun _ k => k (inl a)
          | S fuel' => loop_cps fuel' a
          end
        | inr b => fun _ k => k (inr b)
        end).

    Context (body_cps_ok : forall s {R} f, body_cps s R f = f (body s)).
    Lemma loop_cps_ok n s {R} f : loop_cps n s R f = f (loop n s).
    Proof.
      revert f; revert R; revert s; induction n;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbv [cpsreturn cpscall] in *
               | _ => progress cbn
               | _ => progress rewrite ?body_cps_ok
               | _ => progress rewrite ?IHn
               | |- context [body s] => destruct (body s) eqn:?
               | _ => reflexivity
               end.
    Qed.

    Context (body_cps2 : A -> forall {R}, (A -> R) -> (B -> R) -> R).
    Fixpoint loop_cps2 (fuel : nat) (s : A) {R} (timeout:A->R) (ret:B->R) {struct fuel} : R :=
      body_cps2 s R
                (fun a =>
                   match fuel with
                   | O => timeout a
                   | S fuel' => @loop_cps2 fuel' a R timeout ret
                   end)
                (fun b => ret b).

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
      revert timeout; revert ret; revert R; revert s; induction n;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbv [cpsreturn cpscall] in *
               | _ => progress cbn
               | _ => progress rewrite ?body_cps2_ok
               | _ => progress rewrite ?IHn
               | _ => progress subst
               | |- context [body s] => destruct (body s) eqn:?
               | _ => reflexivity
               end.
    Qed.

    Local Lemma loop_fuel_0 s : loop 0 s = body s.
    Proof. cbv; destruct (body s); reflexivity. Qed.

    Local Lemma loop_fuel_S_first n s : loop (S n) s =
                                  match body s with
                                  | inl a => loop n a
                                  | inr b => inr b
                                  end.
    Proof. reflexivity. Qed.

    Local Lemma loop_fuel_S_last n s : loop (S n) s =
                                 match loop n s with
                                 | inl a => body a
                                 | inr b => loop n s
                                 end.
    Proof.
      revert s; induction n; cbn; intros s.
      { repeat destruct (body _); reflexivity. }
      { destruct (body s); cbn; rewrite <-?IHn; reflexivity. }
    Qed.

    Local Lemma loop_fuel_S_stable n s b (H : loop n s = inr b) : loop (S n) s = inr b.
    Proof.
      revert H; revert b; revert s; induction n; intros ? ? H.
      { cbn [loop nat_rect] in *; destruct (body s); congruence. }
      { rewrite loop_fuel_S_last; destruct (loop (S n) s); congruence. }
    Qed.

    Local Lemma loop_fuel_add_stable n m s b (H : loop n s = inr b) : loop (m+n) s = inr b.
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
        { inversion Hn. reflexivity. }
        { erewrite loop_fuel_S_stable by eassumption. congruence. } }
    Qed.

    Local Lemma by_invariant_fuel' (inv:_->Prop) measure P f s0
          (init : inv s0 /\ measure s0 <= f)
          (step : forall s, inv s -> match body s with
                                     | inl s' => inv s' /\ measure s' < measure s
                                     | inr s' => P s'
                                     end)
      : match loop f s0 with
        | inl a => False
        | inr s => P s
        end.
    Proof.
      revert dependent s0; induction f; intros.
      { specialize (step s0 (proj1 init)); cbv. destruct (body _); [lia|assumption]. }
      { rewrite loop_fuel_S_first.
        specialize (step s0 (proj1 init)); destruct (body s0); [|assumption].
        destruct step.
        exact (IHf a ltac:(split; (assumption || lia))). }
    Qed.

    Lemma by_invariant_fuel (inv:_->Prop) measure P f s0
          (init : inv s0 /\ measure s0 <= f)
          (step : forall s, inv s -> match body s with
                                     | inl s' => inv s' /\ measure s' < measure s
                                     | inr s' => P s'
                                     end)
      : exists b, loop f s0 = inr b /\ P b.
    Proof.
      pose proof (by_invariant_fuel' inv measure P f s0);
        destruct (loop f s0); [exfalso|]; eauto.
    Qed.

    Lemma by_invariant (inv:_->Prop) measure P s0
          (init : inv s0)
          (step : forall s, inv s -> match body s with
                                     | inl s' => inv s' /\ measure s' < measure s
                                     | inr s' => P s'
                                     end)
      : exists b, loop (measure s0) s0 = inr b /\ P b.
    Proof. eapply by_invariant_fuel; eauto. Qed.

    (* Completeness proof *)

    Definition iterations_required fuel s : option nat :=
      nat_rect _ None
               (fun n r =>
                  match r with
                  | Some _ => r
                  | None =>
                    match loop n s with
                    | inl a => None
                    | inr b => Some n
                    end
                  end
               ) fuel.

    Lemma iterations_required_correct fuel s :
      (forall m, iterations_required fuel s = Some m ->
                 m < fuel /\
                 exists b, forall n, (n < m -> exists a, loop n s = inl a) /\ (m <= n -> loop n s = inr b))
      /\
      (iterations_required fuel s = None -> forall n, n < fuel -> exists a, loop n s = inl a).
    Proof.
      induction fuel; intros.
      { cbn. split; [congruence|intros; lia]. }
      { change (iterations_required (S fuel) s)
          with (match iterations_required fuel s with
                | None => match loop fuel s with
                          | inl _ => None
                          | inr _ => Some fuel
                          end
                | Some _ => iterations_required fuel s
                end) in *.
        destruct (iterations_required fuel s) in *.
        { split; intros ? H; [ inversion H; subst | congruence ].
          destruct (proj1 IHfuel _ eq_refl); split; [lia|assumption]. }
        { destruct (loop fuel s) eqn:HSf; split; intros; try congruence.
          { destruct (PeanoNat.Nat.eq_dec n fuel); subst; eauto; [].
            eapply IHfuel; lia || congruence. }
          { split; match goal with H:Some _=Some _|-_=>inversion H end; [lia|].
            exists b; intros; split; intros.
            { eapply IHfuel; congruence || lia. }
            { destruct (PeanoNat.Nat.le_exists_sub m n ltac:(assumption)) as [?[]]; subst.
              eauto using loop_fuel_add_stable. } } } }
    Qed.

    Lemma iterations_required_step fuel s s' n
          (Hs : iterations_required fuel s = Some (S n))
          (Hstep : body s = inl s')
      : iterations_required fuel s' = Some n.
    Proof.
      eapply iterations_required_correct in Hs.
      destruct Hs as [Hn [b Hs]].
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
      { eapply iterations_required_correct in Hs'; [|exact Hn].
        destruct Hs' as [? Hs']; rewrite loop_fuel_S_last, H in Hs'; congruence. }
    Qed.

    Local Lemma invariant_complete (P:_->Prop) f s0 b (H:loop f s0 = inr b) (HP:P b)
      : exists inv measure,
        (inv s0 /\ measure s0 <= f)
        /\ forall s, inv s -> match body s with
                              | inl s' => inv s' /\ measure s' < measure s
                              | inr s' => P s'
                              end.
    Proof.
      set (measure s := match iterations_required (S f) s with None => 0 | Some n => n end).
      exists (fun s => match loop (measure s) s with
                       | inl a => False
                       | inr r => r = b end).
      exists (measure); split; [ |repeat match goal with |- _ /\ _ => split end..].
      { cbv [measure].
        destruct (iterations_required (S f) s0) eqn:Hs0;
          eapply iterations_required_correct in Hs0;
          [ .. | exact (ltac:(lia):f <S f)]; [|destruct Hs0; congruence].
        destruct Hs0 as [? [? Hs0]]; split; [|lia].
        pose proof (proj2 (Hs0 n) ltac:(lia)) as HH; rewrite HH.
        exact (loop_fuel_irrelevant _ _ _ _ _ HH H). }
      { intros s Hinv; destruct (body s) as [s'|c] eqn:Hstep.
        { destruct (loop (measure s) s) eqn:Hs; [contradiction|subst].
          cbv [measure] in *.
          destruct (iterations_required (S f) s) eqn:Hs' in *; try destruct n;
            try (rewrite loop_fuel_0 in Hs; congruence); [].
          pose proof (iterations_required_step _ _ s' _ Hs' Hstep) as HA.
          rewrite HA.
          destruct (proj1 (iterations_required_correct _ _) _ HA) as [? [? [? HE']]].
          pose proof (HE' ltac:(constructor)) as HE; clear HE'.
          split; [|lia].
          rewrite loop_fuel_S_first, Hstep in Hs.
          destruct (loop n s'); congruence. }
        { destruct (loop (measure s) s) eqn:Hs; [contradiction|].
          assert (HH: loop 1 s = inr c) by (cbn; rewrite Hstep; reflexivity).
          rewrite (loop_fuel_irrelevant _ _ _ _ _ HH Hs); congruence. } }
    Qed.

    Lemma invariant_iff P f s0 :
      (exists b, loop f s0 = inr b /\ P b)
      <->
      (exists inv measure,
          (inv s0 /\ measure s0 <= f)
          /\ forall s, inv s -> match body s with
                                | inl s' => inv s' /\ measure s' < measure s
                                | inr s' => P s'
                                end).
    Proof.
      split; [intros [? []] | intros [? [? []]] ];
        eauto using invariant_complete, by_invariant_fuel.
    Qed.
  End Loops.

  Global Arguments loop_cps_ok {A B body body_cps}.
  Global Arguments loop_cps2_ok {A B body body_cps2}.
  Global Arguments by_invariant_fuel {A B body} inv measure P.
  Global Arguments by_invariant {A B body} inv measure P.
  Global Arguments invariant_iff {A B body} P f s0.
  Global Arguments iterations_required_correct {A B body} fuel s.
End core.

Module default.
  Section Default.
    Context {A B} (default : B) (body : A -> A + B).
    Definition loop fuel s : B :=
      match loop body fuel s with
      | inl s => default
      | inr s => s
      end.

    Lemma by_invariant_fuel inv measure (P:_->Prop) f s0
          (init : inv s0 /\ measure s0 <= f)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop f s0).
    Proof.
      edestruct (by_invariant_fuel (body:=body) inv measure P f s0) as [x [HA HB]]; eauto; [].
      apply (f_equal (fun r : A + B => match r with inl s => default | inr s => s end)) in HA.
      cbv [loop]; destruct (core.loop body f s0); congruence.
    Qed.

    Lemma by_invariant (inv:_->Prop) measure P s0
          (init : inv s0)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop (measure s0) s0).
    Proof. eapply by_invariant_fuel; eauto. Qed.
  End Default.
  Global Arguments by_invariant_fuel {A B default body} inv measure P.
  Global Arguments by_invariant {A B default body} inv measure P.
End default.

Module silent.
  Section Silent.
    Context {state} (body : state -> state + state).
    Definition loop fuel s : state :=
      match loop body fuel s with
      | inl s => s
      | inr s => s
      end.

    Lemma by_invariant_fuel inv measure (P:_->Prop) f s0
          (init : inv s0 /\ measure s0 <= f)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop f s0).
    Proof.
      edestruct (by_invariant_fuel (body:=body) inv measure P f s0) as [x [A B]]; eauto; [].
      apply (f_equal (fun r : state + state => match r with inl s => s | inr s => s end)) in A.
      cbv [loop]; destruct (core.loop body f s0); congruence.
    Qed.

    Lemma by_invariant (inv:_->Prop) measure P s0
          (init : inv s0)
          (step: forall s, inv s -> match body s with
                                    | inl s' => inv s' /\ measure s' < measure s
                                    | inr s' => P s'
                                    end)
      : P (loop (measure s0) s0).
    Proof. eapply by_invariant_fuel; eauto. Qed.
  End Silent.

  Global Arguments by_invariant_fuel {state body} inv measure P.
  Global Arguments by_invariant {state body} inv measure P.
End silent.

Module while.
  Section While.
    Context {state}
            (test : state -> bool)
            (body : state -> state).

    Fixpoint while f s :=
      if test s
      then
        let s := body s in
        match f with
        | O => s
        | S f => while f s
        end
      else s.

    Local Definition lbody := fun s => if test s then inl (body s) else inr s.

    Lemma eq_loop f s : while f s = silent.loop lbody f s.
    Proof.
      revert s; induction f; intros s;
        repeat match goal with
               | _ => progress cbn in *
               | _ => progress cbv [silent.loop lbody] in *
               | _ => rewrite IHf
               | |- context[test s] => destruct (test s)
               | _ => congruence
               end.
    Qed.

    Lemma by_invariant_fuel inv measure P f s0
          (init : inv s0 /\ measure s0 <= f)
          (step : forall s, inv s -> if test s
                                     then inv (body s) /\ measure (body s) < measure s
                                     else P s)
      : P (while f s0).
    Proof.
      rewrite eq_loop.
      eapply silent.by_invariant_fuel; eauto; []; intros s H; cbv [lbody].
      specialize (step s H); destruct (test s); eauto.
    Qed.

    Lemma by_invariant (inv:_->Prop) measure P s0
          (init : inv s0)
          (step : forall s, inv s -> if test s
                                     then inv (body s) /\ measure (body s) < measure s
                                     else P s)
      : P (while (measure s0) s0).
    Proof. eapply by_invariant_fuel; eauto. Qed.

    Context (body_cps : state -> forall T, (state -> T) -> T).

    Fixpoint while_cps f s : forall T, (state -> T) -> T :=
      if test s
      then
        body_cps s _ (fun s =>
          match f with
          | O => fun _ k => k s
          | S f =>while_cps f s
          end)
      else fun _ k => k s.

    Context (body_cps_ok : forall s {R} f, body_cps s R f = f (body s)).
    Lemma loop_cps_ok n s {R} f : while_cps n s R f = f (while n s).
    Proof.
      revert s; induction n; intros s;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbv [cpsreturn cpscall] in *
               | _ => progress cbn
               | _ => progress rewrite ?body_cps_ok
               | _ => progress rewrite ?IHn
               | |- context[test s] => destruct (test s)
               | _ => reflexivity
               end.
    Qed.
  End While.
  Global Arguments by_invariant_fuel {state test body} inv measure P.
  Global Arguments by_invariant {state test body} inv measure P.

  Section TwoLoops.
    Context {state1 state2 : Type}
            (test1 : state1 -> bool) (body1 : state1 -> state1)
            (test2 : state2 -> bool) (body2 : state2 -> state2).

    Lemma preservation
          (R : state1 -> state2 -> Prop)
          (Htest: forall s1 s2, R s1 s2 -> test1 s1 = test2 s2)
          (Hbody: forall s1 s2, test2 s2 = true -> R s1 s2 -> R (body1 s1) (body2 s2)) :
      forall fuel init1 init2,
        R init1 init2 ->
        R (while test1 body1 fuel init1) (while test2 body2 fuel init2).
    Proof.
      induction fuel; intros; cbn [while];
        erewrite Htest by eauto; case_eq (test2 init2); auto.
    Qed.
  End TwoLoops.
End while.
Notation while := while.while.

Definition for2 {state} (test : state -> bool) (increment body : state -> state)
  := while test (fun s => let s := body s in increment s).

Definition for3 {state} init test increment body fuel :=
  @for2 state test increment body fuel init.
