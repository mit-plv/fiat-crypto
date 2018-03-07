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

Section Loops.
  Context {A B : Type} (body : A -> A + B).

  Definition loop (fuel : nat) (s : A) : A + B :=
    nat_rect _ (inl s)
             (fun _ s =>
                match s with
                | inl a => body a
                | inr b => s
                end
             ) fuel.

  Context (body_cps : A ~> A + B).
(* WHY does the following not work?
Set Printing Universes.
Check (nat_rect (fun _ => forall R, (A+B -> R)->R)
                (fun R ret => ret (inl s))
                (fun _ recurse =>
                   recurse (forall R, (A + B -> R) -> R)
                           (fun s R ret =>
                              match s with
                              | inl a =>
                                s' <- body_cps a;
                                ret s'
                              | inr b => ret (inr b)
                              end
                ))
                fuel).
The term
 "recurse (~> A + B)
    (fun (s : A + B) (R : Type@{Top.1376}) (ret : A + B -> R) =>
     match s with
     | inl a => s' <- body_cps a;
                ret s'
     | inr b => ret (inr b)
     end)" has type "forall (R : Type@{Top.1376}) (_ : forall _ : sum A B, R), R"
while it is expected to have type
 "forall (R : Type@{Top.1374}) (_ : forall _ : sum A B, R), R"
(universe inconsistency: Cannot enforce Top.1374 <= Top.1376 because Top.1376
< Top.1375 <= Top.1374). *)
  Definition loop_cps (fuel : nat) (s : A) : ~> A+B :=
    nat_rect (fun _ => forall R, (A + B -> R) -> R)
             (fun R ret => ret (inl s))
             (fun _ recurse R =>
                recurse ((A + B -> R) -> R)
                        (fun s ret =>
                           match s with
                           | inl a =>
                             s' <- body_cps a;
                               ret s'
                           | inr b => ret (inr b)
                           end
             )) fuel.

  Context (body_cps_ok : forall s {R} f, body_cps s R f = f (body s)).
  Lemma loop_cps_ok n s {R} f : loop_cps n s R f = f (loop n s).
  Proof.
    revert f; revert R; revert s; induction n; [reflexivity|].
    simpl loop; simpl loop_cps; intros. (* FIXME: unsimpl *)
    rewrite IHn; break_match; [|reflexivity].
    cbv [cpscall]; rewrite body_cps_ok; reflexivity.
  Qed.

  Context (body_cps2 : A -> forall {R}, (A -> R) -> (B -> R) -> R).
  Definition loop_cps2 (fuel : nat) (s : A) :
    forall {R} (timeout : A -> R) (ret : B -> R), R :=
    nat_rect (fun _ => forall R, (A -> R) -> (B -> R) -> R)
             (fun R continue break => continue s)
             (fun _ recurse R continue break =>
                recurse R (fun a => body_cps2 a R continue break) break
             )
             fuel.

  Context (body_cps2_ok : forall s {R} continue break,
              body_cps2 s R continue break =
              match body s with
              | inl a => continue a
              | inr b => break b
              end).
  Lemma loop_cps2_ok n s {R} timeout ret :
    @loop_cps2 n s R timeout ret =
    match loop n s with
    | inl a => timeout a
    | inr b => ret b
    end.
  Proof.
    revert ret; revert timeout; revert R; revert s; induction n;
      [intros; reflexivity|].
    simpl loop; simpl loop_cps2; intros. (* FIXME: unsimpl *)
    repeat (rewrite IHn || rewrite body_cps2_ok || break_match || congruence).
  Qed.

  Lemma loop_fuel_0 s : loop 0 s = inl s.
  Proof. reflexivity. Qed.

  Lemma loop_fuel_S n s : loop (S n) s =
                          match loop n s with
                          | inl a => body a
                          | inr b => loop n s
                          end.
  Proof. reflexivity. Qed.

  Lemma loop_fuel_S_stable n s b (H : loop n s = inr b) : loop (S n) s = inr b.
  Proof.
    revert H; revert b; revert s; induction n; intros ? ? H.
    { cbn [loop nat_rect] in H. congruence_sum. }
    { rewrite loop_fuel_S.
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

  Lemma by_invariant_with_inv_for_measure' (inv P:_->Prop) measure f s0
          (inv_init : inv s0)
          (inv_continue : forall s s', body s = inl s' -> inv s -> inv s')
          (inv_break : forall s s', body s = inr s' -> inv s -> P s')
          (measure_decreases : forall s s', body s = inl s' -> inv s -> measure s' < measure s)
          (measure_fuel : measure s0 < f)
    : match loop f s0 with
      | inl a => inv a
      | inr s => P s
      end.
  Proof.
    revert dependent s0; induction f; intros.
    { exfalso; lia. }
  Abort. (* I don't know how to prove this one *)

  Lemma by_invariant' P inv f s0
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
    { rewrite loop_fuel_S.
      destruct (loop f s0) eqn:Hn;
        [ destruct (body a) eqn:Ha; eauto | eauto ]. }
  Qed.

  Lemma by_invariant P inv f s0 b (H : loop f s0 = inr b)
          (inv_init : inv s0)
          (inv_continue : forall s s', body s = inl s' -> inv s -> inv s')
          (inv_break : forall s s', body s = inr s' -> inv s -> P s')
      : P b.
  Proof.
    pose proof (by_invariant' P inv f s0) as HH.
    rewrite H in HH; eauto.
  Qed.

  Lemma invariant_complete (P:_->Prop) f s0 b (Hf : loop f s0 = inr b) (H : P b) :
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
      rewrite loop_fuel_S, Hn, Hss'. reflexivity. }
    { intros s s' Hss' [n Hn].
      destruct (loop n s0) eqn:Hn_; [|contradiction]; subst a; rename Hn_ into Hn.
      assert (loop (S n) s0 = inr s') as HH by
            (rewrite loop_fuel_S, Hn, Hss'; reflexivity).
      rewrite (loop_fuel_irrelevant _ _ _ _ _ HH Hf); assumption. }
  Qed.

  Lemma loop_invariant_iff P f s0 b (H : loop f s0 = inr b) :
      P b <->
      (exists (inv : A -> Prop),
          inv s0
          /\ (forall s s', body s = inl s' -> inv s -> inv s')
          /\ (forall s s', body s = inr s' -> inv s -> P s')).
  Proof.
    split.
    { intros; eapply invariant_complete; eauto. }
    { intros [? [?[]]]; eapply by_invariant; eauto. }
  Qed.

  (*
WIP WIP
  
  Fixpoint loop' (fuel : nat) (s : A) {struct fuel} : A + B :=
    match fuel with
    | O => inl s
    | S fuel' =>
      match body s with
      | inl s => loop' fuel' s
      | inr b => inr b
      end end.

  Fixpoint loop'_cps (fuel : nat) (s : A) {struct fuel} : ~> A + B :=
    match fuel with
    | O => return (inl s)
    | S fuel' =>
      s_b <- body_cps s;
        match s_b with
        | inl s => loop'_cps fuel' s
        | inr b => return (inr b)
        end
    end.
    
  
  Lemma loop_break_step fuel start state :
    (body start = inl state) ->
    loop fuel start = inr state.
  Proof.
    destruct fuel; simpl loop; break_match; intros; congruence.
  Qed.

  Lemma loop_continue_step fuel start state :
    (body start = inr state) ->
    loop fuel start =
    match fuel with | O => inl state | S fuel' => loop fuel' state end.
  Proof.
    destruct fuel; simpl loop; break_match; intros; congruence.
  Qed.

  (* TODO: provide [invariant state] to proofs of this *)
  Definition progress (measure : continue_state -> nat) :=
    forall state state', body state = inr state' -> measure state' < measure state.
  Definition terminates fuel start := forall l, loop fuel start <> inl l.
  Lemma terminates_by_measure measure (H : progress measure) :
    forall fuel start, measure start <= fuel -> terminates fuel start.
  Proof.
    induction fuel; intros;
      repeat match goal with
             | _ => solve [ congruence | lia ]
             | _ => progress cbv [progress terminates] in *
             | _ => progress cbn [loop]
             | _ => progress break_match
             | H : forall _ _, body _ = inr _ -> _ , Heq : body _ = inr _ |- _ => specialize (H _ _ Heq)
             | _ => eapply IHfuel
    end.
  Qed.

  Definition loop_default fuel start default
    : break_state :=
    sum_rect
      (fun _ => break_state)
      (fun _ => default)
      (fun result => result)
      (loop fuel start).

  Lemma loop_default_eq fuel start default
        (Hterm : terminates fuel start) :
    loop fuel start = inr (loop_default fuel start default).
  Proof.
    cbv [terminates loop_default sum_rect] in *; break_match; congruence.
  Qed.
End Loops.

Definition by_invariant {continue_state break_state body fuel start default}
           invariant measure P invariant_start invariant_continue invariant_break le_start progress 
  := proj2 (@invariant_iff continue_state break_state body fuel start default (terminates_by_measure body measure progress fuel start le_start) P)
           (ex_intro _ invariant (conj invariant_start (conj invariant_continue invariant_break))).
Arguments terminates_by_measure {_ _ _}.
                 
Module while.
  Section While.
    Context {state}
            (test : state -> bool)
            (body : state -> state).

    Fixpoint while (fuel: nat) (s : state) {struct fuel} : state :=
      if test s
      then
        let s := body s in
        match fuel with
        | O => s
        | S fuel' => while fuel' s
        end
      else s.

    Section AsLoop.
      Local Definition lbody := fun s => if test s then inr (body s) else inl s.

      Lemma eq_loop : forall fuel start, while fuel start = loop_default lbody fuel start (while fuel start).
      Proof.
        induction fuel; intros;
          cbv [lbody loop_default sum_rect id] in *;
          cbn [while loop]; [|rewrite IHfuel]; break_match; auto.
      Qed.

      Lemma by_invariant fuel start 
            (invariant : state -> Prop) (measure : state -> nat) (P : state -> Prop)
            (_: invariant start)
            (_: forall s, invariant s -> if test s then invariant (body s) else P s)
            (_: measure start <= fuel)
            (_: forall s, if test s then measure (body s) < measure s else True)
        : P (while fuel start).
      Proof.
        rewrite eq_loop; cbv [lbody].
        eapply (by_invariant invariant measure);
          repeat match goal with
                 | [ H : forall s, invariant s -> _, G: invariant ?s |- _ ] => unique pose proof (H _ G)
                 | [ H : forall s, if ?f s then _ else _, G: ?f ?s = _ |- _ ] => unique pose proof (H s)
                 | _ => solve [ trivial | congruence ]
                 | _ => progress cbv [progress]
                 | _ => progress intros
                 | _ => progress subst
                 | _ => progress inversion_sum
                 | _ => progress break_match_hyps (* FIXME: this must be last? *)
                 end.
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