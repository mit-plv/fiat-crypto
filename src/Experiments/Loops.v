Require Import Coq.Lists.List.
Require Import Lia. 
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Crypto.Util.ListUtil. (* for tests *)

Section Loops.
  Context {continue_state break_state}
          (body : continue_state -> break_state + continue_state)
          (body_cps : continue_state ->
                  forall {T}, (break_state + continue_state -> T)
                              -> T).

  Definition funapp {A B} (f : A -> B) (x : A) := f x.

  Fixpoint loop_cps (fuel: nat) (start : continue_state)
           {T} (ret : break_state -> T) : continue_state + T :=
    funapp
    (body_cps start _) (fun next =>
                      match next with
                      | inl state => inr (ret state)
                      | inr state =>
                        match fuel with
                        | O => inl state
                        | S fuel' =>
                          loop_cps fuel' state ret
                        end end).
  
  Fixpoint loop (fuel: nat) (start : continue_state)
    : continue_state + break_state :=
    match (body start) with
    | inl state => inr state
    | inr state => 
      match fuel with
      | O => inl state
      | S fuel' => loop fuel' state
      end end.
  
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

  Lemma invariant_iff fuel start default (H : terminates fuel start) P :
      P (loop_default fuel start default) <->
      (exists (inv : continue_state -> Prop),
          inv start
          /\ (forall s s', body s = inr s' -> inv s -> inv s')
          /\ (forall s s', body s = inl s' -> inv s -> P s')).
  Proof.
    split;
      [ exists (fun st => exists f e, (loop f st = inr e /\ P e ))
      | destruct 1 as [?[??]]; revert dependent start; induction fuel ];
      repeat match goal with
             | _ => solve [ trivial | congruence | eauto ] 
             | _ => progress destruct_head' @ex
             | _ => progress destruct_head' @and
             | _ => progress intros
             | _ => progress cbv [loop_default terminates] in *
             | _ => progress cbn [loop] in *
             | _ => progress erewrite loop_default_eq by eassumption
             | _ => progress erewrite loop_continue_step in * by eassumption
             | _ => progress erewrite loop_break_step in * by eassumption
             | _ => progress break_match_hyps
             | _ => progress break_match
             | _ => progress eexists
             | H1:_, c:_ |- _ => progress specialize (H1 c); congruence
             end.
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

Module _test.
  Section GCD.
    Definition gcd_step :=
      fun '(a, b) => if Nat.ltb a b
                     then inr (a, b-a)
                     else if Nat.ltb b a
                          then inr (a-b, b)
                          else inl a.

    Definition gcd fuel a b := loop_default gcd_step fuel (a,b) 0.

    (* Eval cbv [gcd loop_default loop gcd_step] in (gcd 10 5 7). *)
    
    Example gcd_test : gcd 1000 28 35 = 7 := eq_refl.

    Definition gcd_step_cps
      : (nat * nat) -> forall T, (nat + (nat * nat) -> T) -> T 
      :=
        fun st T ret =>
          let a := fst st in
          let b := snd st in
          if Nat.ltb a b
          then ret (inr (a, b-a))
          else if Nat.ltb b a
               then ret (inr (a-b, b))
               else ret (inl a).

    Definition gcd_cps fuel a b {T} (ret:nat->T)
      := loop_cps gcd_step_cps fuel (a,b) ret.

    Example gcd_test2 : gcd_cps 1000 28 35 id = inr 7 := eq_refl.
    
    (* Eval cbv [gcd_cps loop_cps gcd_step_cps id] in (gcd_cps 2 5 7 id). *)

  End GCD.

  (* simple example--set all elements in a list to 0 *)
  Section ZeroLoop.
    Import Crypto.Util.ListUtil.

    Definition zero_body (state : nat * list nat) :
      list nat + (nat * list nat) :=
      if dec (fst state < length (snd state))
      then inr (S (fst state), set_nth (fst state) 0 (snd state))
      else inl (snd state).

    Lemma zero_body_progress (arr : list nat) :
      progress zero_body (fun state : nat * list nat => length (snd state) - fst state).
    Proof.
      cbv [zero_body progress]; intros until 0;
        repeat match goal with
               | _ => progress autorewrite with cancel_pair distr_length
               | _ => progress subst
               | _ => progress break_match; intros
               | _ => congruence
               | H: inl _ = inl _ |- _ => injection H; intros; subst; clear H
               | H: inr _ = inr _ |- _ => injection H; intros; subst ;clear H
               | _ => lia
               end.
    Qed.

    Definition zero_loop (arr : list nat) : list nat :=
      loop_default zero_body (length arr) (0,arr) nil.
    
    Definition zero_invariant (state : nat * list nat) :=
      fst state <= length (snd state)
      /\ forall n, n < fst state -> nth_default 0 (snd state) n = 0.

    Lemma zero_correct (arr : list nat) :
      forall n, nth_default 0 (zero_loop arr) n = 0.
    Proof.
      intros. cbv [zero_loop].
      eapply (by_invariant zero_invariant); eauto using zero_body_progress;
        [ cbv [zero_invariant]; autorewrite with cancel_pair; split; intros; lia | ..];
        cbv [zero_invariant zero_body];
        intros until 0;
        break_match; intros;
          repeat match goal with
                 | _ => congruence
                 | H: inl _ = inl _ |- _ => injection H; intros; subst; clear H
                 | H: inr _ = inr _ |- _ => injection H; intros; subst ;clear H
                 | _ => progress split
                 | _ => progress intros
                 | _ => progress subst
                 | _ => progress (autorewrite with cancel_pair distr_length in * )
                 | _ => rewrite set_nth_nth_default by lia
                 | _ => progress break_match
                 | H : _ /\ _ |- _ => destruct H
                 | H : (_,_) = ?x |- _ =>
                   destruct x; inversion H; subst; destruct H
                 | H : _ |- _ => apply H; lia
                 | _ => lia
                 end.
      destruct (Compare_dec.lt_dec n (fst s)).
      apply H1; lia.
      apply nth_default_out_of_bounds; lia.
    Qed.
  End ZeroLoop.
End _test.