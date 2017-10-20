Require Import Coq.Lists.List.
Require Import Lia. 
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.LetIn.

Notation break := (@inl _ _).
Notation continue := (@inr _ _).

Section Loops.
  Context {continue_state break_state}
          (body : continue_state -> break_state + continue_state)
          (body_cps : continue_state ->
                  forall {T}, (break_state + continue_state -> T)
                              -> T).

  Definition funapp {A B} (f : A -> B) (x : A) := f x.

  Fixpoint loop_cps (fuel: nat) (start : continue_state)
           {T} (ret : break_state -> T) : option T :=
    funapp
    (body_cps start _) (fun next =>
                      match next with
                      | break state => Some (ret state)
                      | continue state =>
                        match fuel with
                        | O => None
                        | S fuel' =>
                          loop_cps fuel' state ret
                        end end).
  
  Fixpoint loop (fuel: nat) (start : continue_state)
    : option break_state :=
    match (body start) with
    | inl state => Some state
    | inr state => 
      match fuel with
      | O => None
      | S fuel' => loop fuel' state
      end end.
  
  Lemma loop_break_step fuel start state :
    (body start = inl state) ->
    loop fuel start = Some state.
  Proof.
    destruct fuel; simpl loop; break_match; intros; congruence.
  Qed.

  Lemma loop_continue_step fuel start state :
    (body start = inr state) ->
    loop fuel start =
    match fuel with | O => None | S fuel' => loop fuel' state end.
  Proof.
    destruct fuel; simpl loop; break_match; intros; congruence.
  Qed.

  Definition terminates fuel start :=
    loop fuel start <> None.

  Definition loop_default fuel start default
    : break_state := match (loop fuel start) with
             | None => default
             | Some result => result
             end.

  Lemma loop_default_eq fuel start default
        (Hterm : terminates fuel start) :
    loop fuel start = Some (loop_default fuel start default).
  Proof.
    cbv [terminates loop_default] in *; break_match; congruence.
  Qed.

  Lemma invariant_iff fuel start default (H : terminates fuel start) P :
      P (loop_default fuel start default) <->
      (exists (inv : continue_state -> Prop),
          inv start
          /\ (forall s s', body s = continue s' -> inv s -> inv s')
          /\ (forall s s', body s = break s' -> inv s -> P s')).
  Proof.
    split;
      [ exists (fun st => exists f e, (loop f st = Some e /\ P e ))
      | destruct 1 as [?[??]]; revert dependent start; induction fuel ];
      repeat match goal with
             | _ => solve [ trivial | congruence | eauto ] 
             | _ => progress destruct_head' @ex
             | _ => progress destruct_head' @and
             | _ => progress intros
             | _ => progress (cbv [loop_default terminates] in * )
             | _ => progress (cbn [loop] in * )
             | _ => progress erewrite loop_default_eq by eassumption
             | _ => progress erewrite loop_continue_step in * by eassumption
             | _ => progress erewrite loop_break_step in * by eassumption
             | _ => progress break_match_hyps
             | _ => progress break_match
             | _ => progress eexists
             end.
  Qed.

  Lemma to_measure (measure : continue_state -> nat) :
    (forall state state', body state = inr state' ->
                          0 <= measure state' < measure state) ->
    forall fuel start,
    measure start <= fuel ->
    terminates fuel start.
  Proof.
    induction fuel; intros;
      repeat match goal with
             | _ => solve [ congruence | lia ]
             | _ => progress cbv [terminates]
             | _ => progress cbn [loop]
             | _ => progress break_match
             | H : forall _ _, body _ = continue _ -> _ , Heq : body _ = continue _ |- _ => specialize (H _ _ Heq)
             | _ => eapply IHfuel
    end.
  Qed.
  
End Loops.

Definition by_invariant {continue_state break_state body fuel start default}
           invariant P term invariant_start invariant_continue invariant_break
  := proj2 (@invariant_iff continue_state break_state body fuel start default term P)
           (ex_intro _ invariant (conj invariant_start (conj invariant_continue invariant_break))).
                 
Section While.
  Context {state}
          (test : state -> bool)
          (body : state -> state).

  Fixpoint while (fuel: nat) (s : state) {struct fuel} : option state :=
    if test s
    then
      match fuel with
      | O => None
      | S fuel' => while fuel' (body s)
      end
    else Some s.

  Section AsLoop.
    Local Definition lbody := fun s => if test s then continue (body s) else break s.
    Definition while_using_loop := loop lbody.

    Lemma while_eq_loop : forall n s, while n s = while_using_loop n s.
    Proof.
      induction n; intros;
        cbv [lbody while_using_loop]; cbn [while loop]; break_match; auto.
    Qed.
  End AsLoop.

  Definition while_default d f s :=
    match while f s with
    | None => d
    | Some x => x
    end.
End While.

Definition for2 {state} (test : state -> bool) (increment body : state -> state)
  := while test (fun s => increment (body s)). 
Definition for2_default {state} d test increment body f s :=
  match @for2 state test increment body f s with
  | None => d
  | Some x => x
  end.

Definition for3 {state} init test increment body fuel := @for2 state test increment body fuel init.
Definition for3_default {state} d init test increment body fuel :=
  match @for3 state init test increment body fuel with
  | None => d
  | Some x => x
  end.

Section GCD.
  Definition gcd_step :=
    fun '(a, b) => if Nat.ltb a b
                   then continue (a, b-a)
                   else if Nat.ltb b a
                        then inr (a-b, b)
                        else break a.

  Definition gcd fuel a b := loop_default gcd_step fuel (a,b) 0.

  Eval cbv [gcd loop_default loop gcd_step] in (gcd 10 5 7).
  
  Example gcd_test : gcd 1000 28 35 = 7 := eq_refl.

  Definition gcd_step_cps
    : (nat * nat) -> forall T, (nat + (nat * nat) -> T) -> T 
    :=
      fun st T ret =>
        let a := fst st in
        let b := snd st in
        if Nat.ltb a b
        then ret (continue (a, b-a))
        else if Nat.ltb b a
             then ret (continue (a-b, b))
             else ret (break a).

  Definition gcd_cps fuel a b {T} (ret:nat->T)
    := loop_cps gcd_step_cps fuel (a,b) ret.

  Example gcd_test2 : gcd_cps 1000 28 35 id = Some 7 := eq_refl.
  
  Eval cbv [gcd_cps loop_cps gcd_step_cps id] in (gcd_cps 2 5 7 id).

End GCD.

(* simple example--set all elements in a list to 0 *)
Section ZeroLoop.

  Definition zero_body (state : nat * list nat) :
    list nat + (nat * list nat) :=
    if dec (fst state < length (snd state))
    then continue (S (fst state), set_nth (fst state) 0 (snd state))
    else break (snd state).

  Lemma zero_body_terminates (arr : list nat) :
    terminates zero_body (length arr) (0,arr).
  Proof.
    eapply to_measure with (measure :=(fun state => length (snd state) - (fst state))); cbv [zero_body]; intros until 0;
      repeat match goal with
             | _ => progress autorewrite with cancel_pair distr_length
             | _ => progress subst
             | _ => progress break_match; intros
             | _ => progress inversion_sum
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
     eapply (by_invariant zero_invariant); auto using zero_body_terminates;
       [ cbv [zero_invariant]; autorewrite with cancel_pair; split; intros; lia | ..];
       cbv [zero_invariant zero_body];
       intros until 0;
       break_match; intros; inversion_sum;
         repeat match goal with
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
         apply nth_default_out_of_bounds; lia. }
   Qed.
End ZeroLoop.