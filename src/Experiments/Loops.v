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

  Definition invariant_for
             (inv : continue_state -> Prop)
             (P : break_state -> Prop) : Prop :=
    (forall state state',
        body state = inr state' -> inv state ->
        inv state') /\ 
    (forall state state',
        body state = inl state' -> inv state ->
        P state').      

  Local Ltac loop_simplify :=
    repeat match goal with
           | _ => progress (simpl loop in * )
           | _ => progress intros
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           | _ => erewrite loop_default_eq by eassumption
           | _ => erewrite loop_continue_step in * by eassumption
           | _ => erewrite loop_break_step in * by eassumption
           | |- context [match (body ?s) with | _ => _ end] =>
             let Heq := fresh "H" in
             case_eq (body s); intros ? Heq; rewrite Heq in *
           | _ => congruence
           | _ => solve [eauto] 
           end.             
  
  Lemma loop_invariant fuel :
    forall start
        (P : break_state -> Prop) default
        (Hterm : terminates fuel start),
    (exists (inv : continue_state -> Prop),
        inv start /\
        invariant_for inv P)
    <-> P (loop_default fuel start default).
  Proof.
    intros; split;
      [ intro H; destruct H as [? [Hstart ?]];
        revert start Hterm Hstart;
        induction fuel |
      exists (fun st =>
                exists f e, (loop f st = Some e /\ P e)) ];
      repeat match goal with
               | _ => progress (cbv [invariant_for
                                       loop_default
                                       terminates] in * )
             | _ => progress intros
             | _ => progress loop_simplify
             | H: _ = ?x |- _ = ?x =>
               etransitivity; [|apply H]
             | H: context
                    [match ?x with | O => _
                              | S _ => _ end] |- _ =>
               destruct x; try congruence
             | _ => eexists
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
             | _ => progress cbv [terminates]
             | _ => progress simpl loop
             | _ => progress break_match; try congruence
             | H : forall _ _, body _ = continue _ -> _ , Heq : body _ = continue _ |- _ => specialize (H _ _ Heq)
             | _ => eapply IHfuel; lia
             | _ => lia
    end.
  Qed.
  
End Loops.

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
     eapply loop_invariant.
     apply zero_body_terminates.
     exists zero_invariant.
     split.
     { cbv [zero_invariant].
       autorewrite with cancel_pair.
       split; intros; lia. }
     { cbv [invariant_for zero_invariant zero_body]. split;
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
         destruct (Compare_dec.lt_dec n (fst state)).
         apply H1; lia.
         apply nth_default_out_of_bounds; lia. }
   Qed.

End ZeroLoop.