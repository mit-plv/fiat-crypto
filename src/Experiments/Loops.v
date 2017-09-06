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

  Inductive trace : continue_state -> continue_state ->
                    list continue_state -> Prop :=
  | Break : forall final, trace final final (final::nil)
  | Cont : forall st st' final tr, body st =  inr st'
                             -> trace st' final tr
                             -> trace st final (st :: tr).
  
  Fixpoint make_trace fuel start tr : list continue_state :=
    match (body start) with
    | inl _ => (tr ++ start :: nil)
    | inr next => 
      match fuel with
      | O => (tr ++ start :: nil)
      | S fuel' => make_trace fuel' next (tr ++ start :: nil)
      end end.
  
  Lemma app_trace : forall tr a b,
      trace a b tr ->
      forall c,
        body b = inr c ->
        trace a c (tr ++ c :: nil).
  Proof.
    induction tr; intros;
      match goal with
      | H : trace _ _ _ |- _ => progress (inversion H; subst)
      end; simpl app; eapply Cont; eauto; apply Break.
  Qed.

  Lemma is_trace' fuel fuel' : forall start middle tr,
      terminates fuel start ->
      terminates fuel' middle ->
      trace start middle (tr ++ middle :: nil) ->
      exists final b, body final = inl b /\
      trace start final (make_trace fuel' middle tr).
  Proof.
    induction fuel';
      repeat match goal with
             | _ => progress (cbv [terminates loop_default])
             | _ => progress (simpl loop; simpl make_trace)
             | _ => progress intros
             | _ => progress break_match; try congruence
             | _ => do 2 eexists; split; eassumption
             end.
      apply IHfuel'; eauto using app_trace.
  Qed.
  
  Lemma is_trace fuel : forall start,
      terminates fuel start ->
      exists final b,
        body final = inl b /\
        trace start final (make_trace fuel start nil).
  Proof. intros. eauto using is_trace', Break. Qed.

  Lemma trace_end d tr :
    forall fuel start final b,
    terminates fuel start ->
    body final = inl b ->
    trace start final tr ->
    loop_default fuel start d = b.
  Proof.
    induction tr; intros.
    { inversion H1. }
    { inversion H1; subst.
      { cbv [loop_default]; erewrite loop_break_step; eauto. }
      { pose proof H;
        cbv [loop_default terminates] in H |- *;
          erewrite loop_continue_step in H |- * by eauto.
        destruct fuel; try congruence.
        eapply IHtr; eauto. } }
  Qed.

  Lemma is_trace_full fuel d : forall start,
      terminates fuel start ->
      exists final,
        body final = inl (loop_default fuel start d) /\
        trace start final (make_trace fuel start nil).
  Proof.
    intros. pose proof H.
    eapply is_trace in H.
    destruct H as [final [? [? ?]]].
    exists final. split; [|assumption].
    erewrite trace_end; eauto.
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
  
  Lemma loop_invariant' (P : break_state -> Prop)
        (inv : continue_state -> Prop)
        default final b (Hfinal : body final = inl b) :
    forall tr fuel start (Htrace: trace start final tr),
        terminates fuel start ->
        inv start ->
        invariant_for inv P ->
        P (loop_default fuel start default).
  Proof.
    cbv [invariant_for];
      induction tr; intros; [inversion Htrace|];
        match goal with | H : _ /\ _ |- _ => destruct H end.
    case_eq (body start); intros.
    { erewrite trace_end; eauto using Break. }
    { unfold loop_default.
      erewrite loop_continue_step by eauto.
      destruct fuel.
      { cbv [terminates] in H. simpl in *.
        match goal with H : body start = _ |- _ =>
        rewrite H in * end; congruence. }
      { assert (terminates fuel c) by (cbv [terminates] in *; erewrite loop_continue_step in * by eauto; congruence).
        eapply IHtr; try eauto.
        inversion Htrace; subst; congruence. } }
  Qed.
  
  Lemma loop_invariant fuel start
        (P : break_state -> Prop) default
        (Hterm : terminates fuel start) :
    (exists (inv : continue_state -> Prop),
        inv start /\
        invariant_for inv P)
    <-> P (loop_default fuel start default).
  Proof.
    cbv [invariant_for]; split.
    { let H := fresh "H" in
      intro H; destruct H as [inv [? [? ?]]].
      pose proof Hterm.
      apply is_trace in Hterm.
      destruct Hterm as [? [? [? ?]]].
      eapply loop_invariant' with (inv:=inv);
        cbv [invariant_for]; eauto.  }
    { intro Hend.
      exists (fun st =>
                exists f e, (loop f st = Some e /\ P e)).
      repeat split.
      { do 2 eexists.
        erewrite loop_default_eq by eassumption.
        split; [f_equal|eassumption]. }
      { intros ? ? ? IH.
        destruct IH as [f IH].
        erewrite loop_continue_step in IH by eauto.
        destruct f.
        { destruct IH as [? [? ?]]; congruence. }
        { eexists; eassumption. } }
      { intros ? ? ? IH.
        destruct IH as [f IH].
        erewrite loop_break_step in IH by eauto.
        destruct IH as [e [HSome HP]].
        congruence. } }
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