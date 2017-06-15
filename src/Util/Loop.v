(** * Definition and Notations for [do { body }] *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Z2Nat.
Require Import Crypto.Util.Notations Crypto.Util.CPSNotations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.

Section with_state.
  Import CPSNotations.
  Context {state : Type}.

  Definition loop_cps_step
             (loop_cps
              : forall (max_iter : nat)
                       (initial : state)
                       (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
                 ~> state)
             (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := fun st body
       => match max_iter with
          | 0
            => (return st)
          | S max_iter'
            => fun T ret
               => body st T (fun st' => @loop_cps max_iter' st' body _ ret) ret
          end.

  Fixpoint loop_cps (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := loop_cps_step loop_cps max_iter.

  Lemma unfold_loop_cps
        (max_iter : nat)
    : loop_cps max_iter
      = loop_cps_step loop_cps max_iter.
  Proof.
    destruct max_iter; reflexivity.
  Qed.

  Theorem loop_cps_def (max_iter : nat)
          (initial : state)
          (body : state -> forall {T} (continue : state -> T) (break : state -> T), T)
          T ret
    : loop_cps (S max_iter) initial body T ret =
      body initial (fun st' => @loop_cps max_iter st' body _ ret) ret.
  Proof.
    reflexivity.
  Qed.

  Theorem loop_cps_ind
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue break,
             (forall v, invariant v -> P (continue v))
             -> (forall v, invariant v -> P (break v))
             -> invariant v
             -> P (body v T continue break))
      -> (forall v, invariant v -> P (rest v))
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody HP; simpl; cbv [cpsreturn]; auto.
  Qed.

  Local Hint Extern 2 => omega.

  (** TODO(andreser): Remove this if we don't need it *)
  Theorem loop_cps_wf_ind_break
          (measure : state -> nat)
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue,
             invariant v
             -> (forall break,
                    (forall v', measure v' < measure v -> invariant v' -> P (continue v'))
                    -> P (body v T continue break))
                \/ P (body v T continue rest))
      -> measure v0 < n
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody Hmeasure; simpl; try omega.
    edestruct Hbody as [Hbody'|Hbody']; eauto.
  Qed.

  Theorem loop_cps_wf_ind
          (measure : state -> nat)
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue,
             invariant v
             -> ((forall v', measure v' < measure v -> invariant v' -> P (continue v'))
                 -> P (body v T continue rest)))
      -> measure v0 < n
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0.
    induction n as [|n IHn]; intros v0 Hinv Hbody Hmeasure; simpl; try omega.
    eauto.
  Qed.

  Theorem eq_loop_cps_large_n
          (measure : state -> nat)
          n n' v0 body T rest
    : measure v0 < n
      -> measure v0 < n'
      -> (forall v continue continue',
             (forall v', measure v' < measure v -> continue v' = continue' v')
             -> measure v <= measure v0
             -> body v T continue rest = body v T continue' rest)
      -> loop_cps n v0 body T rest = loop_cps n' v0 body T rest.
  Proof.
    revert n n'.
    match goal with
    | [ |- forall n n', ?P ] => cut (forall n n', n <= n' -> P)
    end.
    { intros H n n' ???.
      destruct (le_lt_dec n n'); [ | symmetry ]; auto. }
    { intros n n' Hle Hn _.
      revert n' Hle v0 Hn.
      induction n as [|n IHn], n' as [|n']; simpl;
        auto with omega. }
  Qed.
End with_state.

(** N.B. If the body is polymorphic (that is, if the type argument
    shows up in the body), then we need to bind the name of the type
    parameter somewhere in the notation for it to show up; we have a
    separate notation for this case. *)
(** TODO: When these notations are finalized, reserve them in Notations.v and moving the level and formatting rules there *)
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break , @ T ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break ,  @ T )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue _ => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue )  {{ '//' body ']' '//' }} ; '//' rest").

Section with_for_state.
  Import CPSNotations.
  Section with_loop_params.
    Context {state : Type}.
    Context (test : Z -> Z -> bool) (i_final : Z) (upd_i : Z -> Z)
            (body : state -> Z -> forall {T} (continue : state -> T) (break : state -> T), T).

    (* we assume that [upd_i] is linear to compute the fuel *)
    Definition for_cps (i0 : Z) (initial : state)
      : ~> state
      := fun T ret
         => @loop_cps
              (Z * state)
              (S (S (Z.to_nat ((i_final - i0) / (upd_i 0%Z)))))
              (i0, initial)
              (fun '(i, st) T continue break
               => if test i i_final
                  then @body st i T
                             (fun st' => continue (upd_i i, st')%Z)
                             (fun st' => break (i, st'))
                  else break (i, st))
              T (fun '(i, st) => ret st).

    Section lemmas.
      Local Open Scope Z_scope.
      Context (upd_linear : forall x, upd_i x = upd_i 0 + x)
              (upd_nonzero : upd_i 0 <> 0)
              (upd_signed : forall i0, test i0 i_final = true -> 0 <= (i_final - i0) / (upd_i 0)).

      (** TODO: Strengthen this to take into account the value of
                  the loop counter at the end of the loop; based on
                  [ForLoop.v], it should be something like [(finish -
                  Z.sgn (finish - i0 + step - Z.sgn step) * (Z.abs
                  (finish - i0 + step - Z.sgn step) mod Z.abs step) +
                  step - Z.sgn step)] *)
      Theorem for_cps_ind
              (invariant : Z -> state -> Prop)
              T (P : (*Z ->*) T -> Prop) i0 v0 rest
        : invariant i0 v0
          -> (forall i v continue,
                 test i i_final = true
                 -> (forall v, invariant (upd_i i) v -> P (continue v))
                 -> invariant i v
                 -> P (@body v i T continue rest))
          -> (forall i v, test i i_final = false -> invariant i v -> P (rest v))
          -> P (for_cps i0 v0 T rest).
      Proof.
        unfold for_cps, cpscall, cpsreturn.
        intros Hinv IH Hrest.
        eapply @loop_cps_wf_ind with (T:=T)
                                       (invariant := fun '(i, s) => invariant i s)
                                       (measure := fun '(i, s) => Z.to_nat (1 + (i_final - i) / upd_i 0));
          [ assumption
          |
          | solve [ destruct (Z_le_gt_dec 0 ((i_final - i0) / upd_i 0));
                    [ rewrite Z2Nat.inj_add by omega; simpl; omega
                    | rewrite Z2Nat.inj_nonpos by omega; omega ] ] ].
        intros [i st] continue Hinv' IH'.
        destruct (test i i_final) eqn:Hi; [ | solve [ eauto ] ].
        pose proof (upd_signed _ Hi) as upd_signed'.
        assert (upd_i 0 <> 0)
          by (intro H'; rewrite H' in upd_signed'; autorewrite with zsimplify in upd_signed';
              omega).
        specialize (IH i st (fun st' => continue (upd_i i, st')) Hi).
        specialize (fun v pf => IH' (upd_i i, v) pf).
        cbv beta iota in *.
        specialize (fun pf v => IH' v pf).
        rewrite upd_linear in IH'.
        replace ((i_final - (upd_i 0 + i)) / upd_i 0)
        with ((i_final - i) / upd_i 0 - 1)
          in IH'
          by (Z.div_mod_to_quot_rem; nia).
        rewrite <- upd_linear, Zplus_minus, Z2Nat.inj_add in IH' by omega.
        auto with omega.
      Qed.

      Theorem for_cps_unroll1
              T i0 v0 rest
              (body_Proper : Proper (eq ==> eq ==> forall_relation (fun T => (pointwise_relation _ eq) ==> eq ==> eq)) body)
        : for_cps i0 v0 T rest
          = if test i0 i_final
            then @body v0 i0 T
                       (fun v => for_cps (upd_i i0) v T rest)
                       rest
            else rest v0.
      Proof.
        unfold for_cps at 1.
        rewrite loop_cps_def.
        destruct (test i0 i_final) eqn:Hi; [ | reflexivity ].
        apply body_Proper; [ reflexivity | reflexivity | intro st | reflexivity ].
        assert (Hto0 : forall x, x <= 0 -> Z.to_nat x = 0%nat)
          by (intros []; intros; simpl; lia).
        apply eq_loop_cps_large_n with (measure := fun '(i, st) => Z.to_nat (1 + (i_final - i) / upd_i 0));
          repeat first [ progress intros
                       | reflexivity
                       | progress destruct_head'_prod
                       | progress unfold pointwise_relation
                       | break_innermost_match_step
                       | apply body_Proper
                       | omega
                       | rewrite Zdiv.Zdiv_0_r in *
                       | rewrite ?(Z.add_opp_r _ 1), Zplus_minus, <- ?(Z.add_opp_r _ 1) in *
                       | match goal with
                         | [ H : forall v, _ -> ?continue _ = ?continue' _ |- ?continue _ = ?continue' _ ] => apply H
                         | [ |- context[upd_i ?x] ]
                           => lazymatch x with
                              | 0 => fail
                              | _ => rewrite (upd_linear x)
                              end
                         | [ H : ?x = 0 |- context[?x] ] => rewrite H
                         | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : forall i, ?f i ?y = true -> ?R (_ / 0), H' : ?f _ ?y = true |- _ ]
                           => specialize (H _ H')
                         | [ |- context[?i_final - (upd_i 0 + ?i0)] ]
                           => replace (i_final - (upd_i 0 + i0)) with ((i_final - i0) + (-1) * upd_i 0) by omega;
                              rewrite Zdiv.Z_div_plus_full by assumption
                         end
                       | lazymatch goal with
                         | [ H : upd_i 0 = 0 |- _ ] => fail
                         | [ H : upd_i 0 <> 0 |- _ ] => fail
                         | _ => destruct (Z_zerop (upd_i 0))
                         end
                       | match goal with
                         | [ |- context[S (Z.to_nat ?x)] ]
                           => destruct (Z_lt_le_dec 0 x);
                              [ rewrite <- (Z2Nat.inj_succ x) by omega
                              | rewrite !(Hto0 x) by omega ]
                         | [ |- (Z.to_nat _ < Z.to_nat _)%nat ]
                           => apply Z2Nat.inj_lt
                         | [ |- (Z.to_nat ?x < ?n)%nat ]
                           => apply (Z2Nat.inj_lt x (Z.of_nat n)); simpl
                         | [ H : forall i, ?f i ?y = true -> 0 <= _ / _, H' : ?f _ ?y = true |- _ ]
                           => specialize (H _ H')
                         end ].
      Qed.
    End lemmas.
  End with_loop_params.
End with_for_state.

Delimit Scope for_upd_scope with for_upd.
Delimit Scope for_test_scope with for_test.
Notation "i += k" := (Z.add i k) : for_upd_scope.
Notation "i -= k" := (Z.sub i k) : for_upd_scope.
Notation "i ++" := (i += 1)%for_upd : for_upd_scope.
Notation "i --" := (i -= 1)%for_upd : for_upd_scope.
Notation "<" := Z.ltb (at level 71) : for_test_scope.
Notation ">" := Z.gtb (at level 71) : for_test_scope.
Notation "<=" := Z.leb (at level 71) : for_test_scope.
Notation ">=" := Z.geb (at level 71) : for_test_scope.
Notation "≤" := Z.leb (at level 71) : for_test_scope.
Notation "≥" := Z.geb (at level 71) : for_test_scope.
Global Close Scope for_test_scope. (* TODO: make these notations not print all over the place *)

Definition force_idZ (f : Z -> Z) (pf : f = id) {T} (v : T) := v.
(** [lhs] and [cmp_expr] go at level 9 so that they bind more tightly
    than application (so that [i (<)] sticks [i] in [lhs] and [(<)] in
    [cmp_expr], rather than sticking [i (<)] in [lhs] and then
    complaining about a missing value for [cmp_expr].  Unfortunately,
    because the comparison operators need to be at level > 70 to not
    conflict with their infix versions, putting [cmp_expr] at level 9
    forces us to wrap parentheses around the comparison operator. *)
(** TODO(andreser): If it's worth it, duplicate these notations for
      each value of [cmp_expr] so that we don't need to wrap the
      comparison operator in parentheses. *)
(** TODO: When these notations are finalized, reserve them in Notations.v and moving the level and formatting rules there *)
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue , break , @ T ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break ,  @ T )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue )  {{ '//' body ']' '//' }} ; '//' rest").

Section LoopTest.
  Import CPSNotations.
  Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ; x.

  Check
    loop _{ 1234 } ('(i, a) = (0, 0)) labels (continue, break)
    {{
        if i <? 10
        then
          continue (i + 1, a+1)
        else
          break (0, a)
    }};
    a.

  Context (f:nat~>nat).

  Check x <- f 0 ; return x + x.
  Check x <- f 0 ; y <- f x; z <- f y; return (x,y,z).

 Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ;
   return x.

 Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ;
   x <- f x;
   return x.

  Check loop _{ 10 } (x = 0) labels (continue, break) {{ x <- f x ; continue (x) }} ; x.


  Context (s F : Z) (zero : nat).
  Check for ( i = s; i (<) F; i++) updating (P = zero) labels (continue, break)
  {{
      continue (P+P)
  }};
  P.

  Check for ( i = s; i (<) F; i++) updating (P = zero) labels (continue)
  {{
      P <- f P;
      continue (P+P)
  }};
  P.
End LoopTest.

Module CPSBoilerplate.
  Import CPSNotations.
  Definition valid {R} (f:~>R) :=
    forall {T} (continuation:R->T),
      (x <- f; continuation x) = (continuation (f _ id)).
  Existing Class valid.
End CPSBoilerplate.

Require Import Coq.Classes.Morphisms.
Require Import Crypto.Algebra.ScalarMult.
Section ScalarMult.
  Import CPSNotations.

  Context {G} (zero:G) (k w : Z) (add_tbl : G -> Z -> Z ~> G) (nth_limb : Z ~> Z). (* k w-bit limbs *)

  Definition ScalarMultBase :=
    for ( i = 0; i (<) k; i++) updating (P = zero) labels (continue, break)
    {{
      x <- nth_limb i;
      P <- add_tbl P i x;
      continue P
    }};
    P.

  Context {Geq add opp} {Hmonoid:@Algebra.Hierarchy.group G Geq add zero opp}.
  Local Notation smul := (@scalarmult_ref G add zero opp).
  Context {nth_limb_valid : forall a, CPSBoilerplate.valid (nth_limb a)}.
  Context {add_tbl_valid : forall a b c, CPSBoilerplate.valid (add_tbl a b c)}.
  Context {Proper_add_tbl : Proper (Geq ==> eq ==> eq ==> Geq) (fun a b c => add_tbl a b c _ id)}.
  Context (B:G).
  Context {limb_good}
          {nth_limb_good: forall i, (0 <= i < k)%Z -> limb_good i (nth_limb i _ id)}
          {add_tbl_correct : forall P i limb,
              limb_good i limb -> Geq (add_tbl P i limb G id) (add P (smul (2 ^ i * limb) B))}.

  Definition n_upto t : Z :=
    for ( i = 0; i (<) t; i++) updating (n = 0%Z) labels (continue)
    {{
            x <- nth_limb i;
            continue (n + (2^i)*x)%Z
    }};
    n.


  Lemma ScalarMultBase_correct : Geq ScalarMultBase (smul (n_upto k) B).
    cbv [ScalarMultBase].
    eapply for_cps_ind with (invariant := fun i P => Geq P (smul (n_upto i) B )%Z).
    - intros; omega.
    - omega.
    - intros; rewrite Z.ltb_lt in H; autorewrite with zsimplify; omega.
    - autorewrite with zsimplify. symmetry; eapply (scalarmult_0_l(add:=add)).
    - cbv [force_idZ id]; intros. clear H.
      setoid_rewrite nth_limb_valid; setoid_rewrite add_tbl_valid.
      setoid_rewrite <-H0; [reflexivity|]; clear H0.

      etransitivity.
      eapply Proper_add_tbl; [eapply H1|reflexivity|reflexivity].
      clear H1.
      replace (n_upto (i+1))%Z with (n_upto i + (2^i)*(nth_limb i _ id))%Z by admit.
      rewrite scalarmult_add_l.
      rewrite add_tbl_correct; [reflexivity|].
      apply nth_limb_good.
      admit.
  Admitted.
End ScalarMult.
