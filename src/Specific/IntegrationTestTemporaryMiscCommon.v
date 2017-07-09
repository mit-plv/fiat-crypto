(*** XXX TODO MOVE ALL THINGS IN THIS FILE TO BETTER PLACES *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Sigma.Associativity.
Require Import Crypto.Util.Sigma.MapProjections.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.DestructHead.

Definition adjust_tuple2_tuple2_sig {A P Q}
           (v : { a : { a : tuple (tuple A 2) 2 | (P (fst (fst a)) /\ P (snd (fst a))) /\ (P (fst (snd a)) /\ P (snd (snd a))) }
                | Q (exist _ _ (proj1 (proj1 (proj2_sig a))),
                     exist _ _ (proj2 (proj1 (proj2_sig a))),
                     (exist _ _ (proj1 (proj2 (proj2_sig a))),
                      exist _ _ (proj2 (proj2 (proj2_sig a))))) })
  : { a : tuple (tuple (@sig A P) 2) 2 | Q a }.
Proof.
  eexists.
  exact (proj2_sig v).
Defined.

(** TODO MOVE ME *)
(** The [eexists_sig_etransitivity_R R] tactic takes a goal of the form
    [{ a | R (f a) b }], and splits it into two goals, [R ?b' b] and
    [{ a | R (f a) ?b' }], where [?b'] is a fresh evar. *)
Definition sig_R_trans_exist1 {B} (R : B -> B -> Prop) {HT : Transitive R} {A} (f : A -> B)
           (b b' : B)
           (pf : R b' b)
           (y : { a : A | R (f a) b' })
  : { a : A | R (f a) b }
  := let 'exist a p := y in exist _ a (transitivity (R:=R) p pf).
Ltac eexists_sig_etransitivity_R R :=
  lazymatch goal with
  | [ |- @sig ?A ?P ]
    => let RT := type of R in
       let B := lazymatch (eval hnf in RT) with ?B -> _ => B end in
       let lem := constr:(@sig_R_trans_exist1 B R _ A _ _ : forall b' pf y, @sig A P) in
       let lem := open_constr:(lem _) in
       simple refine (lem _ _)
  end.
Tactic Notation "eexists_sig_etransitivity_R" open_constr(R) := eexists_sig_etransitivity_R R.
(** The [eexists_sig_etransitivity] tactic takes a goal of the form
      [{ a | f a = b }], and splits it into two goals, [?b' = b] and
      [{ a | f a = ?b' }], where [?b'] is a fresh evar. *)
Definition sig_eq_trans_exist1 {A B}
  := @sig_R_trans_exist1 B (@eq B) _ A.
Ltac eexists_sig_etransitivity :=
  lazymatch goal with
  | [ |- { a : ?A | @?f a = ?b } ]
    => let lem := open_constr:(@sig_eq_trans_exist1 A _ f b _) in
       simple refine (lem _ (_ : { a : A | _ }))
  end.
Definition sig_R_trans_rewrite_fun_exist1 {B} (R : B -> B -> Prop) {HT : Transitive R}
{A} (f : A -> B) (b : B) (f' : A -> B)
           (pf : forall a, R (f a) (f' a))
           (y : { a : A | R (f' a) b })
  : { a : A | R (f a) b }
  := let 'exist a p := y in exist _ a (transitivity (R:=R) (pf a) p).
Ltac eexists_sig_etransitivity_for_rewrite_fun_R R :=
  lazymatch goal with
  | [ |- @sig ?A ?P ]
    => let RT := type of R in
       let B := lazymatch (eval hnf in RT) with ?B -> _ => B end in
       let lem := constr:(@sig_R_trans_rewrite_fun_exist1 B R _ A _ _ : forall f' pf y, @sig A P) in
       let lem := open_constr:(lem _) in
       simple refine (lem _ _); cbv beta
  end.
Tactic Notation "eexists_sig_etransitivity_for_rewrite_fun_R" open_constr(R)
  := eexists_sig_etransitivity_for_rewrite_fun_R R.
Definition sig_eq_trans_rewrite_fun_exist1 {A B} (f f' : A -> B)
           (b : B)
           (pf : forall a, f' a = f a)
           (y : { a : A | f' a = b })
  : { a : A | f a = b }
  := let 'exist a p := y in exist _ a (eq_trans (eq_sym (pf a)) p).
Ltac eexists_sig_etransitivity_for_rewrite_fun :=
  lazymatch goal with
  | [ |- { a : ?A | @?f a = ?b } ]
    => let lem := open_constr:(@sig_eq_trans_rewrite_fun_exist1 A _ f _ b) in
       simple refine (lem _ _); cbv beta
  end.
Definition sig_conj_by_impl2 {A} {P Q : A -> Prop} (H : forall a : A, Q a -> P a)
           (H' : { a : A | Q a })
  : { a : A | P a /\ Q a }
  := let (a, p) := H' in exist _ a (conj (H a p) p).


(** [apply_lift_sig] picks out which version of the [liftN_sig] lemma
    to apply, and builds the appropriate arguments *)
Ltac make_P_for_apply_lift_sig P :=
  lazymatch P with
  | fun (f : ?F) => forall (a : ?A), @?P f a
    => constr:(fun (a : A)
               => ltac:(lazymatch constr:(fun (f : F)
                                          => ltac:(let v := (eval cbv beta in (P f a)) in
                                                   lazymatch (eval pattern (f a) in v) with
                                                   | ?k _ => exact k
                                                   end))
                        with
                        | fun _ => ?P
                          => let v := make_P_for_apply_lift_sig P in
                             exact v
                        end))
  | _ => P
  end.
Ltac apply_lift_sig :=
  let P := lazymatch goal with |- sig ?P => P end in
  let P := make_P_for_apply_lift_sig P in
  lazymatch goal with
  | [ |- { f | forall a b c d e, _ } ]
    => fail "apply_lift_sig does not yet support ≥ 5 binders"
  | [ |- { f | forall (a : ?A) (b : ?B) (c : ?C) (d : ?D), _ } ]
    => apply (@lift4_sig A B C D _ P)
  | [ |- { f | forall (a : ?A) (b : ?B) (c : ?C), _ } ]
    => apply (@lift3_sig A B C _ P)
  | [ |- { f | forall (a : ?A) (b : ?B), _ } ]
    => apply (@lift2_sig A B _ P)
  | [ |- { f | forall (a : ?A), _ } ]
    => apply (@lift1_sig A _ P)
  | [ |- { f | _ } ]
    => idtac
  end.
Ltac start_preglue :=
  apply_lift_sig; intros;
  let phi := lazymatch goal with |- { f | ?phi _ = _ } => phi end in
  eexists_sig_etransitivity; cbv [phi].
Ltac do_set_sig f_sig :=
  let fZ := fresh f_sig in
  set (fZ := proj1_sig f_sig);
  context_to_dlet_in_rhs fZ; cbv beta delta [fZ];
  try cbv beta iota delta [proj1_sig f_sig];
  cbv beta iota delta [fst snd].
Ltac do_rewrite_with_sig_by f_sig by_tac :=
  let lem := constr:(proj2_sig f_sig) in
  let lemT := type of lem in
  let lemT := (eval cbv beta zeta in lemT) in
  rewrite <- (lem : lemT) by by_tac ();
  do_set_sig f_sig.
Ltac do_rewrite_with_sig f_sig := do_rewrite_with_sig_by f_sig ltac:(fun _ => idtac).
Ltac do_rewrite_with_1sig_add_carry_by f_sig carry_sig by_tac :=
  let fZ := fresh f_sig in
  rewrite <- (proj2_sig f_sig) by by_tac ();
  symmetry; rewrite <- (proj2_sig carry_sig) by by_tac (); symmetry;
  pose (fun a => proj1_sig carry_sig (proj1_sig f_sig a)) as fZ;
  lazymatch goal with
  | [ |- context G[proj1_sig carry_sig (proj1_sig f_sig ?a)] ]
    => let G' := context G[fZ a] in change G'
  end;
  context_to_dlet_in_rhs fZ; cbv beta delta [fZ];
  try cbv beta iota delta [proj1_sig f_sig carry_sig];
  cbv beta iota delta [fst snd].
Ltac do_rewrite_with_1sig_add_carry f_sig carry_sig := do_rewrite_with_1sig_add_carry_by f_sig carry_sig ltac:(fun _ => idtac).
Ltac do_rewrite_with_2sig_add_carry_by f_sig carry_sig by_tac :=
  let fZ := fresh f_sig in
  rewrite <- (proj2_sig f_sig) by by_tac ();
  symmetry; rewrite <- (proj2_sig carry_sig) by by_tac (); symmetry;
  pose (fun a b => proj1_sig carry_sig (proj1_sig f_sig a b)) as fZ;
  lazymatch goal with
  | [ |- context G[proj1_sig carry_sig (proj1_sig f_sig ?a ?b)] ]
    => let G' := context G[fZ a b] in change G'
  end;
  context_to_dlet_in_rhs fZ; cbv beta delta [fZ];
  try cbv beta iota delta [proj1_sig f_sig carry_sig];
  cbv beta iota delta [fst snd].
Ltac do_rewrite_with_2sig_add_carry f_sig carry_sig := do_rewrite_with_2sig_add_carry_by f_sig carry_sig ltac:(fun _ => idtac).
Ltac fin_preglue :=
  [ > reflexivity
  | repeat sig_dlet_in_rhs_to_context;
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)) ].

Ltac factor_out_bounds_and_strip_eval op_bounded op_sig_side_conditions_t :=
  let feBW_small := lazymatch goal with |- { f : ?feBW_small | _ } => feBW_small end in
  Associativity.sig_sig_assoc;
  apply sig_conj_by_impl2;
  [ let H := fresh in
    intros ? H;
    try lazymatch goal with
        | [ |- (?eval _ < _)%Z ]
          => cbv [eval]
        end;
    rewrite H; clear H;
    eapply Z.le_lt_trans;
      [ apply Z.eq_le_incl, f_equal | apply op_bounded ];
      [ repeat match goal with
               | [ |- ?f ?x = ?g ?y ]
                 => is_evar y; unify x y;
                    apply (f_equal (fun fg => fg x))
               end;
        clear; abstract reflexivity
      | .. ];
      op_sig_side_conditions_t ()
  | apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p));
    repeat match goal with
           | [ H : feBW_small |- _ ] => destruct H as [? _]
           end ].
