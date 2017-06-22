(*** XXX TODO MOVE ALL THINGS IN THIS FILE TO BETTER PLACES *)
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tuple.

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
