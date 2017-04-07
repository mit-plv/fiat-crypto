(*** XXX TODO MOVE ALL THINGS IN THIS FILE TO BETTER PLACES *)
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
(** The [eexists_sig_etransitivity] tactic takes a goal of the form
      [{ a | f a = b }], and splits it into two goals, [?b' = b] and
      [{ a | f a = ?b' }], where [?b'] is a fresh evar. *)
Definition sig_eq_trans_exist1 {A B} (f : A -> B)
           (b b' : B)
           (pf : b' = b)
           (y : { a : A | f a = b' })
  : { a : A | f a = b }
  := let 'exist a p := y in exist _ a (eq_trans p pf).
Ltac eexists_sig_etransitivity :=
  lazymatch goal with
  | [ |- { a : ?A | @?f a = ?b } ]
    => let lem := open_constr:(@sig_eq_trans_exist1 A _ f b _) in
       simple refine (lem _ _)
  end.
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
