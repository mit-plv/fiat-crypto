Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Decidable.

Module Level.
  Local Coercion is_true : bool >-> Sortclass.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive Level :=
  | neg_inf
  | level (lvl : Z)
  | pos_inf
  .
  Notation t := Level (only parsing).
  Module Export Exports1.
    Declare Scope level_scope.
    Delimit Scope level_scope with level.
    Bind Scope level_scope with Level.
    Global Coercion level : Z >-> Level.
  End Exports1.
  Local Open Scope level_scope.

  Definition of_nat (n : nat) : Level := Z.of_nat n.
  Definition of_N (n : N) : Level := Z.of_N n.
  Definition of_pos (n : positive) : Level := Z.pos n.

  Module Export Exports2.
    Global Coercion of_nat : nat >-> Level.
    Global Coercion of_N : N >-> Level.
    Global Coercion of_pos : positive >-> Level.
  End Exports2.

  (** next tighter level *)
  Definition next (l : Level) : Level
    := match l with
       | neg_inf => neg_inf
       | level lvl => level (Z.pred lvl)
       | pos_inf => pos_inf
       end.
  (** previous looser level *)
  Definition prev (l : Level) : Level
    := match l with
       | neg_inf => neg_inf
       | level lvl => level (Z.succ lvl)
       | pos_inf => pos_inf
       end.

  Notation eqb := Level_beq.
  Lemma eqb_eq x y : eqb x y = true <-> x = y.
  Proof. split; [ apply internal_Level_dec_bl | apply internal_Level_dec_lb ]. Qed.
  Lemma eqb_neq x y : eqb x y = false <-> x <> y.
  Proof. rewrite <- eqb_eq; destruct (eqb x y); split; congruence. Qed.
  Lemma eqb_refl x : eqb x x = true.
  Proof. rewrite eqb_eq; reflexivity. Qed.
  Lemma eqb_sym x y : eqb x y = eqb y x.
  Proof. destruct (eqb x y) eqn:?, (eqb y x) eqn:?; rewrite ?eqb_eq, ?eqb_neq in *; subst; congruence. Qed.
  Lemma eqb_spec : reflect_rel eq eqb.
  Proof. intros x y; destruct (eqb x y) eqn:?; constructor; rewrite ?eqb_eq, ?eqb_neq in *; assumption. Qed.
  Definition dec_eq_Level : DecidableRel (@eq Level) := dec_rel_of_bool_dec_rel eqb internal_Level_dec_bl internal_Level_dec_lb.
  Lemma eqb_compat : Proper (eq ==> eq ==> eq) eqb.
  Proof. repeat intro; subst; reflexivity. Qed.

  Definition compare (l1 l2 : Level) : comparison
    := match l1, l2 with
       | neg_inf, neg_inf => Eq
       | neg_inf, _ => Lt
       | _, neg_inf => Gt
       | pos_inf, pos_inf => Eq
       | pos_inf, _ => Gt
       | _, pos_inf => Lt
       | level l1, level l2 => Z.compare l1 l2
       end.
  Definition ltb (l1 l2 : Level) : bool
    := match compare l1 l2 with
       | Lt => true
       | _ => false
       end.
  Definition leb (l1 l2 : Level) : bool
    := orb (eqb l1 l2) (ltb l1 l2).
  Definition le : relation Level := leb.
  Definition lt : relation Level := ltb.
  Module Export Exports3.
    Global Arguments le _ _ / .
    Global Arguments lt _ _ / .
    Global Arguments ltb !_ !_ / .
    Global Arguments leb !_ !_ / .
    Global Arguments compare !_ !_ / .
  End Exports3.

  Module Import Notations1.
    Notation "-∞" := neg_inf.
    Notation "∞" := pos_inf.
    Infix "?=" := compare : level_scope.
    Infix "=?" := eqb : level_scope.
    Infix "<=?" := leb : level_scope.
    Infix "<?" := ltb : level_scope.
    Infix "<=" := le : level_scope.
    Infix "<" := lt : level_scope.
    Notation "l1 >=? l2" := (leb l2 l1) (only parsing) : level_scope.
    Notation "l1 >? l2" := (ltb l2 l1) (only parsing) : level_scope.
    Notation "l1 >= l2" := (le l2 l1) (only parsing) : level_scope.
    Notation "l1 > l2" := (lt l2 l1) (only parsing) : level_scope.
  End Notations1.
  Lemma compare_spec x y : CompareSpec (x = y) (x < y) (y < x) (x ?= y).
  Proof.
    destruct x as [|x|], y as [|y|]; cbv [lt ltb compare]; try destruct (Z.compare_spec x y), (Z.compare_spec y x); constructor;
      subst; try reflexivity; try lia.
  Qed.
  Lemma compare_refl x : (x ?= x) = Eq.
  Proof. destruct x; cbn; try reflexivity; now rewrite Z.compare_refl. Qed.
  Lemma compare_antisym x y : (y ?= x) = CompOpp (x ?= y).
  Proof. destruct x, y; cbn; try reflexivity; now rewrite Z.compare_antisym. Qed.
  Lemma compare_eq x y : (x ?= y) = Eq -> x = y.
  Proof. destruct x, y; cbn; try congruence; intro; now apply f_equal, Z.compare_eq. Qed.
  Lemma compare_eq_iff x y : (x ?= y) = Eq <-> x = y.
  Proof. destruct x, y; cbn; rewrite ?Z.compare_eq_iff; split; congruence. Qed.

  Module Export Notations.
    Export Notations1.
  End Notations.

  Module Export Exports.
    Export Exports1.
    Export Exports2.
    Export Exports3.
    Global Existing Instances eqb_spec dec_eq_Level eqb_compat | 10.
  End Exports.
End Level.
Export Level.Notations.
Export Level.Exports.
Notation Level := Level.Level.

Inductive Associativity := LeftAssoc | RightAssoc | NoAssoc | FullyAssoc | ExplicitAssoc (l r : Level).
