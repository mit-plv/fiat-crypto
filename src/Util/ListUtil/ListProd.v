From Stdlib Require Import Bool PeanoNat List Lists.Finite.
Import ListNotations.

Lemma filter_filter [A] f g (l : list A) : filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  induction l; cbn [filter]; trivial.
  case g; cbn [filter]; case f; cbn [andb]; congruence.
Qed.

Lemma negb_existsb [A] f (l : list A) : negb (existsb f l) = forallb (fun x => negb (f x)) l.
Proof.
  induction l; cbn [negb orb existsb forallb]; trivial.
  case f; rewrite ?IHl; trivial.
Qed.

Lemma existsb_as_filter [A] f (l : list A) : existsb f l = negb (length (filter f l) =? 0)%nat.
Proof.
  induction l; trivial.
  cbn [existsb filter]; case f; rewrite ?IHl; trivial.
Qed.

Lemma list_prod_nil_l [A B] l : @list_prod A B nil l = nil.
Proof. trivial. Qed.

Lemma list_prod_cons_l [A B] (x : A) l (l' : list B) :
  list_prod (x::l) l' = map (pair x) l' ++ list_prod l l'.
Proof. trivial. Qed.

Lemma list_prod_map_l [A A' B] (f : A -> A') l (l' : list B) :
  list_prod (map f l) l' = map (fun '(a, b) => (f a, b)) (list_prod l l').
Proof.
  induction l; rewrite ?list_prod_cons, ?map_cons, ?list_prod_cons_l,
    ?map_app, ?map_map, ?IHl; trivial.
Qed.

Lemma list_prod_map_r [A B B'] (f : B -> B') (l : list A) l' :
  list_prod l (map f l') = map (fun '(a, b) => (a, f b)) (list_prod l l').
Proof.
  induction l; rewrite ?list_prod_cons, ?map_cons, ?list_prod_cons_l,
    ?map_app, ?map_map, ?IHl; trivial.
Qed.

Lemma list_prod_map_map [A A' B B'] (f : A -> A') (g : B -> B') l l' :
  list_prod (map f l) (map g l') = map (fun '(x, y) => (f x, g y)) (list_prod l l').
Proof.
  rewrite list_prod_map_l, list_prod_map_r, ?map_map; apply map_ext.
  intros []; trivial.
Qed.

Lemma list_prod_filter_l [A B] (f : A -> _) l (l' : list B) :
  list_prod (filter f l) l' = filter (fun p => f (fst p)) (list_prod l l').
Proof.
  induction l; cbn [filter list_prod]; trivial.
  rewrite filter_app, filter_map_swap; cbn [fst].
  case f; rewrite ?filter_true, ?filter_false; cbn [list_prod map];
  rewrite ?IHl; auto.
Qed.

Lemma list_prod_filter_r [A B] (f : B -> _) (l : list A) l' :
  list_prod l (filter f l') = filter (fun p => f (snd p)) (list_prod l l').
Proof.
  induction l; cbn [filter list_prod]; trivial.
  rewrite filter_app, filter_map_swap; cbn [snd].
  rewrite ?IHl; f_equal.
Qed.

Lemma list_prod_filter_filter [A B] f g (l : list A) (l' : list B) :
  list_prod (filter f l) (filter g l') = filter (fun '(x, y) => f x && g y) (list_prod l l').
Proof.
  rewrite list_prod_filter_l, list_prod_filter_r, ?filter_filter.
  apply filter_ext; intros []; trivial.
Qed.

Lemma NoDup_list_prod [A B] l l' : NoDup l -> NoDup l' -> NoDup (@list_prod A B l l').
Proof.
  intros H G; induction H; intros; cbn [list_prod]; [constructor|].
  apply NoDup_app; trivial.
  { eapply Injective_map_NoDup, G. inversion 1; trivial. }
  intros [] (?&[-> ->]%pair_equal_spec&?)%in_map_iff []%in_prod_iff; tauto.
Qed.
