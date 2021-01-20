Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.Reflect.
Import ListNotations.

Class Listable T := { list_all : list T ; find_index : T -> nat }.

Arguments find_index {T} {_} _.
Arguments list_all T {_}.

Class FinitelyListable T {l : Listable T}
  := { find_index_ok : forall t, nth_error (list_all T) (find_index t) = Some t
       ; enumerate_smallb : fold_right andb true (List.map (fun '(n, t) => Nat.eqb n (find_index t)) (enumerate (list_all T))) = true }.

Ltac prove_FinitelyListable :=
  split;
  [ let t := fresh in
    intro t; destruct t;
    vm_compute; try reflexivity
  | vm_compute; reflexivity ].

Ltac push_S_refine_num ev :=
  lazymatch ev with
  | S ?ev
    => refine (S _); push_S_refine_num ev
  | ?ev => let __ := open_constr:(eq_refl : ev = S _) in
           refine O
  end.

Ltac force_num ev :=
  lazymatch ev with
  | S ?ev => force_num ev
  | ?ev => unify ev O
  end.

Ltac partially_prove_Listable :=
  let fin := open_constr:(_) in
  split;
  [
  | repeat (let t := fresh in intro t; case t; clear t);
    push_S_refine_num fin ];
  force_num fin.

Ltac finish_prove_FinitelyListable :=
  split;
  [ cbv [list_all find_index];
    repeat (let t := fresh in intro t; case t; clear t);
    unshelve
      (repeat match goal with
              | [ |- nth_error (_ :: _) O = _ ] => cbn [nth_error]
              | [ |- nth_error (_ :: ?xs) (S ?n) = ?rhs ] => change (nth_error xs n = rhs)
              | [ |- nth_error ?ev _ = ?rhs ]
                => is_evar ev;
                   let __ := open_constr:(eq_refl : ev = cons _ _) in
                   idtac
              | [ |- Some _ = Some _ ] => reflexivity
              end);
    try exact nil
  | vm_compute; reflexivity ].

Ltac prove_ListableDerive :=
  lazymatch goal with
  | [ |- @FinitelyListable ?T ?H ]
    => revert H; instantiate (1:=ltac:(partially_prove_Listable)); intro H; (* argh, instantiate .. in (value of H) doesn't work in old versions of Coq, and current Coq doesn't know about (Value of H) *)
       cbv [H];
       finish_prove_FinitelyListable
  end.

Ltac prove_ListablePackage T :=
  refine (_ : { l : Listable T | FinitelyListable T });
  unshelve econstructor;
  [ partially_prove_Listable
  | finish_prove_FinitelyListable ].

Ltac get_ListablePackage T :=
  constr:(ltac:(prove_ListablePackage T)).

Section with_listable.
  Context {T}
          {Listable_T : Listable T}
          {FinitelyListable_T : FinitelyListable T}.

  Lemma find_index_iff x n : find_index x = n <-> List.nth_error (list_all T) n = Some x.
  Proof.
    split; [ intro; subst; apply find_index_ok | ].
    generalize enumerate_smallb.
    cbv [enumerate].
    set (offset := O).
    change n with (offset + n)%nat at 2.
    clearbody offset.
    rename x into v.
    intros Hfold Hnth; revert offset n Hfold Hnth.
    induction (list_all T) as [|x xs IHxs]; intros.
    { destruct n; cbn in *; congruence. }
    { cbn in *.
      rewrite Bool.andb_true_iff, Nat.eqb_eq in Hfold.
      destruct Hfold as [Hfold1 Hfold2].
      specialize (IHxs (S offset) (pred n) Hfold2).
      subst offset; destruct n as [|n]; cbn in *.
      { inversion Hnth; subst; lia. }
      { specialize (IHxs Hnth); lia. } }
  Qed.

  Lemma enumerate_unique n m x y
        (Hn : List.nth_error (list_all T) n = Some x)
        (Hm : List.nth_error (list_all T) m = Some y)
        (Hxy : x = y)
    : n = m.
  Proof. rewrite <- !find_index_iff in *; subst; reflexivity. Qed.

  Lemma find_index_inj x y : find_index x = find_index y -> x = y.
  Proof. rewrite find_index_iff, find_index_ok; congruence. Qed.

  Definition eqb_of_listable : T -> T -> bool := fun x y => Nat.eqb (find_index x) (find_index y).
  Lemma eqb_of_listable_refl x : eqb_of_listable x x = true.
  Proof. cbv [eqb_of_listable]. apply Nat.eqb_refl. Qed.
  Lemma eqb_of_listable_lb x y : x = y -> eqb_of_listable x y = true.
  Proof. intros; subst; apply eqb_of_listable_refl. Qed.
  Lemma eqb_of_listable_bl x y : eqb_of_listable x y = true -> x = y.
  Proof. cbv [eqb_of_listable]; rewrite Nat.eqb_eq. apply find_index_inj. Qed.
  Lemma eqb_of_listable_eq x y : eqb_of_listable x y = true <-> x = y.
  Proof. split; auto using eqb_of_listable_lb, eqb_of_listable_bl. Qed.
  Global Instance eq_dec_of_listable : DecidableRel (@eq T)
    := dec_rel_of_bool_dec_rel eqb_of_listable eqb_of_listable_bl eqb_of_listable_lb.
  Global Instance reflect_eqb_of_listable : reflect_rel (@eq T) eqb_of_listable
    := reflect_of_beq eqb_of_listable_bl eqb_of_listable_lb.
End with_listable.
