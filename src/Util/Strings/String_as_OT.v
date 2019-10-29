Require Import Coq.omega.Omega Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Structures.OrderedType.

Lemma nat_compare_eq_refl : forall x, Nat.compare x x = Eq.
  intros; apply Nat.compare_eq_iff; trivial.
Qed.

Hint Rewrite <- nat_compare_lt : nat_comp_hints.
Hint Rewrite <- nat_compare_gt : nat_comp_hints.
Hint Rewrite    Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite <- Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite    nat_compare_eq_refl : nat_comp_hints.

Ltac autorewrite_nat_compare :=
  autorewrite with nat_comp_hints in *.

Lemma nat_compare_consistent :
  forall n0 n1,
    { Nat.compare n0 n1 = Lt /\ Nat.compare n1 n0 = Gt }
    + { Nat.compare n0 n1 = Eq /\ Nat.compare n1 n0 = Eq }
    + { Nat.compare n0 n1 = Gt /\ Nat.compare n1 n0 = Lt }.
Proof.
  intros n0 n1;
  destruct (lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
  [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
  split;
  autorewrite_nat_compare;
  intuition.
Qed.

Module String_as_OT <: OrderedType.
  Definition t := string.

  Fixpoint string_compare str1 str2 :=
    match str1, str2 with
      | EmptyString, EmptyString => Eq
      | EmptyString, _           => Lt
      | _, EmptyString           => Gt
      | String char1 tail1, String char2 tail2 =>
        match Nat.compare (nat_of_ascii char1) (nat_of_ascii char2) with
          | Eq => string_compare tail1 tail2
          | Lt => Lt
          | Gt => Gt
        end
    end.

  Lemma string_compare_eq_refl : forall x, string_compare x x = Eq.
    intro x;
    induction x;
      simpl; trivial;
      autorewrite_nat_compare.
      trivial.
  Qed.

  Ltac comparisons_minicrush :=
    autorewrite_nat_compare;
    match goal with
      | [ |- context [Nat.compare ?a ?b] ] =>
        let H := fresh in
        first [
            assert (Nat.compare a b = Eq) as H by (autorewrite_nat_compare; omega) |
            assert (Nat.compare a b = Lt) as H by (autorewrite_nat_compare; omega) |
            assert (Nat.compare a b = Gt) as H by (autorewrite_nat_compare; omega)
        ]; rewrite H; intuition
    end.

  Ltac destruct_comparisons :=
    repeat match goal with
             | [ H: match ?pred ?a ?b with
                      | Lt => _ | Gt => _ | Eq => _ end = _
                 |- _] =>
               let H := fresh in
               destruct (pred a b) eqn:H;
                 try discriminate
           end.

  Ltac exfalso_from_equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] => assert (b = c) by congruence; discriminate
    end.

  Definition eq := @eq string.

  Hint Resolve string_compare_eq_refl : core.

  Lemma eq_Eq : forall x y, x = y -> string_compare x y = Eq.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma nat_of_ascii_injective :
    forall a b, nat_of_ascii a = nat_of_ascii b <-> a = b.
  Proof.
    intros a b; split; intro H;
    [ apply (f_equal ascii_of_nat) in H;
      repeat rewrite ascii_nat_embedding in H
    | apply (f_equal nat_of_ascii) in H ]; trivial.
  Qed.

  Lemma Eq_eq : forall x y, string_compare x y = Eq -> x = y.
  Proof.
    induction x;
      destruct y;
      simpl;
      first [ discriminate
            | intros;
              f_equal;
              destruct_comparisons;
              autorewrite_nat_compare;
              rewrite nat_of_ascii_injective in *
            | idtac ];
      intuition.
  Qed.

  Lemma Eq_eq_iff : forall x y, x = y <-> string_compare x y = Eq.
  Proof.
    intros; split; eauto using eq_Eq, Eq_eq.
  Qed.

  Definition eq_refl := @eq_refl string.

  Definition eq_sym := @eq_sym string.

  Definition eq_trans := @eq_trans string.

  Definition lt x y :=
    string_compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z;
    generalize x z;
    clear x z;

    induction y;
    destruct x;
    destruct z;
      intros;
      unfold lt in *;
      simpl in *;
      first [ discriminate
            | destruct_comparisons; comparisons_minicrush
            | trivial ]; intuition.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    unfold lt, not in *;
    intros;
    rewrite Eq_eq_iff in *;
    exfalso_from_equalities.
  Qed.

  Lemma Lt_Gt : forall x y, string_compare x y = Gt <-> string_compare y x = Lt.
  Proof.
    intros x;
    induction x as [ | x0 x' Hind ];
      intros y;
      destruct y as [ | y0 y' ];

      simpl;
      split;
      first [ discriminate | trivial ];

      destruct (nat_compare_consistent
                  (nat_of_ascii x0)
                  (nat_of_ascii y0))
          as [ [ (H1, H2) | (H1, H2) ] | (H1, H2) ];
        rewrite H1, H2;
        try rewrite Hind;
        auto.
  Qed.

  Definition compare x y : OrderedType.Compare lt eq x y.
  Proof.
    destruct (string_compare x y) eqn:comp;
      unfold lt;
      [ constructor 2; apply Eq_eq
      | constructor 1
      | constructor 3; apply Lt_Gt];
      trivial.
  Defined.

  Definition eq_dec : forall (x y: string), { x = y } + { x <> y } := string_dec.

End String_as_OT.

(* Usage example:
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Module StringIndexedMap := FMapAVL.Make(String_as_OT).
Definition String2Nat := StringIndexedMap.t nat.

Definition find key (map: String2Nat) := StringIndexedMap.find key map.

Definition bind (pair: string * nat) (map: String2Nat) := StringIndexedMap.add (fst pair) (snd pair) map.

Notation "k >> v" := (pair k v) (at level 100).
Notation "[[ b1 , .. , bn ]]" := (bind b1 .. (bind bn (StringIndexedMap.empty nat)) .. ).

Open Scope string_scope.

Definition population_in_millions :=
 [[ "china" >> 1364, "india" >> 1243, "united states" >> 318, "indonesia" >> 247, "brazil" >> 201, "pakistan" >> 186, "nigeria" >> 174, "bangladesh" >> 153, "russia" >> 144, "japan" >> 127, "mexico" >> 120, "philippines" >> 99, "vietnam" >> 90, "ethiopia" >> 87, "egypt" >> 86, "germany" >> 81, "iran" >> 77, "turkey" >> 77, "democratic republic of the congo" >> 68, "france" >> 66 ]].

Eval compute in (find "france" population_in_millions).
*)
