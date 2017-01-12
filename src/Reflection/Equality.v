Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.FixCoqMistakes.

Section language.
  Context (base_type_code : Type)
          (eq_base_type_code : base_type_code -> base_type_code -> bool)
          (base_type_code_bl : forall x y, eq_base_type_code x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> eq_base_type_code x y = true).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Fixpoint flat_type_beq (X Y : flat_type) {struct X} : bool
    := match X, Y with
       | Tbase T, Tbase T0 => eq_base_type_code T T0
       | Unit, Unit => true
       | Prod A B, Prod A0 B0 => (flat_type_beq A A0 && flat_type_beq B B0)%bool
       | Tbase _, _
       | Prod _ _, _
       | Unit, _
         => false
       end.
  Local Ltac t :=
    repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => assumption
           | _ => progress simpl in *
           | _ => solve [ eauto with nocore ]
           | [ H : False |- _ ] => exfalso; assumption
           | [ H : false = true |- _ ] => apply Bool.diff_false_true in H
           | [ |- Prod _ _ = Prod _ _ ] => apply f_equal2
           | [ |- Arrow _ _ = Arrow _ _ ] => apply f_equal2
           | [ |- Tbase _ = Tbase _ ] => apply f_equal
           | [ H : forall Y, _ = true -> _ = Y |- _ = ?Y' ]
             => is_var Y'; apply H; solve [ t ]
           | [ H : forall X Y, X = Y -> _ = true |- _ = true ]
             => eapply H; solve [ t ]
           | [ H : true = true |- _ ] => clear H
           | [ H : andb ?x ?y = true |- _ ]
             => destruct x, y; simpl in H; solve [ t ]
           | [ H : andb ?x ?y = true |- _ ]
             => destruct x eqn:?; simpl in H
           | [ H : ?f ?x = true |- _ ] => destruct (f x); solve [ t ]
           | [ H : ?x = true |- andb _ ?x = true ]
             => destruct x
           | [ |- andb ?x _ = true ]
             => cut (x = true); [ destruct x; simpl | ]
           end.
  Lemma flat_type_dec_bl X : forall Y, flat_type_beq X Y = true -> X = Y.
  Proof. clear base_type_code_lb; induction X, Y; t. Defined.
  Lemma flat_type_dec_lb X : forall Y, X = Y -> flat_type_beq X Y = true.
  Proof. clear base_type_code_bl; intros; subst Y; induction X; t. Defined.
  Definition flat_type_eq_dec (X Y : flat_type) : {X = Y} + {X <> Y}
    := match Sumbool.sumbool_of_bool (flat_type_beq X Y) with
       | left pf => left (flat_type_dec_bl _ _ pf)
       | right pf => right (fun pf' => let pf'' := eq_sym (flat_type_dec_lb _ _ pf') in
                                       Bool.diff_true_false (eq_trans pf'' pf))
       end.
  Definition type_beq (X Y : type) : bool
    := match X, Y with
       | Arrow A B, Arrow A0 B0 => (flat_type_beq A A0 && flat_type_beq B B0)%bool
       end.
  Lemma type_dec_bl X : forall Y, type_beq X Y = true -> X = Y.
  Proof. clear base_type_code_lb; pose proof flat_type_dec_bl; induction X, Y; t. Defined.
  Lemma type_dec_lb X : forall Y, X = Y -> type_beq X Y = true.
  Proof. clear base_type_code_bl; pose proof flat_type_dec_lb; intros; subst Y; induction X; t. Defined.
  Definition type_eq_dec (X Y : type) : {X = Y} + {X <> Y}
    := match Sumbool.sumbool_of_bool (type_beq X Y) with
       | left pf => left (type_dec_bl _ _ pf)
       | right pf => right (fun pf' => let pf'' := eq_sym (type_dec_lb _ _ pf') in
                                       Bool.diff_true_false (eq_trans pf'' pf))
       end.
End language.

Lemma dec_eq_flat_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (flat_type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; auto.
Defined.
Hint Extern 1 (Decidable (@eq (flat_type ?base_type_code) ?x ?y))
=> simple apply (@dec_eq_flat_type base_type_code) : typeclass_instances.
Lemma dec_eq_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; typeclasses eauto.
Defined.
Hint Extern 1 (Decidable (@eq (type ?base_type_code) ?x ?y))
=> simple apply (@dec_eq_type base_type_code) : typeclass_instances.
