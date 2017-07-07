(** * Context made from an associative list, without modules *)
Require Import Coq.Bool.Sumbool.
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Equality.

Local Open Scope list_scope.
Section ctx.
  Context (key : Type)
          (key_beq : key -> key -> bool)
          (key_bl : forall k1 k2, key_beq k1 k2 = true -> k1 = k2)
          (key_lb : forall k1 k2, k1 = k2 -> key_beq k1 k2 = true)
          base_type_code (var : base_type_code -> Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true).

  Definition var_cast {a b} (x : var a) : option (var b)
    := match Sumbool.sumbool_of_bool (base_type_code_beq a b), Sumbool.sumbool_of_bool (base_type_code_beq b b) with
       | left pf, left pf' => match eq_trans (base_type_code_bl_transparent _ _ pf) (eq_sym (base_type_code_bl_transparent _ _ pf')) with
                              | eq_refl => Some x
                              end
       | right _, _ | _, right _ => None
       end.

  Fixpoint find (k : key) (xs : list (key * { t : _ & var t })) {struct xs}
    : option { t : _ & var t }
    := match xs with
       | nil => None
       | k'x :: xs' =>
         if key_beq k (fst k'x)
         then Some (snd k'x)
         else find k xs'
       end.

  Fixpoint remove (k : key) (xs : list (key * { t : _ & var t })) {struct xs}
    : list (key * { t : _ & var t })
    := match xs with
       | nil => nil
       | k'x :: xs' =>
         if key_beq k (fst k'x)
         then remove k xs'
         else k'x :: remove k xs'
       end.

  Definition add (k : key) (x : { t : _ & var t }) (xs : list (key * { t : _ & var t }))
    : list (key * { t : _ & var t })
    := (k, x) :: xs.

  Lemma find_remove_neq k k' xs (H : k <> k')
    : find k (remove k' xs) = find k xs.
  Proof.
    induction xs as [|x xs IHxs]; [ reflexivity | simpl ].
    break_innermost_match;
      repeat match goal with
             | [ H : key_beq _ _ = true |- _ ] => apply key_bl in H
             | [ H : context[key_beq ?x ?x] |- _ ] => rewrite (key_lb x x) in H by reflexivity
             | [ |- context[key_beq ?x ?x] ] => rewrite (key_lb x x) by reflexivity
             | [ H : ?x = false |- context[?x] ] => rewrite H
             | _ => congruence
             | _ => assumption
             | _ => progress subst
             | _ => progress simpl
             end.
  Qed.

  Lemma find_remove_same k xs
    : find k (remove k xs) = None.
  Proof.
    induction xs as [|x xs IHxs]; [ reflexivity | simpl ].
    break_innermost_match;
      repeat match goal with
             | [ H : key_beq _ _ = true |- _ ] => apply key_bl in H
             | [ H : context[key_beq ?x ?x] |- _ ] => rewrite (key_lb x x) in H by reflexivity
             | [ |- context[key_beq ?x ?x] ] => rewrite (key_lb x x) by reflexivity
             | [ H : ?x = false |- context[?x] ] => rewrite H
             | _ => congruence
             | _ => assumption
             | _ => progress subst
             | _ => progress simpl
             end.
  Qed.

  Lemma find_remove_nbeq k k' xs (H : key_beq k k' = false)
    : find k (remove k' xs) = find k xs.
  Proof.
    rewrite find_remove_neq; [ reflexivity | intro; subst ].
    rewrite key_lb in H by reflexivity; congruence.
  Qed.

  Lemma find_remove_beq k k' xs (H : key_beq k k' = true)
    : find k (remove k' xs) = None.
  Proof.
    apply key_bl in H; subst.
    rewrite find_remove_same; reflexivity.
  Qed.

  Definition AListContext : @Context base_type_code key var
    := {| ContextT := list (key * { t : _ & var t });
          lookupb t ctx n
          := match find n ctx with
             | Some (existT t' v)
               => var_cast v
             | None => None
             end;
          extendb t ctx n v
          := add n (existT _ t v) ctx;
          removeb t ctx n
          := remove n ctx;
          empty := nil |}.

  Lemma length_extendb (ctx : AListContext) k t v
    : length (@extendb _ _ _ AListContext t ctx k v) = S (length ctx).
  Proof. reflexivity. Qed.

  Lemma AListContextOk : @ContextOk base_type_code key var AListContext.
  Proof using base_type_code_lb key_bl key_lb.
    split;
      repeat first [ reflexivity
                   | progress simpl in *
                   | progress intros
                   | rewrite find_remove_nbeq by eassumption
                   | rewrite find_remove_beq by eassumption
                   | rewrite find_remove_neq by congruence
                   | rewrite find_remove_same by congruence
                   | match goal with
                     | [ |- context[key_beq ?x ?y] ]
                       => destruct (key_beq x y) eqn:?
                     | [ H : key_beq ?x ?y = true |- _ ]
                       => apply key_bl in H
                     end
                   | break_innermost_match_step
                   | progress unfold var_cast
                   | rewrite key_lb in * by reflexivity
                   | rewrite base_type_code_lb in * by reflexivity
                   | rewrite concat_pV
                   | congruence
                   | break_innermost_match_hyps_step
                   | progress unfold var_cast in * ].
  Qed.
End ctx.
