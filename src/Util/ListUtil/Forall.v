Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.

Definition Forallb {A} (P : A -> bool) (ls : list A) : bool
  := List.fold_right andb true (List.map P ls).

Lemma unfold_Forallb {A P} ls
  : @Forallb A P ls
    = match ls with
      | nil => true
      | cons x xs => andb (P x) (Forallb P xs)
      end.
Proof using Type. destruct ls; reflexivity. Qed.

Lemma Forall_Forallb_iff {A} (P : A -> bool) (Q : A -> Prop) (ls : list A)
      (H : forall x, In x ls -> P x = true <-> Q x)
  : Forallb P ls = true <-> Forall Q ls.
Proof using Type.
  induction ls as [|x xs IHxs]; simpl; rewrite unfold_Forallb.
  { intuition. }
  { simpl in *.
    rewrite Bool.andb_true_iff, IHxs
      by (intros; apply H; eauto).
    split; intro H'; inversion H'; subst; constructor; intuition;
      apply H; eauto. }
Qed.

Local Ltac t_Forall2_step :=
  first [ progress intros
        | progress subst
        | progress destruct_head'_and
        | progress destruct_head'_ex
        | progress specialize_by_assumption
        | progress split_iff
        | progress split_and
        | apply conj
        | progress cbn [List.map List.seq List.repeat List.rev List.firstn List.skipn List.length] in *
        | exfalso; assumption
        | solve [ eauto ]
        | match goal with
          | [ |- List.Forall2 _ _ _ ] => constructor
          | [ |- List.Forall _ _ ] => constructor
          | [ H : List.Forall2 _ nil (cons _ _) |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) nil |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (cons _ _) ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x (cons _ _) |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ nil ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x nil |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall _ (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (List.app _ _) _ |- _ ] => apply Forall2_app_inv_l in H
          | [ H : List.Forall2 _ _ (List.app _ _) |- _ ] => apply Forall2_app_inv_r in H
          | [ H : nil = _ ++ _ |- _ ] => symmetry in H
          | [ H : _ ++ _ = nil |- _ ] => apply app_eq_nil in H
          | [ H : cons _ _ = nil |- _ ] => inversion H
          | [ H : nil = cons _ _ |- _ ] => inversion H
          | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
          | [ H : _ ++ _ :: nil = _ ++ _ :: nil |- _ ] => apply app_inj_tail in H
          | [ |- List.Forall2 _ (_ ++ _ :: nil) (_ ++ _ :: nil) ] => apply Forall2_app
          end ].
Local Ltac t_Forall2 := repeat t_Forall2_step.

Lemma Forall2_map_l_iff {A A' B R f ls1 ls2}
  : @List.Forall2 A' B R (List.map f ls1) ls2
    <-> @List.Forall2 A B (fun x y => R (f x) y) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_map_r_iff {A B B' R f ls1 ls2}
  : @List.Forall2 A B' R ls1 (List.map f ls2)
    <-> @List.Forall2 A B (fun x y => R x (f y)) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_map_map_iff {A A' B B' R f g ls1 ls2}
  : @List.Forall2 A' B' R (List.map f ls1) (List.map g ls2)
    <-> @List.Forall2 A B (fun x y => R (f x) (g y)) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.

Lemma Forall2_flip_iff {A B P xs ys}
  : @Forall2 A B P xs ys <-> Forall2 (Basics.flip P) ys xs.
Proof using Type. split; induction 1; constructor; assumption. Qed.

Lemma Forall2_Forall {A R ls}
  : @List.Forall2 A A R ls ls
    <-> @List.Forall A (Proper R) ls.
Proof using Type. induction ls as [|l ls IHls]; t_Forall2. Qed.

Lemma Forall_seq {R start len}
  : List.Forall R (seq start len) <-> (forall x, (start <= x < start + len)%nat -> R x).
Proof using Type.
  revert start; induction len as [|len IHlen]; intro start;
    [ | specialize (IHlen (S start)) ].
  all: repeat first [ t_Forall2_step
                    | lia
                    | exfalso; lia
                    | match goal with
                      | [ H : ?R ?x |- ?R ?y ]
                        => destruct (PeanoNat.Nat.eq_dec x y); [ subst; assumption | clear H ]
                      | [ H : _ |- _ ] => apply H; clear H
                      end ].
Qed.

Lemma Forall2_repeat_iff {A B R x y n m}
  : @List.Forall2 A B R (List.repeat x n) (List.repeat y m)
    <-> ((n <> 0%nat -> R x y) /\ n = m).
Proof using Type.
  revert m; induction n as [|n IHn], m as [|m]; [ | | | specialize (IHn m) ];
    t_Forall2; try congruence.
Qed.

Lemma Forall2_rev_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) (List.rev ls2)
    <-> @List.Forall2 A B R ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.

Lemma Forall2_rev_lr_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) ls2 <-> @List.Forall2 A B R ls1 (List.rev ls2).
Proof using Type.
  rewrite <- (rev_involutive ls2), Forall2_rev_iff, !rev_involutive; reflexivity.
Qed.

Lemma Forall2_firstn_skipn_iff n {A B R ls1 ls2}
  : @List.Forall2 A B R ls1 ls2 <-> (List.Forall2 R (List.firstn n ls1) (List.firstn n ls2) /\ List.Forall2 R (List.skipn n ls1) (List.skipn n ls2)).
Proof. revert ls1 ls2; induction n, ls1, ls2; t_Forall2. Qed.

Lemma Forall2_firstn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.firstn n ls1) (List.firstn n ls2).
Proof using Type. rewrite (Forall2_firstn_skipn_iff n); tauto. Qed.

Lemma Forall2_skipn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.skipn n ls1) (List.skipn n ls2).
Proof using Type. rewrite (Forall2_firstn_skipn_iff n); tauto. Qed.

Lemma Forall_firstn_skipn_iff n {A R ls}
  : @List.Forall A R ls <-> (List.Forall R (List.firstn n ls) /\ List.Forall R (List.skipn n ls)).
Proof. revert ls; induction n, ls; t_Forall2. Qed.

Lemma Forall_firstn {A R ls n}
  : @List.Forall A R ls -> @List.Forall A R (List.firstn n ls).
Proof using Type. rewrite (Forall_firstn_skipn_iff n); tauto. Qed.

Lemma Forall_skipn {A R ls n}
  : @List.Forall A R ls -> @List.Forall A R (List.skipn n ls).
Proof using Type. rewrite (Forall_firstn_skipn_iff n); tauto. Qed.

Lemma Forall2_app_l_iff {A B R ls1 ls2 ls}
  : @List.Forall2 A B R (ls1 ++ ls2) ls <-> (List.Forall2 R ls1 (List.firstn (List.length ls1) ls) /\ List.Forall2 R ls2 (List.skipn (List.length ls1) ls)).
Proof. rewrite (Forall2_firstn_skipn_iff (List.length ls1)), firstn_app, skipn_app, firstn_all, skipn_all, PeanoNat.Nat.sub_diag, firstn_O, skipn_O, app_nil_l, app_nil_r; reflexivity. Qed.

Lemma Forall2_app_r_iff {A B R ls1 ls2 ls}
  : @List.Forall2 A B R ls (ls1 ++ ls2) <-> (List.Forall2 R (List.firstn (List.length ls1) ls) ls1 /\ List.Forall2 R (List.skipn (List.length ls1) ls) ls2).
Proof. rewrite Forall2_flip_iff, Forall2_app_l_iff, <- !Forall2_flip_iff; reflexivity. Qed.

Lemma eq_length_Forall2 {A B R ls1 ls2}
  : @List.Forall2 A B R ls1 ls2 -> List.length ls1 = List.length ls2.
Proof using Type.
  revert ls2; induction ls1, ls2; t_Forall2.
Qed.

Lemma Forall2_combine {A B C D R1 R2 R3 ls1 ls2 ls3 ls4}
      (HR : forall x y z w, (R1 x y : Prop) -> (R2 z w : Prop) -> (R3 (x, z) (y, w) : Prop))
  : @List.Forall2 A B R1 ls1 ls2
    -> @List.Forall2 C D R2 ls3 ls4
    -> List.Forall2 R3 (List.combine ls1 ls3) (List.combine ls2 ls4).
Proof using Type.
  revert ls2 ls3 ls4; induction ls1, ls2, ls3, ls4; t_Forall2.
Qed.

Lemma Forall_forall_iff_nth_error {A R ls}
  : @Forall A R ls
    <-> (forall i v, nth_error ls i = Some v -> R v).
Proof using Type.
  rewrite Forall_forall.
  split; eauto using nth_error_In.
  intros ? ? H'; apply In_nth_error in H'.
  firstorder auto.
Qed.

Lemma Forall_forall_iff_nth_error_match {A R ls}
  : @Forall A R ls
    <-> forall i, match nth_error ls i with Some v => R v | None => True end.
Proof using Type.
  rewrite Forall_forall_iff_nth_error.
  split; intros H i; try intro; specialize (H i); break_match; break_match_hyps; eauto; congruence.
Qed.

Lemma Forall2_forall_iff_nth_error {A B R xs ys}
  : @Forall2 A B R xs ys
    <-> forall i, option_eq R (nth_error xs i) (nth_error ys i).
Proof using Type.
  revert ys; induction xs as [|x xs IHxs], ys as [|y ys];
    [ | | | specialize (IHxs ys) ]; t_Forall2.
  all: repeat first [ t_Forall2_step
                    | progress cbn [option_eq nth_error] in *
                    | progress inversion_option
                    | match goal with
                      | [ H : forall x, nth_error (cons _ _) x = None |- _ ] => specialize (H O)
                      | [ H : forall x, option_eq _ (nth_error (cons _ _) x) None |- _ ] => specialize (H O)
                      | [ |- context[nth_error (cons _ _) ?x] ] => is_var x; destruct x
                      | [ H : forall i, option_eq _ _ (nth_error (cons _ _) ?x) |- _ ]
                        => pose proof (H O);
                           pose proof (fun i => H (S i));
                           clear H
                      | [ H : forall i, option_eq _ (nth_error (cons _ _) ?x) _ |- _ ]
                        => pose proof (H O);
                           pose proof (fun i => H (S i));
                           clear H
                      | [ |- context[nth_error nil ?x] ] => is_var x; destruct x
                      end ].
Qed.

Lemma Forall2_forall_iff'' {A B R xs ys d1 d2}
  : (@Forall2 A B R xs ys /\ R d1 d2)
    <-> (length xs = length ys
         /\ (forall i, R (nth_default d1 xs i) (nth_default d2 ys i))).
Proof using Type.
  t_Forall2; cbv [nth_default] in *.
  all: repeat first [ eapply eq_length_Forall2; eassumption
                    | rewrite Forall2_forall_iff_nth_error
                    | t_Forall2_step
                    | progress cbn [option_eq] in *
                    | progress inversion_option
                    | match goal with
                      | [ H : Forall2 _ _ _ |- _ ] => rewrite Forall2_forall_iff_nth_error in H
                      | [ H : forall i : nat, _ |- context[nth_error _ ?n] ]
                        => specialize (H n)
                      | [ H' : List.length ?ls = _, H : forall i : nat, _ |- _ ]
                        => specialize (H (List.length ls)); rewrite ?nth_error_length_error in H by lia
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step
                    | match goal with
                      | [ H : nth_error _ _ = None |- _ ] => rewrite nth_error_None in H
                      | [ H : nth_error ?l ?n = Some _ |- _ ]
                        => assert (n < List.length l) by (apply nth_error_Some; congruence);
                           clear H
                      end
                    | lia ].
Qed.

Lemma Forall2_forall_In_combine_iff {A B} R xs ys
  : @List.Forall2 A B R xs ys
    <-> (List.length xs = List.length ys
         /\ forall x y, List.In (x, y) (List.combine xs ys) -> R x y).
Proof using Type.
  split; revert ys; induction xs as [|x xs IHxs], ys as [|y ys]; cbn in *; intro H.
  all: inversion_clear H; split_and;
    try solve [ repeat constructor; intuition (congruence + eauto) ].
Qed.

Global Instance Forall2_Proper_impl {A B}
  : Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> eq ==> eq ==> Basics.impl)
           (@List.Forall2 A B) | 10.
Proof using Type.
  cbv [Basics.impl respectful pointwise_relation].
  repeat intro; subst; rewrite Forall2_forall_In_combine_iff in *.
  destruct_head'_and; split; eauto.
Qed.

Global Instance Forall2_Proper_iff {A B}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff)
           (@List.Forall2 A B) | 10.
Proof using Type.
  cbv [respectful pointwise_relation].
  repeat intro; subst; rewrite !Forall2_forall_In_combine_iff in *.
  split_iff.
  repeat (split || destruct_head'_and); eauto.
Qed.

Lemma Forall2_Forall_iff_ignore_r {A B P ls1 ls2}
  : @Forall2 A B (fun _ => P) ls1 ls2 <-> (length ls1 = length ls2 /\ Forall P ls2).
Proof using Type.
  revert ls1 ls2; induction ls1, ls2; t_Forall2; exfalso; lia.
Qed.

Lemma Forall2_Forall_ignore_l {A B P ls1 ls2}
  : @Forall2 A B (fun x _ => P x) ls1 ls2 <-> (length ls1 = length ls2 /\ Forall P ls1).
Proof using Type. now rewrite Forall2_flip_iff; cbv [Basics.flip]; rewrite Forall2_Forall_iff_ignore_r. Qed.

Lemma Forall2_flip {A B} {R : A -> B -> Prop} xs ys :
  Forall2 R xs ys -> Forall2 (fun y x => R x y) ys xs.
Proof using Type. induction 1; eauto. Qed.

Lemma length_Forall2 {A B : Type} {xs ys} {P:A->B->Prop} : Forall2 P xs ys -> length xs = length ys.
Proof using Type. induction 1; cbn; eauto. Qed.

Section weaken.
  Context {A B} {P Q:A->B->Prop} (H : forall (a : A) (b : B), P a b -> Q a b).
  Fixpoint Forall2_weaken args args' (pf : Forall2 P args args') : Forall2 Q args args' :=
    match pf with
    | Forall2_nil => Forall2_nil _
    | Forall2_cons _ _ _ _ Rxy k => Forall2_cons _ _ (H _ _ Rxy) (Forall2_weaken _ _ k)
    end.
End weaken.
Lemma Forall2_map_l {A' A B} (f : A' -> A) {R : A -> B -> Prop} (xs : list A') (ys : list B) :
  Forall2 R (List.map f xs) ys <-> Forall2 (fun x y => R (f x) y) xs ys.
Proof using Type.
  remember (List.map f xs) as fxs eqn:Heqn.
  split; intros H; (revert fxs Heqn + revert xs Heqn); induction H; intros ? Heqn;
    try destruct xs; cbn in *; inversion Heqn; clear Heqn; subst;
      try congruence; eauto.
Qed.
Import RelationClasses.
Lemma Reflexive_forall2 {A} {R} : @Reflexive A R -> Reflexive (Forall2 R).
Proof using Type. intros ? l; induction l; eauto. Qed.
Global Hint Extern 1 (Reflexive (Forall2 _)) => simple apply @Reflexive_forall2 : typeclass_instances.
Lemma Forall2_eq {A} (xs ys : list A) : Forall2 eq xs ys <-> xs = ys.
Proof using Type. split; induction 1; subst; eauto; reflexivity. Qed.
Lemma Forall2_trans {A B C} {AB BC} {xs : list A} {ys : list B} :
  Forall2 AB xs ys -> forall {zs : list C}, Forall2 BC ys zs ->
                                            Forall2 (fun x z => exists y, AB x y /\ BC y z) xs zs.
Proof using Type. induction 1; inversion 1; subst; econstructor; eauto. Qed.

Lemma Forall2_nil_nil_iff A B P
  : @Forall2 A B P nil nil <-> True.
Proof using Type. split; eauto. Qed.
Lemma Forall2_nil_cons_iff A B P x y
  : @Forall2 A B P nil (cons x y) <-> False.
Proof using Type. split; firstorder inversion_one_head Forall2. Qed.
Lemma Forall2_nil_l_iff A B P ls
  : @Forall2 A B P nil ls <-> ls = nil.
Proof using Type. split; firstorder (try inversion_one_head Forall2; subst; auto). Qed.
Lemma Forall2_nil_r_iff A B P ls
  : @Forall2 A B P ls nil <-> ls = nil.
Proof using Type. split; firstorder (try inversion_one_head Forall2; subst; auto). Qed.
Lemma Forall2_cons_nil_iff A B P x y
  : @Forall2 A B P (cons x y) nil <-> False.
Proof using Type. split; firstorder inversion_one_head Forall2. Qed.
Lemma Forall2_cons_cons_iff A B P x xs y ys
  : @Forall2 A B P (cons x xs) (cons y ys) <-> (P x y /\ Forall2 P xs ys).
Proof using Type. split; firstorder (inversion_one_head Forall2; auto). Qed.
Lemma Forall2_cons_l_ex_iff A B P x xs ls
  : @Forall2 A B P (cons x xs) ls <-> (exists y ys, ls = cons y ys /\ P x y /\ Forall2 P xs ys).
Proof using Type. split; firstorder (inversion_one_head Forall2; eauto). Qed.
Lemma Forall2_cons_r_ex_iff A B P x xs ls
  : @Forall2 A B P ls (cons x xs) <-> (exists y ys, ls = cons y ys /\ P y x /\ Forall2 P ys xs).
Proof using Type. split; firstorder (inversion_one_head Forall2; eauto). Qed.

Lemma pull_ex_Forall_iff {A B} {R : A -> B -> Prop} {ls}
  : Forall (fun a => ex (R a)) ls <-> exists ls', Forall2 R ls ls'.
Proof using Type.
  induction ls as [|x xs IH];
    rewrite ?Forall_nil_iff, ?Forall_cons_iff, ?IH;
    try setoid_rewrite Forall2_nil_l_iff;
    try setoid_rewrite Forall2_cons_l_ex_iff;
    repeat firstorder (try inversion_one_head Forall; eauto 7).
Qed.

Lemma pull_ex_Forall2_l_iff {A B C} {R : A -> B -> C -> Prop} {ls1 ls2}
  : Forall2 (fun a b => ex (R a b)) ls1 ls2 <-> exists ls3, List.length ls1 = List.length ls3 /\ Forall2 (fun ac b => R (fst ac) b (snd ac)) (List.combine ls1 ls3) ls2.
Proof using Type.
  revert ls2; induction ls1 as [|x xs IH], ls2 as [|y ys]; try specialize (IH ys).
  all: rewrite ?Forall2_nil_nil_iff, ?Forall2_nil_cons_iff, ?Forall2_cons_nil_iff, ?Forall2_cons_cons_iff, ?IH.
  all: try setoid_rewrite Forall2_nil_r_iff.
  all: try setoid_rewrite Forall2_nil_l_iff.
  all: try setoid_rewrite Forall2_cons_r_ex_iff.
  all: repeat first [ progress cbn [List.length List.combine] in *
                    | break_innermost_match_hyps_step
                    | progress subst
                    | solve [ exists nil; eauto ]
                    | match goal with
                      | [ H : S _ = S _ |- _ ] => inversion H; clear H
                      | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
                      end
                    | progress firstorder first [ congruence | eauto 7 ]
                    | eexists (_ :: _) ].
Qed.

Lemma pull_ex_Forall2_r_iff {A B C} {R : A -> B -> C -> Prop} {ls1 ls2}
  : Forall2 (fun a b => ex (R a b)) ls1 ls2 <-> exists ls3, List.length ls2 = List.length ls3 /\ Forall2 (fun a bc => R a (fst bc) (snd bc)) ls1 (List.combine ls2 ls3).
Proof using Type.
  setoid_rewrite Forall2_flip_iff; cbv [Basics.flip].
  rewrite pull_ex_Forall2_l_iff; reflexivity.
Qed.

Lemma Forall2_concat_l_ex_iff A B P xs ls
  : @Forall2 A B P (concat xs) ls <-> (exists ys, ls = concat ys /\ Forall2 (Forall2 P) xs ys).
Proof using Type.
  revert ls; induction xs as [|x xs IH]; cbn [concat]; intros.
  all: rewrite ?Forall2_nil_l_iff, ?Forall2_nil_r_iff.
  all: split; intros; firstorder (subst; auto).
  all: rewrite ?Forall2_nil_l_iff, ?Forall2_nil_r_iff in *; subst; cbn [concat].
  all: try solve [ reflexivity
                 | exists nil; cbn [concat]; eauto ].
  all: repeat first [ progress subst
                    | progress cbn [concat]
                    | assumption
                    | reflexivity
                    | match goal with
                      | [ H : ex _ |- _ ] => destruct H
                      | [ H : and _ _ |- _ ] => destruct H
                      | [ H : Forall2 _ (_ ++ _) _ |- _ ] => apply Forall2_app_inv_l in H
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => rewrite Forall2_cons_l_ex_iff in H
                      end
                    | apply Forall2_app
                    | rewrite IH; eauto
                    | progress rewrite IH in *
                    | eexists (_ :: _); split; cbn [concat]; [ | constructor; eassumption ] ].
Qed.

Lemma Forall2_concat_r_ex_iff A B P ls xs
  : @Forall2 A B P ls (concat xs) <-> (exists ys, ls = concat ys /\ Forall2 (Forall2 P) ys xs).
Proof using Type.
  split; intro H; [ apply Forall2_flip, Forall2_concat_l_ex_iff in H | apply Forall2_flip, Forall2_concat_l_ex_iff ].
  all: destruct H as [ys H]; exists ys; firstorder (subst; auto).
  all: apply Forall2_flip; (eapply Forall2_weaken; [ | eassumption ]).
  all: apply Forall2_flip.
Qed.

Lemma Forall2_concat_concat A B P xs ys
  : Forall2 (Forall2 P) xs ys -> @Forall2 A B P (concat xs) (concat ys).
Proof using Type.
  rewrite Forall2_concat_l_ex_iff; intros; repeat esplit; assumption.
Qed.
