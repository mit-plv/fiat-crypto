
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    EGroup.v

    Given an element a, create the group {e, a, a^2, ..., a^n}
 **********************************************************************)
Require Import ZArith.
Require Import Tactic.
Require Import List.
Require Import ZCAux.
Require Import ZArith Znumtheory.
Require Import Wf_nat.
Require Import UList.
Require Import FGroup.
Require Import Lagrange.

Open Scope Z_scope.

Section EGroup.

Variable A: Set.

Variable A_dec: forall a b: A, {a = b} + {~ a = b}.

Variable op: A -> A -> A.

Variable a: A.

Variable G: FGroup op.

Hypothesis a_in_G: In a G.(s).


(**************************************
  The power function for the group
 **************************************)

Set Implicit Arguments.
Definition gpow n := match n with  Zpos p => iter_pos _ (op a) G.(e) p | _ => G.(e) end.
Unset Implicit Arguments.

Theorem gpow_0: gpow 0 = G.(e).
simpl; sauto.
Qed.

Theorem gpow_1 : gpow 1 = a.
simpl; sauto.
Qed.

(**************************************
  Some properties of the power function
 **************************************)

Theorem gpow_in: forall n, In (gpow n) G.(s).
intros n; case n; simpl; auto.
intros p; apply iter_pos_invariant with (Inv := fun x => In x G.(s)); auto.
Qed.

Theorem gpow_op: forall b p, In b G.(s) -> iter_pos _ (op a) b p = op (iter_pos _ (op a) G.(e) p) b.
intros b p; generalize b; elim p; simpl; auto; clear  b p.
intros p Rec b Hb.
assert (H: In (gpow (Zpos p)) G.(s)).
apply gpow_in.
rewrite (Rec b); try rewrite (fun x y => Rec (op x y)); try rewrite (fun x y => Rec (iter_pos A x y p)); auto.
repeat rewrite G.(assoc); auto.
intros p Rec b Hb.
assert (H: In (gpow (Zpos p)) G.(s)).
apply gpow_in.
rewrite (Rec b); try rewrite (fun x y => Rec (op x y)); try rewrite (fun x y => Rec (iter_pos A x y p)); auto.
repeat rewrite G.(assoc); auto.
intros b H; rewrite e_is_zero_r; auto.
Qed.

Theorem gpow_add: forall n m, 0 <= n -> 0 <= m -> gpow (n + m) = op (gpow n) (gpow m).
intros n; case n.
intros m _ _; simpl; apply sym_equal; apply e_is_zero_l; apply gpow_in.
2: intros p m H; contradict H; auto with zarith.
intros p1 m; case m.
intros _ _; simpl; apply sym_equal; apply e_is_zero_r.
exact (gpow_in (Zpos p1)).
2: intros p2 _ H; contradict H; auto with zarith.
intros p2 _ _; simpl.
rewrite iter_pos_plus; rewrite (fun x y => gpow_op (iter_pos A x y p2)); auto.
exact (gpow_in (Zpos p2)).
Qed.

Theorem gpow_1_more:
  forall n, 0 < n -> gpow n = G.(e) -> forall m, 0 <= m -> exists p, 0 <= p < n /\ gpow m = gpow p.
intros n H1 H2 m Hm;  generalize Hm; pattern m; apply Z_lt_induction; auto with zarith; clear m Hm.
intros m Rec Hm.
case (Zle_or_lt n m); intros H3.
case (Rec (m - n)); auto with zarith.
intros p (H4,H5); exists p; split; auto.
replace m with (n + (m - n)); auto with zarith.
rewrite gpow_add; try rewrite H2; try rewrite H5; sauto; auto with zarith.
generalize gpow_in; sauto.
exists m; auto.
Qed.

Theorem gpow_i: forall n m, 0 <= n -> 0 <= m -> gpow n = gpow (n + m) -> gpow m = G.(e).
intros n m H1 H2 H3; generalize gpow_in; intro PI.
apply g_cancel_l with (g:= G) (a := gpow n); sauto.
rewrite <- gpow_add; try rewrite <- H3; sauto.
Qed.

(**************************************
  We build the support by iterating the power function
 **************************************)

Set Implicit Arguments.

Fixpoint support_aux (b: A) (n: nat) {struct n}: list A :=
b::let c := op a b in
    match n with
       O => nil |
      (S n1) =>if A_dec c G.(e) then nil else  support_aux c n1
    end.

Definition support := support_aux G.(e) (Zabs_nat (g_order G)).

Unset Implicit Arguments.

(**************************************
  Some properties of the support that helps to prove that we have a group
 **************************************)

Theorem support_aux_gpow:
  forall n m b, 0 <=  m -> In b (support_aux (gpow m) n) ->
        exists p, (0 <= p < length (support_aux (gpow m) n))%nat  /\ b = gpow (m + Z_of_nat p).
intros n; elim n; simpl.
intros n1 b Hm [H1 | H1]; exists 0%nat; simpl; rewrite Zplus_0_r; auto; case H1.
intros n1 Rec m b Hm [H1 | H1].
exists 0%nat; simpl; rewrite Zplus_0_r; auto; auto with arith.
generalize H1; case (A_dec (op a (gpow m)) G.(e)); clear H1; simpl; intros H1 H2.
case H2.
case (Rec (1 + m) b); auto with zarith.
rewrite gpow_add; auto with zarith.
rewrite gpow_1; auto.
intros p (Hp1, Hp2); exists (S p); split; auto with zarith.
rewrite <- gpow_1.
rewrite <- gpow_add; auto with zarith.
rewrite inj_S; rewrite Hp2; eq_tac; auto with zarith.
Qed.

Theorem gpow_support_aux_not_e:
  forall n m p, 0 <= m -> m < p < m + Z_of_nat (length (support_aux (gpow m) n)) -> gpow p <> G.(e).
intros n; elim n; simpl.
intros m p Hm (H1, H2); contradict H2; auto with zarith.
intros n1 Rec m p Hm; case (A_dec (op a (gpow m)) G.(e)); simpl.
intros _ (H1, H2); contradict H2; auto with zarith.
assert (tmp: forall p, Zpos (P_of_succ_nat p) = 1 + Z_of_nat p).
intros p1; apply trans_equal with (Z_of_nat (S p1)); auto; rewrite inj_S; auto with zarith.
rewrite tmp.
intros H1 (H2, H3); case (Zle_lt_or_eq (1 + m) p); auto with zarith; intros H4; subst.
apply (Rec (1 + m)); try split; auto with zarith.
rewrite gpow_add; auto with zarith.
rewrite gpow_1; auto with zarith.
rewrite gpow_add; try rewrite gpow_1; auto with zarith.
Qed.

Theorem support_aux_not_e: forall n m b, 0 <= m -> In b (tail (support_aux (gpow m) n)) -> ~ b = G.(e).
intros n; elim n; simpl.
intros m b Hm H; case H.
intros n1 Rec m b Hm; case (A_dec (op a (gpow m)) G.(e)); intros H1 H2; simpl; auto.
assert (Hm1: 0 <= 1 + m); auto with zarith.
generalize( Rec (1 + m) b Hm1) H2; case n1; auto; clear Hm1.
intros _ [H3 | H3]; auto.
contradict H1; subst; auto.
rewrite gpow_add; simpl; try rewrite e_is_zero_r; auto with zarith.
intros n2; case (A_dec (op a (op a (gpow m))) G.(e)); intros H3.
intros _ [H4 | H4].
contradict H1; subst; auto.
case H4.
intros H4 [H5 | H5]; subst; auto.
Qed.

Theorem support_aux_length_le: forall n a, (length (support_aux a n) <= n + 1)%nat.
intros n; elim n; simpl; auto.
intros n1 Rec a1; case (A_dec (op a a1) G.(e)); simpl; auto with arith.
Qed.

Theorem support_aux_length_le_is_e:
   forall n m, 0 <= m ->  (length (support_aux (gpow m) n) <= n)%nat ->
      gpow (m + Z_of_nat (length (support_aux (gpow m) n))) = G.(e) .
intros n; elim n; simpl; auto.
intros m _ H1; contradict H1; auto with arith.
intros n1 Rec m Hm; case (A_dec (op a (gpow m)) G.(e)); simpl;  intros H1.
intros H2; rewrite Zplus_comm; rewrite gpow_add; simpl; try rewrite e_is_zero_r; auto with zarith.
assert (tmp: forall p, Zpos (P_of_succ_nat p) = 1 + Z_of_nat p).
intros p1; apply trans_equal with (Z_of_nat (S p1)); auto; rewrite inj_S; auto with zarith.
rewrite tmp; clear tmp.
rewrite <- gpow_1.
rewrite <- gpow_add; auto with zarith.
rewrite  Zplus_assoc; rewrite (Zplus_comm 1); intros H2; apply Rec; auto with zarith.
Qed.

Theorem support_aux_in:
  forall n m p, 0 <= m ->  (p < length (support_aux (gpow m) n))% nat ->
            (In (gpow (m + Z_of_nat p)) (support_aux (gpow m) n)).
intros n; elim n; simpl; auto; clear n.
intros m p Hm H1; replace p with 0%nat.
left; eq_tac; auto with zarith.
generalize H1; case p; simpl; auto with arith.
intros n H2; contradict H2; apply le_not_lt; auto with arith.
intros n1 Rec m p Hm; case (A_dec (op a (gpow m)) G.(e)); simpl; intros H1 H2; auto.
replace p with 0%nat.
left; eq_tac; auto with zarith.
generalize H2; case p; simpl; auto with arith.
intros n H3; contradict H3; apply le_not_lt; auto with arith.
generalize H2; case p; simpl; clear H2.
rewrite Zplus_0_r; auto.
intros n.
assert (tmp: forall p, Zpos (P_of_succ_nat p) = 1 + Z_of_nat p).
intros p1; apply trans_equal with (Z_of_nat (S p1)); auto; rewrite inj_S; auto with zarith.
rewrite tmp; clear tmp.
rewrite <- gpow_1; rewrite <- gpow_add; auto with zarith.
rewrite  Zplus_assoc; rewrite (Zplus_comm 1); intros H2; right; apply Rec; auto with zarith.
Qed.

Theorem support_aux_ulist:
  forall n m, 0 <= m -> (forall p, 0 <= p < m -> gpow (1 + p) <> G.(e)) -> ulist (support_aux (gpow m) n).
intros n; elim n; auto; clear n.
intros m _ _; auto.
simpl; apply ulist_cons; auto.
intros n1 Rec m Hm H.
simpl; case (A_dec (op a (gpow m)) G.(e)); auto.
intros He; apply ulist_cons; auto.
intros H1; case  (support_aux_gpow n1 (1 + m) (gpow m)); auto with zarith.
rewrite gpow_add; try rewrite gpow_1; auto with zarith.
intros p (Hp1, Hp2).
assert (H2: gpow (1 + Z_of_nat p) = G.(e)).
apply gpow_i with m; auto with zarith.
rewrite Hp2; eq_tac; auto with zarith.
case (Zle_or_lt m  (Z_of_nat p)); intros H3; auto.
2: case (H (Z_of_nat p)); auto with zarith.
case (support_aux_not_e (S n1) m (gpow (1 + Z_of_nat p))); auto.
rewrite gpow_add; auto with zarith; simpl; rewrite e_is_zero_r; auto.
case (A_dec (op a (gpow m)) G.(e)); auto.
intros _; rewrite <- gpow_1; repeat rewrite <- gpow_add; auto with zarith.
replace (1 + Z_of_nat p) with ((1 + m) + (Z_of_nat (p - Zabs_nat m))); auto with zarith.
apply support_aux_in; auto with zarith.
rewrite inj_minus1; auto with zarith.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply inj_le_rev.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite <- gpow_1; repeat rewrite <- gpow_add; auto with zarith.
apply (Rec (1 + m)); auto with zarith.
intros p H1; case (Zle_lt_or_eq p m); intros; subst; auto with zarith.
rewrite  gpow_add; auto with zarith.
rewrite gpow_1; auto.
Qed.

Theorem support_gpow: forall b, (In b support) -> exists p, 0 <= p < Z_of_nat (length support) /\ b = gpow p.
intros b H; case (support_aux_gpow  (Zabs_nat (g_order G)) 0 b); auto with zarith.
intros p ((H1, H2), H3); exists (Z_of_nat p); repeat split; auto with zarith.
apply inj_lt; auto.
Qed.

Theorem support_incl_G: incl support G.(s).
intros a1 H; case (support_gpow a1); auto; intros p (H1, H2); subst; apply gpow_in.
Qed.

Theorem gpow_support_not_e: forall p, 0 < p < Z_of_nat (length support) -> gpow p <> G.(e).
intros p (H1, H2); apply gpow_support_aux_not_e with (m := 0) (n := length G.(s)); simpl;
  try split; auto with zarith.
rewrite  <- (Zabs_nat_Z_of_nat (length G.(s))); auto.
Qed.

Theorem support_not_e: forall b, In b (tail support) -> ~ b = G.(e).
intros b H; apply (support_aux_not_e (Zabs_nat (g_order G)) 0); auto with zarith.
Qed.

Theorem support_ulist:  ulist support.
apply (support_aux_ulist (Zabs_nat (g_order G)) 0); auto with zarith.
Qed.

Theorem support_in_e:  In G.(e) support.
unfold support; case (Zabs_nat (g_order G)); simpl; auto with zarith.
Qed.

Theorem gpow_length_support_is_e: gpow (Z_of_nat (length support)) = G.(e).
apply (support_aux_length_le_is_e (Zabs_nat (g_order G)) 0); simpl; auto with zarith.
unfold g_order; rewrite Zabs_nat_Z_of_nat; apply ulist_incl_length.
rewrite  <- (Zabs_nat_Z_of_nat (length G.(s))); auto.
exact support_ulist.
rewrite  <- (Zabs_nat_Z_of_nat (length G.(s))); auto.
exact support_incl_G.
Qed.

Theorem support_in:  forall p, 0 <= p < Z_of_nat (length support) ->  In (gpow p) support.
intros p (H, H1); unfold support.
rewrite <-  (Zabs_eq p); auto with zarith.
rewrite <-  (inj_Zabs_nat p); auto.
generalize (support_aux_in (Zabs_nat (g_order G)) 0); simpl; intros H2; apply H2; auto with zarith.
rewrite <-  (fun x => Zabs_nat_Z_of_nat (@length A x)); auto.
apply Zabs_nat_lt; split; auto.
Qed.

Theorem support_internal: forall a b, In a support -> In b support -> In (op a b) support.
intros a1 b1 H1 H2.
case support_gpow with (1 := H1); auto; intros p1 ((H3, H4), H5); subst.
case support_gpow with (1 := H2); auto; intros p2 ((H5, H6), H7); subst.
rewrite <- gpow_add; auto with zarith.
case gpow_1_more with (m:= p1 + p2)   (2 := gpow_length_support_is_e); auto with zarith.
intros p3 ((H8, H9), H10); rewrite H10; apply support_in; auto with zarith.
Qed.

Theorem support_i_internal: forall a, In a support -> In (G.(i) a) support.
generalize gpow_in; intros Hp.
intros a1 H1.
case support_gpow with (1 := H1); auto.
intros p1 ((H2, H3), H4); case Zle_lt_or_eq with (1 := H2); clear H2; intros H2; subst.
2: rewrite gpow_0; rewrite i_e; apply support_in_e.
replace (G.(i) (gpow p1)) with (gpow (Z_of_nat (length support - Zabs_nat p1))).
apply support_in; auto with zarith.
rewrite inj_minus1.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply inj_le_rev; rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply g_cancel_l with (g:= G) (a := gpow p1); sauto.
rewrite <- gpow_add; auto with zarith.
replace (p1 + Z_of_nat (length support - Zabs_nat p1)) with (Z_of_nat (length support)).
rewrite gpow_length_support_is_e; sauto.
rewrite inj_minus1; auto with zarith.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply inj_le_rev; rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
Qed.

(**************************************
  We are now ready to build the group
 **************************************)

Definition Gsupport: (FGroup op).
generalize support_incl_G; unfold incl; intros Ho.
apply mkGroup with support G.(e) G.(i); sauto.
apply support_ulist.
apply support_internal.
intros a1 b1 c1 H1 H2 H3; apply G.(assoc); sauto.
apply support_in_e.
apply support_i_internal.
Defined.

(**************************************
  Definition of the order of an element
 **************************************)
Set Implicit Arguments.

Definition e_order := Z_of_nat (length support).

Unset Implicit Arguments.

(**************************************
 Some properties of the order of an element
 **************************************)

Theorem gpow_e_order_is_e: gpow e_order = G.(e).
apply (support_aux_length_le_is_e (Zabs_nat (g_order G)) 0); simpl; auto with zarith.
unfold g_order; rewrite Zabs_nat_Z_of_nat; apply ulist_incl_length.
rewrite  <- (Zabs_nat_Z_of_nat (length G.(s))); auto.
exact support_ulist.
rewrite  <- (Zabs_nat_Z_of_nat (length G.(s))); auto.
exact support_incl_G.
Qed.

Theorem gpow_e_order_lt_is_not_e: forall n, 1 <= n < e_order -> gpow n <> G.(e).
intros n (H1, H2); apply gpow_support_not_e; auto with zarith.
Qed.

Theorem e_order_divide_g_order:  (e_order | g_order G).
change ((g_order Gsupport) | g_order G).
apply lagrange; auto.
exact support_incl_G.
Qed.

Theorem e_order_pos: 0 < e_order.
unfold e_order, support; case (Zabs_nat (g_order G)); simpl; auto with zarith.
Qed.

Theorem e_order_divide_gpow: forall n, 0 <= n -> gpow n = G.(e) -> (e_order | n).
generalize gpow_in; intros Hp.
generalize e_order_pos; intros Hp1.
intros n Hn; generalize Hn; pattern n; apply Z_lt_induction; auto; clear n Hn.
intros n Rec Hn H.
case (Zle_or_lt  e_order n); intros H1.
case (Rec (n - e_order)); auto with zarith.
apply g_cancel_l with (g:= G) (a := gpow e_order); sauto.
rewrite G.(e_is_zero_r); auto with zarith.
rewrite <- gpow_add; try (rewrite gpow_e_order_is_e; rewrite <- H; eq_tac); auto with zarith.
intros k Hk; exists (1 + k).
rewrite Zmult_plus_distr_l; rewrite <- Hk; auto with zarith.
case (Zle_lt_or_eq 0 n); auto with arith; intros H2; subst.
contradict H; apply support_not_e.
generalize H1; unfold e_order, support.
case (Zabs_nat (g_order G)); simpl; auto.
intros H3; contradict H3; auto with zarith.
intros n1; case (A_dec (op a G.(e)) G.(e)); simpl; intros _ H3.
contradict H3; auto with zarith.
generalize H3; clear H3.
assert (tmp: forall p, Zpos (P_of_succ_nat p) = 1 + Z_of_nat p).
intros p1; apply trans_equal with (Z_of_nat (S p1)); auto; rewrite inj_S; auto with zarith.
rewrite tmp; clear tmp; intros H3.
change (In (gpow n) (support_aux (gpow 1) n1)).
replace n with (1 + Z_of_nat (Zabs_nat n - 1)).
apply support_aux_in; auto with zarith.
rewrite <- (fun x => Zabs_nat_Z_of_nat (@length A x)).
replace (Zabs_nat n - 1)%nat  with (Zabs_nat (n - 1)).
apply Zabs_nat_lt; split; auto with zarith.
rewrite G.(e_is_zero_r) in H3; try rewrite gpow_1; auto with zarith.
apply inj_eq_rev; rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite inj_minus1; auto with zarith.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply inj_le_rev; rewrite inj_Zabs_nat; simpl; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite inj_minus1; auto with zarith.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite Zplus_comm; simpl; auto with zarith.
apply inj_le_rev; rewrite inj_Zabs_nat; simpl; auto with zarith.
rewrite Zabs_eq; auto with zarith.
exists 0; auto with arith.
Qed.

End EGroup.

Theorem gpow_gpow: forall (A : Set) (op : A -> A -> A) (a : A) (G : FGroup op),
       In a (s G) -> forall n m, 0 <= n -> 0 <= m -> gpow a G (n * m ) = gpow (gpow a G n) G m.
intros A op a G H n m; case n.
simpl; intros _ H1; generalize H1.
pattern m; apply natlike_ind; simpl; auto.
intros x H2 Rec _; unfold Zsucc; rewrite gpow_add; simpl; auto with zarith.
repeat rewrite G.(e_is_zero_r); auto with zarith.
apply gpow_in; sauto.
intros p1 _; case m; simpl; auto.
assert(H1: In (iter_pos A (op a) (e G) p1) (s G)).
refine (gpow_in _ _ _ _ _ (Zpos p1)); auto.
intros p2 _;  pattern p2; apply Pind; simpl; auto.
rewrite Pmult_1_r; rewrite G.(e_is_zero_r); try rewrite G.(e_is_zero_r); auto.
intros p3 Rec; rewrite Pplus_one_succ_r; rewrite Pmult_plus_distr_l.
rewrite Pmult_1_r.
simpl; repeat rewrite iter_pos_plus; simpl.
rewrite G.(e_is_zero_r); auto.
rewrite gpow_op with (G:= G); try rewrite Rec; auto.
apply sym_equal; apply gpow_op; auto.
intros p Hp; contradict Hp; auto with zarith.
Qed.

Theorem gpow_e: forall (A : Set) (op : A -> A -> A) (G : FGroup op) n, 0 <= n -> gpow G.(e) G n = G.(e).
intros A op G n; case n; simpl; auto with zarith.
intros p _; elim p; simpl; auto; intros p1 Rec; repeat rewrite Rec; auto.
Qed.

Theorem gpow_pow: forall (A : Set) (op : A -> A -> A) (a : A) (G : FGroup op),
       In a (s G) -> forall n, 0 <= n -> gpow a G (2 ^ n) = G.(e) -> forall m, n <= m -> gpow a G (2 ^ m) = G.(e).
intros A op a G H n H1 H2 m Hm.
replace m with (n + (m - n)); auto with zarith.
rewrite Zpower_exp; auto with zarith.
rewrite gpow_gpow; auto with zarith.
rewrite H2; apply gpow_e.
apply Zpower_ge_0; auto with zarith.
Qed.

Theorem gpow_mult: forall (A : Set) (op : A -> A -> A) (a b: A) (G : FGroup op)
       (comm: forall a b,  In a (s G) -> In b (s G) -> op a b = op b a),
       In a (s G) -> In b (s G) -> forall n, 0 <= n -> gpow (op a b) G n = op (gpow a G n) (gpow b G n).
intros A op a  b G comm Ha Hb n; case n; simpl; auto.
intros _; rewrite G.(e_is_zero_r); auto.
2: intros p Hp; contradict Hp; auto with zarith.
intros p _; pattern p; apply Pind; simpl; auto.
repeat rewrite G.(e_is_zero_r); auto.
intros p3 Rec; rewrite Pplus_one_succ_r.
repeat rewrite iter_pos_plus; simpl.
repeat rewrite (fun x y H z => gpow_op A  op x G H (op y z)) ; auto.
rewrite Rec.
repeat rewrite G.(e_is_zero_r); auto.
assert(H1: In (iter_pos A (op a) (e G) p3) (s G)).
refine (gpow_in _ _ _ _ _ (Zpos p3)); auto.
assert(H2: In (iter_pos A (op b) (e G) p3) (s G)).
refine (gpow_in _ _ _ _ _ (Zpos p3)); auto.
repeat rewrite <- G.(assoc); try eq_tac; auto.
rewrite (fun x y => comm (iter_pos A x y p3) b); auto.
rewrite (G.(assoc) a); try apply comm; auto.
Qed.

Theorem Zdivide_mult_rel_prime:  forall a b c : Z, (a | c) -> (b | c) -> rel_prime a b -> (a * b | c).
intros a b c (q1, H1) (q2, H2) H3.
assert (H4: (a | q2)).
apply Gauss with (2 := H3).
exists q1; rewrite <- H1; rewrite H2; auto with zarith.
case H4; intros q3 H5; exists q3; rewrite H2; rewrite H5; auto with zarith.
Qed.

Theorem order_mult: forall (A : Set) (op : A -> A -> A) (A_dec: forall a b: A, {a = b} + {~ a = b}) (G : FGroup op)
       (comm: forall a b,  In a (s G) -> In b (s G) -> op a b = op b a) (a b: A),
       In a (s G) -> In b (s G) -> rel_prime (e_order A_dec a G) (e_order A_dec b G) ->
        e_order A_dec (op a b) G = e_order A_dec a G * e_order A_dec b G.
intros A op A_dec G comm a b Ha Hb Hab.
assert (Hoat: 0 < e_order A_dec a G); try apply e_order_pos.
assert (Hobt: 0 < e_order A_dec b G); try apply e_order_pos.
assert (Hoabt: 0 < e_order A_dec (op a b) G); try apply e_order_pos.
assert (Hoa: 0 <= e_order A_dec a G); auto with zarith.
assert (Hob: 0 <= e_order A_dec b G); auto with zarith.
apply Zle_antisym; apply Zdivide_le; auto with zarith.
apply Zmult_lt_O_compat; auto.
apply e_order_divide_gpow; sauto; auto with zarith.
rewrite gpow_mult; auto with zarith.
rewrite gpow_gpow; auto with zarith.
rewrite gpow_e_order_is_e; auto with zarith.
rewrite gpow_e; auto.
rewrite Zmult_comm.
rewrite gpow_gpow; auto with zarith.
rewrite gpow_e_order_is_e; auto with zarith.
rewrite gpow_e; auto.
apply Zdivide_mult_rel_prime; auto.
apply Gauss with (2 := Hab).
apply e_order_divide_gpow; auto with zarith.
rewrite <- (gpow_e _ _ G (e_order A_dec b G)); auto.
rewrite <- (gpow_e_order_is_e _ A_dec  _ (op a b) G); auto with zarith.
rewrite <- gpow_gpow; auto with zarith.
rewrite (Zmult_comm (e_order A_dec (op a b) G)).
rewrite gpow_mult; auto with zarith.
rewrite gpow_gpow with (a := b); auto with zarith.
rewrite gpow_e_order_is_e; auto with zarith.
rewrite gpow_e; auto with zarith.
rewrite G.(e_is_zero_r); auto with zarith.
apply gpow_in; auto.
apply Gauss with (2 := rel_prime_sym _ _ Hab).
apply e_order_divide_gpow; auto with zarith.
rewrite <- (gpow_e _ _ G (e_order A_dec a G)); auto.
rewrite <- (gpow_e_order_is_e _ A_dec  _ (op a b) G); auto with zarith.
rewrite <- gpow_gpow; auto with zarith.
rewrite (Zmult_comm (e_order A_dec (op a b) G)).
rewrite gpow_mult; auto with zarith.
rewrite gpow_gpow with (a := a); auto with zarith.
rewrite gpow_e_order_is_e; auto with zarith.
rewrite gpow_e; auto with zarith.
rewrite G.(e_is_zero_l); auto with zarith.
apply gpow_in; auto.
Qed.

Theorem fermat_gen: forall (A : Set) (A_dec: forall (a b: A), {a = b} + {a <>b}) (op : A -> A -> A) (a: A) (G : FGroup op),
       In a G.(s) ->  gpow a G (g_order G) = G.(e).
intros A A_dec op a G H.
assert (H1: (e_order A_dec a G | g_order G)).
apply e_order_divide_g_order; auto.
case H1; intros q; intros Hq; rewrite Hq.
assert (Hq1: 0 <= q).
apply Zmult_le_reg_r with (e_order A_dec a G); auto with zarith.
apply Zlt_gt; apply e_order_pos.
rewrite Zmult_0_l; rewrite <- Hq; apply Zlt_le_weak; apply g_order_pos.
rewrite Zmult_comm; rewrite gpow_gpow; auto with zarith.
rewrite gpow_e_order_is_e; auto with zarith.
apply gpow_e; auto.
apply Zlt_le_weak; apply e_order_pos.
Qed.

Theorem order_div: forall (A : Set) (A_dec: forall (a b: A), {a = b} + {a <>b}) (op : A -> A -> A) (a: A) (G : FGroup op) m,
 0 < m -> (forall p, prime p -> (p | m) -> gpow a G (m / p) <> G.(e)) ->
 In a G.(s) -> gpow a G m = G.(e) -> e_order A_dec a G = m.
intros A Adec op a G m Hm H H1 H2.
assert (F1: 0 <= m); auto with zarith.
case (e_order_divide_gpow A Adec op a G H1 m F1 H2); intros q Hq.
assert (F2: 1 <= q).
  case (Zle_or_lt 0 q); intros HH.
    case (Zle_lt_or_eq _ _ HH); auto with zarith.
    intros HH1; generalize Hm; rewrite Hq; rewrite <- HH1;
      auto with zarith.
  assert (F2: 0 <= (- q) * e_order Adec a G); auto with zarith.
    apply Zmult_le_0_compat; auto with zarith.
    apply Zlt_le_weak; apply e_order_pos.
  generalize F2; rewrite Zopp_mult_distr_l_reverse;
      rewrite <- Hq; auto with zarith.
case (Zle_lt_or_eq _ _ F2); intros H3; subst; auto with zarith.
case (prime_dec q); intros Hq.
  case (H q); auto with zarith.
    rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.
  apply gpow_e_order_is_e; auto.
case (Zdivide_div_prime_le_square _ H3 Hq); intros r (Hr1, (Hr2, Hr3)).
case (H _ Hr1); auto.
  apply Zdivide_trans with (1 := Hr2).
  apply Zdivide_factor_r.
case Hr2; intros q1 Hq1; subst.
assert (F3: 0 < r).
  generalize (prime_ge_2 _ Hr1); auto with zarith.
rewrite <- Zmult_assoc; rewrite Zmult_comm; rewrite <- Zmult_assoc;
  rewrite Zmult_comm; rewrite Z_div_mult; auto with zarith.
rewrite gpow_gpow; auto with zarith.
  rewrite gpow_e_order_is_e; try rewrite gpow_e; auto.
  apply Zmult_le_reg_r with r; auto with zarith.
  apply Zlt_le_weak; apply e_order_pos.
apply Zmult_le_reg_r with r; auto with zarith.
Qed.
