(*** Compute the modular inverse of a ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.Nat2Z.
Require Import Crypto.Util.ZUtil.Z2Nat.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Wf1.
Local Open Scope Z_scope.

Module Z.
  (** Quoting https://stackoverflow.com/a/9758173:
<<
def egcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)

def modinv(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    else:
        return x % m
>> *)
  (** We run on fuel, because the well-foundedness lemmas for [Z] are
    opaque, so we can't use them to compute. *)
  Fixpoint egcd (fuel : nat) (a b : Z) : option (Z * Z * Z)
    := match fuel with
       | O => None
       | S fuel'
         => if a <? 0
            then None
            else if a =? 0
                 then Some (b, 0, 1)
                 else
                   match @egcd fuel' (b mod a) a with
                   | Some (g, y, x) => Some (g, x - (b / a) * y, y)
                   | None => None
                   end
       end.
  Definition egcd_by_wf_step (a : Z) (egcd : forall y : Z, 0 <= y < a -> Z -> option (Z * Z * Z)) (b : Z) : option (Z * Z * Z)
    := (if (0 <? a) as b return ((0 <? a) = b -> _)
        then fun pf
             => match @egcd (b mod a) (Z.mod_pos_bound _ _ (proj1 (Z.ltb_lt _ _) ltac:(eassumption))) a with
                | Some (g, y, x) => Some (g, x - (b / a) * y, y)
                | None => None
                end
        else fun _
             => if a =? 0
                then Some (b, 0, 1)
                else None) eq_refl.
  Definition egcd_by_wf (wf : well_founded (fun x y => 0 <= x < y)) (a b : Z) : option (Z * Z * Z)
    := Fix wf (fun _ => Z -> option (Z * Z * Z)) egcd_by_wf_step a b.
  Definition modinv_of_egcd (egcd : Z -> Z -> option (Z * Z * Z)) (a m : Z) : option Z
    := if a <? 0
       then match egcd (-a) m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some ((-x) mod m)
            | None => None
            end
       else match egcd a m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some (x mod m)
            | None => None
            end.
  Definition modinv_fueled (fuel : nat) (a m : Z) : option Z
    := modinv_of_egcd (egcd fuel) a m.
  Definition modinv_by_wf (wf : well_founded (fun x y => 0 <= x < y)) (a m : Z) : option Z
    := modinv_of_egcd (egcd_by_wf wf) a m.
  Definition modinv_by_wf_fuel (fuel : nat) (a m : Z) : option Z
    := modinv_by_wf (Acc_intro_generator fuel (Z.lt_wf 0)) a m.
  (** We way over-estimate the fuel by taking [max a m].  We can assume
    that [Z.to_nat (Z.log2_up (max a m))] is fast, because we already
    have a ~unary representation of [Z.log2_up a] and [Z.log2_up m].  It is
    empirically the case that pulling successors off [2^k] is fast, so
    we can use that for fuel. *)
  Definition modinv' (a m : Z) : option Z
    := modinv_fueled (S (2^Z.to_nat (Z.log2_up (Z.max (Z.abs a) m)))) a m.
  (** For the actual version, which we want to perform well under
      [cbv], we will simply add the log2 representations of [a] and
      [m].  We expect to pull at least about 1 bit off the top each
      round of the gcd calculation. *)
  Definition modinv_opt (a m : Z) : option Z
    := modinv_by_wf (Acc_intro_generator (S (S (Z.to_nat (Z.log2_up (Z.abs a) + Z.log2_up (Z.abs m))))) (Z.lt_wf 0)) a m.
  Definition modinv (a m : Z) : Z
    := Option.value (modinv_opt a m) 0.

  Lemma egcd_by_wf_step_ext x f g (Hext : forall (y : Z) (p : 0 <= y < x) (a : Z), f y p a = g y p a)
    : forall a, egcd_by_wf_step x f a = egcd_by_wf_step x g a.
  Proof.
    cbv [egcd_by_wf_step].
    repeat first [ progress intros
                 | progress subst
                 | reflexivity
                 | progress Z.ltb_to_lt
                 | progress inversion_option
                 | progress inversion_prod
                 | break_innermost_match_step
                 | exfalso; lia
                 | match goal with
                   | [ H1 : ?x = ?y :> bool, H2 : ?x = ?y :> bool |- _ ]
                     => assert (H1 = H2) by (apply UIP_dec; decide equality); subst H2
                   | [ H : forall y p a, ?f y p a = ?g y p a, H1 : ?f _ _ _ = _, H2 : ?g _ _ _ = _ |- _ ]
                     => rewrite H in H1; rewrite H1 in H2; clear H1
                   | [ H : context[proj1 (Z.ltb_lt ?x ?y) ?v] |- _ ]
                     => generalize dependent (proj1 (Z.ltb_lt x y) v); clear v; intros
                   end ].
  Qed.

  Lemma egcd_by_wf_None : forall wf a b, egcd_by_wf wf a b = None -> a < 0.
  Proof.
    intros wf a b.
    cbv [egcd_by_wf].
    apply (@Fix1_rect _ _ _ wf _ egcd_by_wf_step); [ | now apply egcd_by_wf_step_ext ].
    generalize (Fix wf _ egcd_by_wf_step); cbv [egcd_by_wf_step]; intro egcd.
    repeat first [ progress intros
                 | progress break_innermost_match_hyps
                 | progress Z.ltb_to_lt
                 | assumption
                 | congruence
                 | lia
                 | match goal with
                   | [ H : forall y, _ -> forall a, egcd y a = _ -> y < 0, H' : egcd ?v1 ?v2 = _ |- _ ]
                     => specialize (fun pf => H v1 pf v2 H'); Z.div_mod_to_quot_rem; nia
                   end ].
  Qed.

  Lemma egcd_by_wf_bezout : forall wf a b g x y, egcd_by_wf wf a b = Some (g, x, y) -> Z.abs g = Z.gcd a b /\ (0 <= a -> 0 <= b -> 0 <= g) /\ x * a + y * b = g.
  Proof.
    intros wf a b.
    cbv [egcd_by_wf].
    apply (@Fix1_rect _ _ _ wf _ egcd_by_wf_step); [ | now apply egcd_by_wf_step_ext ].
    generalize (Fix wf _ egcd_by_wf_step); cbv [egcd_by_wf_step]; intro egcd.
    repeat first [ progress intros
                 | progress break_innermost_match_hyps
                 | progress Z.ltb_to_lt
                 | progress inversion_option
                 | progress inversion_prod
                 | progress destruct_head'_and
                 | progress subst
                 | progress rewrite ?Z.gcd_mod in * by lia
                 | rewrite Z.gcd_0_r
                 | rewrite Z.gcd_0_l
                 | apply Z.gcd_0_l
                 | lia
                 | match goal with
                   | [ H : forall y, _ -> forall a g x' y', egcd y a = _ -> _, H' : egcd ?v1 ?v2 = _ |- _ ]
                     => specialize (fun pf => H _ pf _ _ _ _ H'); try specialize (H ltac:(Z.div_mod_to_quot_rem; nia))
                   end
                 | Z.div_mod_to_quot_rem; nia
                 | apply conj ].
  Qed.

  Lemma egcd_bezout : forall fuel a b g x y, egcd fuel a b = Some (g, x, y) -> Z.abs g = Z.gcd a b /\ (0 <= a -> 0 <= b -> 0 <= g) /\ x * a + y * b = g.
  Proof.
    induction fuel as [|fuel IH]; cbn [egcd]; [ congruence | ].
    repeat first [ progress intros
                 | progress break_innermost_match_hyps
                 | progress Z.ltb_to_lt
                 | progress inversion_option
                 | progress inversion_prod
                 | progress destruct_head'_and
                 | progress subst
                 | progress rewrite ?Z.gcd_mod in * by lia
                 | apply Z.gcd_0_l
                 | lia
                 | match goal with
                   | [ H : forall _ _ _ _ _, egcd _ _ _ = _ -> _, H' : egcd _ _ _ = _ |- _ ]
                     => specialize (H _ _ _ _ _ H'); try specialize (H ltac:(Z.div_mod_to_quot_rem; nia))
                   end
                 | Z.div_mod_to_quot_rem; nia
                 | apply conj ].
  Qed.

  Lemma egcd_None : forall fuel a b, Z.egcd fuel a b = None -> (fuel <= (if b <? a then S else (fun x => x))%Z (Z.to_nat (Z.min a b)))%nat \/ a < 0 \/ b < 0.
  Proof.
    induction fuel as [|fuel IH]; cbn; [ intros; break_innermost_match; lia | ].
    intros; break_innermost_match_hyps; Z.ltb_to_lt; auto; try congruence.
    specialize (IH _ _ ltac:(eassumption)).
    destruct_head'_or; [ | solve [ auto | exfalso; Z.div_mod_to_quot_rem; nia ] .. ].
    destruct (Z_lt_dec b 0); auto; [].
    left.
    rewrite Z.min_l in * |- by (Z.div_mod_to_quot_rem; nia).
    break_innermost_match_hyps; break_innermost_match; Z.ltb_to_lt; rewrite ?Z.min_r, ?Z.min_l by lia;
      try (Z.div_mod_to_quot_rem; zify; rewrite ?Z2Nat.id in * by lia; lia); [].
    Z.rewrite_mod_small_in_all; lia.
  Qed.

  Lemma modinv_of_egcd_None egcd P a m
        (Hegcd_None : forall a b, egcd a b = None -> P a b \/ a < 0 \/ b < 0)
        (Hegcd_Some : forall a b g x y, egcd a b = Some (g, x, y) -> Z.abs g = Z.gcd a b /\ (0 <= a -> 0 <= b -> 0 <= g) /\ x * a + y * b = g)
    : modinv_of_egcd egcd a m = None -> P (Z.abs a) m \/ m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof.
    destruct (Z_lt_dec m 0); [ now auto | ].
    cbv [modinv_of_egcd]; break_innermost_match; rewrite ?Bool.negb_true_iff in *; Z.ltb_to_lt.
    all: lazymatch goal with
         | [ Hegcd_Some : forall a b g x y, ?egcd a b = Some _ -> _, Hedgc_None : forall a b, ?egcd a b = None -> _, H : ?egcd _ _ = _ |- _ ]
           => first [ apply Hegcd_Some in H | apply Hegcd_None in H ]; clear Hegcd_None Hegcd_Some
         end.
    all: repeat first [ progress intros
                      | progress Z.replace_all_neg_with_pos
                      | progress destruct_head'_and
                      | progress destruct_head'_or
                      | progress break_innermost_match_hyps
                      | progress Z.ltb_to_lt
                      | progress rewrite Z.abs_opp in *
                      | progress rewrite ?Z.abs_eq in * by nia
                      | progress subst
                      | progress specialize_by lia
                      | congruence
                      | solve [ auto ]
                      | exfalso; lia ].
  Qed.

  Lemma bezout_modinv a m x y
        (Hbezout : x * a + y * m = 1)
    : (a * x) mod m = 1 mod m.
  Proof.
    replace (a * x) with (1 - (y * m)) by lia.
    push_Zmod; autorewrite with zsimplify_fast; reflexivity.
  Qed.

  Lemma bezout_modinv_rev a m x
        (Hm : 0 < m)
        (H : (a * x) mod m = 1 mod m)
    : exists y, x * a + y * m = 1.
  Proof.
    exists ((1 - a * x) / m).
    assert ((1 - a * x) mod m = 0)
      by (revert H; push_Zmod; intro H; rewrite H; autorewrite with zsimplify_const; reflexivity).
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma modinv_of_egcd_Some egcd P a m
        (Hegcd_None : forall a b, egcd a b = None -> P a b \/ a < 0 \/ b < 0)
        (Hegcd_Some : forall a b g x y, egcd a b = Some (g, x, y) -> Z.abs g = Z.gcd a b /\ (0 <= a -> 0 <= b -> 0 <= g) /\ x * a + y * b = g)
        (Hm : 0 < m)
    : forall a', modinv_of_egcd egcd a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof.
    cbv [modinv_of_egcd]; break_innermost_match; rewrite ?Bool.negb_true_iff in *; Z.ltb_to_lt.
    all: lazymatch goal with
         | [ Hegcd_Some : forall a b g x y, ?egcd a b = Some _ -> _, Hedgc_None : forall a b, ?egcd a b = None -> _, H : ?egcd _ _ = _ |- _ ]
           => first [ apply Hegcd_Some in H | apply Hegcd_None in H ]; clear Hegcd_None Hegcd_Some
         end.
    all: repeat first [ progress intros
                      | progress Z.replace_all_neg_with_pos
                      | progress destruct_head'_and
                      | progress destruct_head'_or
                      | progress break_innermost_match_hyps
                      | progress rewrite ?Bool.negb_true_iff in *
                      | progress rewrite ?Bool.negb_false_iff in *
                      | progress Z.ltb_to_lt
                      | progress rewrite Z.abs_opp in *
                      | progress rewrite ?Z.abs_eq in * by nia
                      | rewrite Z.mul_opp_r
                      | rewrite Z.opp_involutive
                      | progress subst
                      | progress specialize_by lia
                      | progress inversion_option
                      | congruence
                      | solve [ auto ]
                      | exfalso; lia
                      | apply conj
                      | Z.div_mod_to_quot_rem; nia
                      | progress (push_Zmod; pull_Zmod) ].
    all: generalize dependent (Z.gcd a m); intros; subst; erewrite bezout_modinv by eassumption; reflexivity.
  Qed.

  Lemma modinv_of_egcd_Some_rev egcd P a m
        (Hegcd_None : forall a b, egcd a b = None -> P a b \/ a < 0 \/ b < 0)
        (Hegcd_Some : forall a b g x y, egcd a b = Some (g, x, y) -> Z.abs g = Z.gcd a b /\ (0 <= a -> 0 <= b -> 0 <= g) /\ x * a + y * b = g)
        (Hm : 0 < m)
    : ~P (Z.abs a) m -> forall a', (a * a') mod m = 1 mod m -> modinv_of_egcd egcd a m <> None.
  Proof.
    intros nP a' Ha'.
    apply bezout_modinv_rev in Ha'; [ | assumption ]; destruct Ha' as [? Ha'].
    destruct (modinv_of_egcd egcd a m) eqn:H; [ eapply modinv_of_egcd_Some in H | eapply modinv_of_egcd_None in H ];
      try eassumption; [ try congruence | exfalso ].
    all: repeat first [ progress destruct_head'_and
                      | progress destruct_head'_or
                      | tauto
                      | lia
                      | rewrite <- ?Z.mul_assoc, ?(Z.mul_comm (Z.sgn _) (Z.abs _)), Z.abs_sgn
                      | match goal with
                        | [ H : Z.gcd (Z.abs ?a) ?b <> 1, H' : ?x * ?a + ?y * ?b = 1 |- False ]
                          => apply H, Z.bezout_1_gcd; clear H; exists (x * Z.sgn a), y; rewrite <- H'; clear
                        end ].
  Qed.

  Lemma modinv_fueled_None fuel a m
    : modinv_fueled fuel a m = None -> (fuel <= (if m <? Z.abs a then S else (fun x => x))%Z (Z.to_nat (Z.min (Z.abs a) m)))%nat \/ m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof. now apply (modinv_of_egcd_None (egcd fuel) _ a m (egcd_None fuel) (egcd_bezout fuel)). Qed.
  Lemma modinv_fueled_Some fuel a m
        (Hm : 0 < m)
    : forall a', modinv_fueled fuel a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof. now apply (modinv_of_egcd_Some (egcd fuel) _ a m (egcd_None fuel) (egcd_bezout fuel)). Qed.
  Lemma modinv_fueled_Some_rev fuel a m
        (Hm : 0 < m)
    : ~(fuel <= (if m <? Z.abs a then S else (fun x => x))%Z (Z.to_nat (Z.min (Z.abs a) m)))%nat -> forall a', (a * a') mod m = 1 mod m -> modinv_fueled fuel a m <> None.
  Proof. now apply (modinv_of_egcd_Some_rev (egcd fuel) _ a m (egcd_None fuel) (egcd_bezout fuel)). Qed.

  Lemma modinv_by_wf_None wf a m
    : modinv_by_wf wf a m = None -> m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof.
    intro.
    pose proof (egcd_by_wf_None wf).
    pose proof (egcd_by_wf_bezout wf).
    destruct (modinv_of_egcd_None (egcd_by_wf wf) (fun _ _ => False) a m).
    all: cbv beta in *.
    all: intuition eauto.
  Qed.
  Lemma modinv_by_wf_Some wf a m
        (Hm : 0 < m)
    : forall a', modinv_by_wf wf a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof.
    pose proof (egcd_by_wf_None wf).
    pose proof (egcd_by_wf_bezout wf).
    apply (modinv_of_egcd_Some (egcd_by_wf wf) (fun _ _ => False) a m).
    all: cbv beta in *.
    all: intuition eauto.
  Qed.
  Lemma modinv_by_wf_Some_rev wf a m
        (Hm : 0 < m)
    : forall a', (a * a') mod m = 1 mod m -> modinv_by_wf wf a m <> None.
  Proof.
    pose proof (egcd_by_wf_None wf).
    pose proof (egcd_by_wf_bezout wf).
    apply (modinv_of_egcd_Some_rev (egcd_by_wf wf) (fun _ _ => False) a m).
    all: cbv beta in *.
    all: intuition eauto.
  Qed.

  Lemma modinv_by_wf_fuel_None fuel a m
    : modinv_by_wf_fuel fuel a m = None -> m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof. now apply modinv_by_wf_None. Qed.
  Lemma modinv_by_wf_fuel_Some fuel a m (Hm : 0 < m)
    : forall a', modinv_by_wf_fuel fuel a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof. now apply modinv_by_wf_Some. Qed.
  Lemma modinv_by_wf_fuel_Some_rev fuel a m (Hm : 0 < m)
    : forall a', (a * a') mod m = 1 mod m -> modinv_by_wf_fuel fuel a m <> None.
  Proof. now apply modinv_by_wf_Some_rev. Qed.

  Lemma modinv'_fuel_good a m
    : ((if (m <? Z.abs a)%Z then S else fun x : nat => x) (Z.to_nat (Z.min (Z.abs a) m)) < S (2 ^ Z.to_nat (Z.log2_up (Z.max (Z.abs a) m))))%nat.
  Proof.
    assert (0 <= Z.log2_up (if Z_lt_dec a 0 then -a else a)) by auto with zarith.
    assert (0 <= Z.log2_up m) by auto with zarith.
    destruct (Z_lt_dec a 0), (Z_zerop a), (Z_lt_dec m 0); subst; Z.replace_all_neg_with_pos; rewrite ?Z.abs_opp, ?Z.abs_eq in * by lia.
    all: break_innermost_match; Z.ltb_to_lt.
    all: repeat first [ rewrite Z.min_l by lia
                      | rewrite Z.min_r by lia
                      | rewrite Z.max_l by lia
                      | rewrite Z.max_r by lia
                      | exfalso; lia
                      | lia
                      | progress change ((2^Z.to_nat (Z.log2_up 0))%nat) with 1%nat
                      | match goal with
                        | [ |- context[Z.to_nat ?x] ] => rewrite (Z2Nat.inj_nonpos x) by lia
                        end ].
    all: change 2%nat with (Z.to_nat 2).
    all: eapply Nat.lt_le_trans;
      [
      | apply le_n_S; zify; set_evars; autorewrite with push_Zof_nat; rewrite ?Z2Nat.id by lia; subst_evars;
        etransitivity; [ | apply Z.log2_log2_up_spec; change (2^Z.log2 1) with 1 in *; zify; rewrite ?Z2Nat.id by lia; lia ];
        rewrite Z2Nat.id; [ reflexivity | change (2^Z.log2 1) with 1 in *; zify; rewrite ?Z2Nat.id by lia; lia ] ].
    all: zify; rewrite ?Z2Nat.id by lia; lia.
  Qed.

  Lemma modinv'_None a m
    : modinv' a m = None -> m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof.
    intro H.
    pose proof (modinv'_fuel_good a m).
    pose proof (modinv_fueled_None _ a m H); destruct_head'_or; auto; try (exfalso; lia).
  Qed.
  Lemma modinv'_Some a m (Hm : 0 < m)
    : forall a', modinv' a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof. now apply modinv_fueled_Some. Qed.
  Lemma modinv'_Some_rev a m (Hm : 0 < m)
    : forall a', (a * a') mod m = 1 mod m -> modinv' a m <> None.
  Proof.
    pose proof (modinv'_fuel_good a m).
    apply modinv_fueled_Some_rev; try assumption; lia.
  Qed.

  Lemma modinv_opt_None a m
    : modinv_opt a m = None -> m < 0 \/ Z.gcd (Z.abs a) m <> 1.
  Proof. apply modinv_by_wf_None. Qed.
  Lemma modinv_opt_Some a m (Hm : 0 < m)
    : forall a', modinv_opt a m = Some a' -> (a * a') mod m = 1 mod m /\ 0 <= a' < m.
  Proof. now apply modinv_by_wf_Some. Qed.
  Lemma modinv_opt_Some_rev a m (Hm : 0 < m)
    : forall a', (a * a') mod m = 1 mod m -> modinv_opt a m <> None.
  Proof. now apply modinv_by_wf_Some_rev. Qed.

  Lemma modinv_correct a m
        (Hm : 0 < m)
        (Hgcd : Z.gcd (Z.abs a) m = 1)
    : (a * modinv a m) mod m = 1 mod m /\ 0 <= modinv a m < m.
  Proof.
    pose proof (modinv_opt_None a m) as H0.
    pose proof (modinv_opt_Some a m Hm) as H1.
    pose proof (modinv_opt_Some_rev a m Hm) as H2.
    cbv [modinv]; edestruct modinv_opt.
    { now apply H1. }
    { specialize (H0 eq_refl).
      exfalso; lia. }
  Qed.
End Z.
