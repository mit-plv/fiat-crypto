Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Arithmetic.Saturated.Wrappers.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple Crypto.Util.LetIn.
Local Notation "A ^ n" := (tuple A n) : type_scope.

(* Canonicalize bignums by fully reducing them modulo p.
   This works on unsaturated digits, but uses saturated add/subtract
   loops.*)
Section Freeze.
    Context (weight : nat->Z)
            {weight_0 : weight 0%nat = 1}
            {weight_nonzero : forall i, weight i <> 0}
            {weight_positive : forall i, weight i > 0}
            {weight_multiples : forall i, weight (S i) mod weight i = 0}
            {weight_divides : forall i : nat, weight (S i) / weight i > 0}
    .


  (*
    The input to [freeze] should be less than 2*m (this can probably
    be accomplished by a single carry_reduce step, for most moduli).

    [freeze] has the following steps:
    (1) subtract modulus in a carrying loop (in our framework, this
    consists of two steps; [Columns.unbalanced_sub_cps] combines the
    input p and the modulus m such that the ith limb in the output is
    the list [p[i];-m[i]]. We can then call [Columns.compact].)
    (2) look at the final carry, which should be either 0 or -1. If
    it's -1, then we add the modulus back in. Otherwise we add 0 for
    constant-timeness.
    (3) discard the carry after this last addition; it should be 1 if
    the carry in step 3 was -1, so they cancel out.
   *)
  Definition freeze_cps {n} mask (m:Z^n) (p:Z^n) {T} (f : Z^n->T) :=
    Columns.unbalanced_sub_cps (n3:=n) weight p m
      (fun carry_p => Columns.conditional_add_cps (n3:=n) weight mask (fst carry_p) (snd carry_p) m
      (fun carry_r => f (snd carry_r)))
  .

  Definition freeze {n} mask m p :=
    @freeze_cps n mask m p _ id.
  Lemma freeze_id {n} mask m p T f:
    @freeze_cps n mask m p T f = f (freeze mask m p).
  Proof.
    cbv [freeze_cps freeze]; repeat progress autounfold;
      autorewrite with uncps push_id; reflexivity.
  Qed.
  Hint Opaque freeze : uncps.
  Hint Rewrite @freeze_id : uncps.

  Lemma freezeZ m s c y y0 z z0 c0 a :
    m = s - c ->
    0 < c < s ->
    s <> 0 ->
    0 <= y < 2*m ->
    y0 = y - m ->
    z = y0 mod s ->
    c0 = y0 / s ->
    z0 = z + (if (dec (c0 = 0)) then 0 else m) ->
    a = z0 mod s ->
    a mod m = y0 mod m.
  Proof.
    clear. intros. subst. break_match.
    { rewrite Z.add_0_r, Z.mod_mod by omega.
      assert (-(s-c) <= y - (s-c) < s-c) by omega.
      match goal with H : s <> 0 |- _ =>
                      rewrite (proj2 (Z.mod_small_iff _ s H))
                              by (apply Z.div_small_iff; assumption)
      end.
      reflexivity. }
    { rewrite <-Z.add_mod_l, Z.sub_mod_full.
      rewrite Z.mod_same, Z.sub_0_r, Z.mod_mod by omega.
      rewrite Z.mod_small with (b := s)
      by (pose proof (Z.div_small (y - (s-c)) s); omega).
      f_equal. ring. }
  Qed.

  Lemma eval_freeze {n} c mask m p
        (n_nonzero:n<>0%nat)
        (Hc : 0 < B.Associational.eval c < weight n)
        (Hmask : Tuple.map (Z.land mask) m = m)
        modulus (Hm : B.Positional.eval weight m = Z.pos modulus)
        (Hp : 0 <= B.Positional.eval weight p < 2*(Z.pos modulus))
        (Hsc : Z.pos modulus = weight n - B.Associational.eval c)
    :
      mod_eq modulus
             (B.Positional.eval weight (@freeze n mask m p))
             (B.Positional.eval weight p).
  Proof.
    cbv [freeze_cps freeze].
    repeat progress autounfold.
    pose proof Z.add_get_carry_full_mod.
    pose proof Z.add_get_carry_full_div.
    pose proof div_correct. pose proof modulo_correct.
    autorewrite with uncps push_id push_basesystem_eval.

    pose proof (weight_nonzero n).

    remember (B.Positional.eval weight p) as y.
    remember (y + -B.Positional.eval weight m) as y0.
    rewrite Hm in *.

    transitivity y0; cbv [mod_eq].
    { eapply (freezeZ (Z.pos modulus) (weight n) (B.Associational.eval c) y y0);
        try assumption; reflexivity. }
    { subst y0.
      assert (Z.pos modulus <> 0) by auto using Z.positive_is_nonzero, Zgt_pos_0.
      rewrite Z.add_mod by assumption.
      rewrite Z.mod_opp_l_z by auto using Z.mod_same.
      rewrite Z.add_0_r, Z.mod_mod by assumption.
      reflexivity. }
  Qed.
End Freeze.