(** * Alternate forms for Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.LegacyArithmetic.Interface.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.AutoRewrite.
Require Import Crypto.Util.Notations.

Local Open Scope type_scope.
Local Open Scope Z_scope.

Import BoundedRewriteNotations.
Local Notation bit b := (if b then 1 else 0).

Lemma decoder_eta {n W} (decode : decoder n W) : decode = {| Interface.decode := decode |}.
Proof. destruct decode; reflexivity. Defined.

Section InstructionGallery.
  Context (n : Z) (* bit-width of width of [W] *)
          {W : Type} (* bounded type, [W] for word *)
          (Wdecoder : decoder n W).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Definition Build_is_spread_left_immediate' (sprl : spread_left_immediate W)
             (pf : forall r count, 0 <= count < n
                                   -> _ /\ _)
    := {| decode_fst_spread_left_immediate r count H := proj1 (pf r count H);
          decode_snd_spread_left_immediate r count H := proj2 (pf r count H) |}.

  Definition Build_is_add_with_carry' (adc : add_with_carry W)
             (pf : forall x y c, _ /\ _)
    := {| bit_fst_add_with_carry x y c := proj1 (pf x y c);
          decode_snd_add_with_carry x y c := proj2 (pf x y c) |}.

  Definition Build_is_sub_with_carry' (subc : sub_with_carry W)
             (pf : forall x y c, _ /\ _)
    : is_sub_with_carry subc
    := {| fst_sub_with_carry x y c := proj1 (pf x y c);
          decode_snd_sub_with_carry x y c := proj2 (pf x y c) |}.

  Definition Build_is_mul_double' (muldw : multiply_double W)
             (pf : forall x y, _ /\ _)
    := {| decode_fst_mul_double x y := proj1 (pf x y);
          decode_snd_mul_double x y := proj2 (pf x y) |}.

  Lemma is_spread_left_immediate_alt
        {sprl : spread_left_immediate W}
        {isdecode : is_decode Wdecoder}
    : is_spread_left_immediate sprl
      <-> (forall r count, 0 <= count < n -> decode (fst (sprl r count)) + decode (snd (sprl r count)) << n = (decode r << count) mod (2^n*2^n))%Z.
  Proof using Type.
    split; intro H; [ | apply Build_is_spread_left_immediate' ];
      intros r count Hc;
      [ | specialize (H r count Hc); revert H ];
      unfold bounded_in_range_cls in *;
      pose proof (decode_range r);
      assert (0 < 2^n) by auto with zarith;
      assert (0 <= 2^count < 2^n)%Z by auto with zarith;
      assert (0 <= decode r * 2^count < 2^n * 2^n)%Z by (generalize dependent (decode r); intros; nia);
      rewrite ?decode_fst_spread_left_immediate, ?decode_snd_spread_left_immediate
        by typeclasses eauto with typeclass_instances core;
      autorewrite with Zshift_to_pow zsimplify push_Zpow.
    { reflexivity. }
    { intro H'; rewrite <- H'.
      autorewrite with zsimplify; split; reflexivity. }
  Qed.

  Lemma is_mul_double_alt
        {muldw : multiply_double W}
        {isdecode : is_decode Wdecoder}
    : is_mul_double muldw
      <-> (forall x y, decode (fst (muldw x y)) + decode (snd (muldw x y)) << n = (decode x * decode y) mod (2^n*2^n)).
  Proof using Type.
    split; intro H; [ | apply Build_is_mul_double' ];
      intros x y;
      [ | specialize (H x y); revert H ];
      pose proof (decode_range x);
      pose proof (decode_range y);
      assert (0 < 2^n) by auto with zarith;
      assert (0 <= decode x * decode y < 2^n * 2^n)%Z by nia;
      (destruct (0 <=? n) eqn:?; Z.ltb_to_lt;
       [ | assert (2^n = 0) by auto with zarith; exfalso; omega ]);
      rewrite ?decode_fst_mul_double, ?decode_snd_mul_double
        by typeclasses eauto with typeclass_instances core;
      autorewrite with Zshift_to_pow zsimplify push_Zpow.
    { reflexivity. }
    { intro H'; rewrite <- H'.
      autorewrite with zsimplify; split; reflexivity. }
  Qed.
End InstructionGallery.

Global Arguments is_spread_left_immediate_alt {_ _ _ _ _}.
Global Arguments is_mul_double_alt {_ _ _ _ _}.

Ltac bounded_solver_tac :=
  solve [ eassumption | typeclasses eauto | omega ].

Global Instance decode_proj n W (dec : W -> Z)
  : @decode n W {| decode := dec |} =~> dec.
Proof. reflexivity. Qed.

Global Instance decode_if_bool n W (decode : decoder n W)
  : forall (b : bool) x y,
    decode (if b then x else y)
    =~> if b then decode x else decode y.
Proof. destruct b; reflexivity. Qed.

Global Instance decode_mod_small {n W} {decode : decoder n W} {x b}
       {H : bounded_in_range_cls 0 (decode x) b}
  : decode x <~= decode x mod b.
Proof.
  Z.rewrite_mod_small; reflexivity.
Qed.

Global Instance decode_mod_range {n W decode} {H : @is_decode n W decode} x
  : decode x <~= decode x mod 2^n.
Proof. exact _. Qed.

Lemma decode_exponent_nonnegative {n W} (decode : decoder n W) {isdecode : is_decode decode}
      (isinhabited : W)
  : (0 <= n)%Z.
Proof.
  pose proof (decode_range isinhabited).
  assert (0 < 2^n) by omega.
  destruct (Z_lt_ge_dec n 0) as [H'|]; [ | omega ].
  assert (2^n = 0) by auto using Z.pow_neg_r.
  omega.
Qed.

Section adc_subc.
  Context {n W}
          {decode : decoder n W}
          {adc : add_with_carry W}
          {subc : sub_with_carry W}
          {isdecode : is_decode decode}
          {isadc : is_add_with_carry adc}
          {issubc : is_sub_with_carry subc}.
  Global Instance bit_fst_add_with_carry_false
    : forall x y, bit (fst (adc x y false)) <~=~> (decode x + decode y) >> n.
  Proof using isadc.
    intros; erewrite bit_fst_add_with_carry by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
  Global Instance bit_fst_add_with_carry_true
    : forall x y, bit (fst (adc x y true)) <~=~> (decode x + decode y + 1) >> n.
  Proof using isadc.
    intros; erewrite bit_fst_add_with_carry by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
  Global Instance fst_add_with_carry_leb
    : forall x y c, fst (adc x y c) <~= (2^n <=? (decode x + decode y + bit c)).
  Proof using isadc isdecode.
    intros x y c; hnf.
    assert (0 <= n)%Z by eauto using decode_exponent_nonnegative.
    pose proof (decode_range x); pose proof (decode_range y).
    assert (0 <= bit c <= 1)%Z by (destruct c; omega).
    lazymatch goal with
    | [ |- fst ?x = (?a <=? ?b) :> bool ]
      => cut (((if fst x then 1 else 0) = (if a <=? b then 1 else 0))%Z);
           [ destruct (fst x), (a <=? b); intro; congruence | ]
    end.
    push_decode.
    autorewrite with Zshift_to_pow.
    rewrite Z.div_between_0_if by auto with zarith.
    reflexivity.
  Qed.
  Global Instance fst_add_with_carry_false_leb
    : forall x y, fst (adc x y false) <~= (2^n <=? (decode x + decode y)).
  Proof using isadc isdecode.
    intros; erewrite fst_add_with_carry_leb by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
  Global Instance fst_add_with_carry_true_leb
    : forall x y, fst (adc x y true) <~=~> (2^n <=? (decode x + decode y + 1)).
  Proof using isadc isdecode.
    intros; erewrite fst_add_with_carry_leb by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
  Global Instance fst_sub_with_carry_false
    : forall x y, fst (subc x y false) <~=~> ((decode x - decode y) <? 0).
  Proof using issubc.
    intros; erewrite fst_sub_with_carry by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
  Global Instance fst_sub_with_carry_true
    : forall x y, fst (subc x y true) <~=~> ((decode x - decode y - 1) <? 0).
  Proof using issubc.
    intros; erewrite fst_sub_with_carry by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
End adc_subc.

Hint Extern 2 (rewrite_right_to_left_eq decode_tag _ (_ <=? (@decode ?n ?W ?decoder ?x + @decode _ _ _ ?y)))
=> apply @fst_add_with_carry_false_leb : typeclass_instances.
Hint Extern 2 (rewrite_right_to_left_eq decode_tag _ (_ <=? (@decode ?n ?W ?decoder ?x + @decode _ _ _ ?y + 1)))
=> apply @fst_add_with_carry_true_leb : typeclass_instances.
Hint Extern 2 (rewrite_right_to_left_eq decode_tag _ (_ <=? (@decode ?n ?W ?decoder ?x + @decode _ _ _ ?y + if ?c then _ else _)))
=> apply @fst_add_with_carry_leb : typeclass_instances.


(* We take special care to handle the case where the decoder is
   syntactically different but the decoded expression is judgmentally
   the same; we don't want to split apart variables that should be the
   same. *)
Ltac set_decode_step check :=
  match goal with
  | [ |- context G[@decode ?n ?W ?dr ?w] ]
    => check w;
      first [ match goal with
              | [ d := @decode _ _ _ w |- _ ]
                => change (@decode n W dr w) with d
              end
            | generalize (@decode_range n W dr _ w);
              let d := fresh "d" in
              set (d := @decode n W dr w);
              intro ]
  end.
Ltac set_decode check := repeat set_decode_step check.
Ltac clearbody_decode :=
  repeat match goal with
         | [ H := @decode _ _ _ _ |- _ ] => clearbody H
         end.
Ltac generalize_decode_by check := set_decode check; clearbody_decode.
Ltac generalize_decode := generalize_decode_by ltac:(fun w => idtac).
Ltac generalize_decode_var := generalize_decode_by ltac:(fun w => is_var w).
