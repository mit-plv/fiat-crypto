(*** Proofs About Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.BoundedArithmetic.DoubleBounded.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion Pos.to_nat : positive >-> nat.
Local Notation eta x := (fst x, snd x).

Section generic_constructions.
  Section decode.
    Context {n W} {decode : decoder n W}.
    Section with_k.
      Context {k : nat}.
      Local Notation limb_widths := (repeat n k).

      Lemma decode_bounded {isdecode : is_decode decode} w
        : 0 <= n -> bounded limb_widths (map decode (rev (to_list k w))).
      Proof.
        intro.
        eapply bounded_uniform; try solve [ eauto using repeat_spec ].
        { distr_length. }
        { intros z H'.
          apply in_map_iff in H'.
          destruct H' as [? [? H'] ]; subst; apply decode_range. }
      Qed.

      (** TODO: Clean up this proof *)
      Global Instance tuple_is_decode {isdecode : is_decode decode}
        : is_decode (tuple_decoder (k := k)).
      Proof.
        unfold tuple_decoder; hnf; simpl.
        intro w.
        destruct (zerop k); [ subst | ].
        { unfold BaseSystem.decode, BaseSystem.decode'; simpl; omega. }
        assert (0 <= n)
          by (destruct k as [ | [|] ]; [ omega | | destruct w ];
              eauto using decode_exponent_nonnegative).
        replace (2^(k * n)) with (upper_bound limb_widths)
          by (erewrite upper_bound_uniform by eauto using repeat_spec; distr_length).
        apply decode_upper_bound; auto using decode_bounded.
        { intros ? H'.
          apply repeat_spec in H'; omega. }
        { distr_length. }
      Qed.
    End with_k.

    Local Arguments base_from_limb_widths : simpl never.
    Local Arguments repeat : simpl never.
    Local Arguments Z.mul !_ !_.
    Lemma tuple_decoder_S {k} w : 0 <= n -> (tuple_decoder (k := S (S k)) w = tuple_decoder (k := S k) (fst w) + (decode (snd w) << (S k * n)))%Z.
    Proof.
      intro Hn.
      destruct w as [? w]; simpl.
      replace (decode w) with (decode w * 1 + 0)%Z by omega.
      rewrite map_app, map_cons, map_nil.
      erewrite decode_shift_uniform_app by (eauto using repeat_spec; distr_length).
      distr_length.
      autorewrite with push_skipn natsimplify push_firstn.
      reflexivity.
    Qed.
    Lemma tuple_decoder_O w : tuple_decoder (k := 1) w = decode w.
    Proof.
      unfold tuple_decoder, BaseSystem.decode, BaseSystem.decode', accumulate, base_from_limb_widths, repeat.
      simpl.
      omega.
    Qed.
    Lemma tuple_decoder_m1 w : tuple_decoder (k := 0) w = 0.
    Proof. reflexivity. Qed.
  End decode.
  Local Arguments tuple_decoder : simpl never.
  Local Opaque tuple_decoder.
  Hint Rewrite @tuple_decoder_S @tuple_decoder_O @tuple_decoder_m1 using solve [ auto with zarith ] : simpl_tuple_decoder.

  Hint Extern 1 (decoder _ (tuple ?W 2)) => apply (fun n decode => @tuple_decoder n W decode 2 : decoder (2 * n) (tuple W 2)) : typeclass_instances.

  Lemma ripple_carry_tuple_SS {T} f k xss yss carry
    : @ripple_carry_tuple T f (S (S k)) xss yss carry
      = let '(xs, x) := eta xss in
        let '(ys, y) := eta yss in
        let '(carry, zs) := eta (@ripple_carry_tuple _ f (S k) xs ys carry) in
        let '(carry, z) := eta (f x y carry) in
        (carry, (zs, z)).
  Proof. reflexivity. Qed.

  Lemma carry_is_good (n z0 z1 k : Z)
    : 0 <= n ->
      0 <= k ->
      (z1 + z0 >> k) >> n = (z0 + z1 << k) >> (k + n) /\
      (z0 mod 2 ^ k + ((z1 + z0 >> k) mod 2 ^ n) << k)%Z = (z0 + z1 << k) mod (2 ^ k * 2 ^ n).
  Proof.
    intros.
    assert (0 < 2 ^ n) by auto with zarith.
    assert (0 < 2 ^ k) by auto with zarith.
    assert (0 < 2^n * 2^k) by nia.
    autorewrite with Zshift_to_pow push_Zpow.
    rewrite <- (Zmod_small ((z0 mod _) + _) (2^k * 2^n)) by (Z.div_mod_to_quot_rem; nia).
    rewrite <- !Z.mul_mod_distr_r by lia.
    rewrite !(Z.mul_comm (2^k)); pull_Zmod.
    split; [ | apply f_equal2 ];
      Z.div_mod_to_quot_rem; nia.
  Qed.

  Definition carry_is_good_carry n z0 z1 k H0 H1 := proj1 (@carry_is_good n z0 z1 k H0 H1).
  Definition carry_is_good_value n z0 z1 k H0 H1 := proj2 (@carry_is_good n z0 z1 k H0 H1).

  Section ripple_carry_adc.
    Context {n W} {decode : decoder n W} (adc : add_with_carry W).

    Lemma ripple_carry_adc_SS k xss yss carry
      : ripple_carry_adc (k := S (S k)) adc xss yss carry
        = let '(xs, x) := eta xss in
          let '(ys, y) := eta yss in
          let '(carry, zs) := eta (ripple_carry_adc (k := S k) adc xs ys carry) in
          let '(carry, z) := eta (adc x y carry) in
          (carry, (zs, z)).
    Proof. apply ripple_carry_tuple_SS. Qed.

    Local Existing Instance tuple_decoder.

    Global Instance ripple_carry_is_add_with_carry {k}
           {isdecode : is_decode decode}
           {is_adc : is_add_with_carry adc}
      : is_add_with_carry (ripple_carry_adc (k := k) adc).
    Proof.
      destruct k as [|k].
      { constructor; simpl; intros; autorewrite with zsimplify; reflexivity. }
      { induction k as [|k IHk].
        { cbv [ripple_carry_adc ripple_carry_tuple to_list].
          constructor; simpl @fst; simpl @snd; intros;
            autorewrite with simpl_tuple_decoder;
            push_decode;
            autorewrite with zsimplify; reflexivity. }
        { apply Build_is_add_with_carry'; intros x y c.
          assert (0 <= n) by (destruct x; eauto using decode_exponent_nonnegative).
          assert (2^n <> 0) by auto with zarith.
          assert (0 <= S k * n) by nia.
          rewrite !tuple_decoder_S, !ripple_carry_adc_SS by assumption.
          simplify_projections; push_decode; generalize_decode.
          erewrite carry_is_good_carry, carry_is_good_value by lia.
          autorewrite with pull_Zpow push_Zof_nat zsimplify Zshift_to_pow.
          split; apply f_equal2; nia. } }
    Qed.

  End ripple_carry_adc.

  Section tuple2.
    Section spread_left_correct.
      Context {n W} {decode : decoder n W} {sprl : spread_left_immediate W}
              {isdecode : is_decode decode}.
      Lemma is_spread_left_immediate_alt
        : is_spread_left_immediate sprl
          <-> (forall r count, 0 <= count < n -> tuple_decoder (k := 2) (sprl r count) = (decode r << count) mod 2^(2*n)).
      Proof.
        split; intro H; [ | apply Build_is_spread_left_immediate' ];
          intros r count Hc;
          [ | specialize (H r count Hc); revert H ];
          pose proof (decode_range r);
          assert (0 < 2^n) by auto with zarith;
          assert (0 <= 2^count < 2^n) by auto with zarith;
          assert (0 <= decode r * 2^count < 2^n * 2^n) by (generalize dependent (decode r); intros; nia);
          autorewrite with simpl_tuple_decoder; push_decode;
            autorewrite with Zshift_to_pow zsimplify push_Zpow.
        { reflexivity. }
        { intro H'; rewrite <- H'.
          autorewrite with zsimplify; split; reflexivity. }
      Qed.
    End spread_left_correct.

    Local Arguments Z.pow !_ !_.
    Local Arguments Z.mul !_ !_.

    Section spread_left.
      Context (n : Z) {W}
              {ldi : load_immediate W}
              {shl : shift_left_immediate W}
              {shr : shift_right_immediate W}
              {decode : decoder n W}
              {isdecode : is_decode decode}
              {isldi : is_load_immediate ldi}
              {isshl : is_shift_left_immediate shl}
              {isshr : is_shift_right_immediate shr}.

      Lemma spread_left_from_shift_correct
            r count
            (H : 0 < count < n)
        : (decode (shl r count) + decode (shr r (n - count)) << n = decode r << count mod 2^(2*n))%Z.
      Proof.
        assert (0 <= n - count < n) by lia.
        assert (0 < 2^(n-count)) by auto with zarith.
        assert (2^count < 2^n) by auto with zarith.
        pose proof (decode_range r).
        assert (0 <= decode r * 2 ^ count < 2 ^ n * 2^n) by auto with zarith.
        simpl.
        push_decode; autorewrite with Zshift_to_pow zsimplify.
        replace (decode r / 2^(n-count) * 2^n)%Z with ((decode r / 2^(n-count) * 2^(n-count)) * 2^count)%Z
          by (rewrite <- Z.mul_assoc; autorewrite with pull_Zpow zsimplify; reflexivity).
        rewrite Z.mul_div_eq' by lia.
        autorewrite with push_Zmul zsimplify.
        rewrite <- Z.mul_mod_distr_r_full, Z.add_sub_assoc.
        repeat autorewrite with pull_Zpow zsimplify in *.
        reflexivity.
      Qed.

      Global Instance is_spread_left_from_shift
        : is_spread_left_immediate (sprl_from_shift n).
      Proof.
        apply is_spread_left_immediate_alt.
        intros r count; intros.
        pose proof (decode_range r).
        assert (0 < 2^n) by auto with zarith.
        assert (decode r < 2^n * 2^n) by (generalize dependent (decode r); intros; nia).
        autorewrite with simpl_tuple_decoder.
        destruct (Z_zerop count).
        { subst; autorewrite with Zshift_to_pow zsimplify.
          simpl; push_decode.
          autorewrite with push_Zpow zsimplify.
          reflexivity. }
        simpl.
        rewrite <- spread_left_from_shift_correct by lia.
        autorewrite with zsimplify Zpow_to_shift.
        reflexivity.
      Qed.
    End spread_left.

    Local Opaque ripple_carry_adc.
    Section full_from_half.
      Context {W}
              {mulhwll : multiply_low_low W}
              {mulhwhl : multiply_high_low W}
              {mulhwhh : multiply_high_high W}
              {adc : add_with_carry W}
              {shl : shift_left_immediate W}
              {shr : shift_right_immediate W}
              {half_n : Z}
              {ldi : load_immediate W}
              {decode : decoder (2 * half_n) W}
              {ismulhwll : is_mul_low_low half_n mulhwll}
              {ismulhwhl : is_mul_high_low half_n mulhwhl}
              {ismulhwhh : is_mul_high_high half_n mulhwhh}
              {isadc : is_add_with_carry adc}
              {isshl : is_shift_left_immediate shl}
              {isshr : is_shift_right_immediate shr}
              {isldi : is_load_immediate ldi}
              {isdecode : is_decode decode}.

      Local Arguments Z.mul !_ !_.
      Lemma spread_left_from_shift_half_correct
            r
        : (decode (shl r half_n) + decode (shr r half_n) * (2^half_n * 2^half_n)
           = (decode r * 2^half_n) mod (2^half_n*2^half_n*2^half_n*2^half_n))%Z.
      Proof.
        destruct (0 <? half_n) eqn:Hn; Z.ltb_to_lt.
        { pose proof (spread_left_from_shift_correct (2*half_n) r half_n) as H.
          specialize_by lia.
          autorewrite with Zshift_to_pow push_Zpow zsimplify in *.
          rewrite !Z.mul_assoc in *.
          simpl in *; rewrite <- H; reflexivity. }
        { pose proof (decode_range r).
          pose proof (decode_range (shr r half_n)).
          pose proof (decode_range (shl r half_n)).
          simpl in *.
          autorewrite with push_Zpow in *.
          destruct (Z_zerop half_n).
          { subst; simpl in *.
            autorewrite with zsimplify.
            nia. }
          assert (half_n < 0) by lia.
          assert (2^half_n = 0) by auto with zarith.
          assert (0 < 0) by nia; omega. }
      Qed.

      Lemma decode_mul_double_mod x y
        : (tuple_decoder (mul_double half_n x y) = (decode x * decode y) mod (2^(2 * half_n) * 2^(2*half_n)))%Z.
      Proof.
        assert (0 <= 2 * half_n) by eauto using decode_exponent_nonnegative.
        assert (0 <= half_n) by omega.
        unfold mul_double.
        push_decode; autorewrite with simpl_tuple_decoder; simplify_projections.
        autorewrite with zsimplify Zshift_to_pow push_Zpow.
        rewrite !spread_left_from_shift_half_correct.
        push_decode.
        generalize_decode_var.
        simpl in *.
        autorewrite with push_Zpow in *.
        repeat autorewrite with Zshift_to_pow zsimplify push_Zpow.
        rewrite <- !(Z.mul_mod_distr_r_full _ _ (_^_ * _^_)), ?Z.mul_assoc.
        Z.rewrite_mod_small.
        push_Zmod; pull_Zmod.
        apply f_equal2; [ | reflexivity ].
        Z.div_mod_to_quot_rem; nia.
      Qed.

      Lemma decode_mul_double x y
        : tuple_decoder (mul_double half_n x y) = (decode x * decode y)%Z.
      Proof.
        rewrite decode_mul_double_mod; generalize_decode_var.
        simpl in *; Z.rewrite_mod_small; reflexivity.
      Qed.

      Hint Rewrite
           (fun n (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (tuple W 2) (@tuple_decoder n W decode 2) w = _))
           (fun n (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (W * W) (@tuple_decoder n W decode 2) w = _))
           using solve [ auto with zarith ]
        : simpl_tuple_decoder.
      Local Ltac t :=
        hnf; intros [??] [??];
        assert (0 <= 2 * half_n) by eauto using decode_exponent_nonnegative;
        assert (0 <= half_n) by omega;
        simpl @Interface.mulhwhh; simpl @Interface.mulhwhl; simpl @Interface.mulhwll;
        rewrite decode_mul_double_mod; push_decode; autorewrite with simpl_tuple_decoder;
        simpl;
        push_decode; generalize_decode_var;
        autorewrite with Zshift_to_pow zsimplify;
        autorewrite with push_Zpow in *; Z.rewrite_mod_small;
        try reflexivity.

      Global Instance mul_double_is_multiply_low_low : is_mul_low_low (2 * half_n) mul_double_multiply_low_low.
      Proof. t. Qed.
      Global Instance mul_double_is_multiply_high_low : is_mul_high_low (2 * half_n) mul_double_multiply_high_low.
      Proof. t. Qed.
      Global Instance mul_double_is_multiply_high_high : is_mul_high_high (2 * half_n) mul_double_multiply_high_high.
      Proof. t. Qed.
    End full_from_half.
  End tuple2.
End generic_constructions.

Hint Resolve (fun n W decode pf => (@tuple_is_decode n W decode 2 pf : @is_decode (2 * n) (tuple W 2) (@tuple_decoder n W decode 2))) : typeclass_instances.
Hint Extern 3 (@is_decode _ (tuple ?W ?k) _) => let kv := (eval simpl in (Z.of_nat k)) in apply (fun n decode pf => (@tuple_is_decode n W decode k pf : @is_decode (kv * n) (tuple W k) (@tuple_decoder n W decode k : decode (kv * n) W))) : typeclass_instances.

Hint Extern 2 (@is_add_with_carry _ (tuple ?W ?k) (@tuple_decoder ?n _ ?decode _) (@ripple_carry_adc _ ?adc _))
    => apply (@ripple_carry_is_add_with_carry n W decode adc k) : typeclass_instances.

Hint Rewrite @tuple_decoder_S @tuple_decoder_O @tuple_decoder_m1 using solve [ auto with zarith ] : simpl_tuple_decoder.
Hint Rewrite
     (fun n W (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (tuple W 2) (@tuple_decoder n W decode 2) w = _))
     (fun n W (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (W * W) (@tuple_decoder n W decode 2) w = _))
     using solve [ auto with zarith ]
  : simpl_tuple_decoder.
