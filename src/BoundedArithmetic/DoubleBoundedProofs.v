(*** Proofs About Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
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
Require Import Crypto.Util.LetIn.
Import Bug5107WorkAround.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion Pos.to_nat : positive >-> nat.
Local Notation eta x := (fst x, snd x).

Import BoundedRewriteNotations.
Local Open Scope Z_scope.

Section decode.
  Context {n W} {decode : decoder n W}.
  Section with_k.
    Context {k : nat}.
    Local Notation limb_widths := (repeat n k).

    Lemma decode_bounded {isdecode : is_decode decode} w
      : 0 <= n -> bounded limb_widths (List.map decode (rev (to_list k w))).
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
  Global Instance tuple_decoder_O w : tuple_decoder (k := 1) w =~> decode w.
  Proof.
    unfold tuple_decoder, BaseSystem.decode, BaseSystem.decode', accumulate, base_from_limb_widths, repeat.
    simpl; hnf.
    omega.
  Qed.
  Global Instance tuple_decoder_m1 w : tuple_decoder (k := 0) w =~> 0.
  Proof. reflexivity. Qed.

  Lemma tuple_decoder_n_neg k w {H : is_decode decode} : n <= 0 -> tuple_decoder (k := k) w =~> 0.
  Proof.
    pose proof (tuple_is_decode w) as H'; hnf in H'.
    intro; assert (k * n <= 0) by nia.
    assert (2^(k * n) <= 2^0) by (apply Z.pow_le_mono_r; omega).
    simpl in *; hnf.
    omega.
  Qed.
  Lemma tuple_decoder_O_ind_prod
         (P : forall n, decoder n W -> Type)
         (P_ext : forall n (a b : decoder n W), (forall x, a x = b x) -> P _ a -> P _ b)
    : (P _ (tuple_decoder (k := 1)) -> P _ decode)
      * (P _ decode -> P _ (tuple_decoder (k := 1))).
  Proof.
    unfold tuple_decoder, BaseSystem.decode, BaseSystem.decode', accumulate, base_from_limb_widths, repeat.
    simpl; hnf.
    rewrite Z.mul_1_l.
    split; apply P_ext; simpl; intro; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Global Instance tuple_decoder_2' w : (0 <= n)%bounded_rewrite -> tuple_decoder (k := 2) w <~= (decode (fst w) + decode (snd w) << (1%nat * n))%Z.
  Proof.
    intros; rewrite !tuple_decoder_S, !tuple_decoder_O by assumption.
    reflexivity.
  Qed.
  Global Instance tuple_decoder_2 w : (0 <= n)%bounded_rewrite -> tuple_decoder (k := 2) w <~= (decode (fst w) + decode (snd w) << n)%Z.
  Proof.
    intros; rewrite !tuple_decoder_S, !tuple_decoder_O by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
End decode.

Local Arguments tuple_decoder : simpl never.
Local Opaque tuple_decoder.

Global Instance tuple_decoder_n_O
      {W} {decode : decoder 0 W}
      {is_decode : is_decode decode}
  : forall k w, tuple_decoder (k := k) w =~> 0.
Proof. intros; apply tuple_decoder_n_neg; easy. Qed.

Lemma is_add_with_carry_1tuple {n W decode adc}
      (H : @is_add_with_carry n W decode adc)
  : @is_add_with_carry (1 * n) W (@tuple_decoder n W decode 1) adc.
Proof.
  apply tuple_decoder_O_ind_prod; try assumption.
  intros ??? ext [H0 H1]; apply Build_is_add_with_carry'.
  intros x y c; specialize (H0 x y c); specialize (H1 x y c).
  rewrite <- !ext; split; assumption.
Qed.

Hint Extern 1 (@is_add_with_carry _ _ (@tuple_decoder ?n ?W ?decode 1) ?adc)
=> apply (@is_add_with_carry_1tuple n W decode adc) : typeclass_instances.

Hint Resolve (fun n W decode pf => (@tuple_is_decode n W decode 2 pf : @is_decode (2 * n) (tuple W 2) (@tuple_decoder n W decode 2))) : typeclass_instances.
Hint Extern 3 (@is_decode _ (tuple ?W ?k) _) => let kv := (eval simpl in (Z.of_nat k)) in apply (fun n decode pf => (@tuple_is_decode n W decode k pf : @is_decode (kv * n) (tuple W k) (@tuple_decoder n W decode k : decoder (kv * n)%Z (tuple W k)))) : typeclass_instances.

Hint Rewrite @tuple_decoder_S @tuple_decoder_O @tuple_decoder_m1 @tuple_decoder_n_O using solve [ auto with zarith ] : simpl_tuple_decoder.
Hint Rewrite Z.mul_1_l : simpl_tuple_decoder.
Hint Rewrite
     (fun n W (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (tuple W 2) (@tuple_decoder n W decode 2) w = _))
     (fun n W (decode : decoder n W) w pf => (@tuple_decoder_S n W decode 0 w pf : @Interface.decode (2 * n) (W * W) (@tuple_decoder n W decode 2) w = _))
     (fun n W decode w => @tuple_decoder_m1 n W decode w : @Interface.decode (Z.of_nat 0 * n) unit (@tuple_decoder n W decode 0) w = _)
     using solve [ auto with zarith ]
  : simpl_tuple_decoder.

Hint Rewrite @tuple_decoder_S @tuple_decoder_O @tuple_decoder_m1 using solve [ auto with zarith ] : simpl_tuple_decoder.

Global Instance tuple_decoder_mod {n W} {decode : decoder n W} {k} {isdecode : is_decode decode} (w : tuple W (S (S k)))
  : tuple_decoder (k := S k) (fst w) <~= tuple_decoder w mod 2^(S k * n).
Proof.
  pose proof (snd w).
  assert (0 <= n) by eauto using decode_exponent_nonnegative.
  assert (0 <= (S k) * n) by nia.
  assert (0 <= tuple_decoder (k := S k) (fst w) < 2^(S k * n)) by apply decode_range.
  autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify.
  reflexivity.
Qed.

Global Instance tuple_decoder_div {n W} {decode : decoder n W} {k} {isdecode : is_decode decode} (w : tuple W (S (S k)))
  : decode (snd w) <~= tuple_decoder w / 2^(S k * n).
Proof.
  pose proof (snd w).
  assert (0 <= n) by eauto using decode_exponent_nonnegative.
  assert (0 <= (S k) * n) by nia.
  assert (0 <= k * n) by nia.
  assert (0 < 2^n) by auto with zarith.
  assert (0 <= tuple_decoder (k := S k) (fst w) < 2^(S k * n)) by apply decode_range.
  autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify.
  reflexivity.
Qed.

Global Instance tuple2_decoder_mod {n W} {decode : decoder n W} {isdecode : is_decode decode} (w : tuple W 2)
  : decode (fst w) <~= tuple_decoder w mod 2^n.
Proof.
  generalize (@tuple_decoder_mod n W decode 0 isdecode w).
  autorewrite with simpl_tuple_decoder; trivial.
Qed.

Global Instance tuple2_decoder_div {n W} {decode : decoder n W} {isdecode : is_decode decode} (w : tuple W 2)
  : decode (snd w) <~= tuple_decoder w / 2^n.
Proof.
  generalize (@tuple_decoder_div n W decode 0 isdecode w).
  autorewrite with simpl_tuple_decoder; trivial.
Qed.

Lemma decode_is_spread_left_immediate_iff
      {n W}
      {decode : decoder n W}
      {sprl : spread_left_immediate W}
      {isdecode : is_decode decode}
  : is_spread_left_immediate sprl
    <-> (forall r count,
            0 <= count < n
            -> tuple_decoder (sprl r count) = decode r << count).
Proof.
  rewrite is_spread_left_immediate_alt by assumption.
  split; intros H r count Hc; specialize (H r count Hc); revert H;
    pose proof (decode_range r);
    assert (0 < 2^count < 2^n) by auto with zarith;
    autorewrite with simpl_tuple_decoder;
    simpl; intro H'; rewrite H';
      autorewrite with Zshift_to_pow;
      Z.rewrite_mod_small; reflexivity.
Qed.

Global Instance decode_is_spread_left_immediate
       {n W}
       {decode : decoder n W}
       {sprl : spread_left_immediate W}
       {isdecode : is_decode decode}
       {issprl : is_spread_left_immediate sprl}
  : forall r count,
    (0 <= count < n)%bounded_rewrite
    -> tuple_decoder (sprl r count) <~=~> decode r << count
  := proj1 decode_is_spread_left_immediate_iff _.

Lemma decode_mul_double_iff
      {n W}
      {decode : decoder n W}
      {muldw : multiply_double W}
      {isdecode : is_decode decode}
  : is_mul_double muldw
    <-> (forall x y, tuple_decoder (muldw x y) = (decode x * decode y)%Z).
Proof.
  rewrite is_mul_double_alt by assumption.
  split; intros H x y; specialize (H x y); revert H;
    pose proof (decode_range x); pose proof (decode_range y);
      assert (0 <= decode x * decode y < 2^n * 2^n) by nia;
      assert (0 <= n) by eauto using decode_exponent_nonnegative;
      autorewrite with simpl_tuple_decoder;
      simpl; intro H'; rewrite H';
        Z.rewrite_mod_small; reflexivity.
Qed.

Global Instance decode_mul_double
           {n W}
           {decode : decoder n W}
           {muldw : multiply_double W}
           {isdecode : is_decode decode}
           {ismuldw : is_mul_double muldw}
  : forall x y, tuple_decoder (muldw x y) <~=~> (decode x * decode y)%Z
  := proj1 decode_mul_double_iff _.


Lemma ripple_carry_tuple_SS' {T} f k xss yss carry
  : @ripple_carry_tuple T f (S (S k)) xss yss carry
    = dlet xss := xss in
      dlet yss := yss in
      let '(xs, x) := eta xss in
      let '(ys, y) := eta yss in
      dlet addv := (@ripple_carry_tuple _ f (S k) xs ys carry) in
      let '(carry, zs) := eta addv in
      dlet fxy := (f x y carry) in
      let '(carry, z) := eta fxy in
      (carry, (zs, z)).
Proof. reflexivity. Qed.

(* This turns a goal like [x = Let_In p (fun v => let '(x, y) := f v
   in x + y)] into a goal like [x = fst (f p) + snd (f p)].  Note that
   it inlines [Let_In] as well as destructuring lets. *)
Local Ltac eta_expand :=
  repeat match goal with
         | _ => progress unfold Let_In
         | [ |- context[let '(x, y) := ?e in _] ]
           => rewrite (surjective_pairing e)
         | _ => rewrite <- !surjective_pairing
         end.

Lemma ripple_carry_tuple_SS {T} f k xss yss carry
  : @ripple_carry_tuple T f (S (S k)) xss yss carry
    = let '(xs, x) := eta xss in
      let '(ys, y) := eta yss in
      let '(carry, zs) := eta (@ripple_carry_tuple _ f (S k) xs ys carry) in
      let '(carry, z) := eta (f x y carry) in
      (carry, (zs, z)).
Proof.
  rewrite ripple_carry_tuple_SS'.
  eta_expand.
  reflexivity.
Qed.

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
Section carry_sub_is_good.
  Context (n k z0 z1 : Z)
          (Hn : 0 <= n)
          (Hk : 0 <= k)
          (Hz1 : -2^n < z1 < 2^n)
          (Hz0 : -2^k <= z0 < 2^k).

  Lemma carry_sub_is_good_carry
    : ((z1 - if z0 <? 0 then 1 else 0) <? 0) = ((z0 + z1 << k) <? 0).
  Proof.
    clear n Hn Hz1.
    assert (0 < 2 ^ k) by auto with zarith.
    autorewrite with Zshift_to_pow.
    repeat match goal with
           | _ => progress break_match
           | [ |- context[?x <? ?y] ] => destruct (x <? y) eqn:?
           | _ => reflexivity
           | _ => progress Z.ltb_to_lt
           | [ |- true = false ] => exfalso
           | [ |- false = true ] => exfalso
           | [ |- False ] => nia
           end.
  Qed.
  Lemma carry_sub_is_good_value
    : (z0 mod 2 ^ k + ((z1 - if z0 <? 0 then 1 else 0) mod 2 ^ n) << k)%Z
      = (z0 + z1 << k) mod (2 ^ k * 2 ^ n).
  Proof.
    assert (0 < 2 ^ n) by auto with zarith.
    assert (0 < 2 ^ k) by auto with zarith.
    assert (0 < 2^n * 2^k) by nia.
    autorewrite with Zshift_to_pow push_Zpow.
    rewrite <- (Zmod_small ((z0 mod _) + _) (2^k * 2^n)) by (Z.div_mod_to_quot_rem; nia).
    rewrite <- !Z.mul_mod_distr_r by lia.
    rewrite !(Z.mul_comm (2^k)); pull_Zmod.
    apply f_equal2; Z.div_mod_to_quot_rem; break_match; Z.ltb_to_lt; try reflexivity;
      match goal with
      | [ q : Z |- _ = _ :> Z ]
        => first [ cut (q = -1); [ intro; subst; ring | nia ]
                 | cut (q = 0); [ intro; subst; ring | nia ]
                 | cut (q = 1); [ intro; subst; ring | nia ] ]
      end.
  Qed.
End carry_sub_is_good.

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

  Local Opaque Z.of_nat.
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
          simpl; pull_decode; reflexivity. }
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

Hint Extern 2 (@is_add_with_carry _ (tuple ?W ?k) (@tuple_decoder ?n _ ?decode _) (@ripple_carry_adc _ ?adc _))
=> apply (@ripple_carry_is_add_with_carry n W decode adc k) : typeclass_instances.

Section ripple_carry_subc.
  Context {n W} {decode : decoder n W} (subc : sub_with_carry W).

  Lemma ripple_carry_subc_SS k xss yss carry
    : ripple_carry_subc (k := S (S k)) subc xss yss carry
      = let '(xs, x) := eta xss in
        let '(ys, y) := eta yss in
        let '(carry, zs) := eta (ripple_carry_subc (k := S k) subc xs ys carry) in
        let '(carry, z) := eta (subc x y carry) in
        (carry, (zs, z)).
  Proof. apply ripple_carry_tuple_SS. Qed.

  Local Opaque Z.of_nat.
  Global Instance ripple_carry_is_sub_with_carry {k}
         {isdecode : is_decode decode}
         {is_subc : is_sub_with_carry subc}
    : is_sub_with_carry (ripple_carry_subc (k := k) subc).
  Proof.
    destruct k as [|k].
    { constructor; repeat (intros [] || intro); autorewrite with simpl_tuple_decoder zsimplify; reflexivity. }
    { induction k as [|k IHk].
      { cbv [ripple_carry_subc ripple_carry_tuple to_list].
        constructor; simpl @fst; simpl @snd; intros;
          simpl; push_decode; autorewrite with zsimplify; reflexivity. }
      { apply Build_is_sub_with_carry'; intros x y c.
        assert (0 <= n) by (destruct x; eauto using decode_exponent_nonnegative).
        assert (2^n <> 0) by auto with zarith.
        assert (0 <= S k * n) by nia.
        rewrite !tuple_decoder_S, !ripple_carry_subc_SS by assumption.
        simplify_projections; push_decode; generalize_decode.
        erewrite (carry_sub_is_good_carry (S k * n)), carry_sub_is_good_value by (break_match; lia).
        autorewrite with pull_Zpow push_Zof_nat zsimplify Zshift_to_pow.
        split; apply f_equal2; nia. } }
  Qed.

End ripple_carry_subc.

Hint Extern 2 (@is_sub_with_carry _ (tuple ?W ?k) (@tuple_decoder ?n _ ?decode _) (@ripple_carry_subc _ ?subc _))
=> apply (@ripple_carry_is_sub_with_carry n W decode subc k) : typeclass_instances.

Section tuple2.
  Local Arguments Z.pow !_ !_.
  Local Arguments Z.mul !_ !_.

  Section select_conditional.
    Context {n W}
            {decode : decoder n W}
            {is_decode : is_decode decode}
            {selc : select_conditional W}
            {is_selc : is_select_conditional selc}.

    Global Instance is_select_conditional_double
      : is_select_conditional selc_double.
    Proof.
      intros b x y.
      destruct n.
      { rewrite !(tuple_decoder_n_O (W:=W) 2); now destruct b. }
      { rewrite (tuple_decoder_2 x), (tuple_decoder_2 y), (tuple_decoder_2 (selc_double b x y))
          by apply Zle_0_pos.
        push_decode.
        now destruct b. }
      { rewrite !(tuple_decoder_n_neg (W:=W) 2); now destruct b. }
    Qed.
  End select_conditional.

  Section load_immediate.
    Context {n W}
            {decode : decoder n W}
            {is_decode : is_decode decode}
            {ldi : load_immediate W}
            {is_ldi : is_load_immediate ldi}.

    Global Instance is_load_immediate_double
      : is_load_immediate (ldi_double n).
    Proof.
      intros x H; hnf in H.
      pose proof (decode_exponent_nonnegative decode (ldi x)).
      assert (0 <= x mod 2^n < 2^n) by auto with zarith.
      assert (x / 2^n < 2^n)
        by (apply Z.div_lt_upper_bound; autorewrite with pull_Zpow zsimplify; auto with zarith).
      assert (0 <= x / 2^n < 2^n) by (split; Z.zero_bounds).
      unfold ldi_double, load_immediate_double; simpl.
      autorewrite with simpl_tuple_decoder Zshift_to_pow; simpl; push_decode.
      autorewrite with zsimplify; reflexivity.
    Qed.
  End load_immediate.

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
      : (decode (shl r count) + decode (shr r (n - count)) << n = decode r << count mod (2^n*2^n))%Z.
    Proof.
      assert (0 <= count < n) by lia.
      assert (0 <= n - count < n) by lia.
      assert (0 < 2^(n-count)) by auto with zarith.
      assert (2^count < 2^n) by auto with zarith.
      pose proof (decode_range r).
      assert (0 <= decode r * 2 ^ count < 2 ^ n * 2^n) by auto with zarith.
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
      unfold mul_double; eta_expand.
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

    Lemma decode_mul_double_function x y
      : tuple_decoder (mul_double half_n x y) = (decode x * decode y)%Z.
    Proof.
      rewrite decode_mul_double_mod; generalize_decode_var.
      simpl in *; Z.rewrite_mod_small; reflexivity.
    Qed.

    Global Instance mul_double_is_multiply_double : is_mul_double mul_double_multiply.
    Proof.
      apply decode_mul_double_iff; apply decode_mul_double_function.
    Qed.
  End full_from_half.

  Section half_from_full.
    Context {n W}
            {decode : decoder n W}
            {muldw : multiply_double W}
            {isdecode : is_decode decode}
            {ismuldw : is_mul_double muldw}.

    Local Ltac t :=
      hnf; intros [??] [??];
      assert (0 <= n) by eauto using decode_exponent_nonnegative;
      assert (0 < 2^n) by auto with zarith;
      assert (forall x y, 0 <= x < 2^n -> 0 <= y < 2^n -> 0 <= x * y < 2^n * 2^n) by auto with zarith;
      simpl @Interface.mulhwhh; simpl @Interface.mulhwhl; simpl @Interface.mulhwll;
      rewrite decode_mul_double; autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify push_Zpow;
      Z.rewrite_mod_small;
      try reflexivity.

    Global Instance mul_double_is_multiply_low_low : is_mul_low_low n mul_double_multiply_low_low.
    Proof. t. Qed.
    Global Instance mul_double_is_multiply_high_low : is_mul_high_low n mul_double_multiply_high_low.
    Proof. t. Qed.
    Global Instance mul_double_is_multiply_high_high : is_mul_high_high n mul_double_multiply_high_high.
    Proof. t. Qed.
  End half_from_full.
End tuple2.
