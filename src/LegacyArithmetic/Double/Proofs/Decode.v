Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Require Import Crypto.LegacyArithmetic.Interface.
Require Import Crypto.LegacyArithmetic.InterfaceProofs.
Require Import Crypto.LegacyArithmetic.Double.Core.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.

Require Crypto.LegacyArithmetic.Pow2Base.
Require Crypto.LegacyArithmetic.Pow2BaseProofs.

Local Open Scope nat_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.

Import BoundedRewriteNotations.
Local Open Scope Z_scope.

Section decode.
  Context {n W} {decode : decoder n W}.
  Section with_k.
    Context {k : nat}.
    Local Notation limb_widths := (repeat n k).

    Lemma decode_bounded {isdecode : is_decode decode} w
      : 0 <= n -> Pow2Base.bounded limb_widths (List.map decode (rev (to_list k w))).
    Proof using Type.
      intro.
      eapply Pow2BaseProofs.bounded_uniform; try solve [ eauto using repeat_spec ].
      { distr_length. }
      { intros z H'.
        apply in_map_iff in H'.
        destruct H' as [? [? H'] ]; subst; apply decode_range. }
    Qed.

    (** TODO: Clean up this proof *)
    Global Instance tuple_is_decode {isdecode : is_decode decode}
      : is_decode (tuple_decoder (k := k)).
    Proof using Type.
      unfold tuple_decoder; hnf; simpl.
      intro w.
      destruct (zerop k); [ subst | ].
      { cbv; intuition congruence. }
      assert (0 <= n)
        by (destruct k as [ | [|] ]; [ omega | | destruct w ];
            eauto using decode_exponent_nonnegative).
      replace (2^(k * n)) with (Pow2Base.upper_bound limb_widths)
        by (erewrite Pow2BaseProofs.upper_bound_uniform by eauto using repeat_spec; distr_length).
      apply Pow2BaseProofs.decode_upper_bound; auto using decode_bounded.
      { intros ? H'.
        apply repeat_spec in H'; omega. }
      { distr_length. }
    Qed.
  End with_k.

  Local Arguments Pow2Base.base_from_limb_widths : simpl never.
  Local Arguments repeat : simpl never.
  Local Arguments Z.mul !_ !_.
  Lemma tuple_decoder_S {k} w : 0 <= n -> (tuple_decoder (k := S (S k)) w = tuple_decoder (k := S k) (fst w) + (decode (snd w) << (S k * n)))%Z.
  Proof using Type.
    intro Hn.
    destruct w as [? w]; simpl.
    replace (decode w) with (decode w * 1 + 0)%Z by omega.
    rewrite map_app, map_cons, map_nil.
    erewrite Pow2BaseProofs.decode_shift_uniform_app by (eauto using repeat_spec; distr_length).
    distr_length.
    autorewrite with push_skipn natsimplify push_firstn.
    reflexivity.
  Qed.
  Global Instance tuple_decoder_O w : tuple_decoder (k := 1) w =~> decode w.
  Proof using Type.
    cbv [tuple_decoder LegacyArithmetic.BaseSystem.decode LegacyArithmetic.BaseSystem.decode' LegacyArithmetic.BaseSystem.accumulate Pow2Base.base_from_limb_widths repeat].
    simpl; hnf; lia.
  Qed.
  Global Instance tuple_decoder_m1 w : tuple_decoder (k := 0) w =~> 0.
  Proof using Type. reflexivity. Qed.

  Lemma tuple_decoder_n_neg k w {H : is_decode decode} : n <= 0 -> tuple_decoder (k := k) w =~> 0.
  Proof using Type.
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
  Proof using Type.
    unfold tuple_decoder, BaseSystem.decode, BaseSystem.decode', BaseSystem.accumulate, Pow2Base.base_from_limb_widths, repeat.
    simpl; hnf.
    rewrite Z.mul_1_l.
    split; apply P_ext; simpl; intro; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Global Instance tuple_decoder_2' w : (0 <= n)%bounded_rewrite -> tuple_decoder (k := 2) w <~= (decode (fst w) + decode (snd w) << (1%nat * n))%Z.
  Proof using Type.
    intros; rewrite !tuple_decoder_S, !tuple_decoder_O by assumption.
    reflexivity.
  Qed.
  Global Instance tuple_decoder_2 w : (0 <= n)%bounded_rewrite -> tuple_decoder (k := 2) w <~= (decode (fst w) + decode (snd w) << n)%Z.
  Proof using Type.
    intros; rewrite !tuple_decoder_S, !tuple_decoder_O by assumption.
    autorewrite with zsimplify_const; reflexivity.
  Qed.
End decode.

Global Arguments tuple_decoder : simpl never.
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

Global Instance tuple_decoder_mod : forall {n W} {decode : decoder n W} {k} {isdecode : is_decode decode} (w : tuple W (S (S k))),
    tuple_decoder (k := S k) (fst w) <~= tuple_decoder w mod 2^(S k * n).
Proof.
  intros n W decode k isdecode w.
  pose proof (snd w).
  assert (0 <= n) by eauto using decode_exponent_nonnegative.
  assert (0 <= (S k) * n) by nia.
  assert (0 <= tuple_decoder (k := S k) (fst w) < 2^(S k * n)) by apply decode_range.
  autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify.
  reflexivity.
Qed.

Global Instance tuple_decoder_div : forall {n W} {decode : decoder n W} {k} {isdecode : is_decode decode} (w : tuple W (S (S k))),
    decode (snd w) <~= tuple_decoder w / 2^(S k * n).
Proof.
  intros n W decode k isdecode w.
  pose proof (snd w).
  assert (0 <= n) by eauto using decode_exponent_nonnegative.
  assert (0 <= (S k) * n) by nia.
  assert (0 <= k * n) by nia.
  assert (0 < 2^n) by auto with zarith.
  assert (0 <= tuple_decoder (k := S k) (fst w) < 2^(S k * n)) by apply decode_range.
  autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify.
  reflexivity.
Qed.

Global Instance tuple2_decoder_mod : forall {n W} {decode : decoder n W} {isdecode : is_decode decode} (w : tuple W 2),
    decode (fst w) <~= tuple_decoder w mod 2^n.
Proof.
  intros n W decode isdecode w.
  generalize (@tuple_decoder_mod n W decode 0 isdecode w).
  autorewrite with simpl_tuple_decoder; trivial.
Qed.

Global Instance tuple2_decoder_div : forall {n W} {decode : decoder n W} {isdecode : is_decode decode} (w : tuple W 2),
    decode (snd w) <~= tuple_decoder w / 2^n.
Proof.
  intros n W decode isdecode w.
  generalize (@tuple_decoder_div n W decode 0 isdecode w).
  autorewrite with simpl_tuple_decoder; trivial.
Qed.
