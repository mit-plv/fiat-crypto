Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import NTT.Polynomial NTT.NTT.
Require PrimeFieldTheorems.

Section Utils.
  (* There is only equivalence if c <> 0 *)
  Lemma flat_map_constant_nth_error {A B: Type} (c: nat) (f: A -> list B) (l: list A):
    (forall x : A, In x l -> length (f x) = c) ->
    forall k x, nth_error (flat_map f l) k = Some x ->
           exists y, nth_error l (PeanoNat.Nat.div k c) = Some y /\
                nth_error (f y) (PeanoNat.Nat.modulo k c) = Some x.
  Proof.
    destruct (NatUtil.nat_eq_dec c 0%nat) as [->|Hcnz].
    { intros Hl k x Hx. apply nth_error_In in Hx.
      apply in_flat_map in Hx. destruct Hx as [z [Hz Hzz]].
      apply Hl in Hz. apply ListUtil.length0_nil in Hz.
      rewrite Hz in Hzz. elim (in_nil Hzz). }
    induction l; intros Hl k x Hx; simpl in Hx.
    - rewrite ListUtil.nth_error_nil_error in Hx; inversion Hx.
    - rewrite ListUtil.nth_error_app, Hl in Hx; [|apply in_eq].
      destruct (Compare_dec.lt_dec k c).
      + rewrite PeanoNat.Nat.div_small, PeanoNat.Nat.mod_small by Lia.lia.
        simpl. eexists; split; eauto.
      + apply IHl in Hx; [|intros; apply Hl; apply in_cons; auto].
        assert (k = (k - c) + c)%nat as -> by Lia.lia.
        rewrite NatUtil.div_minus by Lia.lia.
        assert (k - c + c = (k - c) + 1 * c)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.Div0.mod_add.
        assert (_ + 1 = S (PeanoNat.Nat.div (k - c) c))%nat as -> by Lia.lia.
        simpl. exact Hx.
  Qed.

  Lemma set_nth_set_nth {T} n (x y: T) l:
    ListUtil.set_nth n x (ListUtil.set_nth n y l) = ListUtil.set_nth n x l.
  Proof.
    apply nth_error_ext; intros i; repeat rewrite ListUtil.nth_set_nth.
    rewrite ListUtil.length_set_nth.
    destruct (PeanoNat.Nat.eq_dec i n); auto.
  Qed.

  Lemma set_nth_app_l {T} n (x: T) l1 l2:
    (n < length l1)%nat ->
    ListUtil.set_nth n x (l1 ++ l2) = (ListUtil.set_nth n x l1) ++ l2.
  Proof.
    intro Hl; apply nth_error_ext; intro i.
    rewrite ListUtil.nth_set_nth, length_app, nth_error_app.
    rewrite nth_error_app, ListUtil.nth_set_nth, ListUtil.length_set_nth.
    destruct (PeanoNat.Nat.eq_dec i n) as [->|Hne]; auto.
    destruct (Compare_dec.lt_dec n _); [|Lia.lia].
    destruct (Compare_dec.lt_dec n _); [|Lia.lia].
    rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) Hl). reflexivity.
  Qed.

  Lemma set_nth_app_r {T} n (x: T) l1 l2:
    (length l1 <= n)%nat ->
    ListUtil.set_nth n x (l1 ++ l2) = l1 ++ (ListUtil.set_nth (n - length l1) x l2).
  Proof.
    intro Hl; apply nth_error_ext; intro i.
    rewrite ListUtil.nth_set_nth, length_app, nth_error_app.
    rewrite nth_error_app, ListUtil.nth_set_nth.
    destruct (PeanoNat.Nat.eq_dec i n) as [->|Hne].
    - rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _) Hl).
      destruct (PeanoNat.Nat.eq_dec _ _) as [_|]; [|Lia.lia].
      do 2 (destruct (Compare_dec.lt_dec _ _)); auto; Lia.lia.
    - pose proof (PeanoNat.Nat.ltb_spec i (length l1)) as Hs.
      destruct (PeanoNat.Nat.ltb i _); inversion Hs; clear Hs; auto.
      destruct (PeanoNat.Nat.eq_dec _ _); auto; Lia.lia.
  Qed.

  Lemma firstn_enumerate {A} k n (l: list A):
    firstn k (enumerate n l) = enumerate n (firstn k l).
  Proof.
    unfold enumerate. rewrite ListUtil.firstn_combine, firstn_seq, length_firstn. reflexivity.
  Qed.

  Lemma skipn_enumerate {A} k n (l: list A):
    skipn k (enumerate n l) = enumerate (n + k) (skipn k l).
  Proof.
    unfold enumerate. rewrite ListUtil.skipn_combine, ListUtil.skipn_seq, length_skipn.
    f_equal. f_equal. Lia.lia.
  Qed.

  Lemma firstn_concat_same_length {A: Type} (k c : nat) (l: list (list A)):
    Forall (fun x => length x = c) l ->
    firstn (k * c) (concat l) = concat (firstn k l).
  Proof.
    revert l. induction k; intros l HF.
    - rewrite PeanoNat.Nat.mul_0_l; reflexivity.
    - destruct l as [|x].
      + rewrite firstn_nil, concat_nil. reflexivity.
      + rewrite firstn_cons, concat_cons, concat_cons, <- IHk; [|inversion HF; auto].
        assert (S k * c = length x + k * c)%nat as -> by (inversion HF; Lia.lia).
        rewrite firstn_app_2. reflexivity.
  Qed.

  Lemma skipn_concat_same_length {A: Type} (k c : nat) (l: list (list A)):
    Forall (fun x => length x = c) l ->
    skipn (k * c) (concat l) = concat (skipn k l).
  Proof.
    revert l. induction k; intros l HF.
    - rewrite PeanoNat.Nat.mul_0_l; reflexivity.
    - destruct l as [|x].
      + rewrite skipn_nil, concat_nil. reflexivity.
      + rewrite skipn_cons, <- IHk; [|inversion HF; auto].
        simpl. rewrite <- ListUtil.skipn_skipn.
        rewrite skipn_app_r; auto.
        inversion HF; auto.
  Qed.

  Lemma list_sum_constant c l:
    Forall (fun x => x = c) l ->
    (list_sum l = c * length l)%nat.
  Proof.
    induction 1; [rewrite PeanoNat.Nat.mul_0_r; reflexivity|].
    subst x. simpl. rewrite IHForall. Lia.lia.
  Qed.
End Utils.

Section Zetas.
  (* Define the array that contains the powers of zeta *)

  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q).
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.

  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  (* We only keep one half of the coefficients since the other half can be recovered from it *)
  Fixpoint zeta_powers (l i: nat) :=
    match i with
    | O => @decompose m O l
    | S i => (zeta_powers l i) ++ (List.map (fun k => nth_default 0%nat (@decompose m (S i) l) (2 * k)%nat) (seq 0%nat (Nat.pow 2 i)))
    end.

  Lemma zeta_powers_length (l i: nat):
    length (zeta_powers l i) = Nat.pow 2 i.
  Proof.
    induction i; [reflexivity|].
    simpl; rewrite length_app, length_map, length_seq, IHi.
    Lia.lia.
  Qed.

  Lemma decompose_zeta_powers_nth:
    forall i j k l, (S i <= j)%nat ->
               (k < Nat.pow 2 i)%nat ->
               exists v, nth_error (zeta_powers l j) (Nat.pow 2 i + k) = Some v /\
                    nth_error (@decompose m (S i) l) (2 * k)%nat = Some v.
  Proof.
    assert (IH: forall l j i, (S i <= j)%nat -> exists tl, zeta_powers l j = zeta_powers l i ++ (map (fun k : nat => nth_default 0%nat (@decompose m (S i) l) (2 * k)) (seq 0 (Nat.pow 2 i))) ++ tl).
    { induction j; intros i Hi; [Lia.lia|].
      assert (S i <= j \/ i = j) as [Hlt|<-] by Lia.lia.
      - simpl. destruct (IHj _ Hlt) as [tl Heq].
        rewrite Heq. repeat rewrite <- List.app_assoc.
        eexists; f_equal.
      - exists nil. rewrite List.app_nil_r. reflexivity. }
    intros i j k l Hj Hk.
    pose proof (zeta_powers_length l j) as Hlenj.
    pose proof (PeanoNat.Nat.pow_le_mono_r 2%nat _ _ ltac:(Lia.lia) Hj) as Hle.
    rewrite PeanoNat.Nat.pow_succ_r' in Hle.
    destruct (ListUtil.nth_error_length_exists_value (Nat.pow 2 i + k) (zeta_powers l j) ltac:(Lia.lia)) as [x Hx].
    eexists; split; eauto.
    destruct (IH l _ _ Hj) as [tl Heq].
    rewrite Heq, nth_error_app2 in Hx by (rewrite zeta_powers_length; Lia.lia).
    rewrite zeta_powers_length in Hx.
    rewrite nth_error_app1 in Hx by (rewrite length_map, length_seq; Lia.lia).
    rewrite nth_error_map in Hx.
    replace (Nat.pow 2 i + k - _)%nat with k in Hx by Lia.lia.
    rewrite ListUtil.nth_error_seq in Hx.
    destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [_|]; [|Lia.lia].
    rewrite PeanoNat.Nat.add_0_l in Hx. cbn [option_map] in Hx.
    erewrite ListUtil.nth_error_Some_nth_default; eauto.
    rewrite length_decompose, PeanoNat.Nat.pow_succ_r'. Lia.lia.
  Qed.

  Lemma decompose_nth:
    forall i k l,
      (2 * k + 1 < Nat.pow 2 i)%nat ->
      exists v, nth_error (@NTT.decompose m i l) (2 * k) = Some v /\
           nth_error (@NTT.decompose m i l) (2 * k + 1) = Some (Nat.pow 2 m + v)%nat.
  Proof.
    induction i; intros k l Hk.
    - rewrite PeanoNat.Nat.pow_0_r in Hk; Lia.lia.
    - cbn [NTT.decompose decompose_body].
      unfold decompose_body'.
      rewrite PeanoNat.Nat.pow_succ_r' in Hk.
      destruct (Decidable.dec_lt_nat (2 * k + 1) (Nat.pow 2 i)) as [Hlt|Hnlt].
      + rewrite nth_error_app1 by (rewrite length_decompose; Lia.lia).
        rewrite nth_error_app1 by (rewrite length_decompose; Lia.lia).
        apply IHi; auto.
      + destruct (Decidable.dec_lt_nat (Nat.pow 2 i) (2 * k + 1)) as [Hlt'|Hnlt'].
        * assert (Nat.pow 2 i <= 2 * k) as Hle by Lia.lia.
          rewrite nth_error_app2 by (rewrite length_decompose; Lia.lia).
          rewrite nth_error_app2 by (rewrite length_decompose; Lia.lia).
          rewrite length_decompose. destruct i; [simpl in *; Lia.lia|].
          rewrite PeanoNat.Nat.pow_succ_r' in *.
          assert (2 * k - 2 * Nat.pow 2 i = 2 * (k - Nat.pow 2 i))%nat as -> by Lia.lia.
          assert (2 * k + 1 - 2 * Nat.pow 2 i = 2 * (k - Nat.pow 2 i) + 1)%nat as -> by Lia.lia.
          apply IHi. Lia.lia.
        * assert (Nat.pow 2 i = 2 * k + 1)%nat as Heq by Lia.lia.
          clear -Heq Hk. destruct i.
          { simpl in *. assert (k = 0)%nat as -> by Lia.lia.
            simpl. eauto. }
          { assert (Nat.even (Nat.pow 2 (S i)) = true) as HX by (rewrite PeanoNat.Nat.even_pow by congruence; reflexivity).
            rewrite Heq, PeanoNat.Nat.even_odd in HX. congruence. }
  Qed.

  Lemma decompose_S_eq:
    forall i l,
      @NTT.decompose m (S i) l = flat_map (fun v => [Nat.div v 2; Nat.pow 2 m + Nat.div v 2]%nat) (@NTT.decompose m i l).
  Proof.
    induction i; intros; [reflexivity|].
    assert (decompose (S i) l = @decompose m i (Nat.div l 2) ++ @decompose m i (Nat.pow 2 m + Nat.div l 2))%nat as -> by reflexivity.
    rewrite flat_map_app. repeat rewrite <- IHi.
    reflexivity.
  Qed.

  Lemma decompose_mod:
    forall i, (i <= m)%nat ->
         forall x, In x (@NTT.decompose m i (Nat.pow 2 m)) ->
              (Nat.modulo x (Nat.pow 2 (m - i)) = 0)%nat.
  Proof.
    induction i; intros Hi p Hin.
    - cbn in Hin. destruct Hin as [<-|Hin]; [|elim Hin].
      rewrite PeanoNat.Nat.sub_0_r. apply PeanoNat.Nat.Div0.mod_same.
    - rewrite decompose_S_eq in Hin.
      apply In_nth_error in Hin. destruct Hin as [k Hin].
      cbn -[Nat.div] in Hin. eapply flat_map_constant_nth_error in Hin; [|simpl; reflexivity].
      destruct Hin as (n1 & (Hn1 & Hn2)).
      pose proof (IHi ltac:(Lia.lia) n1 ltac:(eapply nth_error_In; eauto)) as A.
      assert (m - i = S (m - S i))%nat as C by Lia.lia.
      rewrite C, PeanoNat.Nat.pow_succ_r' in A.
      assert (Nat.modulo (Nat.div n1 2) (Nat.pow 2 (m - S i)) = 0)%nat as Hmod1.
      { apply PeanoNat.Nat.Div0.div_exact.
        apply PeanoNat.Nat.Div0.div_exact in A.
        rewrite A at 1.
        assert (2 * _ * _ = (Nat.div n1 (2 * Nat.pow 2 (m - S i)) * Nat.pow 2 (m - S i)) * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.div_mul by congruence.
        rewrite <- PeanoNat.Nat.Div0.div_div. Lia.lia. }
      assert (Nat.modulo (Nat.pow 2 m + Nat.div n1 2) (Nat.pow 2 (m - S i)) = 0)%nat as Hmod2.
      { rewrite PeanoNat.Nat.Div0.add_mod, Hmod1.
        rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.Div0.mod_mod.
        assert (Nat.pow 2 m = Nat.pow 2 (S i) * Nat.pow 2 (m - S i))%nat as ->; [|apply PeanoNat.Nat.Div0.mod_mul].
        rewrite <- PeanoNat.Nat.pow_add_r. f_equal; Lia.lia. }
      assert (Nat.modulo k 2 = 0 \/ Nat.modulo k 2 = 1)%nat as X by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      destruct X as [X|X]; rewrite X in Hn2; cbn -[Nat.div] in Hn2; inversion Hn2; subst p; clear Hn2; auto.
  Qed.

  Lemma decompose_inv_nth:
    forall i, (i <= m)%nat ->
         forall k, (k < Nat.pow 2 i)%nat ->
              forall a b,
                nth_error (@NTT.decompose m i (Nat.pow 2 m)) k = Some a ->
                nth_error (@NTT.decompose m i (Nat.pow 2 m)) (Nat.pow 2 i - 1 - k) = Some b ->
                (a + b = Nat.pow 2 (S m))%nat.
  Proof.
    induction i; intros Hi k Hk a b Ha Hb.
    - destruct k; cbn in Ha, Hb, Hk; [|Lia.lia].
      inversion Ha; inversion Hb; subst a; subst b; clear Ha Hb.
      assert (_ + _ = 2 * Nat.pow 2 m)%nat as -> by Lia.lia.
      rewrite <- PeanoNat.Nat.pow_succ_r'. reflexivity.
    - rewrite decompose_S_eq in Ha, Hb.
      apply (flat_map_constant_nth_error 2%nat) in Ha, Hb; try reflexivity.
      destruct Ha as (ya & Hya & Ha). destruct Hb as (yb & Hyb & Hb).
      rewrite PeanoNat.Nat.pow_succ_r' in Hk.
      apply PeanoNat.Nat.Div0.div_lt_upper_bound in Hk.
      assert (Nat.modulo k 2 = 0 \/ Nat.modulo k 2 = 1)%nat as Hkmod by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      assert (Nat.div (Nat.pow 2 (S i) - 1 - k) 2 = Nat.pow 2 i - 1 - Nat.div k 2)%nat as Hdivk2.
      { rewrite (PeanoNat.Nat.div_mod_eq k 2) at 1.
        rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.sub_add_distr.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - 2 * PeanoNat.Nat.div k 2 - PeanoNat.Nat.modulo k 2 = 2 * (PeanoNat.Nat.pow 2 i - PeanoNat.Nat.div k 2 - 1) + (1 - PeanoNat.Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.div_add_l' by Lia.lia.
        rewrite (PeanoNat.Nat.div_small (1 - _)) by Lia.lia.
        Lia.lia. }
      rewrite Hdivk2 in Hyb.
      pose proof (IHi ltac:(Lia.lia) _ Hk _ _ Hya Hyb) as Hy.
      assert (PeanoNat.Nat.modulo (PeanoNat.Nat.pow 2 (S i) - 1 - k) 2 = 1 - Nat.modulo k 2)%nat as Hmodk2.
      { rewrite PeanoNat.Nat.pow_succ_r', (PeanoNat.Nat.div_mod_eq k 2) at 1.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - _ = 2 * (PeanoNat.Nat.pow 2 i - 1 - Nat.div k 2) + (1 - Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.mod_add_l' by Lia.lia.
        apply PeanoNat.Nat.mod_small. Lia.lia. }
      rewrite Hmodk2 in Hb.
      assert (Nat.div ya 2 + Nat.div yb 2 = Nat.pow 2 m)%nat as Hyab.
      { rewrite (PeanoNat.Nat.div_mod_eq ya 2) in Hy.
        rewrite (PeanoNat.Nat.div_mod_eq yb 2) in Hy.
        rewrite PeanoNat.Nat.pow_succ_r' in Hy.
        assert (2 * (Nat.div ya 2 + Nat.div yb 2) + Nat.modulo ya 2 + Nat.modulo yb 2 = 2 * Nat.pow 2 m)%nat as Hy2 by Lia.lia.
        apply nth_error_In in Hya, Hyb.
        pose proof (decompose_mod i ltac:(Lia.lia) _ Hya) as Hmodya.
        pose proof (decompose_mod i ltac:(Lia.lia) _ Hyb) as Hmodyb.
        assert (forall x y, 2 * x = 2 * y -> x = y)%nat as Z by Lia.lia; apply Z.
        rewrite <- Hy.
        assert (Nat.modulo ya 2 = 0)%nat as ->.
        { apply PeanoNat.Nat.Div0.mod_divides in Hmodya.
          destruct Hmodya as (? & ->). apply PeanoNat.Nat.Div0.mod_divides.
          assert (m - i = S (m - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_succ_r'. exists (Nat.pow 2 (m - S i) * x)%nat; Lia.lia. }
        assert (Nat.modulo yb 2 = 0)%nat as ->.
        { apply PeanoNat.Nat.Div0.mod_divides in Hmodyb.
          destruct Hmodyb as (? & ->). apply PeanoNat.Nat.Div0.mod_divides.
          assert (m - i = S (m - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_succ_r'. exists (Nat.pow 2 (m - S i) * x)%nat; Lia.lia. }
        Lia.lia. }
      assert (a + b = Nat.div ya 2 + Nat.div yb 2 + Nat.pow 2 m)%nat as ->.
      { destruct Hkmod as [e|e]; rewrite e in Ha, Hb; inversion Ha; inversion Hb; subst a; subst b; cbn in *; Lia.lia. }
      rewrite Hyab. rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia.
  Qed.

  Lemma decompose_S_nth:
    forall i k l,
      forall v, nth_error (@NTT.decompose m i l) k = Some v ->
           nth_error (@NTT.decompose m (S i) l) (2 * k) = Some (Nat.div v 2) /\
           nth_error (@NTT.decompose m (S i) l) (2 * k + 1) = Some (Nat.pow 2 m + Nat.div v 2)%nat.
  Proof.
    intros i k l v Hv. rewrite decompose_S_eq.
    pose proof (nth_error_Some_bound_index _ _ _ Hv) as Hk.
    rewrite length_decompose in Hk.
    assert (Hk': 2 * k + 1 < 2 * Nat.pow 2 i) by Lia.lia.
    assert (Nat.div (2 * k) 2 = k)%nat as X1 by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 0); Lia.lia).
    assert (Nat.div (2 * k + 1) 2 = k)%nat as X2 by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 1); Lia.lia).
    split.
    all: match goal with
         | |- nth_error ?ll ?ii = _ =>
             assert (Hll: (length ll = 2 * Nat.pow 2 i)%nat) by (rewrite (flat_map_const_length _ 2%nat) by reflexivity; rewrite length_decompose; reflexivity);
             destruct (ListUtil.nth_error_length_exists_value ii ll ltac:(Lia.lia)) as [v' Hv'];
             rewrite Hv';
             apply (flat_map_constant_nth_error 2%nat) in Hv'; try reflexivity;
             destruct Hv' as (y & Hy & <-);
             assert (y = v) as -> by congruence
         end.
    - rewrite (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.Div0.mod_mul.
      reflexivity.
    - assert (Nat.modulo _ _ = 1)%nat as ->; [|reflexivity].
      symmetry; apply (PeanoNat.Nat.mod_unique _ 2 k 1); Lia.lia.
  Qed.

  Definition zetas (l i: nat) := List.map (fun k => F.pow zeta (N.of_nat k)) (zeta_powers l i).

End Zetas.

Section Gallina.
  (* Lower-level Gallina code for implementing (inverse) NTT *)

  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q).
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
  Context {P} {poly_ops: @Polynomial.polynomial_ops F P}.
  Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  Local Notation nttl' := (@nttl' q field P poly_ops poly_defs zeta m Hm).
  Local Notation nttl := (@nttl q field P poly_ops poly_defs zeta m Hm).
  Local Notation Pmod_cyclotomic_list := (@PolynomialCRT.Pmod_cyclotomic_list F F.zero F.add F.sub F.mul).
  Local Notation inttl' := (@inttl' q field P poly_ops poly_defs zeta m Hm).
  Local Notation inttl := (@inttl q field P poly_ops poly_defs zeta m Hm).
  Local Notation recompose_cyclotomic_list := (@PolynomialCRT.recompose_cyclotomic_list F F.zero F.add F.sub F.mul).

  Section Unopt.
    (* No optimization *)

    Fixpoint nttl_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
          let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) p in
          (nttl_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p')) ++
          (nttl_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p'))
      end.

    Lemma nttl_gallina_spec:
      forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) p,
        proj1_sig (nttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l p) = nttl_gallina r k l (proj1_sig p).
    Proof.
      induction r; intros.
      - reflexivity.
      - cbn -[ntt_bodyl]. cbn [ntt_bodyl].
        erewrite proj1_sig_ntt_bodyl_eq; eauto.
    Qed.

    Fixpoint inttl_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
          map (F.mul (F.inv (1 + 1)))
            (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2)))
               ((inttl_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p)) ++
                (inttl_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p))))
      end.

    Lemma inttl_gallina_spec:
      forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) p,
        proj1_sig (inttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l p) = inttl_gallina r k l (proj1_sig p).
    Proof.
      induction r; intros.
      - reflexivity.
      - cbn -[F.inv Nat.div intt_bodyl].
        unfold intt_bodyl.
        erewrite proj1_sig_intt_bodyl_eq; eauto.
        apply length_decompose.
    Qed.
  End Unopt.

  Section Delayed_mul.
    (* Delay the multiplications by F.inv (1 + 1) to the end for the inverse ntt *)
    Fixpoint inttl_nomul_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
            (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2)))
               ((inttl_nomul_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p)) ++
                  (inttl_nomul_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p))))
      end.

    Lemma inttl_nomul_gallina_length:
      forall r k l p,
        length (inttl_nomul_gallina r k l p) = length p.
    Proof.
      induction r; [reflexivity|].
      intros; cbn [inttl_nomul_gallina].
      rewrite PolynomialCRT.recompose_cyclotomic_list_length.
      rewrite length_app, IHr, IHr.
      rewrite <- length_app, firstn_skipn. reflexivity.
    Qed.

    Lemma inttl_nomul_gallina_spec:
      forall r k l p (Hr_leq_k: (r <= k)%nat) (Hp: length p >= Nat.pow 2 k),
        inttl_gallina r k l p = List.map (F.mul (F.inv (F.pow (1 + 1) r))) (inttl_nomul_gallina r k l p).
    Proof.
      induction r; intros.
      - rewrite (map_ext _ (fun x => x)), map_id; [reflexivity|].
        intro. rewrite F.pow_0_r, Hierarchy.commutative, <- Hierarchy.field_div_definition.
        apply Field.div_one.
      - cbn [inttl_gallina inttl_nomul_gallina].
        assert (Hp': length p >= 2 * Nat.pow 2 (k - 1)) by (rewrite <- PeanoNat.Nat.pow_succ_r'; assert (S (k - 1) = k) as -> by Lia.lia; assumption).
        rewrite IHr by (try rewrite length_firstn; Lia.lia).
        rewrite IHr by (try rewrite length_skipn; Lia.lia).
        rewrite <- map_app.
        match goal with
        | |- context [recompose_cyclotomic_list ?k ?a (map ?f ?l)] =>
            assert (recompose_cyclotomic_list k a (map f l) = map f (recompose_cyclotomic_list k a l)) as ->
        end; [|rewrite map_map; apply map_ext].
        2:{ intros. rewrite Hierarchy.associative. f_equal.
            apply Field.left_inv_unique.
            assert (N.of_nat (S r) = N.succ (N.of_nat r)) as -> by Lia.lia.
            rewrite F.pow_succ_r.
            rewrite (Hierarchy.commutative (1 + 1)), Hierarchy.associative, <- (Hierarchy.associative (F.inv (1 + 1))), Hierarchy.left_multiplicative_inverse, Hierarchy.right_identity, Hierarchy.left_multiplicative_inverse; auto.
            - pose proof (char_ge_3 (BinNums.xO BinNums.xH) ltac:(cbv; reflexivity)) as Hchar.
              simpl in Hchar. rewrite Hierarchy.left_identity in Hchar. exact Hchar.
            - clear -field char_ge_3. induction r.
              + rewrite F.pow_0_r. symmetry.
                apply Hierarchy.integral_domain_is_zero_neq_one.
              + assert (N.of_nat (S r) = N.succ (N.of_nat r)) as -> by Lia.lia.
                rewrite F.pow_succ_r. intro X.
                apply Hierarchy.integral_domain_is_zero_product_zero_factor in X.
                destruct X; [|contradiction].
                pose proof (char_ge_3 (BinNums.xO BinNums.xH) ltac:(cbv; reflexivity)) as Hchar.
                simpl in Hchar. rewrite Hierarchy.left_identity in Hchar. contradiction. }
        assert (X: forall (A: Type) (l1 l2: list A), Forall2 eq l1 l2 -> l1 = l2); [|apply X].
        { induction 1; simpl; congruence. }
        rewrite ListUtil.Forall2_forall_iff by (rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_map, length_map, PolynomialCRT.recompose_cyclotomic_list_length; reflexivity).
        rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_map. intros.
        rewrite ListUtil.map_nth_default_always.
        rewrite PolynomialCRT.recompose_cyclotomic_list_nth_default by (rewrite length_map, length_app, inttl_nomul_gallina_length, inttl_nomul_gallina_length, <- length_app, firstn_skipn; assumption).
        rewrite PolynomialCRT.recompose_cyclotomic_list_nth_default by (rewrite length_app, inttl_nomul_gallina_length, inttl_nomul_gallina_length, <- length_app, firstn_skipn; assumption).
        repeat rewrite ListUtil.map_nth_default_always.
        assert (0 = F.mul (F.inv ((1 + 1) ^ N.of_nat r)) 0) as -> by (rewrite Ring.mul_0_r; reflexivity).
        repeat rewrite ListUtil.map_nth_default_always.
        assert (F.mul (F.inv ((1 + 1) ^ N.of_nat r)) 0 = 0) as -> by (rewrite Ring.mul_0_r; reflexivity).
        destruct (Decidable.dec_lt_nat i _).
        + cbn zeta. rewrite <- Hierarchy.left_distributive. reflexivity.
        + destruct (Decidable.dec_lt_nat i _); [|reflexivity].
          cbn zeta. rewrite <- Hierarchy.left_distributive.
          repeat rewrite Hierarchy.associative. rewrite (Hierarchy.commutative (F.inv _) (F.inv _)). reflexivity.
          Unshelve. exact 0.
    Qed.
  End Delayed_mul.

  Section PrecomputedZetas.
    (* Use precomputed zetas *)
    Variable (precomp_zetas: list F).
    Hypothesis (precomp_zetas_eq: precomp_zetas = @zetas q zeta m (Nat.pow 2 m) m).

    Section Forward.
      Fixpoint nttl_precomp (r k u v: nat) (p: list F) :=
        match r with
        | O => p
        | S r' =>
            let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (nth_default 0%F precomp_zetas (Nat.pow 2 u + v)) p in
            (nttl_precomp r' (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p')) ++
            (nttl_precomp r' (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p'))
        end.

      Lemma nttl_precomp_length:
        forall r k u v p,
          length (nttl_precomp r k u v p) = length p.
      Proof.
        induction r; [reflexivity|].
        intros k u v p. cbn.
        rewrite length_app, IHr, IHr, <- length_app, firstn_skipn, PolynomialCRT.Pmod_cyclotomic_list_length.
        reflexivity.
      Qed.

      Lemma nttl_precomp_spec:
        forall r k u v l p,
          (r + u <= m) ->
          (v < Nat.pow 2 u) ->
          nth_default 0%nat (@NTT.decompose m u (Nat.pow 2 m)) v = l ->
          nttl_precomp r k u v p = nttl_gallina r k l p.
      Proof.
        induction r; [reflexivity|].
        cbn -[decompose Nat.div Nat.mul]; intros k u v l p Hru Hv Heq.
        pose proof (ListUtil.nth_error_Some_nth_default v 0%nat (@decompose m u (Nat.pow 2 m)) ltac:(rewrite length_decompose; assumption)) as Hl.
        rewrite Heq in Hl.
        pose proof (@decompose_S_nth m u v (Nat.pow 2 m) l Hl) as (Hll & Hlr).
        rewrite precomp_zetas_eq; unfold zetas.
        assert (Hlt: Nat.pow 2 u + v < Nat.pow 2 m).
        { apply (PeanoNat.Nat.lt_le_trans _ (Nat.pow 2 (S u))).
          - rewrite PeanoNat.Nat.pow_succ_r'.
            Lia.lia.
          - apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
        rewrite (ListUtil.map_nth_default _ _ _ _ 0%nat) by (rewrite zeta_powers_length; auto).
        destruct (@decompose_zeta_powers_nth m u m v (Nat.pow 2 m) ltac:(Lia.lia) Hv) as (x & Hx1 & Hx2).
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx1).
        assert (x = Nat.div l 2) as -> by congruence.
        assert (Hv': 2 * v + 1 < Nat.pow 2 (S u)) by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        f_equal; apply IHr; try Lia.lia.
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hll).
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hlr).
      Qed.

      Lemma nttl_precomp_S_eq:
        forall r k u v p,
          (S r <= k)%nat ->
          length p = Nat.pow 2 k ->
          nttl_precomp (S r) k u v p =
          concat
            (map (fun '(i, chk) => Pmod_cyclotomic_list (Nat.pow 2 (k - S r)) (nth_default 0%F precomp_zetas (Nat.pow 2 (u + r) + i)) chk)
               (enumerate ((Nat.pow 2 r) * v) (chunk (Nat.pow 2 (k - r)) (nttl_precomp r k u v p)))).
      Proof.
        induction r; intros k u v p Hr_leq_l Hlength.
        - cbn -[chunk]. rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r.
          pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)) as Hnz.
          rewrite chunk_small by Lia.lia.
          cbn. rewrite app_nil_r, firstn_skipn, PeanoNat.Nat.add_0_r. reflexivity.
        - assert (nttl_precomp (S (S r)) k u v p = let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (nth_default 0%F precomp_zetas (Nat.pow 2 u + v)) p in
            (nttl_precomp (S r) (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p')) ++
            (nttl_precomp (S r) (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p'))) as -> by reflexivity.
          assert (Nat.pow 2 k = 2 * (Nat.pow 2 (k - 1)))%nat as Hlength' by (rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia).
          cbn zeta. rewrite (IHr (k - 1)%nat), (IHr (k - 1)%nat); try Lia.lia.
          2: rewrite length_skipn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength; Lia.lia.
          2: rewrite length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength, PeanoNat.Nat.min_l by Lia.lia; reflexivity.
          rewrite <- concat_app, <- map_app.
          match goal with
          | |- context [enumerate _ ?l ++ enumerate _ _] =>
              assert (Nat.pow 2 r * (2 * v + 1) = (Nat.pow 2 r * (2 * v)) + length l)%nat as ->
          end.
          { rewrite length_chunk by (apply NatUtil.pow_nonzero; Lia.lia).
            rewrite nttl_precomp_length, length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength.
            rewrite PeanoNat.Nat.min_l by Lia.lia.
            assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * Nat.pow 2 (k - 1 - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
            rewrite Nat.div_up_exact by (apply NatUtil.pow_nonzero; Lia.lia). Lia.lia. }
          rewrite <- enumerate_app, <- chunk_app.
          2: apply NatUtil.pow_nonzero; congruence.
          2:{ rewrite nttl_precomp_length, length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength, PeanoNat.Nat.min_l by Lia.lia.
              assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * Nat.pow 2 (k - 1 - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
              apply PeanoNat.Nat.Div0.mod_mul. }
          f_equal. match goal with | |- map ?f ?x = map ?g ?y => assert (x = y) as -> end.
          { f_equal.
            - rewrite PeanoNat.Nat.mul_assoc, (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'; reflexivity.
            - assert (k - 1 - r = k - S r)%nat as -> by Lia.lia.
              reflexivity. }
          apply map_ext; intros.
          assert (k - 1 - (S r) = k - S (S r))%nat as -> by Lia.lia.
          assert (S u + r = u + S r)%nat as -> by Lia.lia.
          reflexivity.
      Qed.
    End Forward.
    Section Backward.
      Fixpoint inttl_precomp (r k u v: nat) (p: list F) :=
        match r with
        | O => p
        | S r' =>
            recompose_cyclotomic_list
              (Nat.pow 2 (k - 1))
              (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u) - 1 - v)))
              ((inttl_precomp r' (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p)) ++
               (inttl_precomp r' (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p)))
        end.

      Lemma inttl_precomp_length:
        forall r k u v p,
          length (inttl_precomp r k u v p) = length p.
      Proof.
        induction r; [reflexivity|].
        intros k u v p. cbn.
        rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_app, IHr, IHr, <- length_app, firstn_skipn.
        reflexivity.
      Qed.

      Lemma inttl_precomp_spec:
        forall r k u v l p,
          (r + u <= m) ->
          (v < Nat.pow 2 u) ->
          nth_default 0%nat (@NTT.decompose m u (Nat.pow 2 m)) v = l ->
          inttl_precomp r k u v p = inttl_nomul_gallina r k l p.
      Proof.
        induction r; [reflexivity|].
        cbn -[decompose Nat.div Nat.mul F.inv]; intros k u v l p Hru Hv Heq.
        pose proof (ListUtil.nth_error_Some_nth_default v 0%nat (@decompose m u (Nat.pow 2 m)) ltac:(rewrite length_decompose; assumption)) as Hl.
        rewrite Heq in Hl.
        destruct (ListUtil.nth_error_length_exists_value (Nat.pow 2 (S u) - 1 - (2 * v)) (@decompose m (S u) (Nat.pow 2 m)) ltac:(rewrite length_decompose, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as (b & Hb).
        pose proof (@decompose_S_nth m u v (Nat.pow 2 m) l Hl) as (Hll & Hlr).
        pose proof (@decompose_inv_nth m (S u) ltac:(Lia.lia) (2 * v) ltac:(rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia) _ _ Hll Hb) as Hlb.
        assert (F.inv _ = F.pow zeta (N.of_nat b)) as ->.
        { symmetry; apply Field.right_inv_unique.
          rewrite <- F.pow_add_r, <- Nnat.Nat2N.inj_add, Hlb, Nnat.Nat2N.inj_pow.
          assert (N.of_nat _ ^ _ = 2 ^ N.succ (N.of_nat m))%N as -> by Lia.lia.
          apply (zeta_pow_succ_m (Hm:=Hm)). }
        rewrite precomp_zetas_eq; unfold zetas.
        assert (Hlt: 2 * Nat.pow 2 u - 1 - v < Nat.pow 2 m).
        { apply (PeanoNat.Nat.lt_le_trans _ (Nat.pow 2 (S u))).
          - rewrite PeanoNat.Nat.pow_succ_r'.
            Lia.lia.
          - apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
        rewrite (ListUtil.map_nth_default _ _ _ _ 0%nat) by (rewrite zeta_powers_length; Lia.lia).
        destruct (@decompose_zeta_powers_nth m u m (Nat.pow 2 u - 1 - v) (Nat.pow 2 m) ltac:(Lia.lia) ltac:(Lia.lia)) as (x & Hx1 & Hx2).
        assert (2 * Nat.pow 2 u - 1 - v = Nat.pow 2 u + (Nat.pow 2 u - 1 - v))%nat as -> by Lia.lia.
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx1).
        destruct (@decompose_nth m (S u) (Nat.pow 2 u - 1 - v)%nat (Nat.pow 2 m) ltac:(rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia)) as (? & Hv1 & Hv2).
        rewrite Hv1 in Hx2; inversion Hx2; subst x; clear Hx2.
        replace (Nat.pow 2 (S u) - 1 - 2 * v)%nat with (2 * (Nat.pow 2 u - 1 - v) + 1)%nat in Hb by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        rewrite Hb in Hv2; inversion Hv2; subst b; clear Hv2.
        rewrite (@neg_zeta_power_eq q _ zeta m Hm).
        rewrite Nnat.Nat2N.inj_add, Nnat.Nat2N.inj_pow.
        assert (Hv': 2 * v + 1 < Nat.pow 2 (S u)) by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        f_equal. f_equal; apply IHr; try Lia.lia.
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hll).
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hlr).
      Qed.

      Lemma inttl_precomp_S_eq:
        forall r k u v p,
          (S r <= k)%nat ->
          length p = Nat.pow 2 k ->
          inttl_precomp (S r) k u v p =
          inttl_precomp r k u v
            (concat
               (map (fun '(i, chk) => recompose_cyclotomic_list (Nat.pow 2 (k - S r)) (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u + r) - 1 - i))) chk)
                  (enumerate ((Nat.pow 2 r) * v) (chunk (Nat.pow 2 (k - r)) p)))).
      Proof.
        induction r; intros k u v p Hr Hp.
        - rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.sub_0_r, PeanoNat.Nat.pow_0_r, PeanoNat.Nat.mul_1_l.
          cbn [inttl_precomp]. pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)) as Hnz.
          rewrite chunk_small by Lia.lia.
          rewrite firstn_skipn.
          cbn -[Nat.pow]. rewrite app_nil_r. reflexivity.
        - assert (inttl_precomp (S (S r)) k u v p = recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u) - 1 - v))) ((inttl_precomp (S r) (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p)) ++ (inttl_precomp (S r) (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p)))) as -> by reflexivity.
          assert (length (firstn (Nat.pow 2 (k - 1)) p) = Nat.pow 2 (k - 1))%nat as Hlenl.
          { rewrite length_firstn, PeanoNat.Nat.min_l; [reflexivity|].
            rewrite Hp. apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          assert (length (skipn (Nat.pow 2 (k - 1)) p) = Nat.pow 2 (k - 1))%nat as Hlenr.
          { rewrite length_skipn, Hp. assert (Nat.pow 2 k = 2 * Nat.pow 2 (k - 1))%nat; [|Lia.lia].
            rewrite <- PeanoNat.Nat.pow_succ_r'. f_equal. Lia.lia. }
          rewrite (IHr (k - 1)%nat), (IHr (k - 1)%nat) by Lia.lia.
          cbn [inttl_precomp]. f_equal.
          assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * (Nat.pow 2 (k - 1 - r)))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
          rewrite <- firstn_chunk by (apply NatUtil.pow_nonzero; congruence).
          rewrite <- skipn_chunk by (apply NatUtil.pow_nonzero; congruence).
          rewrite <- firstn_enumerate, <- firstn_map.
          assert (Nat.pow 2 r * (2 * v + 1) = Nat.pow 2 r * (2 * v) + Nat.pow 2 r)%nat as -> by Lia.lia.
          rewrite <- skipn_enumerate, <- skipn_map.
          assert (k - 1 - r = k - (S r))%nat as -> by Lia.lia.
          assert (k - 1 - S r = k - S (S r))%nat as -> by Lia.lia.
          assert (Nat.pow 2 r * (2 * v) = Nat.pow 2 (S r) * v)%nat as -> by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
          assert (S (S u) + r = S u + S r)%nat as -> by Lia.lia.
          assert (Forall (fun x : list F => length x = Nat.pow 2 (k - S r)) (map (fun '(i, chk) => recompose_cyclotomic_list (Nat.pow 2 (k - S (S r))) (F.opp (nth_default 0 precomp_zetas (Nat.pow 2 (S u + S r) - 1 - i))) chk) (enumerate (Nat.pow 2 (S r) * v) (chunk (Nat.pow 2 (k - S r)) p)))) as HF.
          { apply Forall_map. rewrite Forall_forall.
            intros x Hx. destruct x as (x & y). apply in_combine_r in Hx.
            rewrite PolynomialCRT.recompose_cyclotomic_list_length.
            apply In_nth_error in Hx. destruct Hx as [i Hi].
            pose proof (nth_error_Some_bound_index _ _ _ Hi) as Hlen.
            rewrite length_chunk in Hlen by (apply NatUtil.pow_nonzero; congruence).
            rewrite (nth_error_chunk (Nat.pow 2 _) ltac:(apply NatUtil.pow_nonzero; Lia.lia) _ _ Hlen) in Hi.
            inversion Hi; subst y. rewrite length_firstn, length_skipn, Hp.
            rewrite Hp in Hlen. apply PeanoNat.Nat.min_l.
            replace (Nat.pow 2 k) with (Nat.pow 2 (S r) * Nat.pow 2 (k - S r))%nat in * by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
            rewrite Nat.div_up_exact in Hlen by (apply NatUtil.pow_nonzero; Lia.lia).
            Lia.nia. }
          symmetry; f_equal; f_equal; [apply firstn_concat_same_length|apply skipn_concat_same_length]; auto.
      Qed.
    End Backward.
  End PrecomputedZetas.

  Section Loops.
    (* Gallina code closer to loops *)

    (* [fold_left f (seq start len) state] is roughly equivalent to
       [for (i = start; i < start + len; i++) { f i; }]
       where [f] transforms the state *)

    (* Assume we have a precomputed array of powers of zeta *)
    Variable (precomp_zetas: list F).
    Hypothesis (precomp_zetas_eq: precomp_zetas = @zetas q zeta m (Nat.pow 2 m) m).

    Section ForwardNTT.
      (* Decompose one polynomial of size [2 * len] *)
      Definition polynomial_decompose_loop (start len: nat) (z: F) (p: list F) :=
        List.fold_left
          (fun (p: list F) (i: nat) =>
             let t0 := nth_default 0 p (i + len) in
             let t1 := z * t0 in
             let t2 := nth_default 0 p i in
             let p' := ListUtil.set_nth (i + len) (t2 - t1) p in
             ListUtil.set_nth i (t2 + t1) p')
          (seq start len)
          p.

      Lemma polynomial_decompose_loop_spec:
        forall start len z p,
          polynomial_decompose_loop start len z p = (firstn start p) ++ Pmod_cyclotomic_list len z (skipn start p).
      Proof.
        intros. destruct (Decidable.dec_le_nat (length p) start).
        - rewrite firstn_all2 by Lia.lia.
          rewrite skipn_all by Lia.lia.
          assert (Pmod_cyclotomic_list _ _ _ = nil) as ->.
          { apply ListUtil.length0_nil.
            rewrite PolynomialCRT.Pmod_cyclotomic_list_length. reflexivity. }
          rewrite app_nil_r.
          unfold polynomial_decompose_loop.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k, fold_left f (seq start k) p = p) as ->; [|reflexivity]
          end.
          induction k.
          + reflexivity.
          + rewrite seq_S, fold_left_app, IHk.
            cbn. apply nth_error_ext. intro i.
            do 2 rewrite ListUtil.nth_set_nth.
            rewrite ListUtil.length_set_nth.
            destruct (Compare_dec.lt_dec i (length p)).
            * do 2 (destruct (PeanoNat.Nat.eq_dec _ _); [Lia.lia|]).
              reflexivity.
            * repeat rewrite ListUtil.nth_error_length_error by Lia.lia.
              repeat (destruct (PeanoNat.Nat.eq_dec _ _)); reflexivity.
        - unfold polynomial_decompose_loop, Pmod_cyclotomic_list.
          apply nth_error_ext; intros i.
          destruct (Decidable.dec_lt_nat i start).
          + rewrite nth_error_app1 by (rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            rewrite nth_error_firstn by assumption.
            match goal with
            | |- context [fold_left ?f _ _] =>
                assert (forall k, nth_error (fold_left f (seq start k) p) i = nth_error p i) as ->; [|reflexivity]
            end.
            induction k; [reflexivity|].
            rewrite seq_S, fold_left_app.
            cbn [fold_left].
            repeat rewrite ListUtil.nth_set_nth.
            repeat rewrite ListUtil.length_set_nth.
            destruct (PeanoNat.Nat.eq_dec i _); [Lia.lia|].
            destruct (PeanoNat.Nat.eq_dec i _); [Lia.lia|].
            apply IHk.
          + rewrite nth_error_app2 by (rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
            match goal with
            | |- nth_error (fold_left ?f _ _) i = nth_error (fold_left ?g _ _) _ =>
                assert (forall k i, (i >= start) -> nth_error (fold_left f (seq start k) p) i = nth_error (fold_left g (seq 0 k) (skipn start p)) (i - start)) as ->; [|reflexivity|Lia.lia]
            end.
            clear. induction k; intros i Hi.
            * cbn. rewrite nth_error_skipn. f_equal; Lia.lia.
            * do 2 (rewrite seq_S, fold_left_app).
              rewrite PeanoNat.Nat.add_0_l.
              cbn [fold_left].
              repeat rewrite ListUtil.nth_set_nth.
              repeat rewrite ListUtil.length_set_nth.
              pose proof (IHk (start + k)%nat ltac:(Lia.lia)) as IHk1.
              pose proof (IHk (start + k + len)%nat ltac:(Lia.lia)) as IHk2.
              match goal with
              | |- context [length (fold_left ?f ?l ?x)] =>
                  assert (length (fold_left f l x) = length x) as Hl1
              end; [|rewrite Hl1].
              { clear; induction k; [reflexivity|].
                rewrite seq_S, fold_left_app.
                cbn [fold_left]. repeat rewrite ListUtil.length_set_nth.
                rewrite IHk. reflexivity. }
              match goal with
              | |- context [length (fold_left ?f ?l ?x)] =>
                  assert (length (fold_left f l x) = length x) as Hl2
              end; [|rewrite Hl2].
              { clear; induction k; [reflexivity|].
                rewrite seq_S, fold_left_app.
                cbn [fold_left]. repeat rewrite ListUtil.length_set_nth.
                rewrite IHk. reflexivity. }
              rewrite length_skipn.
              replace (start + k - start)%nat with k in IHk1 by Lia.lia.
              replace (start + k + len - start)%nat with (k + len)%nat in IHk2 by Lia.lia.
              destruct (PeanoNat.Nat.eq_dec i (start + k)) as [->|].
              { destruct (PeanoNat.Nat.eq_dec _ _) as [->|]; [|Lia.lia].
                do 2 (destruct (Compare_dec.lt_dec _ _)); try Lia.lia; auto.
                f_equal.
                rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl1; auto).
                rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl2, length_skipn; auto).
                f_equal; try congruence.
                f_equal.
                destruct (Compare_dec.lt_dec (start + k + len) (length p)).
                - rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl1; auto).
                  rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl2, length_skipn; Lia.lia).
                  congruence.
                - rewrite ListUtil.nth_default_out_of_bounds by (rewrite Hl1; Lia.lia).
                  rewrite ListUtil.nth_default_out_of_bounds by (rewrite Hl2, length_skipn; Lia.lia).
                  reflexivity. }
              destruct (PeanoNat.Nat.eq_dec (i - start) k); [Lia.lia|].
              destruct (PeanoNat.Nat.eq_dec i _); destruct (PeanoNat.Nat.eq_dec (i - start) _); try Lia.lia; [|apply IHk; Lia.lia].
              do 2 (destruct (Compare_dec.lt_dec _ _)); try Lia.lia; auto.
              f_equal.
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl1; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl2, length_skipn; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl1; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl2, length_skipn; Lia.lia).
              congruence.
      Qed.

      (* One layer decomposition *)
      Definition polynomial_list_loop (k old_len len: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state _ =>
             let '(l, start, p) := state in
             let l := (l + 1)%nat in
             let z := nth_default 0 precomp_zetas l in
             let p := polynomial_decompose_loop start len z p in
             let start := (start + old_len)%nat in
             (l, start, p))
          (seq 0 k)
          state.

      Lemma polynomial_list_loop_spec:
        forall k old_len len l start p,
          (0 < 2 * len <= old_len)%nat ->
          (start + k * old_len <= length p) ->
          polynomial_list_loop k old_len len (l, start, p) = (l + k, start + k * old_len, firstn start p ++ concat (map (fun '(i, chk) => Pmod_cyclotomic_list len (nth_default 0%F precomp_zetas (l + 1 + i)) chk) (enumerate 0 (firstn k (chunk old_len (skipn start p))))) ++ skipn (start + k * old_len) p)%nat.
      Proof.
        unfold polynomial_list_loop.
        induction k; intros old_len len l start p Hold_len Hp.
        - cbn. repeat rewrite PeanoNat.Nat.add_0_r.
          rewrite firstn_skipn. reflexivity.
        - rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l.
          cbn [fold_left].
          rewrite IHk by Lia.lia.
          rewrite polynomial_decompose_loop_spec.
          f_equal; [f_equal; Lia.lia|].
          rewrite firstn_app, firstn_firstn.
          rewrite PeanoNat.Nat.min_r by Lia.lia.
          rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          rewrite skipn_app, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * old_len - start = k * old_len)%nat as -> by Lia.lia.
          rewrite (skipn_all (start + k * old_len) (firstn _ _)) by (rewrite length_firstn; Lia.lia).
          rewrite app_nil_l. rewrite firstn_app.
          assert (k < (length (chunk old_len (skipn start p))))%nat as Hk.
          { rewrite length_chunk, length_skipn by Lia.lia.
            apply (PeanoNat.Nat.lt_le_trans _ (Nat.div_up (S k * old_len) old_len)).
            - rewrite Nat.div_up_exact by Lia.lia. Lia.lia.
            - apply PeanoNat.Nat.Div0.div_le_mono. Lia.lia. }
          match goal with | |- context [length (concat ?l)] => assert (length (concat l) = k * old_len)%nat as Hco end.
          { rewrite length_concat.
            assert (forall c l, (forall x, In x l -> x = c) -> list_sum l = c * length l)%nat as Hl.
            { clear. induction l; intros; simpl.
              - rewrite PeanoNat.Nat.mul_0_r. reflexivity.
              - rewrite IHl by (intros; apply H; right; auto).
                rewrite (H a ltac:(left; reflexivity)). Lia.lia. }
            rewrite (Hl old_len).
            2:{ intros x Hx. rewrite in_map_iff in Hx.
                destruct Hx as (y & Hy & Hin).
                subst x. rewrite in_map_iff in Hin.
                destruct Hin as ((i & chk) & Hz & Hzz).
                subst y. rewrite PolynomialCRT.Pmod_cyclotomic_list_length.
                apply in_combine_r in Hzz.
                rewrite firstn_chunk in Hzz by Lia.lia.
                apply In_nth_error in Hzz. destruct Hzz as (j & Hj).
                pose proof (ListUtil.nth_error_value_length _ _ _ _ Hj) as Hjj.
                rewrite length_chunk in Hjj by Lia.lia.
                rewrite (nth_error_chunk old_len ltac:(Lia.lia) _ _ Hjj) in Hj.
                inversion Hj; subst chk; clear Hj.
                rewrite length_firstn, length_skipn, length_firstn, length_skipn.
                rewrite (PeanoNat.Nat.min_l (k * _)) by Lia.lia.
                rewrite length_firstn, length_skipn in Hjj.
                rewrite PeanoNat.Nat.min_l in Hjj by Lia.lia.
                rewrite Nat.div_up_exact in Hjj by Lia.lia.
                apply PeanoNat.Nat.min_l.
                rewrite <- PeanoNat.Nat.mul_sub_distr_r.
                transitivity (1 * old_len)%nat; try Lia.lia.
                apply PeanoNat.Nat.mul_le_mono_r. Lia.lia. }
            rewrite length_map, length_map.
            unfold enumerate. rewrite length_combine, length_seq, PeanoNat.Nat.min_id.
            rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia. }
          rewrite Hco, PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
          rewrite (ListUtil.firstn_all (k * old_len)) by Lia.lia.
          rewrite skipn_app. rewrite Hco, PeanoNat.Nat.sub_diag, skipn_O.
          rewrite (skipn_all (k * old_len)) by Lia.lia.
          rewrite app_nil_l. rewrite (ListUtil.firstn_succ nil) by Lia.lia.
          rewrite enumerate_app, length_firstn.
          rewrite PeanoNat.Nat.min_l by Lia.lia.
          rewrite map_app, concat_app. repeat rewrite <- app_assoc. f_equal.
          f_equal. cbn. assert (l + k + 1 = l + S k)%nat as -> by Lia.lia.
          rewrite app_nil_r, (nth_default_eq _ _ nil).
          rewrite length_chunk in Hk by Lia.lia.
          rewrite nth_chunk by Lia.lia.
          rewrite skipn_skipn. assert (start + k * old_len = k * old_len + start)%nat as <- by Lia.lia.
          assert (forall n1 n2 a l, (2 * n1 <= n2)%nat -> Pmod_cyclotomic_list n1 a l = Pmod_cyclotomic_list n1 a (firstn n2 l) ++ (skipn n2 l)) as X.
          { clear. unfold Pmod_cyclotomic_list.
            set (f a n1 := (fun (l0 : list F) (i : nat) => ListUtil.set_nth i (nth_default 0 l0 i + a * nth_default 0 l0 (i + n1)) (ListUtil.set_nth (i + n1) (nth_default 0 l0 i - a * nth_default 0 l0 (i + n1)) l0))).
            assert (forall k n1 n2 a l, (k <= n1)%nat -> (2 * n1 <= n2)%nat -> fold_left (f a n1) (seq 0 k) l = fold_left (f a n1) (seq 0 k) (firstn n2 l) ++ skipn n2 l) as X; [|intros; apply X; auto].
            induction k; intros n1 n2 a l Hk Hl.
            - cbn. rewrite firstn_skipn. reflexivity.
            - destruct (Decidable.dec_lt_nat n2 (length l)) as [Hlt|Hnlt].
              + rewrite seq_S, fold_left_app, fold_left_app, PeanoNat.Nat.add_0_l.
                rewrite (IHk n1 n2) by Lia.lia. cbn. unfold f.
                repeat rewrite ListUtil.nth_default_app.
                assert (length (fold_left (f a n1) (seq 0 k) (firstn n2 l)) = length (firstn n2 l)) as Y; [|unfold f in Y; repeat rewrite Y].
                { clear. induction k; [reflexivity|].
                  rewrite seq_S, fold_left_app.
                  simpl; unfold f in *; repeat rewrite ListUtil.length_set_nth. auto. }
                rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
                destruct (Compare_dec.lt_dec _ n2); [|Lia.lia].
                destruct (Compare_dec.lt_dec _ n2); [|Lia.lia].
                assert (forall A k (x: A) l1 l2, (k < length l1) -> ListUtil.set_nth k x (l1 ++ l2) = ListUtil.set_nth k x l1 ++ l2) as Z; [|repeat rewrite Z; auto; [rewrite ListUtil.length_set_nth|]; rewrite Y, length_firstn; Lia.lia].
                clear. intros.
                apply nth_error_ext; intros.
                rewrite ListUtil.nth_set_nth, nth_error_app, nth_error_app, length_app, ListUtil.length_set_nth, ListUtil.nth_set_nth.
                destruct (PeanoNat.Nat.eq_dec i k) as [->|Hn]; auto.
                destruct (Compare_dec.lt_dec k _); [|Lia.lia].
                rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) H).
                destruct (Compare_dec.lt_dec _ _); [reflexivity|Lia.lia].
              + rewrite skipn_all by Lia.lia.
                rewrite firstn_all2 by Lia.lia.
                rewrite app_nil_r; reflexivity. }
          rewrite (X len old_len) by Lia.lia.
          assert (l + 1 + k = l + S k)%nat as -> by Lia.lia.
          rewrite skipn_skipn. f_equal. f_equal. Lia.lia.
      Qed.

      (* Iterate the layer decomposition n times *)
      Definition polynomial_layer_decomposition_loop (start n: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state i =>
             let '(l, len, p) := state in
             let old_len := len in
             let len := Nat.shiftr len 1 in
             let start := 0%nat in
             let '(l, start, p) := polynomial_list_loop (Nat.shiftl 1 i) old_len len (l, start, p) in
             (l, len, p))
          (seq start n)
          state.

      Definition ntt_loop (r n: nat) (p: list F) :=
        let l := 0%nat in
        let len := Nat.pow 2 n in
        let '(_, _, p) := polynomial_layer_decomposition_loop 0 r (l, len, p)
        in p.

      Lemma ntt_loop_spec:
        forall r n p (Hr_leq_n: (r <= n)%nat) (Hr_leq_m: (r <= m)%nat) (Hp: length p = Nat.pow 2 n),
          ntt_loop r n p = nttl_gallina r n (Nat.pow 2 m) p.
      Proof.
        unfold ntt_loop.
        intros. rewrite <- (@nttl_precomp_spec precomp_zetas precomp_zetas_eq r n 0 0); try Lia.lia; try reflexivity; [|cbv; Lia.lia].
        do 2 rewrite (surjective_pairing _).
        revert r n p Hr_leq_n Hr_leq_m Hp.
        assert (IH: forall r n p (Hr_leq_n: (r <= n)%nat) (Hr_leq_m: (r <= m)%nat) (Hp: length p = Nat.pow 2 n), polynomial_layer_decomposition_loop 0 r (0%nat, Nat.pow 2 n, p) = ((Nat.pow 2 r) - 1, Nat.pow 2 (n - r), nttl_precomp precomp_zetas r n 0 0 p)%nat).
        { induction r; intros.
          - cbv -[Nat.pow Nat.sub].
            rewrite PeanoNat.Nat.sub_0_r. reflexivity.
          - unfold polynomial_layer_decomposition_loop.
            match goal with
            | |- context [fold_left ?f ?l ?state] =>
                assert (fold_left f l state = f (polynomial_layer_decomposition_loop 0 r state) r) as ->
            end.
            { rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l. reflexivity. }
            rewrite nttl_precomp_S_eq by Lia.lia.
            rewrite IHr by Lia.lia.
            assert (Nat.shiftr (Nat.pow 2 (n - r)) 1 = Nat.pow 2 (n - S r)) as ->.
            { rewrite PeanoNat.Nat.shiftr_div_pow2.
              rewrite <- PeanoNat.Nat.pow_sub_r by Lia.lia.
              f_equal; Lia.lia. }
            clear IHr.
            rewrite PeanoNat.Nat.shiftl_1_l.
            rewrite polynomial_list_loop_spec.
            3:{ rewrite nttl_precomp_length.
                rewrite <- PeanoNat.Nat.pow_add_r.
                assert (r + (n - r) = n)%nat as ->; Lia.lia. }
            2:{ rewrite <- PeanoNat.Nat.pow_succ_r'.
                assert (S (n - S r) = n - r)%nat as -> by Lia.lia.
                pose proof (NatUtil.pow_nonzero 2 (n - r) ltac:(Lia.lia)); Lia.lia. }
            assert (Nat.pow 2 r - 1 + _ = 2 * Nat.pow 2 r - 1)%nat as -> by Lia.lia.
            rewrite <- PeanoNat.Nat.pow_succ_r'.
            rewrite <- PeanoNat.Nat.pow_add_r.
            assert (r + (n - r) = n)%nat as -> by Lia.lia.
            rewrite firstn_O, app_nil_l, PeanoNat.Nat.mul_0_r, skipn_O, skipn_all by (rewrite nttl_precomp_length; Lia.lia).
            rewrite app_nil_r, PeanoNat.Nat.add_0_l, firstn_all2.
            2:{ rewrite length_chunk by (apply NatUtil.pow_nonzero; congruence).
                rewrite nttl_precomp_length, Hp.
                assert (Nat.pow 2 n = Nat.pow 2 r * Nat.pow 2 (n - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
                rewrite Nat.div_up_exact; [|apply NatUtil.pow_nonzero]; Lia.lia. }
            f_equal. f_equal. apply map_ext; intros a; destruct a.
            f_equal. f_equal. pose proof (NatUtil.pow_nonzero 2 r ltac:(congruence)); Lia.lia. }
        intros; rewrite IH; auto.
      Qed.
    End ForwardNTT.
    Section BackwardNTT.
      (* Multiply coefficients by c, will be instantiated with c = F.inv (2 ^ n) for some n *)
      Definition div_loop (n: nat) (c: F) (p: list F): list F :=
        fold_left
          (fun l i =>
             let x := nth_default 0%F l i in
             ListUtil.set_nth i (c * x) l)
          (seq 0 n)
          p.

      Lemma div_loop_spec:
        forall n c p, div_loop n c p = (List.map (F.mul c) (firstn n p)) ++ (skipn n p).
      Proof.
        unfold div_loop. induction n; [reflexivity|].
        intros c p. rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l.
        rewrite IHn. cbn [fold_left]. apply nth_error_ext; intros i.
        destruct (Decidable.dec_lt_nat n (length p)) as [Hlt|Hnlt].
        - rewrite ListUtil.nth_error_app, ListUtil.nth_set_nth, nth_error_map, ListUtil.nth_error_app, nth_error_map, length_map.
          rewrite length_map, length_app, length_map, <- length_app, firstn_skipn, ListUtil.nth_default_app, length_map.
          repeat rewrite length_firstn. repeat (rewrite PeanoNat.Nat.min_l by Lia.lia).
          destruct (Compare_dec.lt_dec n n) as [|_]; [Lia.lia|].
          rewrite ListUtil.nth_default_skipn. assert (n + (_ - _) = n)%nat as -> by Lia.lia.
          destruct (PeanoNat.Nat.eq_dec i n) as [->|].
          + destruct (Compare_dec.lt_dec n (length p)) as [_|]; [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
            rewrite nth_error_firstn by Lia.lia.
            rewrite (ListUtil.nth_error_Some_nth_default _ 0%F _ Hlt). reflexivity.
          + destruct (Compare_dec.lt_dec i n).
            * destruct (Compare_dec.lt_dec i _); [|Lia.lia].
              do 2 (rewrite nth_error_firstn by Lia.lia).
              reflexivity.
            * destruct (Compare_dec.lt_dec i (S n)); [Lia.lia|].
              do 2 rewrite nth_error_skipn.
              f_equal. Lia.lia.
        - repeat (rewrite skipn_all by Lia.lia). rewrite app_nil_r, app_nil_r.
          repeat (rewrite firstn_all2 by Lia.lia).
          rewrite ListUtil.nth_set_nth.
          destruct (PeanoNat.Nat.eq_dec i n); [subst i|]; auto.
          rewrite length_map. destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          rewrite nth_error_map, ListUtil.nth_error_length_error; [reflexivity|Lia.lia].
      Qed.

      (* Recompose the two polynomials represented by p[start..start+old_len) and p[start+old_en..start+2*old_len) *)
      Definition inverse_polynomial_recompose_loop (i start old_len: nat) (z: F) (p: list F) :=
        List.fold_left
          (fun p j =>
             let tmp := nth_default 0%F p j in
             let x := nth_default 0%F p (j + old_len)%nat in
             let p := ListUtil.set_nth j (tmp + x) p in
             let x := (x - tmp)%F in
             let p := ListUtil.set_nth (j + old_len)%nat (z * x)%F p in
             p
          )
          (seq start i)
          p.

      Lemma inverse_polynomial_recompose_loop_spec:
        forall n start z p,
          inverse_polynomial_recompose_loop n start n z p = (firstn start p) ++ (recompose_cyclotomic_list n (F.opp z) (skipn start p)).
      Proof.
        intros n start z p.
        destruct (Decidable.dec_le_nat (length p) start) as [Hle|Hnle].
        - rewrite firstn_all2 by Lia.lia.
          rewrite skipn_all by Lia.lia.
          assert (recompose_cyclotomic_list _ _ _ = []) as ->.
          { apply ListUtil.length0_nil. rewrite <- (@length_nil F).
            apply PolynomialCRT.recompose_cyclotomic_list_length. }
          rewrite app_nil_r.
          unfold inverse_polynomial_recompose_loop.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k, fold_left f (seq start k) p = p) as ->; [|reflexivity]
          end.
          clear -Hle. induction k; [reflexivity|].
          rewrite seq_S, fold_left_app, IHk. cbn.
          rewrite ListUtil.set_nth_equiv_splice_nth, ListUtil.length_set_nth, ListUtil.set_nth_equiv_splice_nth.
          destruct (Compare_dec.lt_dec _ (length p)); [Lia.lia|].
          destruct (Compare_dec.lt_dec _ (length p)); [Lia.lia|].
          reflexivity.
        - unfold inverse_polynomial_recompose_loop, recompose_cyclotomic_list.
          erewrite (ListUtil.fold_left_ext _ _ _ _ _ (skipn start p)).
          2:{ intros. assert (forall A (l: list A) i x y, ListUtil.set_nth i x (ListUtil.set_nth i y l) = ListUtil.set_nth i x l) as ->.
              { intros. apply nth_error_ext. intro k.
                repeat rewrite ListUtil.nth_set_nth.
                destruct (PeanoNat.Nat.eq_dec k i); auto.
                rewrite ListUtil.length_set_nth. reflexivity. }
              reflexivity. }
          rewrite <- (firstn_skipn start p) at 1.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k l1 l2, length l1 = start -> fold_left f (seq start k) (l1 ++ l2) = l1 ++ (fold_left f (seq 0 k) l2)) as ->
          end.
          3: rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia.
          2:{ f_equal. apply ListUtil.fold_left_ext.
              intros l j. repeat rewrite ListUtil.set_nth_nth_default_full.
              repeat rewrite ListUtil.length_set_nth.
              destruct (PeanoNat.Nat.eq_dec _ _) as [_|]; [|congruence].
              destruct (Compare_dec.lt_dec _ _) as [Hlt|Hnlt].
              + f_equal. rewrite Ring.mul_opp_l, <- Ring.mul_opp_r.
                do 2 rewrite Hierarchy.ring_sub_definition.
                rewrite Group.inv_op, Group.inv_inv. reflexivity.
              + repeat rewrite (ListUtil.set_nth_equiv_splice_nth (j + n)).
                repeat rewrite ListUtil.length_set_nth.
                destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|]. reflexivity. }
          induction k; intros l1 l2 Hl1; [reflexivity|].
          rewrite seq_S, fold_left_app, IHk; auto.
          rewrite seq_S, fold_left_app. rewrite PeanoNat.Nat.add_0_l.
          cbn [fold_left].
          rewrite ListUtil.nth_default_app.
          destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          assert (start + k + n - length l1 = k + n)%nat as -> by Lia.lia.
          rewrite ListUtil.nth_default_app.
          destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          assert (start + k - length l1 = k)%nat as -> by Lia.lia.
          assert (forall A k (x: A) l1 l2, (length l1 <= k)%nat -> ListUtil.set_nth k x (l1 ++ l2) = l1 ++ ListUtil.set_nth (k - length l1) x l2) as Z; [|repeat rewrite Z; try Lia.lia; repeat (f_equal; try Lia.lia)].
          clear. induction k; intros x l1 l2 Hk.
          + destruct l1; [|cbn in Hk; Lia.lia].
            reflexivity.
          + destruct l1; [reflexivity|].
            cbn in Hk. rewrite <- app_comm_cons, <- ListUtil.cons_set_nth.
            rewrite IHk by Lia.lia.
            cbn [length]. assert (S k - S _ = k - length l1)%nat as -> by Lia.lia.
            rewrite app_comm_cons. reflexivity.
      Qed.

      (* Iterate once over the whole array and recompose all polynomials *)
      Definition inverse_polynomial_list_loop (k old_len len: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state _ =>
             let '(l, start, p) := state in
             let l := (l - 1)%nat in
             let z := nth_default 0%F precomp_zetas l in
             let p := inverse_polynomial_recompose_loop old_len start old_len z p in
             let start := (start + len)%nat in
             (l, start, p))
          (seq 0 k)
          state.

      Lemma inverse_polynomial_list_loop_spec:
        forall k old_len len l start p,
          (k <= l)%nat ->
          (0 < 2 * old_len <= len)%nat ->
          (start + k * len <= length p) ->
          inverse_polynomial_list_loop k old_len len (l, start, p) =
            (l - k, start + k * len, firstn start p ++ concat (map (fun '(i, chk) => recompose_cyclotomic_list old_len (F.opp (nth_default 0%F precomp_zetas (l - 1 - i))) chk) (enumerate 0 (firstn k (chunk len (skipn start p))))) ++ skipn (start + k * len) p)%nat.
      Proof.
        unfold inverse_polynomial_list_loop.
        induction k; intros old_len len l start p Hl Hlen Hp.
        - cbn. rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r.
          rewrite firstn_skipn. reflexivity.
        - rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l, IHk by Lia.lia.
          cbn [fold_left]. f_equal; [f_equal; Lia.lia|].
          rewrite inverse_polynomial_recompose_loop_spec.
          rewrite firstn_app, firstn_firstn, PeanoNat.Nat.min_r by Lia.lia.
          rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * len - start = k * len)%nat as -> by Lia.lia.
          rewrite firstn_app.
          assert (k < (length (chunk len (skipn start p))))%nat as Hk.
          { rewrite length_chunk, length_skipn by Lia.lia.
            apply (PeanoNat.Nat.lt_le_trans _ (Nat.div_up (S k * len) len)).
            - rewrite Nat.div_up_exact by Lia.lia. Lia.lia.
            - apply PeanoNat.Nat.Div0.div_le_mono. Lia.lia. }
          match goal with | |- context [length (concat ?l)] => assert (length (concat l) = k * len)%nat as Hco end.
          { rewrite length_concat.
            assert (forall c l, (forall x, In x l -> x = c) -> list_sum l = c * length l)%nat as Hcl.
            { clear. induction l; intros; simpl.
              - rewrite PeanoNat.Nat.mul_0_r. reflexivity.
              - rewrite IHl by (intros; apply H; right; auto).
                rewrite (H a ltac:(left; reflexivity)). Lia.lia. }
            rewrite (Hcl len).
            2:{ intros x Hx. rewrite in_map_iff in Hx.
                destruct Hx as (y & Hy & Hin).
                subst x. rewrite in_map_iff in Hin.
                destruct Hin as ((i & chk) & Hz & Hzz).
                subst y. rewrite PolynomialCRT.recompose_cyclotomic_list_length.
                apply in_combine_r in Hzz.
                rewrite firstn_chunk in Hzz by Lia.lia.
                apply In_nth_error in Hzz. destruct Hzz as (j & Hj).
                pose proof (ListUtil.nth_error_value_length _ _ _ _ Hj) as Hjj.
                rewrite length_chunk in Hjj by Lia.lia.
                rewrite (nth_error_chunk len ltac:(Lia.lia) _ _ Hjj) in Hj.
                inversion Hj; subst chk; clear Hj.
                rewrite length_firstn, length_skipn, length_firstn, length_skipn.
                rewrite (PeanoNat.Nat.min_l (k * _)) by Lia.lia.
                rewrite length_firstn, length_skipn in Hjj.
                rewrite PeanoNat.Nat.min_l in Hjj by Lia.lia.
                rewrite Nat.div_up_exact in Hjj by Lia.lia.
                apply PeanoNat.Nat.min_l.
                rewrite <- PeanoNat.Nat.mul_sub_distr_r.
                transitivity (1 * len)%nat; try Lia.lia.
                apply PeanoNat.Nat.mul_le_mono_r. Lia.lia. }
            rewrite length_map, length_map.
            unfold enumerate. rewrite length_combine, length_seq, PeanoNat.Nat.min_id.
            rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia. }
          rewrite (@firstn_all2 _ (k * len)%nat) by Lia.lia.
          rewrite Hco, PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
          rewrite skipn_app, (skipn_all (start + k * len)) by (rewrite length_firstn; Lia.lia).
          rewrite app_nil_l, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * len - start = k * len)%nat as -> by Lia.lia.
          rewrite skipn_app, Hco, PeanoNat.Nat.sub_diag, skipn_O.
          rewrite (ListUtil.firstn_succ nil), enumerate_app, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          rewrite map_app, PeanoNat.Nat.add_0_l. cbn.
          rewrite concat_app, (nth_default_eq _ _ []), nth_chunk by (rewrite length_chunk in Hk; Lia.lia).
          rewrite skipn_skipn, (skipn_all (k * len)) by Lia.lia.
          rewrite app_nil_l. cbn [concat]. rewrite app_nil_r.
          assert (forall n1 n2 a l, (2 * n1 <= n2)%nat -> recompose_cyclotomic_list n1 a l = recompose_cyclotomic_list n1 a (firstn n2 l) ++ (skipn n2 l)) as X.
          { clear. unfold recompose_cyclotomic_list.
            set (f a n1 := (fun (l0 : list F) (i : nat) => ListUtil.set_nth (i + n1) (a *nth_default 0(ListUtil.set_nth (i + n1) (nth_default 0 l0 i - nth_default 0 l0 (i + n1)) (ListUtil.set_nth i (nth_default 0 l0 i + nth_default 0 l0 (i + n1)) l0)) (i + n1)) (ListUtil.set_nth (i + n1) (nth_default 0 l0 i - nth_default 0 l0 (i + n1)) (ListUtil.set_nth i (nth_default 0 l0 i + nth_default 0 l0 (i + n1)) l0)))).
            assert (forall k n1 n2 a l, (k <= n1)%nat -> (2 * n1 <= n2)%nat -> fold_left (f a n1) (seq 0 k) l = fold_left (f a n1) (seq 0 k) (firstn n2 l) ++ skipn n2 l) as X; [|intros; apply X; auto].
            assert (forall A g k n2 (l: list A), (forall l i, (i < k)%nat -> g l i = g (firstn n2 l) i ++ skipn n2 l) -> (forall l i, length (g l i) = length l)%nat -> fold_left g (seq 0 k) l = fold_left g (seq 0 k) (firstn n2 l) ++ skipn n2 l) as Z.
            2: { intros; apply Z.
                 - intros. unfold f.
                   repeat rewrite set_nth_set_nth.
                   destruct (Decidable.dec_le_nat (length l0) n2).
                   { rewrite firstn_all2 by Lia.lia.
                     rewrite skipn_all by Lia.lia.
                     rewrite app_nil_r. reflexivity. }
                   rewrite <- set_nth_app_l by (rewrite ListUtil.length_set_nth, length_firstn; Lia.lia).
                   rewrite <- set_nth_app_l by (rewrite length_firstn; Lia.lia).
                   rewrite firstn_skipn. repeat rewrite ListUtil.nth_default_firstn.
                   destruct (Compare_dec.le_dec n2 (length l0)); [|Lia.lia].
                   do 2 (destruct (Compare_dec.lt_dec _ _); [|Lia.lia]).
                   f_equal. f_equal.
                   repeat rewrite ListUtil.set_nth_nth_default_full.
                   repeat rewrite ListUtil.length_set_nth.
                   rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
                   destruct (PeanoNat.Nat.eq_dec _ (i + n1)) as [_|]; [|Lia.lia].
                   do 2 destruct (Compare_dec.lt_dec _ _); auto; Lia.lia.
                 - intros; unfold f; repeat rewrite ListUtil.length_set_nth. reflexivity. }
            clear f. induction k; intros n2 l Hg Hlen; [cbn; rewrite firstn_skipn; reflexivity|].
            destruct (Decidable.dec_le_nat (length l) n2) as [Hle|Hnle].
            { rewrite firstn_all2, skipn_all by Lia.lia.
              rewrite app_nil_r. reflexivity. }
            rewrite seq_S, fold_left_app, fold_left_app, PeanoNat.Nat.add_0_l, (IHk n2); auto.
            cbn [fold_left]. assert (forall l z, length (fold_left g l z) = length z) as W.
            { clear -Hlen. induction l; intros; cbn; [|rewrite IHl, Hlen]; reflexivity. }
            rewrite (Hg (_ ++ _)) by Lia.lia.
            rewrite firstn_app. rewrite W, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
            rewrite PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
            rewrite ListUtil.skipn_app_sharp by (rewrite W, length_firstn; apply PeanoNat.Nat.min_l; Lia.lia).
            rewrite firstn_all2 by (rewrite W, length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            reflexivity. }
          rewrite (X old_len len) by Lia.lia.
          rewrite skipn_skipn. repeat rewrite <- app_assoc.
          repeat (f_equal; try Lia.lia).
      Qed.

      (* Iterate r times the polynomial recomposition *)
      Definition inverse_layer_recomposition_loop (r: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state i =>
             let '(l, len, p) := state in
             let start := 0%nat in
             let old_len := len in
             let len := Nat.shiftl len 1 in
             let '(l, _, p) :=
               inverse_polynomial_list_loop (Nat.shiftl 1 ((r - 1) - i))%nat old_len len (l, start, p) in
             (l, len, p))
          (seq 0 r)
          state.

      Lemma inverse_layer_recomposition_loop_spec:
        forall r k l len p,
          (length p = Nat.pow 2 k) ->
          (r <= k)%nat ->
          (len = Nat.pow 2 (k - r))%nat ->
          (l = Nat.pow 2 r)%nat ->
          inverse_layer_recomposition_loop r (l, len, p) = (1, Nat.shiftl len r, inttl_precomp precomp_zetas r k 0 0 p)%nat.
      Proof.
        induction r; intros n l len p Hp Hrn Hlen Hl.
        - cbn. rewrite Hl. reflexivity.
        - assert (len <> 0)%nat as Hlennz by (rewrite Hlen; apply NatUtil.pow_nonzero; congruence).
          subst len. subst l.
          unfold inverse_layer_recomposition_loop in IHr.
          unfold inverse_layer_recomposition_loop.
          rewrite <- cons_seq, ListUtil.List.fold_left_cons.
          rewrite <- seq_shift, ListUtil.fold_left_map.
          rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.shiftl_1_l, PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.pow_1_r.
          rewrite inverse_polynomial_list_loop_spec.
          2:{ apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          2:{ Lia.lia. }
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.add_0_l.
              rewrite <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite firstn_O, app_nil_l, skipn_O, PeanoNat.Nat.add_0_l, skipn_all.
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'.
              rewrite <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite app_nil_r. rewrite inttl_precomp_S_eq by assumption.
          rewrite PeanoNat.Nat.mul_0_r. rewrite firstn_chunk by Lia.lia.
          rewrite firstn_all2.
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r', <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'.
          assert (S (n - S r) = n - r)%nat as -> by Lia.lia.
          assert (1 + r = S r)%nat as -> by Lia.lia.
          erewrite ListUtil.fold_left_ext.
          + erewrite (IHr n); try Lia.lia.
            * f_equal. f_equal.
              do 2 rewrite PeanoNat.Nat.shiftl_mul_pow2.
              rewrite <- PeanoNat.Nat.pow_add_r, <- PeanoNat.Nat.pow_add_r.
              f_equal; Lia.lia.
            * rewrite (length_concat_same_length (Nat.pow 2 (n - r))).
              { rewrite length_map. unfold enumerate.
                rewrite length_combine, length_chunk by (apply NatUtil.pow_nonzero; congruence).
                rewrite length_seq, PeanoNat.Nat.min_id.
                rewrite Hp. assert (Nat.pow 2 n = Nat.pow 2 r * Nat.pow 2 (n - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
                rewrite Nat.div_up_exact by (apply NatUtil.pow_nonzero; congruence).
                reflexivity. }
              apply Forall_map. rewrite Forall_forall.
              intros x Hx. destruct x as (x & y). apply in_combine_r in Hx.
              rewrite PolynomialCRT.recompose_cyclotomic_list_length.
              apply In_nth_error in Hx. destruct Hx as [i Hi].
              pose proof (nth_error_Some_bound_index _ _ _ Hi) as Hlen.
              rewrite length_chunk in Hlen by (apply NatUtil.pow_nonzero; congruence).
              rewrite (nth_error_chunk (Nat.pow 2 _) ltac:(apply NatUtil.pow_nonzero; Lia.lia) _ _ Hlen) in Hi.
              inversion Hi; subst y. rewrite length_firstn, length_skipn, Hp.
              rewrite Hp in Hlen. apply PeanoNat.Nat.min_l.
              replace (Nat.pow 2 n) with (Nat.pow 2 r * Nat.pow 2 (n - r))%nat in * by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
              rewrite Nat.div_up_exact in Hlen by (apply NatUtil.pow_nonzero; Lia.lia).
              Lia.nia.
            * assert (S r - 1 = r)%nat as -> by Lia.lia.
              rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia.
          + intros ((a & b) & c) d. cbn zeta.
            assert (S r - 1 - S d = r - 1 - d)%nat as -> by Lia.lia.
            reflexivity.
      Qed.

      (* The whole thing  *)
      (* length p = 2 ^ k *)
      (* Each polynomial have size 2 ^ (k - r) at the beginning *)
      Definition inverse_ntt_loop (r k: nat) (p: list F) :=
        let l := Nat.shiftl 1 r in
        let len := Nat.shiftl 1 (k - r) in
        let '(_, _, p) :=
          inverse_layer_recomposition_loop r (l, len, p) in
        let p := div_loop (Nat.shiftl 1 k) (F.inv (F.pow (1 + 1) r)) p
        in p.

      Lemma inverse_ntt_loop_spec:
        forall r k p,
          (r <= k)%nat ->
          (r <= m)%nat ->
          length p = Nat.pow 2 k ->
          inverse_ntt_loop r k p = inttl_gallina r k (Nat.pow 2 m) p.
      Proof.
        intros r k p Hrk Hrm Hp. rewrite inttl_nomul_gallina_spec by Lia.lia.
        unfold inverse_ntt_loop.
        repeat rewrite PeanoNat.Nat.shiftl_mul_pow2.
        repeat rewrite PeanoNat.Nat.mul_1_l.
        rewrite (inverse_layer_recomposition_loop_spec _ k) by Lia.lia.
        rewrite <- (inttl_precomp_spec _ precomp_zetas_eq _ _ 0 0); try (cbn; Lia.lia).
        rewrite div_loop_spec.
        assert (Nat.pow 2 k = length (inttl_precomp precomp_zetas r k 0 0 p)) as -> by (rewrite inttl_precomp_length; auto).
        rewrite firstn_all, skipn_all by Lia.lia.
        rewrite app_nil_r. reflexivity.
      Qed.
    End BackwardNTT.

    (* Full specs relating to the dependent-type-style specifications *)
    Lemma ntt_loop_full_spec:
      forall n p,
        proj1_sig (nttl n p) = ntt_loop (Nat.min n m) n (proj1_sig p).
    Proof.
      intros. unfold nttl. rewrite nttl_gallina_spec.
      symmetry; apply ntt_loop_spec; [Lia.lia|Lia.lia|].
      rewrite (proj2_sig p), PolynomialCRT.posicyclic_measure; [Lia.lia|].
      pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)); Lia.lia.
    Qed.

    Lemma inverse_ntt_loop_full_spec:
      forall n p,
        proj1_sig (inttl n p) = inverse_ntt_loop (Nat.min n m) n (proj1_sig p).
    Proof.
      intros. unfold inttl. rewrite inttl_gallina_spec.
      symmetry; apply inverse_ntt_loop_spec; [Lia.lia|Lia.lia|].
      rewrite (proj2_sig p), map_map, (list_sum_constant (Nat.pow 2 (n - Nat.min n m))).
      - rewrite length_map, length_decompose, <- PeanoNat.Nat.pow_add_r.
        f_equal; Lia.lia.
      - apply Forall_map. rewrite Forall_forall.
        intros. rewrite PolynomialCRT.posicyclic_measure; [Lia.lia|].
        pose proof (NatUtil.pow_nonzero 2 (n - Nat.min n m) ltac:(congruence)); Lia.lia.
    Qed.
  End Loops.
End Gallina.
