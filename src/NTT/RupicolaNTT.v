Require Import Spec.ModularArithmetic.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.InlineTables.
Require Import Rupicola.Lib.Alloc.
Require Import Rupicola.Lib.SepLocals.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.NTT.Polynomial.
Require Import Crypto.NTT.CyclotomicDecomposition.
Require Import Crypto.Util.ListUtil.

Section Utils.
  (* To be moved somewhere ? *)
  Lemma nat_rect_to_nat_iter (A: Type) (a: A) (f: nat -> A -> A) (i: nat):
    nat_rect (fun _ => A) a f i = P2.cdr (Nat.iter i (fun a => \<S (P2.car a), f (P2.car a) (P2.cdr a)\>) \<0%nat, a\>).
  Proof.
    assert (Nat.iter i _ \<0%nat, a\> = \<i, nat_rect (fun _ : nat => A) a f i\>) as ->.
    { induction i; [reflexivity|].
      simpl in *. rewrite IHi. reflexivity. }
    reflexivity.
  Qed.

  Lemma nat_iter_mul:
    forall (p q : nat) (A : Type) (f : A -> A) (x : A),
      Nat.iter (p * q)%nat f x = Nat.iter p (Nat.iter q f) x.
  Proof.
    induction p; intros; [reflexivity|].
    simpl. rewrite Nat.iter_add, IHp. reflexivity.
  Qed.

  Lemma z_range'_seq:
    forall len from,
      (0 <= from)%Z ->
      z_range' from len = List.map Z.of_nat (seq (Z.to_nat from) len).
  Proof.
    induction len; intros from Hfrom; [reflexivity|].
    simpl. rewrite IHlen by Lia.lia.
    rewrite Z2Nat.id by Lia.lia.
    rewrite <- Z2Nat.inj_succ by Lia.lia.
    rewrite Z.add_1_r. reflexivity.
  Qed.

  Lemma seq_add:
    forall a b len,
      seq (a + b)%nat len = List.map (fun x => x + b)%nat (seq a len).
  Proof.
    induction len; [reflexivity|].
    rewrite seq_S, seq_S, map_app, IHlen; simpl.
    f_equal. f_equal. Lia.lia.
  Qed.

  Lemma put_eq_set_nth {K: Type} {Conv: Convertible K nat}
    {V: Type} {HD: HasDefault V}:
    forall a k (v: V),
      ListArray.put a k v = set_nth (cast k) v a.
  Proof.
    unfold ListArray.put. intros.
    assert (forall l i (x: V), replace_nth i l x = set_nth i x l) as IH.
    { induction l; intros; [rewrite set_nth_nil; reflexivity|].
      simpl. destruct i.
      - rewrite set_nth_cons. reflexivity.
      - rewrite IHl. rewrite <- cons_set_nth.
        reflexivity. }
    apply IH.
  Qed.

  Lemma get_eq_nth_default {K: Type} {Conv: Convertible K nat}
    {V: Type} {HD: HasDefault V}:
    forall (a: list V) k,
      ListArray.get a k = nth_default default a (cast k).
  Proof. unfold ListArray.get; intros; rewrite nth_default_eq; reflexivity. Qed.

  Lemma set_nth_app {T: Type} (i: nat) (v: T) (l1 l2: list T):
    set_nth i v (l1 ++ l2) = if lt_dec i (length l1) then (set_nth i v l1) ++ l2 else l1 ++ (set_nth (i - length l1) v l2).
  Proof.
    apply nth_error_ext.
    intros j. rewrite nth_set_nth.
    destruct (Nat.eq_dec j i); [subst j|].
    - destruct (lt_dec i (length (l1 ++ l2))) as [Hlt|Hnlt].
      + destruct (lt_dec i (length l1)).
        * rewrite nth_error_app1 by (rewrite length_set_nth; Lia.lia).
          rewrite nth_set_nth, NatUtil.eq_nat_dec_refl.
          destruct (lt_dec _ _); [reflexivity|Lia.lia].
        * rewrite nth_error_app2 by Lia.lia.
          rewrite nth_set_nth, NatUtil.eq_nat_dec_refl.
          rewrite app_length in Hlt.
          destruct (lt_dec _ _); [|Lia.lia]. reflexivity.
      + rewrite app_length in Hnlt. destruct (lt_dec _ _) as [|_]; [Lia.lia|].
        rewrite nth_error_app2 by Lia.lia.
        rewrite nth_set_nth, NatUtil.eq_nat_dec_refl.
        destruct (lt_dec _ _); [Lia.lia|reflexivity].
    - destruct (lt_dec j (length l1)) as [Hlt|Hnlt].
      + rewrite nth_error_app1 by Lia.lia.
        destruct (lt_dec i (length l1)) as [Hll|Hll].
        * rewrite nth_error_app1 by (rewrite length_set_nth; Lia.lia).
          rewrite nth_set_nth. destruct (Nat.eq_dec j i) as [|_]; [congruence|].
          reflexivity.
        * rewrite nth_error_app1 by Lia.lia. reflexivity.
      + rewrite nth_error_app2 by Lia.lia.
        destruct (lt_dec i (length l1)) as [Hll|Hll].
        * rewrite nth_error_app2 by (rewrite length_set_nth; Lia.lia).
          rewrite length_set_nth; reflexivity.
        * rewrite nth_error_app2 by Lia.lia.
          rewrite nth_set_nth. destruct (Nat.eq_dec _ _) as [|_]; [Lia.lia|].
          reflexivity.
  Qed.

End Utils.

Section NTT.
  Context {q: positive}.
  Local Notation F := (F q).
  Context {n: nat} {km1: nat}.
  Local Open Scope F_scope.

  Variable (zetas: list F).

  Local Instance HasDefault_F: HasDefault F := 0%F.

  Definition polynomial_decompose_loop (i start len: Z) (z: F) (p: ListArray.t F) :=
    nd_ranged_for_all start (start + i)
      (fun p j =>
         let/n x := ListArray.get p (j + len)%Z in
         let/n tmp := z * x in
         let/n y := ListArray.get p j in
         let/n p := ListArray.put p (j + len)%Z (y - tmp) in
         let/n p := ListArray.put p j (y + tmp) in
         p
      )
      p.

  Definition polynomial_list_loop (k old_len len: Z) (state: \<< Z, Z, ListArray.t F \>>) :=
    nd_ranged_for_all 0%Z k
      (fun state _ =>
         let '\< m, start, p \> := state in
         let/n m := (m + 1)%Z in
         let/n z := InlineTable.get zetas m in
         let/n p := polynomial_decompose_loop len start len z p in
         let/n start := (start + old_len)%Z in
         \< m, start, p \>
      )
      state.

  Definition layer_decomposition_loop (n: nat) (state: \<< Z, Z, ListArray.t F \>>) :=
      nd_ranged_for_all 0%Z (Z.of_nat n)
        (fun state i =>
           let '\< m, len, p \> := state in
           let/n old_len := len in
           let/n len := Z.shiftr len 1 in
           let/n start := 0%Z in
           let/n (m, start, p) := polynomial_list_loop (Z.pow 2 i) old_len len \< m, start, p\> in
           \< m, len, p \>
        )
        state.

  Definition NTT_gallina (p: ListArray.t F): ListArray.t F :=
    let/n m := 0%Z in
    let/n len := (Z.pow 2 (Z.of_nat n)) in
    let/n (m, len, p) :=
      layer_decomposition_loop km1 (\< m, len, p \>) in p.

  Section Correctness.
    Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
      {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.

    Context {zeta: F}.

    Local Notation NTT_spec := (@NTT_phi_list q zeta (N.of_nat km1) n km1).
    Local Notation NTT_layer_spec := (@NTT_phi_layer_list q zeta (N.of_nat km1) n).
    Local Notation enumerate := Datatypes.List.enumerate.

    Hypothesis n_ge_km1: (km1 <= n)%nat.
    Hypothesis zetas_eq: zetas = List.map (fun k => F.pow zeta k) (@zeta_powers (N.of_nat km1) km1).

    Lemma NTT_gallina_correct (p: list F) (Hp: length p = Nat.pow 2 n):
      NTT_gallina p = NTT_spec p.
    Proof.
      unfold NTT_gallina, layer_decomposition_loop, polynomial_list_loop, polynomial_decompose_loop, NTT_spec. unfold nlet.
      replace (Z.of_nat km1) with (0 + Z.of_nat km1)%Z by Lia.lia.
      rewrite <- fold_left_as_nd_ranged_for_all.
      unfold z_range. rewrite Z.add_simpl_l.
      rewrite Nat2Z.id. rewrite z_range'_seq by Lia.lia.
      assert (Z.to_nat 0 = 0)%nat as -> by Lia.lia.
      rewrite ListUtil.fold_left_map.
      match goal with | |- context [fold_left ?ff _ _] => set (f:=ff) end.
      assert (forall k, (k <= km1)%nat -> fold_left f (seq 0 k) \< 0%Z, (2 ^ Z.of_nat n)%Z, p \> = \< ((2 ^ Z.of_nat k) - 1)%Z,  (2 ^ (Z.of_nat (n - k)%nat))%Z, nat_rect _ p NTT_layer_spec k \>) as IH.
      { induction k; intros Hk.
        - simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
        - rewrite seq_S, PeanoNat.Nat.add_0_l.
          rewrite fold_left_app. cbn [fold_left]; rewrite IHk by Lia.lia.
          cbn [nat_rect].
          set (l := (nat_rect _ p NTT_layer_spec k)).
          unfold f. assert (2 ^ Z.of_nat k = 0 + Z.of_nat (Nat.pow 2 k))%Z as ->.
          { rewrite Z2Nat.Z.pow_Zpow. Lia.lia. }
          rewrite <- Nat_iter_as_nd_ranged_for_all.
          rewrite Z.add_0_l, Z2Nat.Z.pow_Zpow.
          assert (Z.of_nat 2%nat = 2%Z) as -> by Lia.lia.
          assert (Z.shiftr _ 1 = 2 ^ Z.of_nat (n - S k))%Z as ->.
          { rewrite Z.shiftr_div_pow2, <- ZLib.Z.pow2_div2 by Lia.lia.
            f_equal. Lia.lia. }
          clear IHk. clear f. set (f := Nat.iter _ _ _).
          assert (f = \< (2 ^ Z.of_nat (S k) - 1)%Z, (2 ^ Z.of_nat n)%Z, NTT_layer_spec k l \>) as ->; [|reflexivity].
          unfold f. clear f. unfold NTT_layer_spec.
          unfold fold_left_chunked.
          assert (Hl: length l = length p).
          { unfold l. induction k; [reflexivity|].
            simpl. erewrite NTT_phi_layer_list_length.
            rewrite IHk by Lia.lia. reflexivity.
            Unshelve. rewrite Nnat.Nat2N.id. Lia.lia. }
          assert (Hlen: length (enumerate 0%nat (chunk (Nat.pow 2 (n - k)) l)) = Nat .pow 2 k).
          { unfold enumerate. rewrite combine_length, seq_length, PeanoNat.Nat.min_id, length_chunk.
            2: generalize (NatUtil.pow_nonzero 2 (n - k) ltac:(Lia.lia)); Lia.lia.
            rewrite Hl, Hp. replace n with (k + (n - k))%nat at 1 by Lia.lia.
            rewrite PeanoNat.Nat.pow_add_r.
            rewrite Nat.div_up_exact; [reflexivity|].
            apply NatUtil.pow_nonzero. Lia.lia. }
          match goal with
          | |- Nat.iter ?m ?f (\< ?x, ?y, ?z \>) = \< _, _, fold_left ?g ?a _ \> =>
              assert (forall j, (j <= m)%nat -> Nat.iter j f \<x, y, z\> = \< (x + Z.of_nat j)%Z, (y + Z.of_nat j * 2 ^ Z.of_nat (n - k))%Z, (fold_left g (List.firstn j a) nil) ++ (concat (List.map snd (List.skipn j a))) \>) as IH
          end.
          { induction j; intros Hj.
            - simpl. rewrite Nat2Z.inj_0, Z.add_0_r. f_equal.
              f_equal. unfold enumerate. rewrite ListUtil.map_snd_combine.
              rewrite seq_length. rewrite List.firstn_all.
              rewrite concat_chunk; reflexivity.
            - rewrite Nat.iter_succ, IHj by Lia.lia.
              f_equal; [Lia.lia|].
              f_equal; [Lia.lia|].
              rewrite <- (firstn_nth _ j (enumerate 0 (chunk (2 ^ (n - k)) l)) (0%nat, nil)) by (rewrite Hlen; Lia.lia).
              rewrite (ListUtil.skipn_nth_default j _ (0%nat, nil)) by (rewrite Hlen; Lia.lia).
              rewrite fold_left_app. cbn [fold_left].
              unfold enumerate. rewrite combine_nth by (rewrite seq_length; reflexivity).
              set (acc := fold_left _ _ _).
              rewrite map_cons, concat_cons, nth_default_eq.
              rewrite combine_nth by (rewrite seq_length; reflexivity).
              cbn [snd]. unfold Pmod_cyclotomic_list.
              rewrite <- fold_left_as_nd_ranged_for_all.
              unfold z_range. rewrite Z.add_simpl_l, Z.add_0_l.
              rewrite Z2Nat.inj_pow by Lia.lia.
              rewrite Nat2Z.id. assert (Z.to_nat 2 = 2)%nat as -> by Lia.lia.
              rewrite z_range'_seq by Lia.lia.
              rewrite Z2Nat.inj_mul, Z2Nat.inj_pow, Nat2Z.id, Nat2Z.id by Lia.lia.
              assert (Z.to_nat 2 = 2)%nat as -> by Lia.lia.
              rewrite ListUtil.fold_left_map.
              rewrite <- (PeanoNat.Nat.add_0_l (j * _)).
              rewrite (seq_add 0%nat).
              rewrite ListUtil.fold_left_map.
              clear IHj. rewrite <- List.app_assoc.
              assert (Hlen2: (length acc = j * Nat.pow 2 (n - k))%nat).
              { unfold acc. clear acc.
                erewrite ListUtil.fold_left_ext; [rewrite <- ListUtil.eq_flat_map_fold_left|].
                2: instantiate (1:=(fun y => Pmod_cyclotomic_list (snd y) (2 ^ (n - S k)) (nth_default 0 (List.map (fun x0 : N => zeta ^ x0) (cyclotomic_decompose (S k)))  (2 * (fst y))))); intros x y; destruct y; reflexivity.
                rewrite (flat_map_constant_length (c:=Nat.pow 2 (n - k))).
                - unfold enumerate in Hlen.
                  rewrite firstn_length, Hlen.
                  assert (Init.Nat.min j _ = j) as -> by Lia.lia.
                  Lia.lia.
                - intros x Hx. rewrite Pmod_cyclotomic_list_length.
                  destruct x as [? x].
                  apply ListUtil.In_firstn in Hx.
                  apply in_combine_r in Hx. simpl.
                  eapply (Forall_In (P:=fun x => length x = _)); [|apply Hx].
                  apply (Forall_chunk_length_eq _ (Nat.pow 2 k)). rewrite Hl, Hp.
                  rewrite <- PeanoNat.Nat.pow_add_r. f_equal. Lia.lia. }
              match goal with
              | |- fold_left ?f _ ?l = acc ++ fold_left ?g _ ?l2 ++ ?l3 =>
                  assert (forall m, (m <= Nat.pow 2 (n - S k))%nat -> fold_left f (seq 0%nat m) l = acc ++ fold_left g (seq 0%nat m) l2 ++ l3) as IH
              end.
              { induction m; intros Hm; [reflexivity|].
                rewrite seq_S, fold_left_app, fold_left_app, PeanoNat.Nat.add_0_l.
                rewrite IHm by Lia.lia. cbn [fold_left].
                set (middle:=fold_left _ _ _).
                repeat rewrite put_eq_set_nth.
                repeat rewrite get_eq_nth_default.
                unfold InlineTable.get. repeat rewrite <- nth_default_eq.
                cbv [cast Convertible_Z_nat].
                repeat rewrite Nat2Z.id.
                assert (Z.to_nat (2 ^ Z.of_nat k - 1 + Z.of_nat j + 1) = (Nat.pow 2 k) + j)%nat as ->.
                { repeat rewrite Z2Nat.inj_add by Lia.lia.
                  rewrite Z2Nat.inj_sub by Lia.lia.
                  rewrite Z2Nat.inj_pow by Lia.lia.
                  repeat rewrite Nat2Z.id.
                  assert (Z.to_nat 1 = 1)%nat as -> by Lia.lia.
                  assert (Z.to_nat 2 = 2)%nat as -> by Lia.lia. Lia.lia. }
                assert (Z.to_nat (Z.of_nat (m + j * 2 ^ (n - k)) + 2 ^ Z.of_nat (n - S k)) = m + j * Nat.pow 2 (n - k) + Nat.pow 2 (n - S k))%nat as ->.
                { repeat rewrite Z2Nat.inj_add by Lia.lia.
                  rewrite Z2Nat.inj_pow by Lia.lia.
                  repeat rewrite Nat2Z.id.
                  reflexivity. }
                rewrite <- Hlen2.
                rewrite ListUtil.nth_default_app.
                destruct (lt_dec (m + _) _) as [|_]; [Lia.lia|].
                repeat match goal with | |- context [(?a + ?b - ?b)%nat] => assert (a + b - b = a)%nat as -> by Lia.lia end.
                assert (Hmiddle: (length middle = 2 * Nat.pow 2 (n - S k))%nat).
                { unfold middle. rewrite <- PeanoNat.Nat.pow_succ_r'.
                  assert (S (n - S k) = n - k)%nat as -> by Lia.lia.
                  match goal with | |- context [fold_left ?f _ _] => assert (forall l x, length (fold_left f l x) = length x) as -> end.
                  { induction l0; intros; [reflexivity|].
                    simpl. rewrite IHl0. do 2 rewrite length_set_nth. reflexivity. }
                  eapply (Forall_In (P:=fun x => length x = _)); [apply (Forall_chunk_length_eq _ (Nat.pow 2 k)); rewrite Hl, Hp, <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia|].
                  apply nth_In.
                  unfold enumerate in Hlen. rewrite combine_length, seq_length, Nat.min_id in Hlen.
                  rewrite Hlen. Lia.lia. }
                rewrite ListUtil.nth_default_app, Hmiddle.
                destruct (lt_dec m _) as [_|]; [|Lia.lia].
                rewrite ListUtil.nth_default_app.
                destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                rewrite set_nth_app.
                destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                assert (m + length acc + Nat.pow 2 (n - S k) - length acc = m + Nat.pow 2 (n - S k))%nat as -> by Lia.lia.
                rewrite ListUtil.nth_default_app.
                destruct (lt_dec _ _) as [_|Hnlt]; [|rewrite Hmiddle in Hnlt; Lia.lia].
                rewrite set_nth_app.
                destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                assert (m + length acc - length acc = m)%nat as -> by Lia.lia.
                f_equal.
                rewrite set_nth_app.
                destruct (lt_dec _ _) as [_|Hnlt]; [|rewrite Hmiddle in Hnlt; Lia.lia].
                rewrite set_nth_app.
                rewrite length_set_nth.
                destruct (lt_dec _ _) as [_|Hnlt]; [|rewrite Hmiddle in Hnlt; Lia.lia].
                rewrite nth_default_seq_inbounds.
                2:{ unfold enumerate in Hlen.
                    rewrite combine_length, seq_length, Nat.min_id in Hlen.
                    rewrite Hlen. Lia.lia. }
                rewrite PeanoNat.Nat.add_0_l.
                f_equal. cbv [default HasDefault_F].
                assert (nth_default 0 zetas (2 ^ k + j) = nth_default 0 (List.map (fun x : N => zeta ^ x) (cyclotomic_decompose (S k))) (2 * j)) as <-.
                { rewrite zetas_eq.
                  erewrite map_nth_default.
                  2:{ rewrite zeta_powers_length.
                      generalize (Nat.pow_le_mono_r 2%nat _ _ ltac:(Lia.lia) Hk).
                      rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia. }
                  destruct (@cyclotomic_decompose_zeta_powers_nth (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia) k km1 j Hk ltac:(Lia.lia)) as [v [Hv1 Hv2]].
                  instantiate (1 := N0).
                  rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hv1).
                  erewrite map_nth_default.
                  2:{ rewrite cyclotomic_decompose_length, PeanoNat.Nat.pow_succ_r'; Lia.lia. }
                  instantiate (1 := N0).
                  rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hv2).
                  reflexivity. }
                f_equal. }
              apply IH. Lia.lia. }
          rewrite IH by Lia.lia. cbn. rewrite Z2Nat.Z.pow_Zpow.
          assert (Z.of_nat 2 = 2)%Z as -> by Lia.lia.
          rewrite <- Z.pow_add_r by Lia.lia.
          f_equal; [rewrite Nat2Z.inj_succ, Z.pow_succ_r by Lia.lia; Lia.lia|].
          f_equal; [f_equal; Lia.lia|].
          rewrite <- Hlen, firstn_all, skipn_all by Lia.lia.
          rewrite ListUtil.List.map_nil, concat_nil, app_nil_r. reflexivity. }
      rewrite IH by Lia.lia. simpl. reflexivity.
    Qed.
  End Correctness.
End NTT.

Section NTT_INVERSE.
  Context {q: positive}.
  Local Notation F := (F q).
  Context {n: nat} {km1: nat}.
  Local Open Scope F_scope.

  Variables (zetas: list F) (c: F).

  Local Existing Instance HasDefault_F.

  Definition div_loop (i:Z) (p: ListArray.t F): ListArray.t F :=
    nd_ranged_for_all 0%Z i
      (fun p j =>
         let/n x := ListArray.get p j in
         let/n p := ListArray.put p j (c * x) in
         p)
      p.

  Definition inverse_polynomial_decompose_loop (i start old_len: Z) (z: F) (p: ListArray.t F) :=
    nd_ranged_for_all start (start + i)
      (fun p j =>
         let/n tmp := ListArray.get p j in
         let/n x := ListArray.get p (j + old_len)%Z in
         let/n p := ListArray.put p j (tmp + x) in
         let/n x := (x - tmp) in
         let/n p := ListArray.put p (j + old_len)%Z (z * x) in
         p
      )
      p.

  Definition inverse_polynomial_list_loop (k old_len len: Z) (state: \<< Z, Z, ListArray.t F \>>) :=
    nd_ranged_for_all 0%Z k
      (fun state _ =>
         let '\< m, start, p \> := state in
         let/n m := (m - 1)%Z in
         let/n z := InlineTable.get zetas m in
         let/n p :=
           inverse_polynomial_decompose_loop old_len start old_len z p in
         let/n start := (start + len)%Z in
         \< m, start, p \>
      )
      state.

  Definition inverse_layer_decomposition_loop (n: nat) (state: \<< Z, Z, ListArray.t F \>>) :=
      nd_ranged_for_all 0%Z (Z.of_nat n)
        (fun state i =>
           let '\< m, len, p \> := state in
           let/n start := 0%Z in
           let/n old_len := len in
           let/n len := Z.shiftl len 1 in
           let/n (m, start, p) :=
             inverse_polynomial_list_loop (Z.pow 2 (Z.of_nat km1 - (i + 1))) old_len len \< m, start, p\> in
           \< m, len, p \>
        )
        state.

  Definition NTT_inverse_gallina (p: ListArray.t F): ListArray.t F :=
    let/n m := (Z.pow 2 (Z.of_nat km1)) in
    let/n len := (Z.pow 2 (Z.of_nat (n - km1))) in
    let/n (m, len, p) :=
      inverse_layer_decomposition_loop km1 \< m, len, p \> in
    let/n p := div_loop (Z.pow 2 (Z.of_nat n)) p
    in p.

  Section Correctness.
    Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
      {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.

    Context {zeta: F}.

    Local Notation NTT_inverse_nodiv_spec := (@NTT_psi_list_no_div q zeta (N.of_nat km1) n).
    Local Notation NTT_inverse_spec := (@NTT_psi_list q zeta (N.of_nat km1) n km1).
    Local Notation NTT_inverse_layer_spec := (@NTT_psi_layer_list q zeta (N.of_nat km1) n).
    Local Notation enumerate := Datatypes.List.enumerate.

    Hypothesis n_ge_km1: (km1 <= n)%nat.
    Hypothesis zetas_eq: zetas = List.map (fun k => F.pow zeta k) (@zeta_powers (N.of_nat km1) km1).
    Hypothesis Hkm1: zeta ^ (N.pow 2 (N.of_nat km1)) = F.opp 1.
    Hypothesis c_eq: c = F.inv (F.of_Z _ (Zpower.two_power_nat km1)).

    Lemma NTT_inverse_nodiv_spec_as_fold_right:
      forall k p,
        NTT_inverse_nodiv_spec k p = fold_right NTT_inverse_layer_spec p (seq 0 k).
    Proof.
      induction k; intros; [reflexivity|].
      rewrite seq_S, fold_right_app, PeanoNat.Nat.add_0_l; simpl.
      apply IHk.
    Qed.

    Lemma NTT_inverse_gallina_correct (p: list F) (Hp: length p = Nat.pow 2 n):
      NTT_inverse_gallina p = NTT_inverse_spec p.
    Proof.
      unfold NTT_inverse_gallina, div_loop, inverse_layer_decomposition_loop, inverse_polynomial_list_loop, inverse_polynomial_decompose_loop.
      unfold nlet.
      match goal with
      | |- context [nd_ranged_for_all 0%Z (Z.of_nat km1) ?f ?x] =>
          assert (nd_ranged_for_all 0%Z (Z.of_nat km1) f x = \< 1%Z, Z.pow 2 (Z.of_nat n), NTT_inverse_nodiv_spec km1 p \>) as ->
      end.
      { rewrite <- (Z.add_0_l (Z.of_nat km1)), <- fold_left_as_nd_ranged_for_all, Z.add_0_l.
        unfold z_range; rewrite z_range'_seq by reflexivity.
        rewrite Z.sub_0_r, Nat2Z.id. rewrite fold_left_map.
        match goal with
        | |- fold_left ?f (seq _ ?up) \< ?m, ?len, ?p \> = _ =>
            assert (forall i, (i <= up)%nat -> fold_left f (seq (Z.to_nat 0) i) \< m, len, p \> = \< (Z.pow 2 (Z.of_nat (km1 - i)%nat))%Z, (Z.pow 2 (Z.of_nat (n - km1 + i)%nat)%Z), fold_right NTT_inverse_layer_spec p (seq (up - i) i) \>) as ->; try Lia.lia
        end.
        { induction i; intros Hi. unfold NTT_inverse_nodiv_spec.
          - simpl. rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r.
            reflexivity.
          - rewrite seq_S, fold_left_app, Nat.add_0_l, IHi by Lia.lia.
            cbn [fold_left]. cbn [P2.car P2.cdr]. clear IHi.
            rewrite Z.shiftl_mul_pow2 by Lia.lia.
            rewrite <- Z.pow_add_r by Lia.lia.
            assert (Z.of_nat km1 - (Z.of_nat i + 1) = Z.of_nat (km1 - S i))%Z as -> by Lia.lia.
            assert (Z.of_nat (n - km1 + i) + 1 = Z.of_nat (n - km1 + S i))%Z as -> by Lia.lia.
            match goal with
            | |- context [nd_ranged_for_all ?a ?b ?f ?x] =>
                assert (nd_ranged_for_all a b f x = nd_ranged_for_all a (0 + Z.of_nat (Nat.pow 2 (km1 - S i))) f x) as ->
            end.
            { f_equal. rewrite <- (Z.add_0_l (Z.pow 2 _)). f_equal.
              rewrite Nat2Z.inj_pow. reflexivity. }
            rewrite <- Nat_iter_as_nd_ranged_for_all.
            cbn [seq fold_right]. assert (S (km1 - S i) = km1 - i)%nat as -> by Lia.lia.
            set (l := fold_right _ _ _).
            unfold NTT_inverse_layer_spec, fold_left_chunked.
            assert (Hl: length l = length p).
            { unfold l. apply ListUtil.fold_right_invariant; [reflexivity|].
              intros. rewrite (@NTT_psi_layer_list_length q zeta (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia)). auto. }
            rewrite Hp in Hl.
            assert (length (chunk (2 ^ (n - (km1 - S i))) l) = Nat.pow 2 (km1 - S i))%nat as Hlen.
            { rewrite length_chunk by (generalize (NatUtil.pow_nonzero 2 (n - (km1 - S i)) ltac:(Lia.lia)); Lia.lia).
              rewrite Hl.
              replace n with ((km1- S i) + (n - (km1 - S i)))%nat at 1 by Lia.lia.
              rewrite PeanoNat.Nat.pow_add_r.
              apply Nat.div_up_exact.
              generalize (NatUtil.pow_nonzero 2 (n - (km1 - S i))%nat ltac:(Lia.lia)); Lia.lia. }
            assert (length (enumerate 0 (chunk (2 ^ (n - (km1 - S i))) l)) = Nat.pow 2 (km1 - S i))%nat as Hlen2.
            { unfold enumerate. rewrite combine_length, seq_length, PeanoNat.Nat.min_id, Hlen; reflexivity. }
            assert (HF: Forall (fun x => length x = (2 ^ (n - (km1 - S i)))%nat) (chunk (2 ^ (n - (km1 - S i))) l)).
            { eapply Forall_chunk_length_eq. rewrite Hl.
              replace n with ((n - (km1 - S i)) + (km1 - S i))%nat at 1 by Lia.lia.
              rewrite PeanoNat.Nat.pow_add_r. reflexivity. }
            match goal with
            | |- context [Nat.iter ?up ?f \< ?m, ?start, ?p \>] =>
                match goal with
                | |- context [fold_left ?g ?a nil] =>
                assert (forall k, (k <= up)%nat -> Nat.iter k f \< m, start, p \> = \< (m - Z.of_nat k)%Z, (start + Z.of_nat k * 2 ^ Z.of_nat (n - km1 + S i))%Z, (fold_left g (List.firstn k a) nil) ++ (concat (List.map snd (List.skipn k a))) \>) as ->; try Lia.lia
                end
            end.
            { induction k; intro Hk.
              - simpl. rewrite Z.sub_0_r.
                unfold enumerate. rewrite map_combine_snd by (rewrite seq_length; reflexivity).
                rewrite concat_chunk. reflexivity.
              - rewrite Nat.iter_succ, IHk by Lia.lia.
                f_equal; [Lia.lia|]. f_equal; [Lia.lia|].
                clear IHk. rewrite Z.add_0_l.
                rewrite <- fold_left_as_nd_ranged_for_all.
                rewrite <- (firstn_nth _ _ _ (0%nat, nil)) by (rewrite Hlen2; Lia.lia).
                rewrite (ListUtil.skipn_nth_default k _ (0%nat, nil)) by (rewrite Hlen2; Lia.lia).
                unfold z_range. rewrite Z.add_simpl_l.
                rewrite Z2Nat.inj_pow by Lia.lia.
                rewrite Nat2Z.id. assert (Z.to_nat 2 = 2)%nat as -> by Lia.lia.
                rewrite z_range'_seq by Lia.lia.
                rewrite Z2Nat.inj_mul, Z2Nat.inj_pow, Nat2Z.id, Nat2Z.id by Lia.lia.
                assert (Z.to_nat 2 = 2)%nat as -> by Lia.lia.
                rewrite fold_left_app. cbn [fold_left].
                set (hd := fold_left _ (List.firstn _ _) nil).
                rewrite nth_default_eq.
                unfold enumerate. rewrite combine_nth by (rewrite seq_length; Lia.lia).
                rewrite seq_nth by (rewrite Hlen; Lia.lia).
                cbn [List.map snd concat].
                set (middle := nth k _ nil).
                set (tl := concat _).
                rewrite PeanoNat.Nat.add_0_l.
                unfold NTT_base_psi_unpacked_list.
                assert (length hd = k * (Nat.pow 2 (n - (km1 - S i))))%nat as Hlen_hd.
                { unfold hd. erewrite fold_left_ext; [rewrite <- ListUtil.eq_flat_map_fold_left|].
                  2: instantiate (1:=(fun y => NTT_base_psi_unpacked_list (snd y) (2 ^ (n - S (km1 - S i))) (F.inv (zeta ^ nth_default 0%N (cyclotomic_decompose (S (km1 - S i))) (2 * (fst y))%nat)))).
                  2: intros a b; destruct b; reflexivity.
                  erewrite flat_map_constant_length.
                  2:{ intros x Hx. rewrite NTT_base_psi_unpacked_list_length.
                      apply ListUtil.In_firstn in Hx.
                      unfold enumerate in Hx.
                      destruct x. apply in_combine_r in Hx.
                      eapply (Forall_In HF). auto. }
                  rewrite firstn_length. unfold enumerate.
                  rewrite combine_length, seq_length, Hlen, PeanoNat.Nat.min_id.
                  rewrite Nat.min_l by Lia.lia. reflexivity. }
                assert (length middle = (2 ^ (n - (km1 - S i))))%nat as Hlen_mid.
                { eapply (Forall_In HF). unfold middle.
                  apply nth_In. rewrite Hlen. Lia.lia. }
                rewrite <- (PeanoNat.Nat.add_0_l (k * _)).
                rewrite seq_add, List.map_map, fold_left_map.
                assert (n - S (km1 - S i) = n - km1 + i)%nat as <- by Lia.lia.
                rewrite <- List.app_assoc.
                match goal with
                | |- fold_left ?f _ ?l = hd ++ (fold_left ?g _ ?l2) ++ tl =>
                    assert (forall m, (m <= Nat.pow 2 (n - S (km1 - S i)))%nat -> fold_left f (seq 0%nat m) l = hd ++ fold_left g (seq 0%nat m) l2 ++ tl) as ->; try Lia.lia
                end.
                { induction m; intros Hm; [reflexivity|].
                  rewrite seq_S, fold_left_app, fold_left_app, IHm by Lia.lia.
                  set (acc := fold_left _ _ middle).
                  clear IHm. rewrite PeanoNat.Nat.add_0_l.
                  cbn [fold_left].
                  unfold InlineTable.get. rewrite <- nth_default_eq.
                  repeat rewrite put_eq_set_nth.
                  repeat rewrite get_eq_nth_default.
                  cbv [cast Convertible_Z_nat].
                  rewrite Nat2Z.inj_add.
                  repeat rewrite Z2Nat.inj_add by Lia.lia.
                  repeat rewrite Z2Nat.inj_sub by Lia.lia.
                  repeat rewrite Z2Nat.inj_pow by Lia.lia.
                  repeat rewrite Nat2Z.id.
                  assert (Z.to_nat 2 = 2)%nat as -> by reflexivity.
                  assert (n - km1 + S i = n - (km1 - S i))%nat as -> by Lia.lia.
                  assert (length acc = length middle) as Hlen_acc.
                  { unfold acc. apply fold_left_invariant; [reflexivity|].
                    intros. repeat rewrite length_set_nth; auto. }
                  rewrite ListUtil.nth_default_app.
                  rewrite Hlen_hd. destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                  rewrite ListUtil.nth_default_app.
                  rewrite Hlen_acc, Hlen_mid.
                  assert (2 ^ (n - S (km1 - S i)) < 2 ^ (n - (km1 - S i)))%nat as Hmono.
                  { apply Nat.pow_lt_mono_r; Lia.lia. }
                  assert (m + k * 2 ^ (n - (km1 - S i)) + 2 ^ (n - S (km1 - S i)) - k * 2 ^ (n - (km1 - S i)) = m + 2 ^ (n - S (km1 - S i)))%nat as -> by Lia.lia.
                  assert (2 ^ (n - (km1 - S i)) = 2 * (2 ^ (n - S (km1 - S i))))%nat as Heq.
                  { rewrite <- PeanoNat.Nat.pow_succ_r'.
                    f_equal. Lia.lia. }
                  destruct (lt_dec _ _) as [_|]; [|Lia.lia].
                  rewrite ListUtil.nth_default_app, Hlen_hd.
                  destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                  rewrite ListUtil.nth_default_app, Hlen_acc, Hlen_mid.
                  destruct (lt_dec _ _); [|Lia.lia].
                  rewrite set_nth_app, Hlen_hd.
                  destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                  rewrite set_nth_app, Hlen_hd.
                  destruct (lt_dec _ _) as [|_]; [Lia.lia|].
                  rewrite set_nth_app, Hlen_acc, Hlen_mid.
                  destruct (lt_dec _ _) as [_|]; [|Lia.lia].
                  rewrite set_nth_app, length_set_nth, Hlen_acc, Hlen_mid.
                  destruct (lt_dec _ _) as [_|]; [|Lia.lia].
                  assert (m + k * 2 ^ (n - (km1 - S i)) - k * 2 ^ (n - (km1 - S i)) = m)%nat as -> by Lia.lia.
                  assert (m + k * 2 ^ (n - (km1 - S i)) + 2 ^ (n - S (km1 - S i)) - k * 2 ^ (n - (km1 - S i)) = m + 2 ^ (n - S (km1 - S i)))%nat as -> by Lia.lia.
                  f_equal. f_equal.
                  apply nth_error_ext.
                  intros o. repeat rewrite nth_set_nth.
                  repeat rewrite length_set_nth.
                  rewrite Hlen_acc, Hlen_mid.
                  cbv [default HasDefault_F].
                  destruct (Nat.eq_dec o (m + _)) as [->|].
                  - destruct (lt_dec _ _) as [_|]; [|Lia.lia].
                    rewrite set_nth_nth_default, NatUtil.eq_nat_dec_refl by (rewrite length_set_nth, Hlen_acc, Hlen_mid; Lia.lia).
                    f_equal.
                    transitivity ((F.opp (nth_default 0 zetas (2 ^ (km1 - i) - k - Z.to_nat 1))) * (nth_default 0 acc m - nth_default 0 acc (m + 2 ^ (n - S (km1 - S i))))).
                    { set (x := nth_default 0 zetas (2 ^ (km1 - i) - k - Z.to_nat 1)).
                      set (y := nth_default 0 acc (m + 2 ^ (n - S (km1 - S i)))).
                      set (z := nth_default 0 acc m).
                      (* Now goal is x * (y - z) = F.opp x * (z - y) *)
                      rewrite Ring.mul_opp_l, <- Ring.mul_opp_r.
                      do 2 rewrite Hierarchy.ring_sub_definition.
                      rewrite Group.inv_op, Group.inv_inv. reflexivity. }
                    f_equal.
                    rewrite zetas_eq.
                    erewrite map_nth_default.
                    2:{ rewrite zeta_powers_length.
                        generalize (NatUtil.pow_nonzero 2%nat (km1 - i)%nat ltac:(Lia.lia)).
                        generalize (Nat.pow_le_mono_r 2%nat (km1 - i)%nat km1 ltac:(Lia.lia) ltac:(Lia.lia)).
                        Lia.lia. }
                    rewrite (@neg_zeta_power_eq _ _ (N.of_nat km1) Hkm1).
                    destruct (@cyclotomic_decompose_zeta_powers_nth (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia) (km1 - S i) km1 k ltac:(Lia.lia) ltac:(Lia.lia)) as [v [Hv1 Hv2]].
                    assert (km1 - i = S (km1 - S i))%nat as -> by Lia.lia.
                    rewrite PeanoNat.Nat.pow_succ_r'.
                    assert (2 * 2 ^ (km1 - S i) - k - Z.to_nat 1 = 2 ^ (km1 - S i) + (2 ^ (km1 - S i) - k - 1))%nat as -> by Lia.lia.
                    destruct (@cyclotomic_decompose_zeta_powers_nth (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia) (km1 - S i) km1 (2 ^ (km1 - S i) - k - 1) ltac:(Lia.lia) ltac:(Lia.lia)) as [v' [Hv1' Hv2']].
                    instantiate (1 := N0).
                    rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hv1'), (ListUtil.nth_error_value_eq_nth_default _ _ _ Hv2).
                    assert (nth_error (@cyclotomic_decompose (N.of_nat km1) (S (km1 - S i))) (2 ^ S (km1 - S i) - 1 - 2 * k) = Some (2 ^ N.of_nat km1 + v')%N) as Hvv.
                    { rewrite PeanoNat.Nat.pow_succ_r'.
                      assert (2 * 2 ^ (km1 - S i) - 1 - 2 * k = 2 * (2 ^ (km1 - S i) - k - 1) + 1)%nat as -> by Lia.lia.
                      destruct (nth_error_length_exists_value (2 ^ (km1 - S i) - k - 1) (@cyclotomic_decompose (N.of_nat km1) (km1 - S i)) ltac:(rewrite cyclotomic_decompose_length; Lia.lia)) as [vx Hvx].
                      destruct (@cyclotomic_decompose_S_nth_error (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia) (km1 - S i) ltac:(Lia.lia) (2 ^ (km1 - S i) - k - 1) vx Hvx) as [X1 [X2 _]].
                      rewrite X2. rewrite X1 in Hv2'. congruence. }
                    destruct (@cyclotomic_decompose_inv q zeta (N.of_nat km1) Hkm1 n ltac:(rewrite Nnat.Nat2N.id; Lia.lia) (S (km1 - S i)) ltac:(Lia.lia) (2 * k) ltac:(rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia) v (2 ^ N.of_nat km1 + v') Hv2 Hvv) as [XA XB].
                    apply Field.right_inv_unique. auto.
                  - destruct (Nat.eq_dec o m) as [->|].
                    + destruct (lt_dec _ _); reflexivity.
                    + reflexivity. }
                reflexivity. }
            f_equal.
            + rewrite Nat2Z.inj_pow. assert (km1 - i = S (km1 - S i))%nat as -> by Lia.lia.
              rewrite Nat2Z.inj_succ, Z.pow_succ_r by Lia.lia.
              Lia.lia.
            + f_equal. f_equal.
              rewrite firstn_all, skipn_all by Lia.lia.
              cbn [List.map concat]. rewrite List.app_nil_r. reflexivity. }
        rewrite PeanoNat.Nat.sub_diag, Nat2Z.inj_0, Z.pow_0_r.
        assert (n - km1 + km1 = n)%nat as -> by Lia.lia.
        rewrite NTT_inverse_nodiv_spec_as_fold_right.
        f_equal. }
      unfold NTT_inverse_spec.
      assert (Z.pow 2 _ = Z.of_nat (length (NTT_inverse_nodiv_spec km1 p))) as ->.
      { rewrite (@NTT_psi_list_no_div_length q zeta (N.of_nat km1) n ltac:(rewrite Nnat.Nat2N.id; Lia.lia)), Hp, Nat2Z.inj_pow. reflexivity. }
      symmetry; eapply map_as_nd_ranged_for_all.
      unfold acts_as_replace_nth. intros.
      rewrite put_eq_set_nth, get_eq_nth_default.
      cbv [cast Convertible_Z_nat]. rewrite Nat2Z.id.
      rewrite nth_default_app, set_nth_app.
      destruct (lt_dec _ _) as [|_]; [Lia.lia|].
      rewrite PeanoNat.Nat.sub_diag.
      rewrite nth_default_cons, set_nth_cons, c_eq.
      f_equal. rewrite Hierarchy.field_div_definition.
      rewrite Hierarchy.commutative. f_equal.
    Qed.
  End Correctness.
End NTT_INVERSE.
