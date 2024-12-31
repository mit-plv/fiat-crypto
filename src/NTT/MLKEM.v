Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.CyclotomicDecomposition.
Require Import Crypto.NTT.BedrockNTT.
Require Import Crypto.NTT.RupicolaBarrettReduction.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Api.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Section MLKEM.
  Local Notation q := 3329%positive.
  Local Notation F := (F q).
  Local Notation zeta := (F.of_Z q 17%Z).
  Local Notation n := 8%nat.
  Local Notation km1 := 7%nat.
  Local Notation add := "mlkem_felem_add".
  Local Notation sub := "mlkem_felem_sub".
  Local Notation mul := "mlkem_felem_mul".
  Local Notation reduce := "mlkem_barrett_reduce".
  Local Notation reduce_small := "mlkem_barrett_reduce_small".

  Local Notation mlkem_make_zetas := (@make_zetas q zeta).

  (* Sanity check *)
  Lemma mlkem_prime_q: prime (Z.pos q).
  Proof.
    apply (Pocklington_refl
             (Pock_certif 3329 3 ((2,8)::nil)%positive 1)
             ((Proof_certif 2 prime_2) ::
                nil)).
    native_cast_no_check (refl_equal true).
  Qed.

  (* ζ^0 to ζ^128 *)
  Definition mlkem_zetas_128 :=
    [1%Z; 17; 289; 1584; 296; 1703; 2319; 2804; 1062; 1409; 650; 1063; 1426; 939;
     2647; 1722; 2642; 1637; 1197; 375; 3046; 1847; 1438; 1143; 2786; 756; 2865;
     2099; 2393; 733; 2474; 2110; 2580; 583; 3253; 2037; 1339; 2789; 807; 403; 193;
     3281; 2513; 2773; 535; 2437; 1481; 1874; 1897; 2288; 2277; 2090; 2240; 1461;
     1534; 2775; 569; 3015; 1320; 2466; 1974; 268; 1227; 885; 1729; 2761; 331;
     2298; 2447; 1651; 1435; 1092; 1919; 2662; 1977; 319; 2094; 2308; 2617; 1212;
     630; 723; 2304; 2549; 56; 952; 2868; 2150; 3260; 2156; 33; 561; 2879; 2337;
     3110; 2935; 3289; 2649; 1756; 3220; 1476; 1789; 452; 1026; 797; 233; 632; 757;
     2882; 2388; 648; 1029; 848; 1100; 2055; 1645; 1333; 2687; 2402; 886; 1746;
     3050; 1915; 2594; 821; 641; 910; 2154; -1].

  Lemma mlkem_zetas_128_spec:
    mlkem_make_zetas 128 = List.map (F.of_Z _) mlkem_zetas_128.
  Proof.
    pose (list_eq_strong := fix list_eq_strong A B (eqx: A -> B -> Prop) x y :=
            match x with
            | nil => match y with
                    | nil => True
                    | _ => False
                    end
            | x0::x1 => match y with
                       | nil => False
                       | y0::y1 => eqx x0 y0 /\ (eqx x0 y0 -> list_eq_strong A B eqx x1 y1)
                       end
            end).
    assert (Hstrong: forall A B eq x y, list_eq_strong A B eq x y -> @ListUtil.list_eq A B eq x y).
    { induction x; simpl; auto.
      intros; destruct y; auto. destruct H; split; auto. }
    apply ListUtil.list_eq_to_leq, Hstrong.
    split; [reflexivity|intro H].
    repeat (split; [rewrite H; rewrite <- ModularArithmeticTheorems.F.of_Z_mul; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|clear H; intro H]).
    reflexivity.
  Qed.

  (* Sanity check ζ^(2^km1) = -1 *)
  Lemma mlkem_zeta_km1_ok:
    F.pow zeta (N.of_nat (Nat.pow 2 km1)) = F.of_Z _ (-1).
  Proof.
    assert (Nat.pow 2 7 = 128)%nat as -> by reflexivity.
    generalize (@make_zetas_spec q zeta 128%nat 128%nat ltac:(reflexivity)).
    rewrite mlkem_zetas_128_spec. intro X.
    unfold mlkem_zetas_128 in X. cbv [List.map nth_error] in X.
    congruence.
  Qed.

  Definition mlkem_zetas := List.map (fun k => nth_default 0%F (List.map (F.of_Z q) mlkem_zetas_128) (N.to_nat k)) (@zeta_powers (N.of_nat km1) km1).

  Lemma mlkem_zetas_correct:
    mlkem_zetas = List.map (fun k => F.pow zeta k) (@zeta_powers (N.of_nat km1) km1).
  Proof.
    unfold mlkem_zetas. rewrite <- mlkem_zetas_128_spec.
    apply nth_error_ext. intros.
    do 2 rewrite ListUtil.nth_error_map.
    destruct (nth_error (zeta_powers km1) i) as [k|] eqn:Hk; [|reflexivity].
    cbn [option_map].
    assert (N.to_nat k <= 128)%nat as Hk'.
    { cbv in Hk. do 128 (destruct i as [|i]; [simpl in Hk; inversion Hk; subst k; Lia.lia|]).
      destruct i; cbn in Hk; congruence. }
    apply (@make_zetas_spec q zeta) in Hk'.
    rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hk').
    rewrite Nnat.N2Nat.id. reflexivity.
  Qed.

  Definition mlkem_c: F := F.of_Z _ 3303.

  Lemma mlkem_c_correct:
    mlkem_c = F.inv (F.of_Z q (two_power_nat km1)).
  Proof.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    reflexivity.
  Qed.

  Definition mlkem_ntt := @br2_ntt 64 (Naive.word _) q n km1 mlkem_zetas F_to_Z add sub mul.
  Definition mlkem_inverse_ntt := @br2_ntt_inverse 64 (Naive.word _) q n km1 mlkem_c mlkem_zetas F_to_Z add sub mul.

  Definition mlkem_barrett_reduce_small := @reduce_small_br2fn 64 (Naive.word _) q.
  Definition mlkem_barrett_reduce := @reduce_br2fn 64 (Naive.word _) q.
  Definition mlkem_felem_add := @add_br2fn reduce_small.
  Definition mlkem_felem_sub := @sub_br2fn q reduce_small.
  Definition mlkem_felem_mul := @mul_br2fn reduce.

  Definition mlkem_funcs :=
    [ ("mlkem_ntt", mlkem_ntt)
    ; ("mlkem_inverse_ntt", mlkem_inverse_ntt)
    ; (reduce_small, mlkem_barrett_reduce_small)
    ; (reduce, mlkem_barrett_reduce)
    ; (add, mlkem_felem_add)
    ; (sub, mlkem_felem_sub)
    ; (mul, mlkem_felem_mul)
    ].

  Lemma mlkem_reduce_small_ok:
    @spec_of_reduce_small _ _ _ _ _ _ q reduce_small (map.of_list mlkem_funcs).
  Proof.
    apply (reduce_small_br2fn_ok (modulus_pos:=q) (modulus_prime:=mlkem_prime_q) (modulus_not_2:=ltac:(Lia.lia))); auto.
    - cbv. reflexivity.
    - exact I.
  Qed.

  Lemma mlkem_felem_add_ok:
    @spec_of_add _ _ _ _ _ _ _ q add (map.of_list mlkem_funcs).
  Proof.
    apply (add_br2fn_ok (modulus_pos:=q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_small_name:=reduce_small)).
    - compute. reflexivity.
    - reflexivity.
    - apply mlkem_reduce_small_ok.
  Qed.

  Lemma mlkem_felem_sub_ok:
    @spec_of_sub _ _ _ _ _ _ _ q sub (map.of_list mlkem_funcs).
  Proof.
    apply (sub_br2fn_ok (modulus_pos:=q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_small_name:=reduce_small)).
    - compute. reflexivity.
    - reflexivity.
    - apply mlkem_reduce_small_ok.
  Qed.

  Lemma mlkem_reduce_ok:
    @spec_of_reduce _ _ _ _ _ _ q reduce (map.of_list mlkem_funcs).
  Proof.
    apply (reduce_br2fn_ok (modulus_pos:=q) (modulus_prime:=mlkem_prime_q) (modulus_not_2:=ltac:(Lia.lia))); auto.
    - cbv. reflexivity.
    - exact I.
  Qed.

  Lemma mlkem_felem_mul_ok:
    @spec_of_mul _ _ _ _ _ _ _ q mul (map.of_list mlkem_funcs).
  Proof.
    apply (mul_br2fn_ok (modulus_pos:=q) (modulus_prime:=mlkem_prime_q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_name:=reduce)); try reflexivity.
    apply mlkem_reduce_ok.
  Qed.

  Lemma mlkem_ntt_ok:
    @spec_of_ntt _ _ _ _ _ _ "mlkem_ntt" q n km1 mlkem_zetas feval (map.of_list mlkem_funcs).
  Proof.
    eapply br2_ntt_ok.
    3-6: cbn; try Lia.lia.
    - apply F.zero.
    - eapply feval_ok. compute. reflexivity.
    - reflexivity.
    - apply mlkem_felem_mul_ok.
    - apply mlkem_felem_sub_ok.
    - apply mlkem_felem_add_ok.
      Unshelve. Lia.lia.
  Qed.

  Lemma mlkem_inverse_ntt_ok:
    @spec_of_ntt_inverse _ _ _ _ _ _ "mlkem_inverse_ntt" q n km1 mlkem_c mlkem_zetas feval (map.of_list mlkem_funcs).
  Proof.
    eapply br2_ntt_inverse_ok.
    2-5: cbn; Lia.lia.
    - eapply feval_ok. compute. reflexivity.
    - reflexivity.
    - apply mlkem_felem_mul_ok.
    - apply mlkem_felem_sub_ok.
    - apply mlkem_felem_add_ok.
      Unshelve. Lia.lia.
  Qed.

  (* Eval compute in ToCString.c_module mlkem_funcs. *)
End MLKEM.
