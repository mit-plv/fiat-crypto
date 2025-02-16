Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.CyclotomicDecomposition.
Require Import Crypto.NTT.BedrockNTT.
Require Import Crypto.NTT.RupicolaMontgomeryArithmetic.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Api.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Section MLDSA.
  Local Notation q := 8380417%positive.
  Local Notation F := (F q).
  Local Notation zeta := (F.of_Z q 1753%Z).
  Local Notation n := 8%nat.
  Local Notation km1 := 8%nat.
  Local Notation add := "mldsa_felem_montgomery_add".
  Local Notation sub := "mldsa_felem_montgomery_sub".
  Local Notation mul := "mldsa_felem_montgomery_mul".
  Local Notation from_montgomery := "mldsa_from_montgomery".
  Local Notation to_montgomery := "mldsa_to_montgomery".

  Local Notation mldsa_make_zetas := (@make_zetas q zeta).

  (* Sanity check *)
  Lemma mldsa_prime_q: prime (Z.pos q).
  Proof.
    apply (Pocklington_refl
             (Pock_certif 8380417 5 ((2,13)::nil)%positive 1)
             ((Proof_certif 2 prime_2) ::
                nil)).
    native_cast_no_check (refl_equal true).
  Qed.

  (* ζ^0 to ζ^256 *)
  Definition mldsa_zetas_256 :=
    [1%Z; 1753; 3073009; 6757063; 3602218; 4234153; 5801164; 3994671; 5010068;
     8352605; 1528066; 5346675; 3415069; 2998219; 1356448; 6195333; 7778734;
     1182243; 2508980; 6903432; 394148; 3747250; 7062739; 3105558; 5152541;
     6695264; 4213992; 3980599; 5483103; 7921677; 348812; 8077412; 5178923;
     2660408; 4183372; 586241; 5269599; 2387513; 3482206; 3363542; 4855975;
     6400920; 7814814; 5767564; 3756790; 7025525; 4912752; 5365997; 3764867;
     4423672; 2811291; 507927; 2071829; 3195676; 3901472; 860144; 7737789; 4829411;
     1736313; 1665318; 2917338; 2039144; 4561790; 1900052; 3765607; 5720892;
     5744944; 6006015; 2740543; 2192938; 5989328; 7009900; 2663378; 1009365;
     1148858; 2647994; 7562881; 8291116; 2683270; 2358373; 2682288; 636927;
     1937570; 2491325; 1095468; 1239911; 3035980; 508145; 2453983; 2678278;
     1987814; 6764887; 556856; 4040196; 1011223; 4405932; 5234739; 8321269;
     5258977; 527981; 3704823; 8111961; 7080401; 545376; 676590; 4423473; 2462444;
     749577; 6663429; 7070156; 7727142; 2926054; 557458; 5095502; 7270901; 7655613;
     3241972; 1254190; 2925816; 140244; 2815639; 8129971; 5130263; 1163598;
     3345963; 7561656; 6143691; 1054478; 4808194; 6444997; 1277625; 2105286;
     3182878; 6607829; 1787943; 8368538; 4317364; 822541; 482649; 8041997; 1759347;
     141835; 5604662; 3123762; 3542485; 87208; 2028118; 1994046; 928749; 2296099;
     2461387; 7277073; 1714295; 4969849; 4892034; 2569011; 3192354; 6458423;
     8052569; 3531229; 5496691; 6600190; 5157610; 7200804; 2101410; 4768667;
     4197502; 214880; 7946292; 1596822; 169688; 4148469; 6444618; 613238; 2312838;
     6663603; 7375178; 6084020; 5396636; 7192532; 4361428; 2642980; 7153756;
     3430436; 4795319; 635956; 235407; 2028038; 1853806; 6500539; 6458164; 7598542;
     3761513; 6924527; 3852015; 6346610; 4793971; 6653329; 6125690; 3020393;
     6705802; 5926272; 5418153; 3009748; 4805951; 2513018; 5601629; 6187330;
     2129892; 4415111; 4564692; 6987258; 4874037; 4541938; 621164; 7826699;
     1460718; 4611469; 5183169; 1723229; 3870317; 4908348; 6026202; 4606686;
     5178987; 2772600; 8106357; 5637006; 1159875; 5199961; 6018354; 7609976;
     7044481; 4620952; 5046034; 4357667; 4430364; 6161950; 7921254; 7987710;
     7159240; 4663471; 4158088; 6545891; 2156050; 8368000; 3374250; 6866265;
     2283733; 5925040; 3258457; 5011144; 1858416; 6201452; 1744507; 7648983;
     -1].

  Lemma mldsa_zetas_256_spec:
    mldsa_make_zetas 256 = List.map (F.of_Z _) mldsa_zetas_256.
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
  Lemma mldsa_zeta_km1_ok:
    F.pow zeta (N.of_nat (Nat.pow 2 km1)) = F.of_Z _ (-1).
  Proof.
    assert (Nat.pow 2 km1 = 256)%nat as -> by reflexivity.
    generalize (@make_zetas_spec q zeta 256%nat 256%nat ltac:(reflexivity)).
    rewrite mldsa_zetas_256_spec. intro X.
    unfold mldsa_zetas_256 in X. cbv [List.map nth_error] in X.
    congruence.
  Qed.

  Definition mldsa_zetas := List.map (fun k => nth_default 0%F (List.map (F.of_Z q) mldsa_zetas_256) (N.to_nat k)) (@zeta_powers (N.of_nat km1) km1).

  Lemma mldsa_zetas_correct:
    mldsa_zetas = List.map (fun k => F.pow zeta k) (@zeta_powers (N.of_nat km1) km1).
  Proof.
    unfold mldsa_zetas. rewrite <- mldsa_zetas_256_spec.
    apply nth_error_ext. intros.
    do 2 rewrite ListUtil.nth_error_map.
    destruct (nth_error (zeta_powers km1) i) as [k|] eqn:Hk; [|reflexivity].
    cbn [option_map].
    assert (N.to_nat k <= 256)%nat as Hk'.
    { cbv in Hk. do 256 (destruct i as [|i]; [simpl in Hk; inversion Hk; subst k; Lia.lia|]).
      destruct i; congruence. }
    apply (@make_zetas_spec q zeta) in Hk'.
    rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hk').
    rewrite Nnat.N2Nat.id. reflexivity.
  Qed.

  Definition mldsa_c: F := F.of_Z _ 8347681.

  Lemma mldsa_c_correct:
    mldsa_c = F.inv (F.of_Z q (two_power_nat km1)).
  Proof.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    reflexivity.
  Qed.

  Definition mldsa_ntt := @br2_ntt 64 (Naive.word _) q n km1 mldsa_zetas (F_to_Z (width:=64)) add sub mul.
  Definition mldsa_inverse_ntt := @br2_ntt_inverse 64 (Naive.word _) q n km1 mldsa_c mldsa_zetas (F_to_Z (width:=64)) add sub mul.

  Definition mldsa_from_montgomery := @from_montgomery_br2fn 64 (Naive.word _) q.
  Definition mldsa_to_montgomery := @to_montgomery_br2fn1 64 (Naive.word _) q.
  Definition mldsa_felem_add := @add_br2fn 64 (Naive.word _) q.
  Definition mldsa_felem_sub := @sub_br2fn 64 (Naive.word _) q.
  Definition mldsa_felem_mul := @mul_br2fn1 64 (Naive.word _) q.

  Definition mldsa_funcs :=
    [ ("mldsa_ntt", mldsa_ntt)
    ; ("mldsa_inverse_ntt", mldsa_inverse_ntt)
    ; (from_montgomery, mldsa_from_montgomery)
    ; (to_montgomery, mldsa_to_montgomery)
    ; (add, mldsa_felem_add)
    ; (sub, mldsa_felem_sub)
    ; (mul, mldsa_felem_mul)
    ].

  Lemma q_small: 3 <= Zpos q < 2 ^ 64.
  Proof. cbn. Lia.lia. Qed.

  Lemma mldsa_felem_add_ok:
    @spec_of_add _ _ _ _ _ _ _ _ q q_small mldsa_prime_q add (map.of_list mldsa_funcs).
  Proof.
    apply (add_br2fn_ok (modulus_pos:=q) (modulus_small:=q_small) (modulus_prime:=mldsa_prime_q)).
    - cbn. Lia.lia.
    - reflexivity.
  Qed.

  Lemma mldsa_felem_sub_ok:
    @spec_of_sub _ _ _ _ _ _ _ _ q q_small mldsa_prime_q sub (map.of_list mldsa_funcs).
  Proof.
    apply (sub_br2fn_ok (modulus_pos:=q) (modulus_small:=q_small) (modulus_prime:=mldsa_prime_q)).
    - cbn. Lia.lia.
    - reflexivity.
  Qed.

  Lemma mldsa_felem_mul_ok:
    @spec_of_mul _ _ _ _ _ _ _ _ q q_small mldsa_prime_q mul (map.of_list mldsa_funcs).
  Proof.
    apply (mul_br2fn_ok1 (modulus_pos:=q) (modulus_small:=q_small) (modulus_prime:=mldsa_prime_q)).
    - cbn. Lia.lia.
    - reflexivity.
  Qed.

  Lemma mldsa_ntt_ok:
    @spec_of_ntt _ _ _ _ _ _ "mldsa_ntt" q n km1 mldsa_zetas (feval (modulus_small:=q_small) (modulus_prime:=mldsa_prime_q)) (map.of_list mldsa_funcs).
  Proof.
    eapply br2_ntt_ok.
    3-6: cbn; Lia.lia.
    - apply F.zero.
    - eapply feval_ok.
    - reflexivity.
    - apply mldsa_felem_mul_ok.
    - apply mldsa_felem_sub_ok.
    - apply mldsa_felem_add_ok.
  Qed.

  Lemma mldsa_inverse_ntt_ok:
    @spec_of_ntt_inverse _ _ _ _ _ _ "mldsa_inverse_ntt" q n km1 mldsa_c mldsa_zetas (feval (modulus_small:=q_small) (modulus_prime:=mldsa_prime_q)) (map.of_list mldsa_funcs).
  Proof.
    eapply br2_ntt_inverse_ok.
    2-5: cbn; Lia.lia.
    - eapply feval_ok.
    - reflexivity.
    - apply mldsa_felem_mul_ok.
    - apply mldsa_felem_sub_ok.
    - apply mldsa_felem_add_ok.
  Qed.

  (* Eval compute in ToCString.c_module mldsa_funcs. *)
End MLDSA.
