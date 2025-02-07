From Coq Require Import ZArith QArith Qabs Qround.
From Coq Require Import Lia.
Require Import Util.QUtil.

(*
  This is a formalization of (a part of) section 2.4 of the following paper
  Efficient Multiplication of Somewhat Small Integers Using Number-Theoretic Transforms
  Hanno Becker, Vincent Hwang, Matthias J. Kannwischer, Lorenz Panny, Bo-Yin Yang
  IWSEC 2022
*)

Local Open Scope Q_scope.

Section Qround_half_up.
  Local Coercion inject_Z : Z >-> Q.
  Local Coercion Zpos : positive >-> Z.

  Definition Qround_half_up (x: Q): Z := Qfloor (x + (1#2))%Q.

  Lemma Qfloor_approx (x: Q):
    Qabs (x - Qfloor x) < 1%Z.
  Proof.
    rewrite Qabs_Qlt_condition.
    pose proof (Qfloor_le x) as H1.
    pose proof (Qlt_floor x) as H2.
    destruct x as (x_num & x_den).
    cbv [Qlt Qle] in *. simpl in *. lia.
  Qed.

  Lemma Qround_half_up_approx (x: Q):
    Qabs (x - Qround_half_up x) <= 1#2.
  Proof.
    rewrite Qabs_Qle_condition.
    pose proof (Qfloor_le (x + (1#2))) as H1.
    pose proof (Qlt_floor (x + (1#2))) as H2.
    destruct x as (x_num & x_den).
    cbv [Qlt Qle Qplus Qround_half_up] in *. simpl in *. lia.
  Qed.

  Lemma Qfloor_diff (x1 x2: Q) (Hlt: (Qfloor x1 < Qfloor x2)%Z):
    exists (n: Z), x1 < n <= x2.
  Proof.
    exists (Qfloor x2).
    pose proof (Qlt_floor x1) as H1.
    pose proof (Qfloor_le x2) as H2.
    split; [|assumption].
    apply (Qlt_le_trans _ _ _ H1).
    cbv [Qle]; simpl. lia.
  Qed.

  Lemma Qround_half_up_diff (x1 x2: Q)
    (Hlt: (Qround_half_up x1 < Qround_half_up x2)%Z):
    exists (n: Z), x1 < n + (1#2) <= x2.
  Proof.
    unfold Qround_half_up in Hlt.
    apply Qfloor_diff in Hlt.
    destruct Hlt as (n & Hlt & Hle).
    exists (n - 1)%Z.
    destruct x1 as (x_num1 & x_den1).
    destruct x2 as (x_num2 & x_den2).
    cbv [Qlt Qle] in *; simpl in *.
    split; try lia.
  Qed.

  Lemma Qround_half_up_eq (a: Z) (b: positive):
    Qround_half_up (a#b) = if (2 * Z.modulo a b <? b)%Z then Qfloor (a#b) else ((Qfloor (a#b)) + 1)%Z.
  Proof.
    cbv [Qround_half_up Qplus Qnum Qden]. rewrite Z.mul_1_l.
    repeat rewrite Qmake_Qdiv, <- Zdiv_Qdiv.
    pose proof (Z.mod_pos_bound a b ltac:(lia)) as Hab.
    pose proof (Zlt_cases (2 * Z.modulo a b)%Z b) as Hcond.
    pose proof (Z_div_mod_eq_full a b) as Ha.
    symmetry; apply (Z.div_unique_pos _ _ _ (if (2 * Z.modulo a b <? b)%Z then (2 * Z.modulo a b + b)%Z else (2 * Z.modulo a b - b)%Z)).
    all: destruct (_ <? _)%Z; lia.
  Qed.
End Qround_half_up.

Section SignedMod.
  Local Coercion inject_Z : Z >-> Q.
  Local Coercion Zpos : positive >-> Z.

  Definition mod_approx (approx: Q -> Z) (a: Z) (b: positive): Z :=
    (a - b * approx (a#b))%Z.

  Lemma Zmod_is_mod_approx_floor:
    forall (a: Z) (b: positive),
      Z.modulo a b = mod_approx Qfloor a b.
  Proof.
    intros. unfold mod_approx.
    rewrite Qmake_Qdiv, <- Zdiv_Qdiv.
    apply Z.mod_eq. discriminate.
  Qed.

  Definition signed_mod: Z -> positive -> Z := mod_approx Qround_half_up.

  Lemma signed_mod_eq_Zmod (a: Z) (q: positive):
    signed_mod a q = if (2 * Z.modulo a q <? q)%Z then Z.modulo a q else (Z.modulo a q - q)%Z.
  Proof.
    cbv [signed_mod mod_approx].
    rewrite Qround_half_up_eq.
    destruct (_ <? _)%Z; rewrite Zmod_is_mod_approx_floor; [reflexivity|].
    cbv [mod_approx]; lia.
  Qed.

  Lemma Zmod_eq_signed_mod (a: Z) (q: positive):
    Z.modulo a q = if (2 * Z.modulo a q <? q)%Z then signed_mod a q else (signed_mod a q + q)%Z.
  Proof. rewrite signed_mod_eq_Zmod; destruct (_ <? _)%Z; lia. Qed.

  Lemma signed_mod_Zmod (a: Z) (q: positive):
    signed_mod a q = signed_mod (Z.modulo a q) q.
  Proof.
    do 2 rewrite signed_mod_eq_Zmod.
    rewrite Z.mod_mod by congruence. reflexivity.
  Qed.

  Lemma Zmod_signed_mod (a: Z) (q: positive):
    Z.modulo a q = Z.modulo (signed_mod a q) q.
  Proof.
    rewrite signed_mod_eq_Zmod.
    destruct (_ <? _)%Z; [rewrite Z.mod_mod by congruence; reflexivity|].
    rewrite Zminus_mod_idemp_l, Zminus_mod, Z.mod_same, Z.sub_0_r, Z.mod_mod by congruence.
    reflexivity.
  Qed.

  Lemma signed_mod_mod (a: Z) (q: positive):
    signed_mod (signed_mod a q) q = signed_mod a q.
  Proof.
    rewrite (signed_mod_eq_Zmod a q) at 1. symmetry.
    destruct (_ <? _)%Z; [apply signed_mod_Zmod|].
    rewrite (signed_mod_Zmod (_ - _)%Z).
    rewrite Zminus_mod_idemp_l, Zminus_mod, Z.mod_same, Z.sub_0_r, Z.mod_mod by congruence.
    apply signed_mod_Zmod.
  Qed.
End SignedMod.

Section RefinedBarrettReduction.
  Local Coercion inject_Z : Z >-> Q.
  Local Coercion Zpos : positive >-> Z.

  (* Barrett reduction is the special case with b = 1 *)
  Definition barrett_multiplication_approx
    (approx: Q -> Z) (R a b: Z) (q: positive): Z :=
    (a * b - q * Qround_half_up ((a * (approx ((b * R)#q)))%Z / R))%Z.

  (* Not the same bounds on |a| and |b| as in the paper, as theirs cannot be proved *)
  Lemma barrett_multiplication_approx_correct
    (approx: Q -> Z) (M R a b: Z) (k q: positive)
    (Hk: Qabs (((b * R)#q) - approx ((b * R)#q)) <= 1#(Pos.pow 2 k))
    (HOddq: Z.Odd q) (HR: R = Z.pow 2 (M - 1 + Z.log2 q - Z.log2_up (Z.abs b))%Z)
    (HM: (2 <= M)%Z) (Ha: (Z.abs a <= Z.pow 2 (M - 1))%Z)
    (Hb: (Z.abs b <= Z.pow 2 (M - 2))%Z)
    (Ha': (Z.abs a <= Z.pow 2 ((M - 2) - ((Z.log2_up (Z.abs b)) - (k - 1))))%Z):
    barrett_multiplication_approx approx R a b q = signed_mod (a * b)%Z q.
  Proof.
    assert (Hlog2b: (Z.log2_up (Z.abs b) <= M - 2)%Z).
    { refine (proj1 (Log2.Z.log2_up_le_pow2_full _ _ _) Hb). lia. }
    pose proof (Z.log2_nonneg q) as Hlog2q_nonneg.
    pose proof (Z.pow_pos_nonneg 2 (M - 1 + Z.log2 q - Z.log2_up (Z.abs b))%Z ltac:(lia) ltac:(lia)) as HRpos.
    unfold barrett_multiplication_approx, signed_mod, mod_approx.
    assert (Qround_half_up ((a * approx (b * R # q))%Z / R) = Qround_half_up (a * b # q)) as ->; [|reflexivity].
    match goal with |- ?x = ?y => destruct (Z.eq_dec x y) as [?|Hne]; auto end.
    match goal with |- Qround_half_up ?x = Qround_half_up ?y => set (delta := x - y) end.
    assert (Hdelta: Qabs delta == ((Qabs a) / R) * Qabs ((b * R # q) - approx (b * R # q))).
    { unfold delta. rewrite Qabs_Qminus.
      assert ((a * b)#q == (a / R) * ((b * R) # q)) as ->.
      { rewrite Qmake_Qdiv, Qmake_Qdiv.
        repeat rewrite inject_Z_mult. field.
        split; [discriminate|]. cbv [Qeq]; simpl.
        rewrite HR. lia. }
      assert ((a * approx _)%Z / R == a / R * approx (b * R # q)) as ->.
      { repeat rewrite inject_Z_mult. field.
        cbv [Qeq]; simpl. rewrite HR; lia. }
      assert (a / R * _ - a / R * _ == a / R * ((b * R # q) - approx (b * R # q))) as ->.
      { field. cbv [Qeq]; simpl; rewrite HR; lia. }
      rewrite Qabs_Qmult. assert (Qabs (a / R) == Qabs a / R) as ->; [|reflexivity].
      cbv [Qdiv]. rewrite Qabs_Qmult, Qabs_Qinv.
      rewrite (Qabs_pos R); [reflexivity|].
      cbv [Qle]; simpl. rewrite HR; lia. }
    match goal with |- ?x = ?y => assert (x < y \/ y < x)%Z as Hlt by lia end.
    assert (Hdelta': 1#(2 * q)%positive <= Qabs delta).
    { destruct Hlt as [Hlt|Hlt]; apply Qround_half_up_diff in Hlt; destruct Hlt as (n & Hlo & Hhi).
      - apply (proj1 (Qle_minus_iff _ _)) in Hhi.
        apply Qopp_lt_compat in Hlo.
        apply (proj2 (Qplus_lt_r _ _ ((a * b # q)))) in Hlo.
        setoid_replace ((a * b # q) + - ((a * approx (b * R # q))%Z / R)) with (- delta) in Hlo.
        2:{ unfold delta. unfold Qminus. rewrite Qopp_plus, Qopp_involutive, Qplus_comm. reflexivity. }
        rewrite <- Qabs_opp. apply Qabs_ge.
        refine (Qle_trans _ ((a * b # q) + - (n + (1 # 2))) _ _ _).
        2: apply Qlt_le_weak; assumption.
        clear -HOddq Hhi.
        cbv [Qopp Qplus Qle] in *. simpl in *.
        assert (0 < (a * b * 2 + - (n * 2 + 1) * q))%Z; [|nia].
        destruct (Z.eq_dec 0 (a * b * 2 + - (n * 2 + 1) * q)%Z) as [He|?]; [|lia].
        exfalso. apply (Z.Even_Odd_False ((n * 2 + 1) * q)%Z).
        + exists (a * b)%Z. lia.
        + destruct HOddq as (? & ->). exists (2 * n * x + n + x)%Z. lia.
      - apply (proj1 (Qlt_minus_iff _ _)) in Hlo.
        apply (proj2 (Qplus_le_l _ _ (- (a * b # q)))) in Hhi.
        apply Qabs_ge. unfold delta. unfold Qminus.
        refine (Qle_trans _ _ _ _ Hhi).
        clear -HOddq Hlo.
        cbv [Qopp Qplus Qlt Qle] in *. simpl in *.
        assert (0 < ((n * 2 + 1) * q + - (a * b) * 2))%Z; [|nia].
        lia. }
    exfalso. assert (Qabs delta < 1 # 2 * q) as X; [|apply (Qlt_not_le _ _ X); auto].
    rewrite Hdelta.
    pose proof (Qle_lt_or_eq _ _ (Qabs_nonneg a)) as [Hpos|Hz].
    - refine (Qle_lt_trans _ ((Qabs a / R) * (1 # 2 ^ k)) _ _ _).
      + apply Qmult_le_l; auto.
        apply Qlt_shift_div_l; cbv [Qmult Qlt] in *; simpl in *; auto.
        rewrite HR; lia.
      + assert ((Qabs a / R) * (1 # 2 ^ k) == Qabs a / (R * 2 ^ k)%Z) as ->.
        { rewrite HR, <- Z.pow_add_r; try lia.
          rewrite <- (Z2Pos.id (Z.pow 2 _)) by lia.
          rewrite <- (Z2Pos.id (Z.pow 2 (_ + k))) by lia.
          rewrite <- (Zabs_Qabs a xH), <- (Qmake_Qdiv (Z.abs a) _), <- (Qmake_Qdiv (Z.abs a) _).
          cbv [Qmult Qeq Qnum Qden].
          rewrite Z2Pos.id by lia.
          rewrite Pos2Z.inj_mul, Z2Pos.id by lia.
          rewrite Pos2Z.inj_pow, <- Z.pow_add_r by lia. lia. }
        rewrite HR, <- Z.pow_add_r; try lia.
        rewrite <- (Z2Pos.id (Z.pow _ _)) by lia.
        rewrite <- (Zabs_Qabs a xH), <- (Qmake_Qdiv (Z.abs a) (Z.to_pos _)).
        cbv [Qlt Qnum Qden]. rewrite Z2Pos.id by lia.
        apply (Z.le_lt_trans _ (2 ^ (M - 2 - (Z.log2_up (Z.abs b) - (k - 1))) * (2 * Z.pos q))%Z); [nia|].
        rewrite Z.mul_1_l, Z.mul_assoc, (Z.mul_comm _ 2), <- Z.pow_succ_r by lia.
        rewrite <- Z.add_1_r.
        apply (Z.lt_le_trans _ (2 ^ (M - 2 - (Z.log2_up (Z.abs b) - (k - 1)) + 1) * Z.pow 2 (Z.succ (Z.log2 q)))%Z).
        * apply Zmult_lt_compat_l; [|apply Z.log2_spec; lia].
          apply Z.pow_pos_nonneg; lia.
        * rewrite <- Z.add_1_l, <- Z.pow_add_r; [|lia|lia].
          apply Z.pow_le_mono_r; [lia|]. lia.
    - rewrite <- Hz. cbv [Qmult Qlt]; simpl. lia.
  Qed.

  (* Assumes R_pow, c and v are precomputed *)
  (* M is usually the bitwidth              *)
  (* R_pow := M - 1 + Z.log2 q              *)
  (* c := approx ((Z.pow 2 R_pow)#q)        *)
  (* v := Z.shiftl 1 (R_pow - 1)            *)
  Definition barrett_reduce_approx (R_pow c v a: Z) (q: positive): Z :=
    let t := (a * c)%Z in
    let t := (t + v)%Z in
    let t := Z.shiftr t R_pow in
    (a - q * t)%Z.

  Lemma barrett_reduce_approx_eq (approx: Q -> Z) (M R_pow c v a: Z) (q: positive)
    (HM: (2 <= M)%Z)
    (HR_pow: R_pow = (M - 1 + Z.log2 q)%Z)
    (Hc: c = approx ((Z.pow 2 R_pow)#q))
    (Hv: v = Z.shiftl 1 (R_pow - 1)):
    barrett_reduce_approx R_pow c v a q = barrett_multiplication_approx approx (Z.pow 2 (M - 1 + Z.log2 q)%Z) a 1%Z q.
  Proof.
    cbv [barrett_multiplication_approx barrett_reduce_approx Qround_half_up].
    rewrite Z.mul_1_r, Z.mul_1_l.
    subst v; rewrite Z.shiftl_1_l. rewrite <- HR_pow, <- Hc.
    assert (Hle: (0 <= R_pow - 1)%Z) by (rewrite HR_pow; pose proof (Z.log2_nonneg q); lia).
    assert (_ + _ == (a * c + 2 ^ (R_pow - 1))%Z / (Z.pow 2 R_pow)) as ->.
    { rewrite <- (Z2Pos.id (Z.pow 2 R_pow)) by (apply Z.pow_pos_nonneg; lia).
      do 2 rewrite <- (Qmake_Qdiv).
      cbv [Qplus Qnum Qden]. rewrite Z.mul_1_l.
      rewrite <- (Qmult_1_r (_ # (Z.to_pos (Z.pow 2 R_pow)))).
      assert (1 == 2#2) as -> by reflexivity.
      cbv [Qmult Qnum Qden]. rewrite Z.mul_add_distr_r.
      rewrite (Z.mul_comm (Z.pow _ _) 2).
      rewrite <- Z.pow_succ_r by assumption.
      assert (Z.succ _ = R_pow)%Z as -> by lia.
      rewrite Z2Pos.id; [reflexivity|]. apply Z.pow_pos_nonneg; lia. }
    rewrite <- Zdiv_Qdiv, <- Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma barrett_reduce_approx_correct
    (approx: Q -> Z) (M R_pow c v a: Z) (k q: positive)
    (HR_pow: R_pow = (M - 1 + Z.log2 q)%Z)
    (Hc: c = approx ((Z.pow 2 R_pow)#q))
    (Hv: v = Z.shiftl 1 (R_pow - 1))
    (Hk: Qabs (((Z.pow 2 (M - 1 + Z.log2 q)%Z)#q) - approx ((Z.pow 2 (M - 1 + Z.log2 q)%Z)#q)) <= 1#(Pos.pow 2 k))
    (HOddq: Z.Odd q) (HM: (2 <= M)%Z) (Ha: (Z.abs a <= Z.pow 2 (M - 1))%Z)
    (Ha': (Z.abs a <= Z.pow 2 ((M - 2) + (k - 1)))%Z):
    barrett_reduce_approx R_pow c v a q = signed_mod a q.
  Proof.
    erewrite barrett_reduce_approx_eq by eassumption.
    erewrite barrett_multiplication_approx_correct; eauto.
    - rewrite Z.mul_1_r; reflexivity.
    - rewrite Z.mul_1_l. exact Hk.
    - assert (Z.log2_up _ = 0)%Z as -> by reflexivity.
      rewrite Z.sub_0_r. reflexivity.
    - assert (Z.abs 1 = Z.pow 2 0)%Z as -> by reflexivity.
      apply Z.pow_le_mono_r; lia.
    - assert (Z.log2_up _ = 0)%Z as -> by reflexivity.
      assert (M - 2 - (0 - (k - 1)) = M - 2 + (k - 1))%Z as -> by lia.
      exact Ha'.
  Qed.
End RefinedBarrettReduction.

Module ExampleMLKEM.
  Local Coercion inject_Z : Z >-> Q.
  Local Coercion Zpos : positive >-> Z.
  Definition M := 16%Z.
  Definition q := 3329%positive.
  Definition k := 2%positive.

  Definition R_pow := Eval compute in (M - 1 + Z.log2 q)%Z. (* 26%Z *)
  Definition c := Eval compute in Qround_half_up ((Z.pow 2 R_pow)#q). (* 20159%Z *)
  Definition v := Eval compute in Z.shiftl 1 (R_pow - 1)%Z. (* 33554432%Z *)

  Lemma Hk: Qabs (((Z.pow 2 (M - 1 + Z.log2 q)%Z)#q) - Qround_half_up ((Z.pow 2 (M - 1 + Z.log2 q)%Z)#q)) <= 1#(Pos.pow 2 k).
  Proof. compute. congruence. Qed.

  Lemma HOddq: Z.Odd q. Proof. exists (q/2)%Z. reflexivity. Qed.

(* For comparison https://github.com/pq-crystals/kyber/blob/main/ref/reduce.c *)
(* int16_t barrett_reduce(int16_t a) { *)
(*   int16_t t; *)
(*   const int16_t v = ((1<<26) + KYBER_Q/2)/KYBER_Q; *)

(*   t  = ((int32_t)v*a + (1<<25)) >> 26; *)
(*   t *= KYBER_Q; *)
(*   return a - t; *)
(* } *)

  Definition mlkem_barrett_reduce (a: Z): Z :=
    let t := (a * 20159)%Z in
    let t := (t + 33554432)%Z in
    let t := Z.shiftr t 26 in
    (a - q * t)%Z.

  Lemma MLKEM_barrett_reduce_correct (a: Z) (Ha: (Z.abs a <= Z.pow 2 15)%Z):
    mlkem_barrett_reduce a = signed_mod a q.
  Proof.
    assert (mlkem_barrett_reduce a = barrett_reduce_approx R_pow c v a q) as -> by reflexivity.
    apply (barrett_reduce_approx_correct Qround_half_up M R_pow c v a k q ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hk HOddq ltac:(unfold M; lia) ltac:(apply Ha) ltac:(apply Ha)).
  Qed.
End ExampleMLKEM.
