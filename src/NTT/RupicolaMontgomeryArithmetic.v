Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.SepLocals.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.NTT.BedrockNTT.
Require Import Crypto.Spec.ModularArithmetic.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
    {mem: map.map word Byte.byte} {loc: map.map String.string word}
    {ext_spec: bedrock2.Semantics.ExtSpec}
    {word_ok : word.ok word} {map_ok : map.ok mem}
    {loc_ok : map.ok loc}
    {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {modulus_pos: positive}.
  Let modulus := Zpos modulus_pos.
  Context {modulus_small: 3 <= modulus < 2 ^ width}.
  Context {modulus_prime: Znumtheory.prime modulus}.
  Definition r: Z := 2 ^ width.
  Definition r2: Z := (r * r) mod modulus.
  Definition r': Z := Z.modinv r modulus.
  Definition modulus': Z := Z.modinv (-modulus) r.

  Section Utils.
    (* TODO: turn into a compile lemma and upstream to rupicola ? *)
    Lemma overflow_bit (a b: word):
      word.unsigned (@word.b2w _ word (word.ltu (word.add a b) b)) = (word.unsigned a + word.unsigned b) / 2 ^ width.
    Proof.
      rewrite word.unsigned_ltu, word.unsigned_add. unfold word.wrap, r.
      pose proof (word.unsigned_range a) as Ha.
      pose proof (word.unsigned_range b) as Hb.
      rewrite word.b2w_if.
      destruct (Z_lt_dec (word.unsigned a + word.unsigned b) (2 ^ width)) as [Hlt|Hnlt].
      - rewrite Z.mod_small by Lia.lia.
        destruct (Z.ltb (word.unsigned a + word.unsigned b) (word.unsigned b)) eqn:Hcond; [apply Z.ltb_lt in Hcond; Lia.lia|].
        rewrite word.unsigned_of_Z_0. symmetry; apply Zdiv_small. Lia.lia.
      - rewrite Modulo.Z.mod_small_0_if; [|apply Z.pow_nonzero; destruct BW; Lia.lia|Lia.lia].
        pose proof (Zle_cases (2 ^ width) (word.unsigned a + word.unsigned b)) as Hle; destruct (_ <=? _); [|Lia.lia].
        pose proof (Zlt_cases (word.unsigned a + word.unsigned b - 2 ^ width) (word.unsigned b)) as Hlt; destruct (_ <? _); [|Lia.lia].
        rewrite word.unsigned_of_Z_1.
        assert (1 <= (word.unsigned a + word.unsigned b) / 2 ^ width < 2); [|Lia.lia].
        split; [apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound]; Lia.lia.
    Qed.

    Lemma underflow_bit (a b: word):
      @word.b2w _ word (word.ltu a (word.sub a b)) = if Z_lt_dec (word.unsigned a) (word.unsigned b) then word.of_Z 1 else word.of_Z 0.
    Proof.
      rewrite word.b2w_if, word.unsigned_ltu, word.unsigned_sub. unfold word.wrap, r.
      pose proof (word.unsigned_range a) as Ha.
      pose proof (word.unsigned_range b) as Hb.
      destruct (Z_lt_dec _ _) as [Hlt|Hnlt].
      - rewrite Modulo.Z.mod_neg_small by Lia.lia.
        pose proof (Zlt_cases (word.unsigned a) (2 ^ width + (word.unsigned a - word.unsigned b))).
        destruct (_ <? _); [reflexivity|Lia.lia].
      - rewrite Z.mod_small by Lia.lia.
        pose proof (Zlt_cases (word.unsigned a) (word.unsigned a - word.unsigned b)).
        destruct (_ <? _); [Lia.lia|reflexivity].
    Qed.
  End Utils.

  Lemma modulus_nonzero:
    modulus <> 0.
  Proof. Lia.lia. Qed.

  Lemma gcd_modulus_r:
    Z.gcd modulus r = 1.
  Proof.
    generalize (Z.gcd_divide_r modulus r); intro Hr.
    generalize (Z.gcd_divide_l modulus r); intro Hl.
    generalize (Z.gcd_nonneg modulus r); intro Hn.
    generalize (Znumtheory.prime_divisors _ modulus_prime _ Hl).
    intros [? | [? | [? | ?]]]; try Lia.lia.
    generalize (Zpow_facts.prime_power_prime modulus 2 width ltac:(destruct BW; Lia.lia) modulus_prime Znumtheory.prime_2 ltac:(rewrite <- H; auto)). intro X.
    subst modulus; Lia.lia.
  Qed.

  Lemma modulus_correct':
    Z.equiv_modulo r (modulus * modulus') (-1).
  Proof.
    unfold Z.equiv_modulo.
    assert (modulus = (-1) * (- modulus)) as -> by Lia.lia.
    rewrite <- Z.mul_assoc, Zmult_mod, (Z.mul_comm (- modulus)).
    unfold modulus'. rewrite Z.invmod_coprime.
    - rewrite Z.mul_1_r, Z.mod_mod; [reflexivity|]. unfold r. Lia.lia.
    - unfold r. Lia.lia.
    - rewrite Z.gcd_opp_l. apply gcd_modulus_r.
  Qed.

  Lemma modulus_range':
    0 <= modulus' < r.
  Proof.
    apply Z.modinv_correct.
    - unfold r. apply Z.pow_pos_nonneg; destruct BW; Lia.lia.
    - assert (Z.abs _ = modulus) as ->; [|apply gcd_modulus_r].
      rewrite Z.abs_neq; Lia.lia.
  Qed.

  Lemma r_correct':
    Z.equiv_modulo modulus (r * r') 1.
  Proof.
    unfold Z.equiv_modulo, r'. rewrite Z.mul_comm.
    rewrite Z.invmod_coprime, Z.mod_small; try Lia.lia.
    rewrite Z.gcd_comm. apply gcd_modulus_r.
  Qed.

  (* Reduces systematically *)
  Definition montgomery_add (x y: word): word :=
    let/n res := word.add x y in
    let/n c := word.b2w (word.ltu (word.of_Z (Z.pred modulus)) res) in
    let/n res := word.sub res (word.mul c (word.of_Z modulus)) in
    res.

  Lemma montgomery_add_eq x y (Hx: 0 <= word.unsigned x < modulus) (Hy: 0 <= word.unsigned y <= modulus) (modulus_smaller: 2 * modulus < 2 ^ width):
    word.unsigned (montgomery_add x y) = if Z_lt_dec (word.unsigned x + word.unsigned y) modulus then word.unsigned x + word.unsigned y else word.unsigned x + word.unsigned y - modulus.
  Proof.
    unfold montgomery_add, nlet.
    pose proof (word.ltu_spec (word.of_Z (Z.pred modulus)) (word.add x y)) as Hltuspec.
    rewrite word.unsigned_add_nowrap in Hltuspec by Lia.lia.
    rewrite word.unsigned_of_Z_nowrap in Hltuspec by Lia.lia.
    rewrite word.unsigned_sub_nowrap.
    - destruct (Z_lt_dec _ _) as [Hlt|Hnlt].
      + rewrite word.unsigned_add_nowrap by Lia.lia.
        rewrite word.b2w_if. destruct (word.ltu _ _); inversion Hltuspec; [Lia.lia|].
        rewrite word.mul_0_l, word.unsigned_of_Z_0, Z.sub_0_r. reflexivity.
      + rewrite word.unsigned_mul_nowrap by (rewrite word.b2w_if, word.unsigned_of_Z_nowrap by Lia.lia; destruct (word.ltu _ _); [rewrite word.unsigned_of_Z_1|rewrite word.unsigned_of_Z_0]; Lia.lia).
        rewrite word.b2w_if. destruct (word.ltu _ _); inversion Hltuspec; [|Lia.lia].
        rewrite word.unsigned_of_Z_1, Z.mul_1_l.
        rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        rewrite word.unsigned_add_nowrap by Lia.lia. reflexivity.
    - rewrite word.unsigned_add_nowrap by Lia.lia.
      rewrite word.unsigned_mul_nowrap by (rewrite word.b2w_if, word.unsigned_of_Z_nowrap by Lia.lia; destruct (word.ltu _ _); [rewrite word.unsigned_of_Z_1|rewrite word.unsigned_of_Z_0]; Lia.lia).
        rewrite word.b2w_if. destruct (word.ltu _ _); inversion Hltuspec; [rewrite word.unsigned_of_Z_1|rewrite word.unsigned_of_Z_0]; rewrite word.unsigned_of_Z_nowrap; Lia.lia.
  Qed.

  (* Assumes 2 * modulus < 2 ^ width, reduces systematically *)
  Definition montgomery_sub (x y: word): word :=
    let/n res := word.sub x y in
    let/n c := word.b2w (word.ltu x res) in
    let/n res := word.add res (word.mul c (word.of_Z modulus)) in
    res.

  Lemma montgomery_sub_eq x y (Hx: 0 <= word.unsigned x < modulus) (Hy: 0 <= word.unsigned y < modulus) (modulus_smaller: 2 * modulus < 2 ^ width):
    word.unsigned (montgomery_sub x y) = if Z_lt_dec (word.unsigned x) (word.unsigned y) then word.unsigned x + (modulus - word.unsigned y) else word.unsigned x - word.unsigned y.
  Proof.
    unfold montgomery_sub, nlet.
    rewrite underflow_bit. destruct (Z_lt_dec _ _) as [Hlt|Hnlt].
    - rewrite word.unsigned_add, word.unsigned_sub, word.unsigned_mul_nowrap by (repeat rewrite word.unsigned_of_Z_nowrap; Lia.lia).
      rewrite word.unsigned_of_Z_1, Z.mul_1_l.
      rewrite word.unsigned_of_Z_nowrap by Lia.lia.
      unfold word.wrap.
      rewrite (Modulo.Z.mod_neg_small (_ - _)) by Lia.lia.
      assert (2 ^ width + (word.unsigned x - word.unsigned y) + modulus = 2 ^ width + (word.unsigned x + (modulus - word.unsigned y))) as -> by Lia.lia.
      rewrite <- Zplus_mod_idemp_l, Z.mod_same by Lia.lia.
      rewrite Z.add_0_l.
      apply Z.mod_small. Lia.lia.
    - rewrite word.mul_0_l, word.add_0_r.
      apply word.unsigned_sub_nowrap. Lia.lia.
  Qed.

  (* When what needs to be reduced fits in a single word *)
  Definition montgomery_reduce1 (x: word): word :=
    let/n m := word.mul x (word.of_Z modulus') in
    let/n t_hi := word.mulhuu m (word.of_Z modulus) in
    let/n t_lo := word.mul m (word.of_Z modulus) in
    let/n carry := word.b2w (word.ltu (word.add x t_lo) t_lo) in
    let/n t := word.add t_hi carry in
    let/n c := word.b2w (word.ltu (word.of_Z (Z.pred modulus)) t) in
    let/n res := word.sub t (word.mul c (word.of_Z modulus)) in
    res.

  (* When input ≤ modulus * 2 ^ width, assumes 2 * modulus < 2 ^ width *)
  Definition montgomery_reduce2 (x_hi x_lo: word): word :=
    let/n m := word.mul x_lo (word.of_Z modulus') in
    let/n t_hi := word.mulhuu m (word.of_Z modulus) in
    let/n t_lo := word.mul m (word.of_Z modulus) in
    let/n carry := word.b2w (word.ltu (word.add x_lo t_lo) t_lo) in
    let/n t_hi := word.add t_hi carry in
    let/n t := word.add t_hi x_hi in
    let/n c := word.b2w (word.ltu (word.of_Z (Z.pred modulus)) t) in
    let/n res := word.sub t (word.mul c (word.of_Z modulus)) in
    res.

  (* If modulus² < 2 ^ width *)
  Definition montgomery_mul1 (x y: word): word :=
    let/n res := word.mul x y in
    let/n res := montgomery_reduce1 res in
    res.

  (* If modulus² ≥ 2 ^ width *)
  Definition montgomery_mul2 (x y: word): word :=
    let/n t_hi := word.mulhuu x y in
    let/n t_lo := word.mul x y in
    let/n res := montgomery_reduce2 t_hi t_lo in
    res.

  (* If modulus² < 2 ^ width *)
  Definition to_montgomery_word1 (x: word): word :=
    let/n t := word.mul x (word.of_Z r2) in
    let/n res := montgomery_reduce1 t in
    res.

  (* If modulus² ≥ 2 ^ width *)
  Definition to_montgomery_word2 (x: word): word :=
    let/n t_hi := word.mulhuu x (word.of_Z r2) in
    let/n t_lo := word.mul x (word.of_Z r2) in
    let/n res := montgomery_reduce2 t_hi t_lo in
    res.

  Definition from_montgomery_word (x: word): word :=
    let/n res := montgomery_reduce1 x in
    res.

  Local Notation reduce_spec := (@reduce modulus r modulus').
  Local Notation to_montgomery_spec := (@to_montgomery modulus r modulus').
  Local Notation from_montgomery_spec := (@from_montgomery modulus r modulus').
  Local Notation mul_spec := (@MontgomeryReduction.Definition.mul modulus r modulus').
  Local Notation reduce_spec_correct :=
    (reduce_correct modulus modulus_nonzero r r' r_correct' modulus' modulus_range' modulus_correct').
  Local Notation from_to_montgomery_spec_correct :=
    (from_to_montgomery modulus modulus_nonzero r r' r_correct' modulus' modulus_range' modulus_correct').
  Local Notation to_from_montgomery_spec_correct :=
    (to_from_montgomery modulus modulus_nonzero r r' r_correct' modulus' modulus_range' modulus_correct').
  Local Notation mul_spec_correct :=
    (mul_correct modulus modulus_nonzero r r' r_correct' modulus' modulus_range' modulus_correct').

  Lemma feval_pre (x: word):
    (fun z : Z => z = z mod Z.pos modulus_pos) (from_montgomery_spec (word.unsigned x)).
  Proof.
    symmetry; apply Z.mod_small.
    unfold from_montgomery_spec. apply reduce_in_range; try Lia.lia.
    apply modulus_range'. pose proof (word.unsigned_range x) as Hx.
    split; [Lia.lia|]. apply Z.lt_le_incl.
    transitivity r; [unfold r; Lia.lia|].
    rewrite <- (Z.mul_1_r r) at 1.
    apply Zmult_lt_compat_l; unfold r; Lia.lia.
  Qed.

  (* Definition feval (x: word): option (F modulus_pos) := *)
  (*   Some (exist _ (from_montgomery_spec (word.unsigned x)) (feval_pre x)). *)

  (* Local Instance F_to_Z: Convertible (F modulus_pos) Z := fun x => to_montgomery_spec (F.to_Z x). *)

  (* Existing Instance F_to_word. *)

  (* Lemma feval_ok: *)
  (*   forall (x: F modulus_pos), feval (cast x) = Some x. *)
  (* Proof. *)
  (*   intros. cbv [cast F_to_word F_to_Z feval]. *)
  (*   f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff. cbn. *)
  (*   pose proof (ModularArithmeticTheorems.F.to_Z_range x ltac:(Lia.lia)) as Hx1. *)
  (*   assert (Hx2: 0 <= to_montgomery_spec (F.to_Z x) < modulus). *)
  (*   { unfold to_montgomery_spec. *)
  (*     apply reduce_in_range; [Lia.lia|apply modulus_range'|]. *)
  (*     pose proof (Z.mod_pos_bound (r * r) modulus ltac:(Lia.lia)) as Hr2. *)
  (*     split; try Lia.lia. apply Zmult_le_compat; try Lia.lia. *)
  (*     apply Z.lt_le_incl. transitivity modulus; unfold modulus, r in *; try Lia.lia. } *)
  (*   pose proof (from_to_montgomery_spec_correct (F.to_Z x)) as Hx. *)
  (*   rewrite word.unsigned_of_Z_nowrap; [|Lia.lia]. *)
  (*   rewrite <- (Z.mod_small (F.to_Z x) modulus Hx1) at 2. *)
  (*   apply Z.equiv_modulo_mod_small; auto. *)
  (*   unfold from_montgomery_spec. apply reduce_in_range; [Lia.lia|apply modulus_range'|]. *)
  (*   split; [|apply Z.lt_le_incl; transitivity modulus]; try Lia.lia. *)
  (*   unfold r. rewrite <- (Z.mul_1_l modulus) at 1. *)
  (*   apply Zmult_lt_compat_r; [Lia.lia|]. *)
  (*   apply Zpow_facts.Zpower_gt_1; [|destruct BW]; Lia.lia. *)
  (* Qed. *)

  (* Lemma feval_is_Some_implies: *)
  (*   forall x y, feval x = Some y -> F.to_Z y = (word.unsigned x * r') mod modulus. *)
  (* Proof. *)
  (*   intros x y Heq. pose proof (word.unsigned_range x) as Hx. *)
  (*   unfold feval in Heq. *)
  (*   inversion Heq; subst y. cbn. *)
  (*   unfold from_montgomery_spec. *)
  (*   apply Z.equiv_modulo_mod_small. *)
  (*   - apply reduce_spec_correct. *)
  (*   - apply (reduce_in_range _ modulus_nonzero _ _ modulus_range'). *)
  (*     split; try Lia.lia. rewrite <- (Z.mul_1_r (word.unsigned x)). *)
  (*     unfold r; apply Zmult_le_compat; Lia.lia. *)
  (* Qed. *)

  Definition feval (x: word): option (F modulus_pos) :=
    if (Z_lt_dec (word.unsigned x) modulus) then Some (exist _ (from_montgomery_spec (word.unsigned x)) (feval_pre x)) else None.

  Local Instance F_to_Z: Convertible (F modulus_pos) Z := fun x => to_montgomery_spec (F.to_Z x).

  Existing Instance F_to_word.

  Lemma feval_ok:
    forall (x: F modulus_pos), feval (cast x) = Some x.
  Proof.
    intros. cbv [cast F_to_word F_to_Z feval].
    pose proof (ModularArithmeticTheorems.F.to_Z_range x ltac:(Lia.lia)) as Hx1.
    assert (Hx2: 0 <= to_montgomery_spec (F.to_Z x) < modulus).
    { unfold to_montgomery_spec.
      apply reduce_in_range; [Lia.lia|apply modulus_range'|].
      pose proof (Z.mod_pos_bound (r * r) modulus ltac:(Lia.lia)) as Hr2.
      split; try Lia.lia. apply Zmult_le_compat; try Lia.lia.
      apply Z.lt_le_incl. transitivity modulus; unfold modulus, r in *; try Lia.lia. }
    pose proof (from_to_montgomery_spec_correct (F.to_Z x)) as Hx.
    destruct (Z_lt_dec _ _) as [|Hnlt].
    2:{ rewrite word.unsigned_of_Z_nowrap in Hnlt; Lia.lia. }
    f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff. cbn.
    rewrite word.unsigned_of_Z_nowrap; [|Lia.lia].
    rewrite <- (Z.mod_small (F.to_Z x) modulus Hx1) at 2.
    apply Z.equiv_modulo_mod_small; auto.
    unfold from_montgomery_spec. apply reduce_in_range; [Lia.lia|apply modulus_range'|].
    split; [|apply Z.lt_le_incl; transitivity modulus]; try Lia.lia.
    unfold r. rewrite <- (Z.mul_1_l modulus) at 1.
    apply Zmult_lt_compat_r; [Lia.lia|].
    apply Zpow_facts.Zpower_gt_1; [|destruct BW]; Lia.lia.
  Qed.

  Lemma feval_is_Some_implies:
    forall x y, feval x = Some y -> 0 <= word.unsigned x < modulus /\ F.to_Z y = (word.unsigned x * r') mod modulus.
  Proof.
    intros x y Heq. pose proof (word.unsigned_range x) as Hx.
    unfold feval in Heq.
    destruct (Z_lt_dec _ _); [|congruence]. split; [Lia.lia|].
    inversion Heq; subst y. cbn.
    unfold from_montgomery_spec.
    apply Z.equiv_modulo_mod_small.
    - apply reduce_spec_correct.
    - apply (reduce_in_range _ modulus_nonzero _ _ modulus_range').
      split; try Lia.lia. rewrite <- (Z.mul_1_r (word.unsigned x)).
      unfold r; apply Zmult_le_compat; Lia.lia.
  Qed.

  Context {reduce_name: string}.
  Context {to_montgomery_name from_montgomery_name: string}.
  Context {add_name sub_name mul_name: string}.

  Instance spec_of_add : spec_of add_name := spec_of_add (q:=modulus_pos) (feval:=feval) (add:=add_name).
  Instance spec_of_sub : spec_of sub_name := spec_of_sub (q:=modulus_pos) (feval:=feval) (sub:=sub_name).
  Instance spec_of_mul : spec_of mul_name := spec_of_mul (q:=modulus_pos) (feval:=feval) (mul:=mul_name).

  (* Only used to derive code using Rupicola *)
  Instance spec_of_add_dummy : spec_of add_name :=
    fnspec! add_name (X Y: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = montgomery_add X Y }.

  Derive add_br2fn SuchThat
    (defn! add_name("x", "y") ~> "res"
       { add_br2fn },
      implements montgomery_add)
    As dummy_add_br2fn_ok.
  Proof. compile. Qed.

  Lemma montgomery_add_correct (modulus_smaller: 2 * modulus < 2 ^ width) x y a b:
    feval x = Some a ->
    feval y = Some b ->
    feval (montgomery_add x y) = Some (a + b)%F.
  Proof.
    intros Ha Hb.
    pose proof (feval_is_Some_implies _ _ Ha) as [Hx Heqa].
    pose proof (feval_is_Some_implies _ _ Hb) as [Hy Heqb].
    assert ((word.unsigned (montgomery_add x y)) < modulus) as Hbound.
    { rewrite montgomery_add_eq by Lia.lia.
      destruct (Z_lt_dec _ _) as [Hlt|Hnlt]; Lia.lia. }
    assert (exists ab, feval (montgomery_add x y) = Some ab) as [ab Hab].
    { unfold feval. destruct (Z_lt_dec _ _) as [_|?]; [|Lia.lia].
      eexists; reflexivity. }
    pose proof (feval_is_Some_implies _ _ Hab) as [Hxy Heqab].
    rewrite Hab. f_equal.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff. cbn.
    rewrite montgomery_add_eq in Heqab by Lia.lia.
    rewrite Heqab, Heqa, Heqb, Z.add_mod_idemp_l, Z.add_mod_idemp_r by congruence.
    rewrite <- Z.mul_add_distr_r.
    destruct (Z_lt_dec _ _) as [Hlt|Hnlt]; [reflexivity|].
    rewrite Z.mul_sub_distr_r.
    rewrite <- Zminus_mod_idemp_r, ZLib.Z.Z_mod_mult', Z.sub_0_r. reflexivity.
  Qed.

  Lemma add_br2fn_ok (modulus_smaller: 2 * modulus < 2 ^ width):
    program_logic_goal_for add_br2fn
      (forall functions : map.rep,
          map.get functions add_name = Some add_br2fn ->
          spec_of_add functions).
  Proof.
    red. intros. red. red. red. intros. destruct H0.
    generalize (dummy_add_br2fn_ok I _ H).
    intros. eapply Proper_call; [|apply dummy_add_br2fn_ok; auto; exact I].
    intros ? ? ? ?. destruct H3 as (? & -> & -> & -> & ->).
    eexists; repeat split; try reflexivity.
    apply montgomery_add_correct; auto.
  Qed.

  (* Only used to derive code using Rupicola *)
  Instance spec_of_sub_dummy : spec_of sub_name :=
    fnspec! sub_name (X Y: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = montgomery_sub X Y }.

  Derive sub_br2fn SuchThat
    (defn! sub_name("x", "y") ~> "res"
       { sub_br2fn },
      implements montgomery_sub)
    As dummy_sub_br2fn_ok.
  Proof. compile. Qed.

  Lemma montgomery_sub_correct (modulus_smaller: 2 * modulus < 2 ^ width) x y a b:
    feval x = Some a ->
    feval y = Some b ->
    feval (montgomery_sub x y) = Some (a - b)%F.
  Proof.
    intros Ha Hb.
    pose proof (feval_is_Some_implies _ _ Ha) as [Hx Heqa].
    pose proof (feval_is_Some_implies _ _ Hb) as [Hy Heqb].
    assert ((word.unsigned (montgomery_sub x y)) < modulus) as Hbound.
    { rewrite montgomery_sub_eq by Lia.lia.
      destruct (Z_lt_dec _ _) as [Hlt|Hnlt]; Lia.lia. }
    assert (exists ab, feval (montgomery_sub x y) = Some ab) as [ab Hab].
    { unfold feval. destruct (Z_lt_dec _ _) as [_|?]; [|Lia.lia].
      eexists; reflexivity. }
    pose proof (feval_is_Some_implies _ _ Hab) as [Hxy Heqab].
    rewrite Hab. f_equal.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff. cbn.
    rewrite montgomery_sub_eq in Heqab by Lia.lia.
    rewrite Heqab, Heqa, Heqb, Z.add_mod_idemp_l, Z.add_mod_idemp_r by congruence.
    destruct (Z_lt_dec _ _) as [Hlt|Hnlt].
    - rewrite Z.mul_add_distr_r.
      rewrite <- Zplus_mod_idemp_r at 1.
      rewrite <- Zmult_mod_idemp_l.
      rewrite <- Zminus_mod_idemp_l, Z.mod_same by Lia.lia.
      rewrite Z.sub_0_l, Zmult_mod_idemp_l.
      rewrite Zplus_mod_idemp_r, Z.mul_opp_l.
      repeat rewrite Z.add_opp_r.
      rewrite Zminus_mod_idemp_r. reflexivity.
    - rewrite Z.add_opp_r, Zminus_mod_idemp_r.
      rewrite <- Zmult_minus_distr_r. reflexivity.
  Qed.

  Lemma sub_br2fn_ok (modulus_smaller: 2 * modulus < 2 ^ width):
    program_logic_goal_for sub_br2fn
      (forall functions : map.rep,
          map.get functions sub_name = Some sub_br2fn ->
          spec_of_sub functions).
  Proof.
    red. intros. red. red. red. intros. destruct H0.
    generalize (dummy_sub_br2fn_ok I _ H).
    intros. eapply Proper_call; [|apply dummy_sub_br2fn_ok; auto; exact I].
    intros ? ? ? ?. destruct H3 as (? & -> & -> & -> & ->).
    eexists; repeat split; try reflexivity.
    apply montgomery_sub_correct; auto.
  Qed.

  Lemma montgomery_reduce_correct1 x (Hx: 0 <= x < 2 ^ width):
    word.unsigned (montgomery_reduce1 (word.of_Z x)) = reduce_spec x.
  Proof.
    pose proof (Z.pow_pos_nonneg 2 width ltac:(Lia.lia) ltac:(destruct BW; Lia.lia)) as ZZ.
    unfold reduce_spec, prereduce, montgomery_reduce1.
    rewrite <- word.ring_morph_mul. set (m := word.of_Z (x * modulus')).
    unfold nlet at 1. repeat rewrite <- word.ring_morph_mul.
    assert ((x mod r * modulus') mod r = word.unsigned (@word.of_Z _ word (x * modulus'))) as ->.
    { rewrite word.unsigned_of_Z.
      rewrite <- PullPush.Z.mul_mod_l. reflexivity. }
    fold m. set (t_hi := word.mulhuu m (word.of_Z modulus)).
    set (t_lo := word.mul m (word.of_Z modulus)).
    do 2 (unfold nlet at 1).
    assert (word.unsigned m * modulus = r * (word.unsigned t_hi) + (word.unsigned t_lo)) as ->.
    { unfold t_hi, t_lo. rewrite word.unsigned_mulhuu_nowrap, word.unsigned_mul.
      rewrite word.unsigned_of_Z_nowrap by Lia.lia.
      apply Z_div_mod_eq_full. }
    assert (Hcond_spec: forall (a b: word), word.ltu (word.add a b) b = true <-> (word.unsigned a + word.unsigned b) >= r).
    { intros. rewrite word.unsigned_ltu, word.unsigned_add. unfold word.wrap, r.
      generalize (word.unsigned_range a); intros Ha.
      generalize (word.unsigned_range b); intros Hb.
      split; intros X.
      - apply Z.ltb_lt in X.
        destruct (Z_lt_dec (word.unsigned a + word.unsigned b) (2 ^ width)); [|Lia.lia].
        rewrite Z.mod_small in X by Lia.lia. Lia.lia.
      - apply Z.ltb_lt.
        generalize (Z_mod_lt (word.unsigned a + word.unsigned b) (2 ^ width) ltac:(Lia.lia)).
        rewrite Modulo.Z.mod_small_0_if; [|apply Z.pow_nonzero; destruct BW; Lia.lia|Lia.lia].
        generalize (Zle_cases (2 ^ width) (word.unsigned a + word.unsigned b)); destruct (_ <=? _); Lia.lia. }
    set (carry := word.ltu (word.add (word.of_Z x) t_lo) t_lo).
    set (t := word.add t_hi (word.b2w carry)).
    do 2 (unfold nlet at 1).
    fold t. assert ((x + (r * word.unsigned t_hi + word.unsigned t_lo)) / r = word.unsigned t) as ->.
    { assert (x + (r * word.unsigned t_hi + word.unsigned t_lo) = (x + word.unsigned t_lo) + (word.unsigned t_hi) * r) as -> by Lia.lia.
      rewrite Z_div_plus by (unfold r; Lia.lia).
      unfold t, carry. rewrite word.unsigned_add_nowrap.
      2:{ generalize (word.unsigned_range t_hi).
          destruct (word.ltu _); unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia; [|Lia.lia].
          intros _. unfold t_hi. rewrite word.unsigned_mulhuu_nowrap.
          pose proof (word.unsigned_range m) as Hm.
          rewrite word.unsigned_of_Z_nowrap by Lia.lia.
          apply (Z.le_lt_trans _ modulus); [|Lia.lia].
          apply Z.lt_pred_le.
          assert (Z.pred _ = (word.unsigned m * modulus) / 2 ^ width) as -> by Lia.lia.
          apply (Zdiv_lt_upper_bound ((word.unsigned m) * modulus) (2 ^ width) modulus ZZ).
          rewrite (Z.mul_comm modulus).
          apply Zmult_lt_compat_r; Lia.lia. }
      rewrite (Z.add_comm (word.unsigned t_hi)). f_equal.
      pose proof (word.unsigned_range t_lo) as Hlo.
      destruct (Z_lt_dec (x + word.unsigned t_lo) r) as [Hlt|Hnlt].
      - rewrite <- (Z.mod_small (x + word.unsigned t_lo) r) by Lia.lia.
        rewrite Zmod_div. pose proof (Hcond_spec (word.of_Z x) t_lo) as W.
        destruct (word.ltu _ _); unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia; [|reflexivity].
        specialize ((proj1 W) eq_refl). rewrite word.unsigned_of_Z_nowrap by Lia.lia. Lia.lia.
      - rewrite (proj2 (Hcond_spec (word.of_Z x) t_lo) ltac:(rewrite word.unsigned_of_Z_nowrap; Lia.lia)).
        unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        pose proof (Zdiv_le_lower_bound (x + word.unsigned t_lo) r 1 ZZ ltac:(Lia.lia)) as Hlow.
        pose proof (Zdiv_lt_upper_bound (x + word.unsigned t_lo) r 2 ZZ ltac:(unfold r; Lia.lia)).
        Lia.lia. }
    assert (modulus <=? word.unsigned t = word.ltu (word.of_Z (Z.pred modulus)) t) as ->.
    { rewrite word.unsigned_ltu, word.unsigned_of_Z_nowrap by Lia.lia.
      pose proof (Zle_cases modulus (word.unsigned t)) as Hcond.
      destruct (_ <=? _); [apply Z.lt_pred_le in Hcond; rewrite (proj2 (Z.ltb_lt _ _)); auto|].
      pose proof (Zlt_cases (Z.pred modulus) (word.unsigned t)); destruct (_ <? _); Lia.lia. }
    pose proof (word.ltu_spec (word.of_Z (Z.pred modulus)) t) as E.
    destruct (word.ltu (word.of_Z (Z.pred modulus)) t); unfold word.b2w, nlet; cbn.
    - rewrite word.mul_1_l. inversion E.
      rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_nowrap; try Lia.lia.
      rewrite word.unsigned_of_Z_nowrap in H by Lia.lia.
      rewrite word.unsigned_of_Z_nowrap; Lia.lia.
    - rewrite word.mul_0_l, word.sub_0_r. reflexivity.
  Qed.

  Lemma montgomery_reduce_correct2 x (Hx: 0 <= x <= r * modulus) (modulus_smaller: 2 * modulus < 2 ^ width):
    word.unsigned (montgomery_reduce2 (word.of_Z (x / r)) (word.of_Z x)) = reduce_spec x.
  Proof.
    pose proof (Z.pow_pos_nonneg 2 width ltac:(Lia.lia) ltac:(destruct BW; Lia.lia)) as ZZ.
    unfold reduce_spec, prereduce, montgomery_reduce2.
    rewrite <- word.ring_morph_mul. set (m := word.of_Z (x * modulus')).
    unfold nlet at 1. repeat rewrite <- word.ring_morph_mul.
    assert ((x mod r * modulus') mod r = word.unsigned (@word.of_Z _ word (x * modulus'))) as ->.
    { rewrite word.unsigned_of_Z.
      rewrite <- PullPush.Z.mul_mod_l. reflexivity. }
    fold m. set (t_hi := word.mulhuu m (word.of_Z modulus)).
    set (t_lo := word.mul m (word.of_Z modulus)).
    do 2 (unfold nlet at 1).
    assert (word.unsigned m * modulus = r * (word.unsigned t_hi) + (word.unsigned t_lo)) as ->.
    { unfold t_hi, t_lo. rewrite word.unsigned_mulhuu_nowrap, word.unsigned_mul.
      rewrite word.unsigned_of_Z_nowrap by Lia.lia.
      apply Z_div_mod_eq_full. }
    assert (Hcond_spec: forall (a b: word), word.ltu (word.add a b) b = true <-> (word.unsigned a + word.unsigned b) >= r).
    { intros. rewrite word.unsigned_ltu, word.unsigned_add. unfold word.wrap, r.
      generalize (word.unsigned_range a); intros Ha.
      generalize (word.unsigned_range b); intros Hb.
      split; intros X.
      - apply Z.ltb_lt in X.
        destruct (Z_lt_dec (word.unsigned a + word.unsigned b) (2 ^ width)); [|Lia.lia].
        rewrite Z.mod_small in X by Lia.lia. Lia.lia.
      - apply Z.ltb_lt.
        generalize (Z_mod_lt (word.unsigned a + word.unsigned b) (2 ^ width) ltac:(Lia.lia)).
        rewrite Modulo.Z.mod_small_0_if; [|apply Z.pow_nonzero; destruct BW; Lia.lia|Lia.lia].
        generalize (Zle_cases (2 ^ width) (word.unsigned a + word.unsigned b)); destruct (_ <=? _); Lia.lia. }
    set (carry := word.ltu (word.add (word.of_Z x) t_lo) t_lo).
    set (t_hi' := word.add t_hi (word.b2w carry)).
    set (t := word.add t_hi' (word.of_Z (x / r))).
    do 3 (unfold nlet at 1).
    fold t_hi' t. assert ((x + (r * word.unsigned t_hi + word.unsigned t_lo)) / r = word.unsigned t) as ->.
    { rewrite (Z_div_mod_eq_full x r).
      assert (r * (x / r) + x mod r + (r * word.unsigned t_hi + word.unsigned t_lo) = (x mod r + word.unsigned t_lo) + (word.unsigned t_hi + (x / r)) * r) as -> by Lia.lia.
      rewrite Z_div_plus by (unfold r; Lia.lia).
      unfold t, t_hi', carry.
      assert (CC: 0 <= x / r <= modulus).
      { generalize (Zdiv_le_upper_bound x r modulus ZZ ltac:(Lia.lia)); intros.
        split; [apply Z.div_pos|]; Lia.lia. }
      assert (SS: word.unsigned t_hi + word.unsigned (@word.b2w _ word (word.ltu (word.add (@word.of_Z _ word x) t_lo) t_lo)) <= modulus).
      { transitivity (word.unsigned t_hi + 1); [destruct (word.ltu _); unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia; Lia.lia|].
        unfold t_hi. rewrite word.unsigned_mulhuu_nowrap.
        pose proof (word.unsigned_range m) as Hm.
        rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        apply Z.lt_pred_le.
        assert (Z.pred _ = (word.unsigned m * modulus) / 2 ^ width) as -> by Lia.lia.
        apply (Zdiv_lt_upper_bound ((word.unsigned m) * modulus) (2 ^ width) modulus ZZ).
        rewrite (Z.mul_comm modulus).
        apply Zmult_lt_compat_r; Lia.lia. }
      repeat rewrite word.unsigned_add_nowrap; try Lia.lia.
      2:{ apply (Z.le_lt_trans _ (2 * modulus)); [|assumption].
          assert (word.unsigned (@word.of_Z _ word (x / r)) <= modulus); [|Lia.lia].
          rewrite word.unsigned_of_Z_nowrap; Lia.lia. }
      rewrite (word.unsigned_of_Z_nowrap (x/r)) by Lia.lia.
      assert ((x mod r + word.unsigned t_lo) / r = word.unsigned (word.b2w (word.ltu (word.add (word.of_Z x) t_lo) t_lo))) as <-; [|Lia.lia].
      pose proof (word.unsigned_range t_lo) as Hlo.
      pose proof (Z.mod_pos_bound x r ZZ) as [Hxlo].
      destruct (Z_lt_dec (x mod r + word.unsigned t_lo) r) as [Hlt|Hnlt].
      - rewrite <- (Z.mod_small ((x mod r) + word.unsigned t_lo) r) by Lia.lia.
        rewrite Zmod_div. pose proof (Hcond_spec (word.of_Z x) t_lo) as W.
        destruct (word.ltu _ _); unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia; [|reflexivity].
        specialize ((proj1 W) eq_refl). rewrite word.unsigned_of_Z. unfold word.wrap.
        unfold r in *. Lia.lia.
      - rewrite (proj2 (Hcond_spec (word.of_Z x) t_lo)).
        2: rewrite word.unsigned_of_Z; unfold word.wrap, r in *; Lia.lia.
        unfold word.b2w; cbn; rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        pose proof (Zdiv_le_lower_bound (x mod r + word.unsigned t_lo) r 1 ZZ ltac:(Lia.lia)) as Hlow.
        pose proof (Zdiv_lt_upper_bound (x mod r + word.unsigned t_lo) r 2 ZZ ltac:(unfold r; Lia.lia)).
        Lia.lia. }
    assert (modulus <=? word.unsigned t = word.ltu (word.of_Z (Z.pred modulus)) t) as ->.
    { rewrite word.unsigned_ltu, word.unsigned_of_Z_nowrap by Lia.lia.
      pose proof (Zle_cases modulus (word.unsigned t)) as Hcond.
      destruct (_ <=? _); [apply Z.lt_pred_le in Hcond; rewrite (proj2 (Z.ltb_lt _ _)); auto|].
      pose proof (Zlt_cases (Z.pred modulus) (word.unsigned t)); destruct (_ <? _); Lia.lia. }
    pose proof (word.ltu_spec (word.of_Z (Z.pred modulus)) t) as E.
    destruct (word.ltu (word.of_Z (Z.pred modulus)) t); unfold word.b2w, nlet; cbn.
    - rewrite word.mul_1_l. inversion E.
      rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_nowrap; try Lia.lia.
      rewrite word.unsigned_of_Z_nowrap in H by Lia.lia.
      rewrite word.unsigned_of_Z_nowrap; Lia.lia.
    - rewrite word.mul_0_l, word.sub_0_r. reflexivity.
  Qed.

  Lemma to_montgomery_word_correct1 x (Hx: 0 <= x < modulus) (modulus_very_small: modulus * modulus < 2 ^ width):
    word.unsigned (to_montgomery_word1 (word.of_Z x)) = to_montgomery_spec x.
  Proof.
    unfold to_montgomery_word1, to_montgomery_spec.
    unfold nlet. rewrite <- word.ring_morph_mul.
    rewrite montgomery_reduce_correct1; [reflexivity|].
    unfold r2. pose proof (Z.mod_pos_bound (r * r) modulus ltac:(Lia.lia)) as XX.
    split; [Lia.lia|]. transitivity (modulus * modulus); [|Lia.lia].
    apply Zmult_lt_compat; Lia.lia.
  Qed.

  Lemma to_montgomery_word_correct2 x (Hx: 0 <= x < 2 ^ width) (modulus_smaller: 2 * modulus < 2 ^ width):
    word.unsigned (to_montgomery_word2 (word.of_Z x)) = to_montgomery_spec x.
  Proof.
    unfold to_montgomery_word2, to_montgomery_spec.
    unfold nlet. rewrite <- word.ring_morph_mul.
    pose proof (Z.mod_pos_bound (r * r) modulus ltac:(Lia.lia)) as XX.
    assert (SS: 0 <= x * ((r * r) mod modulus) <= r * modulus).
    { split; [Lia.lia|]. apply Z.lt_le_incl.
      apply Zmult_lt_compat; unfold r; Lia.lia. }
    rewrite <- montgomery_reduce_correct2; auto.
    assert (word.mulhuu _ _ = (word.of_Z (x * ((r * r) mod modulus) / r))) as ->; [|reflexivity].
    apply word.unsigned_inj.
    rewrite word.unsigned_mulhuu_nowrap.
    repeat rewrite word.unsigned_of_Z_nowrap; try Lia.lia.
    - reflexivity.
    - split; [apply Z.div_pos; unfold r; Lia.lia|].
      apply (Z.le_lt_trans _ modulus); [|Lia.lia].
      apply Z.div_le_upper_bound; [unfold r|]; Lia.lia.
    - unfold r2; Lia.lia.
  Qed.

  Lemma from_montgomery_word_correct x (Hx: 0 <= x < 2 ^ width):
    word.unsigned (from_montgomery_word (word.of_Z x)) = from_montgomery_spec x.
  Proof.
    unfold from_montgomery_word, from_montgomery_spec, nlet.
    apply montgomery_reduce_correct1; auto.
  Qed.

  Lemma montgomery_mul_correct1 (modulus_very_small: modulus * modulus < 2 ^ width) x y a b:
    feval x = Some a ->
    feval y = Some b ->
    feval (montgomery_mul1 x y) = Some (a * b)%F.
  Proof.
    intros Ha Hb.
    pose proof (feval_is_Some_implies _ _ Ha) as [Hx Heqa].
    pose proof (feval_is_Some_implies _ _ Hb) as [Hy Heqb].
    assert ((word.unsigned (montgomery_mul1 x y)) < modulus) as Hbound.
    { unfold montgomery_mul1, nlet.
      rewrite <- (word.of_Z_unsigned x), <- (word.of_Z_unsigned y).
      rewrite <- word.ring_morph_mul.
      rewrite montgomery_reduce_correct1.
      - apply reduce_in_range.
        + apply modulus_nonzero.
        + apply modulus_range'.
        + split; [Lia.lia|]. unfold r; apply Zmult_le_compat; Lia.lia.
      - split; [Lia.lia|]. transitivity (modulus * modulus); [|Lia.lia].
        apply Zmult_lt_compat; Lia.lia. }
    assert (exists ab, feval (montgomery_mul1 x y) = Some ab) as [ab Hab].
    { unfold feval. destruct (Z_lt_dec _ _) as [_|?]; [|Lia.lia].
      eexists; reflexivity. }
    pose proof (feval_is_Some_implies _ _ Hab) as [Hxy Heqab].
    rewrite Hab. f_equal.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    rewrite Heqab. unfold montgomery_mul1, nlet.
    rewrite <- (word.of_Z_unsigned x), <- (word.of_Z_unsigned y).
    rewrite <- word.ring_morph_mul.
    rewrite montgomery_reduce_correct1 by (split; [Lia.lia|]; transitivity (modulus * modulus); [|Lia.lia]; apply Zmult_lt_compat; Lia.lia).
    cbn. rewrite Heqa, Heqb.
    assert (reduce_spec _ = mul_spec (word.unsigned x) (word.unsigned y)) as -> by reflexivity.
    rewrite <- Z.mod_mod at 1 by Lia.lia.
    assert (mul_spec _ _ * _ mod _ = from_montgomery_spec (mul_spec (word.unsigned x) (word.unsigned y))) as ->.
    { unfold from_montgomery_spec.
      rewrite <- (Z.mod_small (reduce_spec _) modulus).
      - rewrite reduce_spec_correct. reflexivity.
      - apply (reduce_in_range _ modulus_nonzero _ _ modulus_range').
        assert (0 <= mul_spec (word.unsigned x) (word.unsigned y) < modulus); [|split; [Lia.lia|]].
        + apply (reduce_in_range _ modulus_nonzero _ _ modulus_range').
          split; [Lia.lia|]. apply Zmult_le_compat; unfold r; Lia.lia.
        + transitivity modulus; [Lia.lia|]. unfold r.
          rewrite <- Z.mul_1_l at 1. apply Zmult_le_compat; Lia.lia. }
    rewrite mul_spec_correct.
    rewrite <- Z.mul_mod_idemp_l, <- Z.mul_mod_idemp_r at 1 by Lia.lia.
    f_equal. f_equal; unfold from_montgomery_spec; apply reduce_spec_correct.
  Qed.

  Lemma montgomery_mul_correct2 (modulus_smaller: 2 * modulus < 2 ^ width) x y a b:
    feval x = Some a ->
    feval y = Some b ->
    feval (montgomery_mul2 x y) = Some (a * b)%F.
  Proof.
    intros Ha Hb.
    pose proof (feval_is_Some_implies _ _ Ha) as [Hx Heqa].
    pose proof (feval_is_Some_implies _ _ Hb) as [Hy Heqb].
    assert ((word.unsigned (montgomery_mul2 x y)) = reduce_spec (word.unsigned x * word.unsigned y)) as XX.
    { unfold montgomery_mul2, nlet.
      rewrite <- (word.of_Z_unsigned x), <- (word.of_Z_unsigned y).
      rewrite <- word.ring_morph_mul.
      assert (word.mulhuu _ _ = (word.of_Z ((word.unsigned x * word.unsigned y) / r))) as ->.
      { apply word.unsigned_inj.
        rewrite word.unsigned_mulhuu_nowrap.
        do 2 rewrite word.of_Z_unsigned.
        symmetry; apply word.unsigned_of_Z_nowrap.
        split; [apply Z.div_le_lower_bound; Lia.lia|].
        apply Z.div_lt_upper_bound; [Lia.lia|].
        apply Zmult_lt_compat; Lia.lia. }
      repeat rewrite word.of_Z_unsigned.
      rewrite montgomery_reduce_correct2; auto.
      split; [Lia.lia|]. transitivity (modulus * modulus); [|unfold r; apply Zmult_le_compat; Lia.lia].
      apply Z.lt_le_incl. apply Zmult_lt_compat; Lia.lia. }
    assert ((word.unsigned (montgomery_mul2 x y)) < modulus) as Hbound.
    { rewrite XX.
      apply reduce_in_range.
      - apply modulus_nonzero.
      - apply modulus_range'.
      - split; [Lia.lia|]. unfold r; apply Zmult_le_compat; Lia.lia. }
    assert (exists ab, feval (montgomery_mul2 x y) = Some ab) as [ab Hab].
    { unfold feval. destruct (Z_lt_dec _ _) as [_|?]; [|Lia.lia].
      eexists; reflexivity. }
    pose proof (feval_is_Some_implies _ _ Hab) as [Hxy Heqab].
    rewrite Hab. f_equal.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    rewrite Heqab. rewrite XX. cbn. rewrite Heqa, Heqb.
    assert (reduce_spec _ = mul_spec (word.unsigned x) (word.unsigned y)) as -> by reflexivity.
    rewrite <- Z.mod_mod at 1 by Lia.lia.
    assert (mul_spec _ _ * _ mod _ = from_montgomery_spec (mul_spec (word.unsigned x) (word.unsigned y))) as ->.
    { unfold from_montgomery_spec.
      rewrite <- (Z.mod_small (reduce_spec _) modulus).
      - rewrite reduce_spec_correct. reflexivity.
      - apply (reduce_in_range _ modulus_nonzero _ _ modulus_range').
        assert (0 <= mul_spec (word.unsigned x) (word.unsigned y) < modulus); [|split; [Lia.lia|]].
        + apply (reduce_in_range _ modulus_nonzero _ _ modulus_range').
          split; [Lia.lia|]. apply Zmult_le_compat; unfold r; Lia.lia.
        + transitivity modulus; [Lia.lia|]. unfold r.
          rewrite <- Z.mul_1_l at 1. apply Zmult_le_compat; Lia.lia. }
    rewrite mul_spec_correct.
    rewrite <- Z.mul_mod_idemp_l, <- Z.mul_mod_idemp_r at 1 by Lia.lia.
    f_equal. f_equal; unfold from_montgomery_spec; apply reduce_spec_correct.
  Qed.

  Instance spec_of_to_montgomery1 : spec_of to_montgomery_name :=
    fnspec! to_montgomery_name (X: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = to_montgomery_word1 X }.

  Derive to_montgomery_br2fn1 SuchThat
    (defn! to_montgomery_name("x") ~> "res"
       { to_montgomery_br2fn1 },
      implements to_montgomery_word1)
    As to_montgomery_br2fn_ok1.
  Proof.
    compile_setup.
    unfold montgomery_reduce1.
    repeat repeat compile_step.
  Qed.

  Instance spec_of_to_montgomery2 : spec_of to_montgomery_name :=
    fnspec! to_montgomery_name (X: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = to_montgomery_word2 X }.

  Derive to_montgomery_br2fn2 SuchThat
    (defn! to_montgomery_name("x") ~> "res"
       { to_montgomery_br2fn2 },
      implements to_montgomery_word2)
    As to_montgomery_br2fn_ok2.
  Proof.
    compile_setup.
    unfold montgomery_reduce2.
    repeat repeat compile_step.
    - unfold v0. apply expr_compile_word_mul.
      + eapply expr_compile_var. instantiate (1 := "x").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      + apply expr_compile_Z_literal.
    - apply expr_compile_word_mulhuu.
      + eapply expr_compile_var. instantiate (1 := "x").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      + apply expr_compile_Z_literal.
  Qed.

  Instance spec_of_from_montgomery : spec_of from_montgomery_name :=
    fnspec! from_montgomery_name (X: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = from_montgomery_word X }.

  Derive from_montgomery_br2fn SuchThat
    (defn! from_montgomery_name("x") ~> "res"
       { from_montgomery_br2fn },
      implements from_montgomery_word)
    As from_montgomery_br2fn_ok.
  Proof.
    compile_setup.
    unfold montgomery_reduce1.
    repeat repeat compile_step.
  Qed.

  Instance spec_of_mul_dummy1 : spec_of mul_name :=
    fnspec! mul_name (X Y: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = montgomery_mul1 X Y }.

  Derive mul_br2fn1 SuchThat
    (defn! mul_name("x", "y") ~> "res"
       { mul_br2fn1 },
      implements montgomery_mul1)
    As dummy_mul_br2fn_ok1.
  Proof.
    compile_setup.
    unfold montgomery_reduce1.
    repeat repeat compile_step.
  Qed.

  Lemma mul_br2fn_ok1 (modulus_very_small: modulus * modulus < 2 ^ width):
    program_logic_goal_for mul_br2fn1
      (forall functions : map.rep,
          map.get functions mul_name = Some mul_br2fn1 ->
          spec_of_mul functions).
  Proof.
    red. intros. red. red. red. intros. destruct H0.
    generalize (dummy_mul_br2fn_ok1 I _ H).
    intros. eapply Proper_call; [|apply dummy_mul_br2fn_ok1; auto; exact I].
    intros ? ? ? ?. destruct H3 as (? & -> & -> & -> & ->).
    eexists; repeat split; try reflexivity.
    apply montgomery_mul_correct1; auto.
  Qed.

  Instance spec_of_mul_dummy2 : spec_of mul_name :=
    fnspec! mul_name (X Y: word) ~> res,
    { requires tr mem :=
        True;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        res = montgomery_mul2 X Y }.

  Derive mul_br2fn2 SuchThat
    (defn! mul_name("x", "y") ~> "res"
       { mul_br2fn2 },
      implements montgomery_mul2)
    As dummy_mul_br2fn_ok2.
  Proof.
    compile_setup.
    unfold montgomery_reduce2.
    repeat repeat compile_step.
    - unfold v0. apply expr_compile_word_mul.
      + eapply expr_compile_var. instantiate (1 := "x").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      + eapply expr_compile_var. instantiate (1 := "y").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
    - apply expr_compile_word_mulhuu.
      + eapply expr_compile_var. instantiate (1 := "x").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      + eapply expr_compile_var. instantiate (1 := "y").
        cbn. repeat rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
  Qed.

  Lemma mul_br2fn_ok2 (modulus_smaller: 2 * modulus < 2 ^ width):
    program_logic_goal_for mul_br2fn2
      (forall functions : map.rep,
          map.get functions mul_name = Some mul_br2fn2 ->
          spec_of_mul functions).
  Proof.
    red. intros. red. red. red. intros. destruct H0.
    generalize (dummy_mul_br2fn_ok2 I _ H).
    intros. eapply Proper_call; [|apply dummy_mul_br2fn_ok2; auto; exact I].
    intros ? ? ? ?. destruct H3 as (? & -> & -> & -> & ->).
    eexists; repeat split; try reflexivity.
    apply montgomery_mul_correct2; auto.
  Qed.

End __.

(* Require Import bedrock2.BasicC64Semantics. *)

(* Eval compute in ToCString.c_func ("to_montgomery", (@to_montgomery_br2fn1 64 (Naive.word _) 8380417)). *)

(* Eval compute in ToCString.c_func ("from_montgomery", (@from_montgomery_br2fn 64 (Naive.word _) 8380417)). *)
