(* Verification of the 256-bit Binary Extended Euclidean modular inverse (beeu_modinv).
 *
 * Proof strategy:
 * - Loop invariants (helper_loop_ok): starting from (a, b, x, y) = (M, b0, 1, 0) with odd M > 1,
 *   each iteration subtracts the smaller of (a, b) from the larger (helper_subtract_ok) and
 *   shifts out up to 63 trailing zeros from each while dividing (x, y) by the corresponding
 *   powers of 2 modulo M (beeu_shrtz_ok). This preserves:
 *   1. GCD: Z.gcd a b = Z.gcd M b0 (via gcd_pow2_l, gcd_pow2_r).
 *   2. Congruences: a ≡ -y * b0 (mod M) and b ≡ x * b0 (mod M) (via mod_pow2_inv, shrtz_cong).
 *   3. 320-bit bounds on (x, y): parameterized by bit-size progress
 *      k = (Z_size a0 + Z_size b0) - (Z_size a + Z_size b) (via Z_size_sub, Z_size_mul_pow2).
 *      Because beeu_shrtz caps shifts at 63 bits (lctz_even_min63), one of (a, b) can remain even
 *      after a 63-bit shift. half_inv / xy_inv track the three resulting parity regimes so that
 *      x + y < 2^320 holds on every iteration (xy_inv_sum_lt_320).
 * - WLOG symmetry: xy_inv_step proves one loop step assuming a <= b; helper_loop_step_complete
 *   handles both a <= b and b < a by swapping (a, y) <-> (b, x) via xy_inv_swap.
 * - Post-loop (beeu_modinv_ok): when b = 0 and a = Z.gcd M b0 = 1, beeu_normalize reduces y mod M
 *   and modinv_from_bezout derives ((M - y mod M) * b0) mod M = 1. *)

From Coq Require Import BinInt String List InitialRing ZArith Lia.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords ArrayCasts Syntax.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2Examples.full_sub bedrock2Examples.full_add bedrock2Examples.u320_add bedrock2Examples.full_mul.
From coqutil Require Import Tactics.Tactics WithBaseName Z.CountTrailingZeros.
Require Import coqutil.Z.PushPullMod coqutil.Word.Properties.

Require Import u320_muladd beeu_normalize u320_sub beeu_shrtz u320_shr u256_shr br_ctz.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Lemma mod2_cases (n : Z) : n mod 2 = 0 \/ n mod 2 = 1.
Proof. pose proof (Z.mod_pos_bound n 2); lia. Qed.

Local Lemma Z_mod_mult' (a b : Z) : (a * b) mod a = 0.
Proof. rewrite Z.mul_comm; apply Z_mod_mult. Qed.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (bits.of_Z _ 8)).

Definition u256_dec := func! (p_x, p_y) ~> b {
    b = $0;
    unpack! d0, b = br_full_sub(load(p_x), load(p_y), b);
    unpack! d1, b = br_full_sub(load(p_x + $8), load(p_y + $8), b);
    unpack! d2, b = br_full_sub(load(p_x + $8 + $8), load(p_y + $8 + $8), b);
    unpack! d3, b = br_full_sub(load(p_x + $8 + $8 + $8), load(p_y + $8 + $8 + $8), b);

    store(p_x, d0);
    store(p_x + $8, d1);
    store(p_x + $8 + $8, d2);
    store(p_x + $8 + $8 + $8, d3)
}.

Definition u256_sub := func! (p_out, p_x, p_y) ~> b {
    b = $0;
    unpack! d0, b = br_full_sub(load(p_x), load(p_y), b);
    unpack! d1, b = br_full_sub(load(p_x + $8), load(p_y + $8), b);
    unpack! d2, b = br_full_sub(load(p_x + $8 + $8), load(p_y + $8 + $8), b);
    unpack! d3, b = br_full_sub(load(p_x + $8 + $8 + $8), load(p_y + $8 + $8 + $8), b);

    store(p_out, d0);
    store(p_out + $8, d1);
    store(p_out + $8 + $8, d2);
    store(p_out + $8 + $8 + $8, d3)
}.

(* Construct a 320-bit integer out of a 256-bit integer. *)
Definition u256_to_u320 := func! (p_out, p_m) {
    store(p_out, load(p_m));
    store(p_out + $8, load(p_m + $8));
    store(p_out + $8 + $8, load(p_m + $8 + $8));
    store(p_out + $8 + $8 + $8, load(p_m + $8 + $8 + $8));
    store(p_out + $8 + $8 + $8 + $8, $0)
}.

Definition u256_set := func! (p_x, p_y) {
    store(p_x, load(p_y));
    store(p_x + $8, load(p_y + $8));
    store(p_x + $8 + $8, load(p_y + $8 + $8));
    store(p_x + $8 + $8 + $8, load(p_y + $8 + $8 + $8))
}.

Definition u320_set_const := func! (p_x, x) {
    store(p_x, x);
    store(p_x + $8, $0);
    store(p_x + $8 + $8, $0);
    store(p_x + $8 + $8 + $8, $0);
    store(p_x + $8 + $8 + $8 + $8, $0)
}.

Definition u256_comp := func! (p_a, w) ~> r {
    r = (load(p_a) ^ w | load(p_a + $8) | load(p_a + $8 + $8) | load(p_a + $8 + $8 + $8))
}.

Definition helper_subtract := func! (p_a, p_b, p_x, p_y) {
    stackalloc 32 as b_minus_a;
    unpack! borrow = u256_sub(b_minus_a, p_b, p_a);

    if borrow {
        unpack! b1 = u256_dec(p_a, p_b);
        unpack! c1 = u320_add(p_y, p_x)
    } else {
        u256_set(p_b, b_minus_a);
        unpack! c1 = u320_add(p_x, p_y)
    }
}.

Definition helper_loop := func! (p_a, p_b, p_x, p_y, p_m, inv_m) {
    unpack! cmp = u256_comp(p_b, $0);
    while (cmp) {
        helper_subtract(p_a, p_b, p_x, p_y);

        beeu_shrtz(p_b, p_x, p_m, inv_m);
        beeu_shrtz(p_a, p_y, p_m, inv_m);
        unpack! cmp = u256_comp(p_b, $0)
    }
}.

Definition beeu_modinv := func! (p_out, p_a, p_m, inv_m) ~> c {
    (* Allocate variables on the stack *)
    stackalloc 32 as a;
    stackalloc 32 as b;
    stackalloc 40 as p_m320;
    stackalloc 40 as x;
    stackalloc 40 as y;

    (* Initialize stack vars *)
    u256_set(a, p_m);
    u256_set(b, p_a);
    u256_to_u320(p_m320, p_m);
    u320_set_const(x, $1);
    u320_set_const(y, $0);


    helper_loop(a, b, x, y, p_m, inv_m);

    unpack! cmp = u256_comp(a, $1);
    if (cmp == $0) {
        c = $1;
        beeu_normalize(y, p_m320);
        unpack! borrow = u256_sub(p_out, p_m, y)
    } else {
        c = $0
    }
}.

#[local] Instance spec_of_helper_loop : spec_of "helper_loop" :=
    fnspec! "helper_loop" (p_a p_b p_x p_y p_m inv_m : word) / (a b x y MOD : list word) R,
    {
        requires t m :=
            m =* array p_a a ⋆ array p_b b ⋆ array p_x x ⋆ array p_y y ⋆ array p_m MOD ⋆ R /\
            length a = 4%nat /\ length b = 4%nat /\ length x = 5%nat /\ length y = 5%nat /\
            length MOD = 4%nat /\
            (eval MOD) mod 2 = 1 /\ (eval MOD) > 1 /\
            (eval a) = (eval MOD) /\ 0 <= eval b < eval MOD /\
            (eval x) = 1 /\ (eval y) = 0 /\
            inv_m * (eval MOD) mod (2^64) = 2^64 - 1;
        ensures T M :=
            T = t /\ exists (A B X Y : list word),
            M =* array p_a A ⋆ array p_b B ⋆ array p_x X ⋆ array p_y Y ⋆ array p_m MOD ⋆ R /\
            length A = 4%nat /\ length B = 4%nat /\
            length X = 5%nat /\ length Y = 5%nat /\
            (eval B) = 0 /\ (eval A) = Z.gcd (eval a) (eval b)
            /\ (eval A) mod (eval MOD) = (-((eval Y) * (eval b))) mod (eval MOD)
    }.

#[local] Instance spec_of_u256_comp : spec_of "u256_comp" :=
    fnspec! "u256_comp" (p_x w : word) / (x : list word) R ~> c,
    {
        requires t m :=
            m =* array p_x x ⋆ R /\
                length x = 4%nat;
        ensures T M :=
            T = t /\ M = m /\
                if (eval x =? w) then
                    c = bits.of_Z _ 0
                else
                    c <> bits.of_Z _ 0
    }.

#[local] Instance spec_of_u256_dec : spec_of "u256_dec" :=
    fnspec! "u256_dec" (p_x p_y : word) / (x y : list word) R ~> b,
    {
        requires t m :=
            m =* array p_x x ⋆ array p_y y ⋆ R /\
            length x = 4%nat /\ length y = 4%nat;
        ensures T M := T = t /\ exists (r : list word),
            M =* array p_x r ⋆ array p_y y ⋆ R /\
            length r = 4%nat /\ eval r - 2^256*b = eval x - eval y
    }.

#[local] Instance spec_of_u256_sub : spec_of "u256_sub" :=
    fnspec! "u256_sub" (p_out p_x p_y : word) / (out x y : list word) R ~> b,
    {
        requires t m :=
            m =* array p_out out ⋆ array p_x x ⋆ array p_y y ⋆ R /\
            length out = 4%nat /\ length x = 4%nat /\ length y = 4%nat;
        ensures T M := T = t /\ exists (r : list word),
            M =* array p_out r ⋆ array p_x x ⋆ array p_y y ⋆ R /\
            length r = 4%nat /\ eval r - 2^256*b = eval x - eval y
    }.

#[local] Instance spec_of_u256_to_u320 : spec_of "u256_to_u320" :=
    fnspec! "u256_to_u320" (p_out p_m : word) / (out m_ : list word) R,
    {
        requires t m :=
            m =* array p_out out ⋆ array p_m m_ ⋆ R /\
            length out = 5%nat /\ length m_ = 4%nat;
        ensures T M :=
            T = t /\ exists r, M =*
                array p_out r ⋆ array p_m m_ ⋆ R /\
            length r = 5%nat /\ eval r = eval m_
    }.
#[local] Instance spec_of_u256_set : spec_of "u256_set" :=
    fnspec! "u256_set" (p_x p_y : word) / (x y : list word) R,
    {
        requires t m :=
            m =* array p_x x ⋆ array p_y y ⋆ R /\
            length x = 4%nat /\ length y = 4%nat;
        ensures T M := T = t /\
            M =* array p_x y ⋆ array p_y y ⋆ R
    }.

#[local] Instance spec_of_u320_set_const : spec_of "u320_set_const" :=
    fnspec! "u320_set_const" (p_x x : word) / (x_ : list word) R,
    {
        requires t m :=
            m =* array p_x x_ ⋆ R /\
            length x_ = 5%nat;
        ensures T M := T = t /\ exists (r : list word),
            M =* array p_x r ⋆ R /\
            length r = 5%nat /\
            eval r = x
    }.

#[local] Instance spec_of_helper_subtract : spec_of "helper_subtract" :=
    fnspec! "helper_subtract" (p_a p_b p_x p_y : word) / (a b x y : list word) R,
    {
        requires t m :=
            m =* array p_a a ⋆ array p_b b ⋆ array p_x x ⋆ array p_y y ⋆ R /\
                length a = 4%nat /\ length b = 4%nat /\ length x = 5%nat /\ length y = 5%nat /\
                eval x + eval y < 2^320;
        ensures T M :=
            T = t /\ exists (A B X Y : list word),
                M=* array p_a A ⋆ array p_b B ⋆ array p_x X ⋆ array p_y Y ⋆ R /\
                length A = 4%nat /\ length B = 4%nat /\ length X = 5%nat /\ length Y = 5%nat
                /\ if (eval a <=? eval b) then
                    A = a /\ (eval B) = (eval b) - (eval a) /\ Y = y /\ eval X = (eval x) + (eval y)
                else
                    (B = b) /\ (eval A) = (eval a) - (eval b) /\ X = x /\ eval Y = (eval x) + (eval y)
    }.



#[export] Instance spec_of_beeu_modinv : spec_of "beeu_modinv" :=
    fnspec! "beeu_modinv" (p_out p_a p_m inv_m : word) / (out a MOD : list word) R ~> c,
    {
        requires t m :=
            m =* array p_out out ⋆ array p_a a ⋆ array p_m MOD ⋆ R /\
            length out = 4%nat /\ length a = 4%nat /\ length MOD = 4%nat /\
            eval MOD > 1 /\ eval MOD mod 2 = 1 /\
            0 <= eval a < eval MOD /\
            inv_m * (eval MOD) mod (2^64) = 2^64 - 1;
        ensures T M := T = t /\ exists OUT,
            M =* array p_out OUT ⋆ array p_a a ⋆ array p_m MOD ⋆ R /\
            length OUT = 4%nat /\
                if (Z.gcd (eval a) (eval MOD) =? 1)
                then
                    c = bits.of_Z _ 1 /\
                    ((eval OUT) * (eval a)) mod (eval MOD) = 1 /\
                    0 <= (eval OUT) < (eval MOD)
                else
                    c = bits.of_Z _ 0
    }.

Lemma array_to_bytes ptr ws :
    Lift1Prop.iff1 (array ptr ws) (@Array.array _ _ mem _ ptsto (bits.of_Z _ 1) ptr (ws2bs 8 ws)).
Proof.
    eapply (@bytes_of_words 64 _ mem _ _).
Qed.

Lemma bytes_to_array ptr bs :
    (length bs mod 8)%nat = 0%nat ->
    Lift1Prop.iff1 (@Array.array _ _ mem _ ptsto (bits.of_Z _ 1) ptr bs) (array ptr (bs2ws 8 bs)).
Proof. intros H. eapply (@words_of_bytes 64 _ mem _ _).
    cbn. replace (PosDef.Pos.to_nat 8) with 8%nat by lia.
    lia.
Qed.

#[local] Ltac ensure_map m := lazymatch type of m with | @Interface.map.rep _ _ _ => true | _ => false end.

#[local] Ltac newest_memory_hyp := match goal with | H: ?G ?m |- _ =>
    match (ensure_map m) with true => H | false => fail end end.

#[local] Ltac alloc_array ptr st :=
    match goal with
    | [H : Datatypes.length st = ?n |- _] =>
        let Hmem := newest_memory_hyp in
        seprewrite_in_by (bytes_to_array ptr st) Hmem ltac:(rewrite H; eauto);
        let prev := fresh "prev" in
        let Heqprev := fresh "Heqprev" in
        remember (bs2ws 8 st) as prev eqn:Heqprev;
        let m := eval cbv in (Z.to_nat (n / 8)) in
        assert (length prev = m) by (rewrite Heqprev, bs2ws_length; try rewrite !H; eauto);
        clear dependent st
    end.

#[local] Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [|x l]; inversion H; clear H end.

#[local] Ltac dealloc_array ptr arr :=
    match goal with
    | [H : Datatypes.length arr = ?n |- _] =>
        let Hmem := newest_memory_hyp in
        seprewrite_in (array_to_bytes ptr arr) Hmem;
        let m := eval cbv in (Z.to_nat (8 * n)) in
            assert (length (ws2bs 8 arr) = m) by (lists_into_elements; eauto)
    end.

Lemma u256_dec_ok : program_logic_goal_for_function! u256_dec.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_ ; _ ; _ ; _]. intuition try ecancel_assumption. cbn [fold_right]. ZnWords.
Qed.

Lemma u256_sub_ok : program_logic_goal_for_function! u256_sub.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_; _; _; _]. intuition try ecancel_assumption.
    cbn [fold_right]. ZnWords.
Qed.

Lemma u256_to_u320_ok : program_logic_goal_for_function! u256_to_u320.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat straightline. eexists [_; _; _; _; _];
    intuition try ecancel_assumption.
Qed.

Lemma u256_set_ok : program_logic_goal_for_function! u256_set.
Proof.
    repeat straightline; lists_into_elements; cbv [array] in *;
    repeat straightline; intuition try ecancel_assumption.
Qed.

Lemma u320_set_const_ok : program_logic_goal_for_function! u320_set_const.
Proof.
    repeat straightline; lists_into_elements; cbv [array] in *;
    repeat straightline; eexists [_; _; _; _; _];
    intuition try ecancel_assumption; cbv [eval] in *; ZnWords.
Qed.

Lemma u256_comp_ok : program_logic_goal_for_function! u256_comp.
Proof.
    repeat straightline. lists_into_elements. cbn [array] in *.
    repeat straightline.
    destruct (eval [x0; x1; x2; x3] =? w) eqn: Hn;
    [ eapply Z.eqb_eq in Hn | eapply Z.eqb_neq in Hn ].
    {
        cbv [fold_right] in *.
        assert (x0 = w) by ZnWords.
        assert (x1 = bits.of_Z _ 0) by ZnWords.
        assert (x2 = bits.of_Z _ 0) by ZnWords.
        assert (x3 = bits.of_Z _ 0) by ZnWords.
        subst. cbv [v].
        rewrite Zmod.of_Z_0, !word.or_0_r.
        apply bits.xor_zero_iff; reflexivity.
    }
    {
        cbv [fold_right] in *. intros contra. cbv [v] in contra.
        rewrite ?Zmod.of_Z_0, !word.lor_0_iff, bits.xor_zero_iff in contra.
        destruct contra as [[[-> ?] ?] ?]; ZnWords.
    }
Qed.
Local Existing Instance spec_of_u320_add.

Local Ltac bigZnWords :=
    lists_into_elements; cbv [eval] in *; ZnWords.

Lemma helper_subtract_ok : program_logic_goal_for_function! helper_subtract.
Proof.
  repeat straightline.
  alloc_array a0 stack.
  repeat (straightline || straightline_call); ssplit; try ecancel_assumption; eauto.
  eexists; ssplit; [ | intros | intros ];
  repeat (straightline || straightline_call); ssplit; try ecancel_assumption; eauto.
  all: dealloc_array a0 x1;
  repeat straightline; eexists _, _, _, _; ssplit; try ecancel_assumption; eauto;
  match goal with
  | [H : ?x <> 0 |- _] =>
    assert (Hcond : (eval a <=? eval b) = false) by bigZnWords
  | [H : ?x = 0 |- _] =>
    assert (Hcond : (eval a <=? eval b) = true) by bigZnWords
  end;
  rewrite Hcond in *; ssplit; eauto; bigZnWords.
Qed.

#[local] Instance spec_of_u256_sub' : spec_of "u256_sub" :=
    fnspec! "u256_sub" (p_out p_x p_y : word) / (out x y : list word) R ~> b,
    {
        requires t m :=
            m =* array p_out out ⋆ array p_x x ⋆ array p_y y ⋆ R /\
            length out = 4%nat /\ length x = 4%nat /\ length y = 5%nat
            /\ (eval y) < 2^256;
        ensures T M := T = t /\ exists (r : list word),
            M =* array p_out r ⋆ array p_x x ⋆ array p_y y ⋆ R /\
            length r = 4%nat /\ eval r - 2^256*b = eval x - eval y
    }.

Lemma u256_sub'_ok : program_logic_goal_for_function! u256_sub.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_; _; _; _]. intuition try ecancel_assumption. cbv [fold_right] in *.
    ZnWords.
Qed.


Ltac keep_length_equations :=
  repeat match goal with
  | [ H : ?T |- _ ] =>
      lazymatch T with
      | length _ = _ => fail
      | _ => clear H
      end
  end.

#[local] Ltac clear_old_memory_hyps :=
    let Hkeep := newest_memory_hyp in
        generalize dependent Hkeep;
    repeat match goal with
    | H : ?G ?m |- _ =>
        match (ensure_map m) with
        | true => clear dependent H
        | false => fail
        end
    end;
    intros.

Lemma modinv_from_bezout (M a y out : Z) :
  M > 1 -> 1 mod M = (- (y * a)) mod M -> out = M - y mod M ->
  (out * a) mod M = 1 /\ 1 <= out < M.
Proof.
  intros HM Hbez ->; pose proof (Z.mod_pos_bound y M ltac:(lia)).
  assert (Hy0 : y mod M <> 0).
  { intros Hy0; rewrite Z.mod_1_l, <- Z.sub_0_l, <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l,
      Hy0, Z.mul_0_l, !Zmod_0_l in Hbez by lia; lia. }
  split; [| lia].
  Z.push_pull_mod; rewrite Z.mul_sub_distr_r; Z.push_mod_step; rewrite Z_mod_mult', Z.sub_0_l.
  Z.push_pull_mod; rewrite Z.sub_0_l, <- Hbez, Z.mod_1_l by lia; reflexivity.
Qed.

Definition Z_size (z : Z) : Z := if z <=? 0 then 0 else Z.succ (Z.log2 z).

Lemma Z_size_nonneg (x : Z) : 0 <= Z_size x.
Proof. cbv [Z_size]; destruct (x <=? 0); [lia | pose proof (Z.log2_nonneg x); lia]. Qed.

Lemma Z_size_sub (a b : Z) : a >= 0 -> b >= 0 -> b <= a -> Z_size (a - b) <= Z_size a.
Proof.
  intros; cbv [Z_size]; destruct (a - b <=? 0) eqn:E1, (a <=? 0) eqn:E2;
    rewrite ?Z.leb_le, ?Z.leb_gt in *; try (pose proof (Z.log2_nonneg a); lia).
  pose proof (Z.log2_le_mono (a - b) a ltac:(lia)); lia.
Qed.

Lemma Z_size_mul_pow2 (a n : Z) : a > 0 -> 0 <= n -> Z_size (a * 2 ^ n) = Z_size a + n.
Proof.
  intros Ha Hn; cbv [Z_size]; assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  destruct (a * 2 ^ n <=? 0) eqn:E1, (a <=? 0) eqn:E2; rewrite ?Z.leb_le, ?Z.leb_gt in *; try nia.
  rewrite Z.log2_mul_pow2 by lia; lia.
Qed.

Lemma Z_size_le (n x : Z) : 0 <= n -> 0 <= x < 2^n -> Z_size x <= n.
Proof.
  intros Hn Hx; cbv [Z_size]; destruct (x <=? 0) eqn:E; [lia | rewrite Z.leb_gt in E].
  pose proof (proj1 (Z.log2_lt_pow2 x n E) ltac:(lia)); lia.
Qed.

Lemma lctz_ge_0 (default x : Z) : 0 <= default -> 0 <= lctz default x.
Proof. intros; destruct x; cbv [lctz]; lia. Qed.

Lemma lctz_odd (default a : Z) : a >= 0 -> a mod 2 = 1 -> lctz default a = 0.
Proof.
  intros; destruct a as [| [p|p|] | p]; try reflexivity; try (cbn in *; lia).
  rewrite Pos2Z.pos_xO, Z.mul_comm, Z.mod_mul in H0 by lia; discriminate.
Qed.

Lemma lctz_ge_1 (default z : Z) : 0 <= default -> z > 0 -> z mod 2 = 0 -> 1 <= lctz default z.
Proof.
  intros; pose proof (lctz_ge_0 default z H); destruct (Z.eq_dec (lctz default z) 0) as [Heq0 | ?]; [|lia].
  destruct (lctz_spec default z ltac:(lia)) as [k [Hk Hz]]; rewrite Heq0, Z.pow_0_r, Z.mul_1_r in Hz; congruence.
Qed.

Lemma lctz_even_min63 (default z q : Z) :
  0 <= default -> z > 0 -> q * 2 ^ Z.min (lctz default z) 63 = z -> q mod 2 = 0 ->
  Z.min (lctz default z) 63 = 63.
Proof.
  intros; pose proof (lctz_ge_0 default z H).
  destruct (Z_lt_ge_dec (lctz default z) 63); [|rewrite Z.min_r by lia; reflexivity].
  rewrite Z.min_l in H1 by lia; destruct (lctz_spec default z ltac:(lia)) as [k [Hk Hz]].
  assert (q = k) by (apply (Z.mul_reg_r _ _ (2 ^ lctz default z)); [apply Z.pow_nonzero; lia | congruence]); congruence.
Qed.

Lemma gcd_double_l (a b : Z) : b mod 2 = 1 -> Z.gcd (2 * a) b = Z.gcd a b.
Proof.
  intros H; destruct a as [| p | p], b as [| [q|q|] | [q|q|]];
  try (discriminate || reflexivity);
  try (rewrite Pos2Z.pos_xO, Z.mul_comm, Z.mod_mul in H by lia; discriminate);
  try (rewrite Pos2Z.neg_xO, Z.mul_comm, Z.mod_mul in H by lia; discriminate);
  try rewrite <- Pos2Z.pos_xO; try rewrite <- Pos2Z.neg_xO;
  try rewrite !(Z.gcd_comm _ 1); try rewrite !(Z.gcd_comm _ (-1)); reflexivity.
Qed.

Lemma gcd_pow2_l (n a b : Z) : n >= 0 -> b mod 2 = 1 -> Z.gcd (a * 2 ^ n) b = Z.gcd a b.
Proof.
  intros Hn Hb; rewrite Z.mul_comm; pattern n; apply natlike_ind; [| | lia].
  { rewrite Z.pow_0_r, Z.mul_1_l; reflexivity. }
  { intros x Hx IH; rewrite Z.pow_succ_r, <- Z.mul_assoc, gcd_double_l by lia; exact IH. }
Qed.

Lemma gcd_pow2_r (n a b : Z) : n >= 0 -> a mod 2 = 1 -> Z.gcd a (b * 2 ^ n) = Z.gcd a b.
Proof. intros; rewrite !(Z.gcd_comm a); apply gcd_pow2_l; auto. Qed.

Lemma mod_pow2_inv (m a b n : Z) : m > 1 -> m mod 2 = 1 -> n >= 0 ->
  a * 2^n mod m = b * 2^n mod m -> a mod m = b mod m.
Proof.
  intros; assert (Hg : Z.gcd (2^n) m = 1) by (rewrite <- (Z.mul_1_l (2^n)), gcd_pow2_l, Z.gcd_1_l by lia; auto).
  destruct (Z.gcd_bezout (2^n) m 1 Hg) as [u [v Huv]].
  replace a with (a * (u * 2^n + v * m)) by (rewrite Huv; ring).
  replace b with (b * (u * 2^n + v * m)) by (rewrite Huv; ring).
  replace (a * (u * 2^n + v * m)) with (a * 2^n * u + a * v * m) by ring.
  replace (b * (u * 2^n + v * m)) with (b * 2^n * u + b * v * m) by ring.
  rewrite !Z_mod_plus_full; Z.push_mod_step; rewrite H2; Z.pull_mod; reflexivity.
Qed.

Lemma shrtz_cong (v v' u u' b0 M s : Z) :
  M > 1 -> M mod 2 = 1 -> s >= 0 ->
  v' * 2^s = v -> u' * 2^s mod M = u mod M ->
  v mod M = (u * b0) mod M ->
  v' mod M = (u' * b0) mod M.
Proof.
  intros HM Hodd Hs Hv Hu Hcong.
  eapply mod_pow2_inv with (n := s); eauto.
  rewrite Hv, Hcong; replace (u' * b0 * 2 ^ s) with (u' * 2 ^ s * b0) by ring.
  rewrite <- (Z.mul_mod_idemp_l (u' * 2 ^ s)), Hu, Z.mul_mod_idemp_l by lia; reflexivity.
Qed.

Lemma pow2_bound_OO (s k : Z) : 0 <= k -> 1 <= s -> 2 ^ (s + 1) + 2 * k + 4 <= 2 ^ s * (3 + k + s).
Proof.
  intros; destruct (Z.eq_dec s 1) as [-> | ?]; [lia |].
  replace (2 ^ (s + 1)) with (2 * 2 ^ s) by (rewrite Z.pow_add_r by lia; lia).
  assert (4 <= 2 ^ s) by (transitivity (2 ^ 2); [lia | apply Z.pow_le_mono_r; lia]); nia.
Qed.

Definition half_inv (u v x M k : Z) : Prop :=
  0 <= x /\
  if u mod 2 =? 1 then
    if v mod 2 =? 1 then 2 * x <= (3 + k) * M
    else 2 * x <= k * M
  else 2^63 * x <= (2^63 + k - 2) * M.

Definition xy_inv (a_ b_ x y M k : Z) : Prop :=
  b_ = 0 \/ (half_inv b_ a_ x M k /\ half_inv a_ b_ y M k).

Lemma xy_inv_init (a_ b_ M : Z) : M > 1 -> a_ mod 2 = 1 -> xy_inv a_ b_ 1 0 M 0.
Proof.
  intros HM Ha; destruct (Z.eq_dec b_ 0) as [-> | Hb]; [left; reflexivity | right].
  unfold half_inv; rewrite Ha; cbn [Z.eqb Pos.eqb].
  destruct (b_ mod 2 =? 1); split; split; lia.
Qed.

Lemma xy_inv_swap (a_ b_ x y M k : Z) :
  a_ <> 0 -> b_ <> 0 -> xy_inv a_ b_ x y M k -> xy_inv b_ a_ y x M k.
Proof. unfold xy_inv; tauto. Qed.

Lemma half_inv_bound (u v x M k : Z) :
  0 <= M -> 0 <= k -> half_inv u v x M k -> 2 * x <= (3 + k) * M.
Proof. unfold half_inv; destruct (u mod 2 =? 1), (v mod 2 =? 1); nia. Qed.

Lemma xy_inv_sum_lt_320 (a_ b_ x y M k : Z) :
  b_ <> 0 -> 0 <= M < 2^256 -> 0 <= k <= 512 ->
  xy_inv a_ b_ x y M k ->
  x + y < 2^320.
Proof.
  intros Hb0 HM Hk [-> | [Hx Hy]]; [contradiction |].
  pose proof (half_inv_bound b_ a_ x M k ltac:(lia) ltac:(lia) Hx).
  pose proof (half_inv_bound a_ b_ y M k ltac:(lia) ltac:(lia) Hy); nia.
Qed.

Lemma xy_inv_step (a_ b_ a' b' x y x' y' s_a s_b M k k' : Z) :
  1 < M -> 1 <= a_ -> 1 <= b_ -> a_ <= b_ ->
  0 <= a' -> 0 <= b' -> 0 <= x' -> 0 <= y' ->
  0 <= k <= 512 ->
  k + (Z_size a_ + Z_size b_) = k' + (Z_size a' + Z_size b') ->
  (a_ mod 2 = 1 \/ b_ mod 2 = 1) ->
  xy_inv a_ b_ x y M k ->
  s_a = Z.min (lctz 64 a_) 63 -> a' * 2^s_a = a_ ->
  y' * 2^s_a <= y + (2^s_a - 1) * M ->
  s_b = Z.min (lctz 64 (b_ - a_)) 63 -> b' * 2^s_b = b_ - a_ ->
  x' * 2^s_b <= x + y + (2^s_b - 1) * M ->
  1 <= a' <= a_ /\ 0 <= b' < b_ /\ k <= k' /\
  Z.gcd a' b' = Z.gcd a_ b_ /\
  (b' <> 0 -> (a' mod 2 = 1 \/ b' mod 2 = 1) /\ xy_inv a' b' x' y' M k').
Proof.
  intros HM Ha_ Hb_ Hle Ha'0 Hb'0 Hx'0 Hy'0 Hk Hkeq Hodd Hinv
         Hsa Ha' Hy' Hsb Hb' Hx'.
  pose proof (Z_size_nonneg a_); pose proof (Z_size_nonneg b_).
  assert (Hsa0 : 0 <= s_a) by (subst s_a; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hsb0 : 0 <= s_b) by (subst s_b; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hpow0 : 1 <= 2^s_a /\ 1 <= 2^s_b)
    by (rewrite <- (Z.pow_0_r 2); split; apply Z.pow_le_mono_r; lia).
  assert (Ha'r : 1 <= a' <= a_) by nia.
  assert (Hb'r : 0 <= b' < b_) by nia.
  assert (Hsza' : Z_size a' + s_a = Z_size a_) by (rewrite <- Ha', Z_size_mul_pow2 by lia; ring).
  assert (Hszb' : Z_size b' <= Z_size b_) by
    (transitivity (Z_size (b_ - a_)); [rewrite <- Hb'; destruct (Z.eq_dec b' 0) as [->|]; [rewrite Z.mul_0_l; lia | rewrite Z_size_mul_pow2; lia] | apply Z_size_sub; lia]).
  assert (Hkle : k + s_a <= k') by lia.
  destruct Hinv as [Hb0 | [[Hx0 Hx] [Hy0 Hy]]]; [lia |].
  destruct (mod2_cases a_) as [Ha2 | Ha2], (mod2_cases b_) as [Hb2 | Hb2]; [lia | | |].
  { (* Case EO: a_ mod 2 = 0, b_ mod 2 = 1 *)
    assert (Hb'odd : (b_ - a_) mod 2 = 1) by (rewrite <- Zminus_mod_idemp_r, Ha2, Z.sub_0_r; exact Hb2).
    assert (Hsb_eq0 : s_b = 0) by (subst s_b; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsb_eq0, Z.pow_0_r, Z.mul_1_r in *; subst b'.
    assert (Hsa1 : 1 <= s_a) by (subst s_a; apply Z.min_glb; [apply lctz_ge_1 |]; lia).
    assert (Hpow_sa : 2 <= 2^s_a) by (transitivity (2^1); [lia | apply Z.pow_le_mono_r; lia]).
    assert (Hgcd : Z.gcd a' (b_ - a_) = Z.gcd a_ b_)
      by (rewrite <- (gcd_pow2_l s_a a' (b_ - a_)), Ha', Z.gcd_sub_diag_r by lia; reflexivity).
    rewrite Ha2, Hb2 in *; cbn [Z.eqb Pos.eqb] in *.
    repeat split; try lia; right; unfold half_inv; rewrite Hb'odd; cbn [Z.eqb Pos.eqb].
    destruct (mod2_cases a') as [Ha'2 | Ha'2]; rewrite Ha'2; cbn [Z.eqb Pos.eqb].
    { assert (Hsa63 : s_a = 63) by (subst s_a; eapply lctz_even_min63; eauto; lia).
      rewrite Hsa63 in *; clear - HM Hk Hkle Hx0 Hx Hy0 Hy Hx' Hy' Hx'0 Hy'0; repeat split; nia. }
    { clear - HM Hk Hsa1 Hkle Hx0 Hx Hy0 Hy Hx' Hy' Hx'0 Hy'0 Hpow_sa; repeat split; nia. }
  }
  { (* Case OE: a_ mod 2 = 1, b_ mod 2 = 0 *)
    assert (Hb'odd : (b_ - a_) mod 2 = 1) by (rewrite <- Zminus_mod_idemp_l, Hb2, Z.sub_0_l, Z_mod_nz_opp_full, Ha2 by lia; reflexivity).
    assert (Hsa_eq0 : s_a = 0) by (subst s_a; rewrite lctz_odd by lia; reflexivity).
    assert (Hsb_eq0 : s_b = 0) by (subst s_b; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsa_eq0, Hsb_eq0, Z.pow_0_r, !Z.mul_1_r in *; subst a' b'.
    assert (Hgcd : Z.gcd a_ (b_ - a_) = Z.gcd a_ b_) by apply Z.gcd_sub_diag_r.
    rewrite Ha2, Hb2 in *; cbn [Z.eqb Pos.eqb] in *.
    repeat split; try lia; right; unfold half_inv; rewrite Ha2, Hb'odd; cbn [Z.eqb Pos.eqb];
      clear - HM Hk Hkle Hx0 Hx Hy0 Hy Hx' Hy' Hx'0 Hy'0; repeat split; nia.
  }
  { (* Case OO: a_ mod 2 = 1, b_ mod 2 = 1 *)
    assert (Hsa_eq0 : s_a = 0) by (subst s_a; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsa_eq0, Z.pow_0_r, !Z.mul_1_r in *; subst a'.
    assert (Hgcd : Z.gcd a_ b' = Z.gcd a_ b_)
      by (rewrite <- (gcd_pow2_r s_b a_ b'), Hb', Z.gcd_sub_diag_r by lia; reflexivity).
    rewrite Ha2, Hb2 in *; cbn [Z.eqb Pos.eqb] in *.
    repeat split; try lia; right.
    assert (Hsb1 : 1 <= s_b) by (subst s_b; apply Z.min_glb; [apply lctz_ge_1; [lia | nia | rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Ha2, Hb2; reflexivity] | lia]).
    assert (Hkle_b : k + s_b <= k') by (assert (Z_size b' + s_b <= Z_size b_) by (rewrite <- Z_size_mul_pow2, Hb' by lia; apply Z_size_sub; lia); lia).
    unfold half_inv; rewrite Ha2; cbn [Z.eqb Pos.eqb].
    destruct (mod2_cases b') as [Hb'2 | Hb'2]; rewrite Hb'2; cbn [Z.eqb Pos.eqb].
    { assert (Hsb63 : s_b = 63) by (subst s_b; eapply lctz_even_min63; eauto; nia).
      rewrite Hsb63 in *; clear - HM Hk Hkle_b Hx0 Hx Hy0 Hy Hx' Hy' Hx'0 Hy'0; repeat split; nia. }
    { pose proof (pow2_bound_OO s_b k ltac:(lia) Hsb1) as Hpow_oo.
      replace (2 ^ (s_b + 1)) with (2 * 2 ^ s_b) in Hpow_oo by (rewrite Z.pow_add_r by lia; lia).
      destruct Hpow0 as [_ Hpow_sb]; split;
        [split; [lia | clear - HM Hk Hsb1 Hkle_b Hx Hy Hx' Hpow_oo Hpow_sb; nia]
        | clear - HM Hk Hsb1 Hkle_b Hy Hy' Hy'0 Hpow_sb; split; nia]. }
  }
Qed.

Opaque xy_inv.

(** Complete loop-body invariant preservation for BOTH branches (a_ <=? b_ = true and false) *)
Lemma helper_loop_step_complete
  (a0 b0 M a_ b_ x y a_mid b_mid x_mid y_mid a' b' x' y' s_a s_b : Z) :
  M > 1 -> M mod 2 = 1 ->
  (Z_size a0 <= 256 /\ Z_size b0 <= 256) ->
  1 <= a_ -> a_ <= M ->
  (1 <= b_ < M /\ 0 <= a' /\ 0 <= b' /\ 0 <= x' /\ 0 <= y') ->
  (a_ mod 2 = 1 \/ b_ mod 2 = 1) ->
  xy_inv a_ b_ x y M ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_)) ->
  Z.gcd a_ b_ = Z.gcd a0 b0 ->
  a_ mod M = (- (y * b0)) mod M ->
  b_ mod M = (x * b0) mod M ->
  (Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_) >= 0 ->
  (if a_ <=? b_ then a_mid = a_ /\ b_mid = b_ - a_ /\ y_mid = y /\ x_mid = x + y
   else b_mid = b_ /\ a_mid = a_ - b_ /\ x_mid = x /\ y_mid = x + y) ->
  s_b = Z.min (lctz 64 b_mid) 63 -> b' * 2^s_b = b_mid ->
  x' * 2^s_b mod M = x_mid mod M -> x' * 2^s_b <= x_mid + (2^s_b - 1) * M ->
  s_a = Z.min (lctz 64 a_mid) 63 -> a' * 2^s_a = a_mid ->
  y' * 2^s_a mod M = y_mid mod M -> y' * 2^s_a <= y_mid + (2^s_a - 1) * M ->
  1 <= a' /\ a' <= M /\ 0 <= b' /\ b' < M /\
  (a' mod 2 = 1 \/ b' mod 2 = 1) /\
  xy_inv a' b' x' y' M ((Z_size a0 + Z_size b0) - (Z_size a' + Z_size b')) /\
  Z.gcd a' b' = Z.gcd a0 b0 /\
  a' mod M = (- (y' * b0)) mod M /\
  b' mod M = (x' * b0) mod M /\
  (Z_size a0 + Z_size b0) - (Z_size a' + Z_size b') >= 0 /\
  0 <= a' + b' /\ a' + b' < a_ + b_.
Proof.
  intros HM1 HModd Hsz0 Ha_1 Ha_2 (Hb_ & Ha'0 & Hb'0 & Hx'0 & Hy'0) Hodd Hinv Hgcd Hca Hcb Hk0 Hsub
         Hsb Hb' Hx'm Hx'b Hsa Ha' Hy'm Hy'b.
  pose proof (Z_size_nonneg a_); pose proof (Z_size_nonneg b_).
  assert (Hsa0 : 0 <= s_a) by (subst s_a; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hsb0 : 0 <= s_b) by (subst s_b; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hca_neg : a_mid mod M = (y_mid * (- b0)) mod M /\ b_mid mod M = (x_mid * b0) mod M).
  { destruct (a_ <=? b_); destruct Hsub as (-> & -> & -> & ->); split;
    Z.push_pull_mod; Z.push_mod; rewrite ?Hca, ?Hcb; Z.push_pull_mod; f_equal; ring. }
  destruct Hca_neg as [Hca_mid Hcb_mid].
  assert (Hcb' : b' mod M = (x' * b0) mod M) by (eapply shrtz_cong with (s := s_b); eauto; lia).
  assert (Hca' : a' mod M = (- (y' * b0)) mod M)
    by (replace (- (y' * b0)) with (y' * (- b0)) by ring; eapply shrtz_cong with (s := s_a); eauto; lia).
  destruct (a_ <=? b_) eqn:Ecmp; [rewrite Z.leb_le in Ecmp | rewrite Z.leb_gt in Ecmp];
    destruct Hsub as (-> & -> & -> & ->).
  { (* Branch 1: a_ <= b_ *)
    destruct (xy_inv_step a_ b_ a' b' x y x' y' s_a s_b M
                ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_))
                ((Z_size a0 + Z_size b0) - (Z_size a' + Z_size b')))
      as (Ha'r & Hb'r & Hkle & Hgcd' & Hrest); try assumption; try lia.
    destruct (Z.eq_dec b' 0) as [-> | Hb'nz].
    { assert (b_ = a_) by (rewrite Z.mul_0_l in Hb'; lia).
      assert (a_ mod 2 = 1) by (subst b_; tauto).
      assert (Hs0 : s_a = 0) by (subst s_a; rewrite lctz_odd by lia; reflexivity).
      rewrite Hs0, Z.pow_0_r, Z.mul_1_r in Ha'; subst a'.
      assert (xy_inv a_ 0 x' y' M (Z_size a0 + Z_size b0 - (Z_size a_ + Z_size 0))) by (left; reflexivity).
      repeat split; try assumption; try lia; try tauto; try congruence. }
    { destruct (Hrest Hb'nz) as [Hodd' Hinv']; repeat split; try assumption; try lia; try congruence. }
  }
  { (* Branch 2: b_ < a_ -> apply xy_inv_step to (b_, a_) via xy_inv_swap *)
    assert (Hinv_sw : xy_inv b_ a_ y x M ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_)))
      by (apply xy_inv_swap; lia || tauto).
    destruct (xy_inv_step b_ a_ b' a' y x y' x' s_b s_a M
                ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_))
                ((Z_size a0 + Z_size b0) - (Z_size a' + Z_size b')))
      as (Hb'r & Ha'r & Hkle & Hgcd' & Hrest); try assumption; try lia; try tauto.
    assert (Ha'nz : a' <> 0) by (intros ->; rewrite Z.mul_0_l in Ha'; lia).
    destruct (Hrest Ha'nz) as [Hodd' Hinv'].
    repeat split; try assumption; try lia; try tauto.
    { apply xy_inv_swap; try lia; tauto. }
    { rewrite Z.gcd_comm, Hgcd', Z.gcd_comm; exact Hgcd. }
  }
Qed.

Lemma helper_loop_ok : program_logic_goal_for_function! helper_loop.
Proof.
    repeat (straightline || straightline_call); intuition try ecancel_assumption.
    refine ((Loops.tailrec
        (HList.polymorphic_list.cons _  (* a *)
                (HList.polymorphic_list.cons _  (* b *)
                (HList.polymorphic_list.cons _  (* x *)
                (HList.polymorphic_list.cons _  (* y *)
                (HList.polymorphic_list.cons _  (* R *)
                HList.polymorphic_list.nil)))))
        (["p_a"; "p_b"; "p_x"; "p_y"; "p_m"; "inv_m"; "cmp"])
    )
        (
            fun v a_ b_ x y R t m p_a p_b p_x p_y p_m inv_m_ cmp => PrimitivePair.pair.mk
                (
                    v = (eval a_) + (eval b_) /\
                    m=* array p_a a_ ⋆ array p_b b_ ⋆ array p_x x ⋆ array p_y y ⋆ array p_m MOD ⋆ R /\
                    (* length invariants *)
                    length a_ = 4%nat /\ length b_ = 4%nat /\ length x = 5%nat /\ length y = 5%nat /\
                    (* Comparison condition *)
                    (if ((eval b_) =? 0) then cmp = bits.of_Z _ 0 else (cmp <> (bits.of_Z _ 0))) /\
                    (* a,b range invariants *)
                    1 <= eval a_ <= eval MOD /\ 0 <= eval b_ < eval MOD /\
                    (* Parity requirement *)
                    ((eval a_) mod 2 = 1 \/ (eval b_) mod 2 = 1) /\
                    (* x, y range invariants *)
                    xy_inv (eval a_) (eval b_) (eval x) (eval y) (eval MOD)
                           ((Z_size (eval a) + Z_size (eval b)) - (Z_size (eval a_) + Z_size (eval b_))) /\
                    (* Gcd invariant *)
                    Z.gcd (eval a_) (eval b_) = Z.gcd (eval a) (eval b) /\
                    (* inv_m invariant *)
                    inv_m_ = inv_m /\
                    (* Congruence invariants *)
                    (eval a_) mod (eval MOD) = (-((eval y) * (eval b))) mod (eval MOD) /\
                    (eval b_) mod (eval MOD) = ((eval x) * (eval b)) mod (eval MOD) /\
                    ((Z_size (eval a) + Z_size (eval b)) - (Z_size (eval a_) + Z_size (eval b_)) >= 0)
                )
                (
                    fun T M P_A P_B P_X P_Y P_M INV_M CMP => T = t /\ exists (A B X Y : list word),
                        M =* array P_A A ⋆ array P_B B ⋆ array P_X X ⋆ array P_Y Y ⋆ array P_M MOD ⋆ R /\
                        P_A = p_a /\ P_B = p_b /\ P_X = p_x /\ P_Y = p_y /\ P_M = p_m /\
                        length A = 4%nat /\ length B = 4%nat /\ length X = 5%nat /\ length Y = 5%nat /\
                        eval A = Z.gcd (eval a) (eval b) /\
                        eval B = 0 /\
                        (eval A) mod (eval MOD) = (-((eval Y) * (eval b)) mod (eval MOD))
                )
        )
        (fun n m => 0 <= n < m)
        _ _ _ _ _ _ _ _ _ _
    ); Loops.loop_simpl.
    { repeat straightline. }
    { eapply Z.lt_wf. }
    { repeat straightline; intuition try ecancel_assumption;
      repeat match goal with H : fold_right _ 0 _ = _ |- _ => progress rewrite H end; try ZnWords.
      { rewrite Z.sub_diag; apply xy_inv_init; lia. }
      { Z.push_pull_mod. rewrite Z.mul_0_l, Z.sub_0_r, Z_mod_same, Z.mod_small by lia; eauto. }
      { Z.push_pull_mod. rewrite Z.mul_1_l. eauto. }
    }
    {
      intros; repeat (straightline || straightline_call).
      1,2,3,4: ssplit; try ecancel_assumption; eauto.
      all:
        destruct (eval x2 =? 0) eqn:Hx20;
            try solve [exfalso; match goal with H1 : context[Zmod.unsigned ?c], H2 : context[?c = _] |- _ => revert H1 H2; clear; intros; ZnWords end].
      all: assert (Hsz : Z_size (eval a) <= 256 /\ Z_size (eval b) <= 256)
        by (split; (apply Z_size_le; [clear; lia | keep_length_equations; bigZnWords])).
      {
        rewrite ?Z.eqb_neq in Hx20.
        assert (Hmod : 0 <= eval MOD < 2^256) by (keep_length_equations; bigZnWords).
        assert (Hk_range : 0 <= (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2)) <= 512)
          by (match goal with Hk0 : _ - _ >= 0 |- _ => clear - Hsz Hk0 end;
              pose proof (Z_size_nonneg (eval x1)); pose proof (Z_size_nonneg (eval x2)); lia).
        eapply xy_inv_sum_lt_320 with (a_ := eval x1) (b_ := eval x2) (M := eval MOD)
          (k := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2)));
          eassumption.
      }
      {
        clear_old_memory_hyps.
        subst v.
        cbv [x21 x18] in *; clear x18 x21.
        rewrite ?Zmod.of_Z_0, ?Zmod.unsigned_0, ?Z.eqb_eq, ?Z.eqb_neq in *.
        assert (Hbnds : 1 <= eval x2 < eval MOD /\ 0 <= eval x19 /\ 0 <= eval x16 /\ 0 <= eval x17 /\ 0 <= eval x20)
          by (repeat split;
              try (match goal with Hb1 : 0 <= fold_right _ _ x2, Hb2 : fold_right _ _ x2 < _ |- _ => clear - Hb1 Hb2 Hx20; lia end);
              keep_length_equations; bigZnWords).
        assert (Hsub : if eval x1 <=? eval x2
                       then eval x11 = eval x1 /\ eval x13 = eval x2 - eval x1 /\ eval x15 = eval x4 /\ eval x14 = eval x3 + eval x4
                       else eval x13 = eval x2 /\ eval x11 = eval x1 - eval x2 /\ eval x14 = eval x3 /\ eval x15 = eval x3 + eval x4)
          by (match goal with H : if _ <=? _ then _ else _ |- _ =>
                destruct (eval x1 <=? eval x2); destruct H as (-> & ? & -> & ?); repeat split; assumption end).
        destruct (helper_loop_step_complete
                    (eval a) (eval b) (eval MOD) (eval x1) (eval x2) (eval x3) (eval x4)
                    (eval x11) (eval x13) (eval x14) (eval x15)
                    (eval x19) (eval x16) (eval x17) (eval x20)
                    (Z.min (lctz 64 (eval x11)) 63) (Z.min (lctz 64 (eval x13)) 63))
          as (Ha'1 & Ha'2 & Hb'1 & Hb'2 & Hodd' & Hinv' & Hgcd' & Hca' & Hcb' & Hk' & Hlt'1 & Hlt'2);
          [ try reflexivity; try eassumption .. |].
        eexists x19, x16, x17, x20, x5, _;
        ssplit; repeat straightline;
        cbv [Markers.right Markers.split]; repeat (intros; try assumption; split);
        try ecancel_assumption; try assumption; try reflexivity.
      }
      {
        eexists _,_,_,_; ssplit; try ecancel_assumption; eauto; try lia.
        rewrite Z.eqb_eq, Hx20, Z.gcd_0_r_nonneg in * by bigZnWords.
        eauto.
      }
    }
    {
        repeat straightline. eexists _,_,_,_; intuition try ecancel_assumption.
    }
Qed.

Lemma beeu_modinv_ok : program_logic_goal_for_function! beeu_modinv.
Proof.
    repeat straightline.
    alloc_array a0 stack.
    alloc_array a1 stack0.
    alloc_array a2 stack1.
    alloc_array a3 stack2.
    alloc_array a4 stack3.
    repeat (straightline || straightline_call);
    intuition try ecancel_assumption.
    eexists; ssplit; try intros br;
    repeat straightline.
    {
        straightline_call; intuition try ecancel_assumption; try ZnWords.
        repeat (straightline || straightline_call); intuition try ecancel_assumption.
        {
            assert ((eval x) < 2^256) by (lists_into_elements; cbv [eval] in *; ZnWords).
            assert ((eval x7) < eval x).
            {
                match goal with H : fold_right _ _ x7 = _ |- _ => rewrite H end. eapply Z.mod_pos_bound. ZnWords.
            }
            ZnWords.
        }
        dealloc_array a0 x2.
        dealloc_array a1 x3.
        dealloc_array a2 x.
        dealloc_array a3 x4.
        dealloc_array a4 x7.
        repeat straightline.
        eexists _; intuition try ecancel_assumption.
        cbv [c] in *.
        match goal with Hgcd : fold_right _ _ x2 = Z.gcd _ _ |- _ => rewrite Z.gcd_comm, <- Hgcd end.
        rewrite bits.unsigned_1 in * by lia.
        destruct (eval x2 =? 1) eqn: Hx2.
        {
            rewrite Z.eqb_eq in *.
            assert (Hx8 : Zmod.unsigned x8 = 0) by (lists_into_elements; cbv [eval] in *; ZnWords).
            destruct (modinv_from_bezout (eval MOD) (eval a) (eval x5) (eval x9)) as [? ?];
              [lia | congruence | match goal with H : fold_right _ _ x = _ |- _ => rewrite H in *; lia end |].
            intuition lia.
        }
        {
            match goal with H : _ |- _ => eapply word.eqb_ne in H; rewrite H in *; contradiction end.
        }
    }
    {
        dealloc_array a0 x2.
        dealloc_array a1 x3.
        dealloc_array a2 x.
        dealloc_array a3 x4.
        dealloc_array a4 x5.
        repeat straightline.
        eexists; intuition try ecancel_assumption.
        cbv [c] in *.
        match goal with Hgcd : fold_right _ _ x2 = Z.gcd _ _ |- _ => rewrite Z.gcd_comm, <- Hgcd end.
        destruct (eval x2 =? 1) eqn: Hx2; eauto.
        (* Contradiction *)
        rewrite Z.eqb_eq, Hx2, bits.unsigned_1 in * by lia.
        match goal with H : _ |- _ => eapply Zmod.eqb_eq in H; rewrite H in *; discriminate end.
    }
Qed.

Definition beeu_modinv_funcs :=
    &[,
        beeu_modinv;
        beeu_normalize;
        helper_loop;
        helper_subtract;
        u256_sub;
        u256_dec;
        u256_to_u320;
        u256_set;
        u320_set_const;
        u256_comp;
        u320_sub;
        beeu_shrtz;
        u320_muladd;
        u320_shr;
        u256_shr;
        br_ctz;
        br_full_add;
        br_full_mul;
        br_full_sub;
        u320_set;
        u320_add].

Lemma link_beeu_modinv : spec_of_beeu_modinv (Interface.map.of_list beeu_modinv_funcs).
Proof.
    apply beeu_modinv_ok;
    repeat (
        apply u256_set_ok ||
        apply u256_to_u320_ok ||
        apply u320_set_ok ||
        apply u320_set_const_ok ||
        apply helper_loop_ok ||
        apply u256_comp_ok ||
        apply beeu_shrtz_ok ||
        apply u256_sub'_ok ||
        apply full_sub_ok ||
        apply u320_muladd_correct ||
        apply full_mul_ok ||
        apply full_add_ok ||
        apply u256_shr_correct ||
        apply helper_subtract_ok ||
        apply u320_shr_correct ||
        apply u256_sub_ok ||
        apply u256_dec_ok ||
        apply u320_add_correct ||
        apply br_ctz_ok ||
        apply beeu_normalize_ok ||
        apply u320_sub_correct ||
        trivial
        ).
Qed.

