(* Verification of the 256-bit Binary Extended Euclidean modular inverse (beeu_modinv).
 * [loop_inv_step] shows that one iteration of [helper_loop] preserves [loop_inv];
 * [beeu_modinv_ok] turns a = gcd M b0 = 1 into the inverse via [modinv_from_bezout]. *)

From Coq Require Import BinInt String List InitialRing ZArith Lia.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords ArrayCasts Syntax.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2Examples.full_sub bedrock2Examples.full_add bedrock2Examples.u320_add bedrock2Examples.full_mul.
From coqutil Require Import Tactics.Tactics WithBaseName Z.CountTrailingZeros.
Require Import coqutil.Z.PushPullMod coqutil.Word.Properties.

Require Import u320_muladd beeu_normalize u320_sub beeu_shrtz u320_shr u256_shr br_ctz.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Lemma Z_mod_mult' (a b : Z) : (a * b) mod a = 0.
Proof. rewrite Z.mul_comm; apply Z_mod_mult. Qed.

Local Lemma mod2_odd (a : Z) : a mod 2 = 1 -> Z.odd a = true.
Proof. intros H; rewrite Zodd_mod, H; reflexivity. Qed.

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


#[local] Ltac keep_length_equations :=
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

#[local] Ltac cmp_contradiction :=
  match goal with H1 : context[Zmod.unsigned ?c], H2 : context[?c = _] |- _ =>
    revert H1 H2; clear; intros; ZnWords end.

Local Lemma gcd_double_l (a b : Z) : Z.odd b = true -> Z.gcd (2 * a) b = Z.gcd a b.
Proof.
  intros H; destruct a as [| p | p], b as [| [q|q|] | [q|q|]]; try discriminate; try reflexivity;
  try rewrite <- Pos2Z.pos_xO; try rewrite <- Pos2Z.neg_xO;
  try rewrite !(Z.gcd_comm _ 1); try rewrite !(Z.gcd_comm _ (-1)); reflexivity.
Qed.

Local Lemma gcd_pow2_l (n a b : Z) : 0 <= n -> Z.odd b = true -> Z.gcd (a * 2 ^ n) b = Z.gcd a b.
Proof.
  intros Hn Hb; rewrite Z.mul_comm; pattern n; apply natlike_ind; [| | lia].
  { rewrite Z.pow_0_r, Z.mul_1_l; reflexivity. }
  { intros x Hx IH.
    rewrite Z.pow_succ_r, <- Z.mul_assoc, gcd_double_l by (lia || assumption); exact IH. }
Qed.

Local Lemma mod_mul_pow2_cancel (M a b n : Z) : 1 < M -> Z.odd M = true -> 0 <= n ->
  a * 2^n mod M = b * 2^n mod M -> a mod M = b mod M.
Proof.
  intros HM HMo Hn H; rewrite Z.cong_iff_0, Z.mod_divide in * by lia.
  apply (Z.gauss _ (2^n)); [rewrite Z.mul_sub_distr_l, !(Z.mul_comm (2^n)); exact H |].
  rewrite Z.gcd_comm, <- (Z.mul_1_l (2^n)), gcd_pow2_l, Z.gcd_1_l by (lia || assumption).
  reflexivity.
Qed.

Local Lemma pow2_bound (s k : Z) : 0 <= k -> 1 <= s -> 2 * 2 ^ s + 2 * k + 4 <= 2 ^ s * (3 + k + s).
Proof.
  intros; destruct (Z.eq_dec s 1) as [-> | ?]; [lia |].
  assert (4 <= 2 ^ s) by (apply (Z.pow_le_mono_r 2 2); lia); nia.
Qed.

Section Loop.
  Context {M b0 : Z} (HM : 1 < M < 2^256) (HMo : Z.odd M = true) (Hb0 : 0 <= b0 < M).

  Local Definition shrtz_rel (s v u v' u' : Z) : Prop :=
    v' * 2^s = v /\ s = Z.min (lctz 64 v) 63 /\
    u' * 2^s mod M = u mod M /\ u' * 2^s <= u + (2^s - 1) * M /\ 0 <= v' /\ 0 <= u'.

  Local Lemma shrtz_s_range {s v u v' u'} : shrtz_rel s v u v' u' -> 0 <= s <= 63.
  Proof. intros (_ & -> & _); destruct v; cbv [lctz]; lia. Qed.

  Local Lemma shrtz_v_range {s v u v' u'} : shrtz_rel s v u v' u' ->
    0 <= v' <= v /\ (0 < v -> 0 < v').
  Proof.
    intros H; pose proof (shrtz_s_range H); destruct H as (Hv' & _ & _ & _ & Hv'0 & _).
    assert (1 <= 2^s) by (apply (Z.pow_le_mono_r 2 0); lia); split; [nia | intros; nia].
  Qed.

  Local Lemma shrtz_odd {s v u v' u'} : shrtz_rel s v u v' u' -> Z.odd v = true -> s = 0 /\ v' = v.
  Proof.
    intros H Hodd; pose proof (shrtz_v_range H); destruct H as (Hv' & Hs & _).
    assert (s = 0) as ->
      by (subst s; destruct v as [| [p|p|] | p]; cbn in *; try discriminate; lia).
    rewrite Z.pow_0_r, Z.mul_1_r in Hv'; auto.
  Qed.

  Local Lemma shrtz_even {s v u v' u'} : shrtz_rel s v u v' u' -> Z.odd v = false -> 1 <= s.
  Proof.
    intros H Hev; pose proof (shrtz_v_range H); destruct H as (_ & Hs & _); subst s.
    destruct v as [| [p|p|] | p]; cbn in *; try discriminate; lia.
  Qed.

  Local Lemma shrtz_even_s63 {s v u v' u'} : shrtz_rel s v u v' u' -> Z.odd v' = false -> s = 63.
  Proof.
    intros H Hev; pose proof (shrtz_s_range H); pose proof (shrtz_v_range H).
    destruct H as (Hv' & Hs & _).
    destruct (Z.eq_dec s 63) as [| Hne]; [assumption | exfalso].
    destruct (Z.eq_dec v 0) as [-> | Hv0]; [cbv [lctz] in Hs; lia |].
    destruct (lctz_spec 64 v ltac:(lia)) as (k & Hk & Hvk).
    rewrite <- (Z.min_l (lctz 64 v) 63), <- Hs in Hvk by lia.
    assert (v' = k) as -> by (apply (Z.mul_reg_r _ _ (2^s)); [apply Z.pow_nonzero |]; lia).
    rewrite Zodd_mod, Hk in Hev; discriminate.
  Qed.

  Local Lemma shrtz_log2 {s v u v' u'} : shrtz_rel s v u v' u' -> 0 < v -> Z.log2 v' + s = Z.log2 v.
  Proof.
    intros H Hv; pose proof (shrtz_s_range H); pose proof (shrtz_v_range H).
    destruct H as (<- & _); rewrite Z.log2_mul_pow2; lia.
  Qed.

  Local Lemma shrtz_cong {s v u v' u' c} : shrtz_rel s v u v' u' ->
    v mod M = (u * c) mod M -> v' mod M = (u' * c) mod M.
  Proof.
    intros H Hcong; pose proof (shrtz_s_range H); destruct H as (Hv' & _ & Hu' & _).
    apply (mod_mul_pow2_cancel M _ _ s); [lia | assumption | lia |].
    rewrite Hv', Hcong, Z.mul_shuffle0; symmetry.
    rewrite <- Z.mul_mod_idemp_l, Hu', Z.mul_mod_idemp_l by lia; reflexivity.
  Qed.

  Local Definition sub_rel (a b x y a1 b1 x1 y1 : Z) : Prop :=
    if a <=? b then a1 = a /\ b1 = b - a /\ x1 = x + y /\ y1 = y
    else a1 = a - b /\ b1 = b /\ x1 = x /\ y1 = x + y.

  Local Lemma sub_cong {v1 u1 v2 u2 c} :
    v1 mod M = (u1 * c) mod M -> v2 mod M = (u2 * - c) mod M ->
    (v1 - v2) mod M = ((u1 + u2) * c) mod M.
  Proof. intros H1 H2; rewrite Zminus_mod, H1, H2, <- Zminus_mod; f_equal; ring. Qed.

  Local Definition odd_bound (k c : Z) : Prop := 0 <= c /\ 2 * c <= (3 + k) * M.
  Local Definition capped_bound : Z -> Prop := odd_bound 0.
  Local Definition banked_bound (k c : Z) : Prop := 0 <= c /\ 2 * c <= k * M.

  Local Definition coeff_inv (k a b x y : Z) : Prop :=
    match Z.odd a, Z.odd b with
    | true,  true  => odd_bound k x /\ odd_bound k y
    | true,  false => capped_bound x /\ banked_bound k y
    | false, true  => banked_bound k x /\ capped_bound y
    | false, false => False
    end.

  Local Lemma coeff_inv_swap {k a b x y} : coeff_inv k a b x y -> coeff_inv k b a y x.
  Proof. cbv [coeff_inv]; destruct (Z.odd a), (Z.odd b); tauto. Qed.

  Local Lemma coeff_inv_odd {k a b x y} : coeff_inv k a b x y -> Z.odd a = true \/ Z.odd b = true.
  Proof. cbv [coeff_inv]; destruct (Z.odd a), (Z.odd b); tauto. Qed.

  Local Lemma coeff_inv_sum {k a b x y} : coeff_inv k a b x y -> 0 <= k -> x + y <= (3 + k) * M.
  Proof.
    cbv [coeff_inv capped_bound odd_bound banked_bound].
    destruct (Z.odd a), (Z.odd b); intuition nia.
  Qed.

  Local Lemma coeff_inv_init : coeff_inv 0 M b0 1 0.
  Proof.
    cbv [coeff_inv capped_bound odd_bound banked_bound]; rewrite HMo.
    destruct (Z.odd b0); lia.
  Qed.

  Local Lemma odd_bound_mono {k k' c} : k <= k' -> odd_bound k c -> odd_bound k' c.
  Proof. cbv [odd_bound]; nia. Qed.

  Local Lemma shrtz_0_le {v u v' u'} : shrtz_rel 0 v u v' u' -> 0 <= u' <= u.
  Proof. intros (_ & _ & _ & H & _ & ?); rewrite Z.pow_0_r in H; lia. Qed.

  Local Lemma shrtz_odd_bound {k s v u v' u'} : shrtz_rel s v u v' u' ->
    0 <= k -> 1 <= s -> u <= (3 + k) * M -> odd_bound (k + s) u'.
  Proof.
    intros (_ & _ & _ & Hu' & _ & Hu'0) Hk Hs Hu.
    pose proof (pow2_bound s k Hk Hs); cbv [odd_bound]; nia.
  Qed.

  Local Lemma shrtz_capped_bound {k v u v' u'} : shrtz_rel 63 v u v' u' ->
    0 <= k <= 512 -> u <= (3 + k) * M -> capped_bound u'.
  Proof. intros (_ & _ & _ & Hu' & _ & Hu'0) Hk Hu; cbv [capped_bound odd_bound]; nia. Qed.

  Local Lemma coeff_inv_step {k k' a b x y a' b' x' y' s_a s_b} :
    coeff_inv k a b x y -> shrtz_rel s_a a y a' y' -> shrtz_rel s_b (b - a) (x + y) b' x' ->
    1 <= a < b -> 0 <= k <= 512 -> k + s_a + s_b <= k' ->
    coeff_inv k' a' b' x' y'.
  Proof.
    intros Hinv Ha Hb Hab Hk Hk'.
    pose proof (coeff_inv_sum Hinv ltac:(lia)) as Hsum.
    pose proof (shrtz_s_range Ha); pose proof (shrtz_s_range Hb).
    cbv [coeff_inv] in Hinv |- *.
    destruct (Z.odd a) eqn:Ea, (Z.odd b) eqn:Eb; [| | | contradiction]; destruct Hinv as [Hx Hy];
      pose proof (Z.odd_sub b a) as Hd; rewrite Ea, Eb in Hd; cbn [xorb] in Hd.
    { destruct (shrtz_odd Ha Ea) as [-> ->]; apply shrtz_0_le in Ha.
      pose proof (shrtz_even Hb Hd).
      rewrite Ea; destruct (Z.odd b') eqn:Eb'; cbn beta iota.
      { split.
        { apply (odd_bound_mono (k := k + s_b)); [lia |]; apply (shrtz_odd_bound Hb); lia. }
        { apply (odd_bound_mono (k := k)); [lia |]; cbv [odd_bound] in *; lia. } }
      { pose proof (shrtz_even_s63 Hb Eb'); subst s_b; split.
        { apply (shrtz_capped_bound (k := k) Hb); lia. }
        { cbv [odd_bound banked_bound] in *; nia. } } }
    { destruct (shrtz_odd Ha Ea) as [-> ->]; apply shrtz_0_le in Ha.
      destruct (shrtz_odd Hb Hd) as [-> ->]; apply shrtz_0_le in Hb.
      rewrite Ea, Hd; cbn beta iota.
      cbv [odd_bound capped_bound banked_bound] in *; split; nia. }
    { destruct (shrtz_odd Hb Hd) as [-> ->]; apply shrtz_0_le in Hb.
      pose proof (shrtz_even Ha Ea).
      rewrite Hd; destruct (Z.odd a') eqn:Ea'; cbn beta iota.
      { split.
        { cbv [odd_bound capped_bound banked_bound] in *; nia. }
        { apply (odd_bound_mono (k := k + s_a)); [lia |].
          apply (shrtz_odd_bound Ha); cbv [banked_bound] in Hx; lia. } }
      { pose proof (shrtz_even_s63 Ha Ea'); subst s_a; split.
        { cbv [odd_bound capped_bound banked_bound] in *; nia. }
        { apply (shrtz_capped_bound (k := k) Ha); cbv [banked_bound] in Hx; lia. } } }
  Qed.

  Local Lemma gcd_step {a b x y a' b' x' y' s_a s_b} :
    shrtz_rel s_a a y a' y' -> shrtz_rel s_b (b - a) (x + y) b' x' ->
    1 <= a <= b -> (Z.odd a = true \/ Z.odd b = true) -> Z.gcd a' b' = Z.gcd a b.
  Proof.
    intros Ha Hb Hab Hodd; pose proof (shrtz_s_range Ha); pose proof (shrtz_s_range Hb).
    rewrite <- (Z.gcd_sub_diag_r a b).
    destruct (Z.odd a) eqn:Ea.
    { destruct (shrtz_odd Ha Ea) as [_ ->]; destruct Hb as (<- & _).
      rewrite !(Z.gcd_comm a), gcd_pow2_l by (lia || assumption); reflexivity. }
    { assert (Hd : Z.odd (b - a) = true)
        by (rewrite Z.odd_sub, Ea; destruct Hodd as [? | ->]; [discriminate | reflexivity]).
      destruct (shrtz_odd Hb Hd) as [_ ->]; destruct Ha as (<- & _).
      rewrite gcd_pow2_l by (lia || assumption); reflexivity. }
  Qed.

  Local Lemma log2_step {a b x y a' b' x' y' s_a s_b} :
    shrtz_rel s_a a y a' y' -> shrtz_rel s_b (b - a) (x + y) b' x' -> 1 <= a <= b ->
    Z.log2 a' + s_a = Z.log2 a /\ Z.log2 b' <= Z.log2 b /\ (a < b -> Z.log2 b' + s_b <= Z.log2 b).
  Proof.
    intros Ha Hb Hab; pose proof (shrtz_v_range Hb).
    ssplit; [apply (shrtz_log2 Ha); lia | apply Z.log2_le_mono; lia |].
    intros; rewrite (shrtz_log2 Hb) by lia; apply Z.log2_le_mono; lia.
  Qed.

  Local Definition bits_removed (a b : Z) : Z := (Z.log2 M + Z.log2 b0) - (Z.log2 a + Z.log2 b).

  Local Definition loop_inv (a b x y : Z) : Prop :=
    1 <= a <= M /\ 0 <= b < M /\ Z.gcd a b = Z.gcd M b0 /\
    a mod M = (- (y * b0)) mod M /\ b mod M = (x * b0) mod M /\
    0 <= bits_removed a b /\ (b <> 0 -> coeff_inv (bits_removed a b) a b x y).

  Local Lemma bits_removed_le_512 {a b} : bits_removed a b <= 512.
  Proof.
    cbv [bits_removed]; pose proof (proj1 (Z.log2_lt_pow2 M 256 ltac:(lia)) ltac:(lia)).
    pose proof (Z.log2_le_mono b0 M ltac:(lia)).
    pose proof (Z.log2_nonneg a); pose proof (Z.log2_nonneg b); lia.
  Qed.

  Local Lemma loop_inv_init : loop_inv M b0 1 0.
  Proof using HM HMo Hb0.
    cbv [loop_inv bits_removed]; ssplit; try lia; try reflexivity.
    { rewrite Z.mul_0_l, Z_mod_same_full; reflexivity. }
    { rewrite Z.mul_1_l; reflexivity. }
    { intros _; rewrite Z.sub_diag; apply coeff_inv_init. }
  Qed.

  Local Lemma loop_inv_fits {a b x y} : loop_inv a b x y -> b <> 0 -> x + y < 2^320.
  Proof using HM HMo Hb0.
    intros (_ & _ & _ & _ & _ & Hk & Hc) Hb; specialize (Hc Hb).
    pose proof (@bits_removed_le_512 a b); pose proof (coeff_inv_sum Hc Hk); nia.
  Qed.

  Local Lemma loop_inv_exit {a x y} : loop_inv a 0 x y ->
    a = Z.gcd M b0 /\ a mod M = (- (y * b0)) mod M.
  Proof using HM HMo Hb0.
    intros (Ha & _ & Hg & Hca & _); rewrite Z.gcd_0_r_nonneg in Hg by lia; auto.
  Qed.

  Local Lemma loop_inv_step {a b x y a1 b1 x1 y1 a' b' x' y' s_a s_b} :
    loop_inv a b x y -> sub_rel a b x y a1 b1 x1 y1 ->
    shrtz_rel s_a a1 y1 a' y' -> shrtz_rel s_b b1 x1 b' x' -> b <> 0 ->
    loop_inv a' b' x' y' /\ 0 <= a' + b' < a + b.
  Proof using HM HMo Hb0.
    intros (Ha & Hb & Hgcd & Hca & Hcb & Hk & Hcoeff) Hsub Hsa Hsb Hbnz.
    specialize (Hcoeff Hbnz); pose proof (coeff_inv_odd Hcoeff) as Hodd.
    pose proof (@bits_removed_le_512 a b).
    pose proof (shrtz_s_range Hsa); pose proof (shrtz_s_range Hsb).
    rewrite <- Z.mul_opp_r in Hca.
    cbv [sub_rel] in Hsub; destruct (a <=? b) eqn:Hle;
      [rewrite Z.leb_le in Hle | rewrite Z.leb_gt in Hle]; destruct Hsub as (-> & -> & -> & ->).
    { destruct (log2_step Hsa Hsb ltac:(lia)) as (Hla & Hlb & Hlt).
      pose proof (shrtz_v_range Hsa); pose proof (shrtz_v_range Hsb).
      cbv [loop_inv bits_removed] in *; ssplit; try lia.
      { rewrite (gcd_step Hsa Hsb ltac:(lia) Hodd); assumption. }
      { rewrite <- Z.mul_opp_r; apply (shrtz_cong Hsa Hca). }
      { apply (shrtz_cong Hsb), sub_cong; assumption. }
      { intros Hb'.
        assert (a <> b)
          by (intros <-; rewrite Z.sub_diag in Hsb; pose proof (shrtz_v_range Hsb); lia).
        apply (coeff_inv_step Hcoeff Hsa Hsb); lia. } }
    { rewrite Z.add_comm in Hsa.
      destruct (log2_step Hsb Hsa ltac:(lia)) as (Hlb & Hla & Hlt).
      pose proof (shrtz_v_range Hsa); pose proof (shrtz_v_range Hsb).
      cbv [loop_inv bits_removed] in *; ssplit; try lia.
      { rewrite Z.gcd_comm, (gcd_step Hsb Hsa ltac:(lia) ltac:(tauto)).
        rewrite Z.gcd_comm; assumption. }
      { rewrite <- Z.mul_opp_r; apply (shrtz_cong Hsa), sub_cong; [assumption |].
        rewrite Z.opp_involutive; assumption. }
      { apply (shrtz_cong Hsb Hcb). }
      { intros _; apply coeff_inv_swap, (coeff_inv_step (coeff_inv_swap Hcoeff) Hsb Hsa); lia. } }
  Qed.
End Loop.

Arguments shrtz_rel : clear implicits.
Arguments loop_inv : clear implicits.

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
    (["p_a"; "p_b"; "p_x"; "p_y"; "p_m"; "inv_m"; "cmp"]))
    (fun v a_ b_ x y R t m p_a p_b p_x p_y p_m inv_m_ cmp => PrimitivePair.pair.mk
      (v = (eval a_) + (eval b_) /\
       m =* array p_a a_ ⋆ array p_b b_ ⋆ array p_x x ⋆ array p_y y ⋆ array p_m MOD ⋆ R /\
       length a_ = 4%nat /\ length b_ = 4%nat /\ length x = 5%nat /\ length y = 5%nat /\
       (if ((eval b_) =? 0) then cmp = bits.of_Z _ 0 else (cmp <> (bits.of_Z _ 0))) /\
       inv_m_ = inv_m /\
       loop_inv (eval MOD) (eval b) (eval a_) (eval b_) (eval x) (eval y))
      (fun T M P_A P_B P_X P_Y P_M INV_M CMP => T = t /\ exists (A B X Y : list word),
         M =* array P_A A ⋆ array P_B B ⋆ array P_X X ⋆ array P_Y Y ⋆ array P_M MOD ⋆ R /\
         P_A = p_a /\ P_B = p_b /\ P_X = p_x /\ P_Y = p_y /\ P_M = p_m /\
         length A = 4%nat /\ length B = 4%nat /\ length X = 5%nat /\ length Y = 5%nat /\
         eval A = Z.gcd (eval a) (eval b) /\
         eval B = 0 /\
         (eval A) mod (eval MOD) = (-((eval Y) * (eval b)) mod (eval MOD))))
    (fun n m => 0 <= n < m)
    _ _ _ _ _ _ _ _ _ _); Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.lt_wf. }
  { repeat straightline; intuition try ecancel_assumption;
      repeat match goal with H : fold_right _ 0 _ = _ |- _ => progress rewrite H end; try ZnWords.
    apply (loop_inv_init (M := eval MOD) (b0 := eval b));
      [split; [lia | keep_length_equations; bigZnWords] | apply mod2_odd; assumption | lia]. }
  { intros; repeat (straightline || straightline_call).
    1,2,3,4: ssplit; try ecancel_assumption; eauto.
    all: destruct (eval x2 =? 0) eqn:Hx20; try solve [exfalso; cmp_contradiction].
    all: assert (HM : 1 < eval MOD < 2^256) by (split; [lia | keep_length_equations; bigZnWords]);
      assert (HMo : Z.odd (eval MOD) = true) by (apply mod2_odd; assumption);
      assert (Hb0 : 0 <= eval b < eval MOD) by lia.
    { rewrite Z.eqb_neq in Hx20; eapply (loop_inv_fits HM HMo Hb0); eassumption. }
    { clear_old_memory_hyps.
      subst v; repeat match goal with x := _ |- _ => subst x end.
      rewrite ?Zmod.of_Z_0, ?Zmod.unsigned_0, ?Z.eqb_eq, ?Z.eqb_neq in *.
      match goal with
      | H : if fold_right _ _ ?a <=? fold_right _ _ ?b
            then ?A = _ /\ fold_right _ _ ?B = _ /\ ?Y = ?y /\
                 fold_right _ _ ?X = fold_right _ _ ?x + _
            else _ |- _ =>
        assert (Hsub : sub_rel (eval a) (eval b) (eval x) (eval y)
                               (eval A) (eval B) (eval X) (eval Y))
          by (cbv [sub_rel]; destruct (_ <=? _); destruct H as (? & ? & ? & ?); ssplit; subst;
              (reflexivity || assumption))
      end.
      match goal with Hinv : loop_inv _ _ _ _ _ _ |- _ =>
        epose proof (loop_inv_step HM HMo Hb0 Hinv Hsub) as Hstep end.
      edestruct Hstep as [Hinv' Hlt];
        [ cbv [shrtz_rel]; ssplit;
            first [eassumption | reflexivity | keep_length_equations; bigZnWords] ..
        | assumption | ].
      eexists x19, x16, x17, x20, x5, _;
        ssplit; repeat straightline;
        cbv [Markers.right Markers.split]; repeat (intros; try assumption; split);
        try ecancel_assumption; try assumption; try reflexivity. }
    { rewrite Z.eqb_eq in Hx20.
      match goal with H : loop_inv _ _ _ _ _ _ |- _ =>
        rewrite Hx20 in H; apply (loop_inv_exit HM HMo Hb0) in H as [Hg Hc] end.
      eexists _, _, _, _; ssplit; try ecancel_assumption; eauto; congruence. } }
  { repeat straightline. eexists _, _, _, _; intuition try ecancel_assumption. }
Qed.

Lemma modinv_from_bezout (M a y out : Z) :
  1 < M -> 1 mod M = (- (y * a)) mod M -> out = M - y mod M ->
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
