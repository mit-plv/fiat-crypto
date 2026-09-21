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
        rewrite ?Zmod.of_Z_0, !word.lor_0_iff, !bits.xor_zero_iff in contra.
        destruct contra as [[[-> ->] ->] ->]; ZnWords.
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
    assert (Hcond : eval a <=? eval b = false) by bigZnWords
  | [H : ?x = 0 |- _] =>
    assert (Hcond : eval a <=? eval b = true) by bigZnWords
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


Ltac prune_unused :=
  repeat match goal with
  | [ H : _ |- _ ] =>
      match goal with
      | [ |- context[H] ] => fail 1          (* Fails if H is in the goal *)
      | [ _ : context[H] |- _ ] => fail 1    (* Fails if H is in another hypothesis *)
      | _ => clear H                        (* Clears H if not found above *)
      end
  end.

Ltac keep_length_equations :=
  repeat match goal with
  | [ H : ?T |- _ ] =>
      lazymatch T with
      | length _ = _ => fail   (* Found a match, don't clear it, fail this match branch *)
      | _ => clear H          (* Not a match, clear the hypothesis *)
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
Definition Z_size (z : Z) : Z :=
  match z with
  | Z.pos p => Zpos (Pos.size p)
  | 0 => 0
  | Z.neg p => Zpos (Pos.size p)
  end.

Lemma Pos_size_nat_size (p : positive) : Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof. induction p; cbn [Pos.size Pos.size_nat]; rewrite ?Pos2Nat.inj_succ; lia. Qed.

Lemma Z_size_sub (a b : Z) : a >= 0 -> b >= 0 -> b <= a -> Z_size (a - b) <= Z_size a.
Proof.
  intros; destruct (Z.eq_dec (a - b) 0) as [-> | ?]; [destruct a; cbv [Z_size]; lia |].
  destruct (a - b) eqn:?, a eqn:?; try lia; cbv [Z_size].
  assert ((p <= p0)%positive) by lia.
  apply Pos2Z.pos_le_pos, Pos2Nat.inj_le; rewrite !Pos_size_nat_size.
  destruct (Pos.lt_total p p0) as [? | [-> | ?]]; [apply Pos.size_nat_monotone; auto | lia | lia].
Qed.

Lemma Z_size_mul_pow2 (a n : Z) : a > 0 -> 0 <= n -> Z_size (a * 2 ^ n) = Z_size a + n.
Proof.
  intros Ha Hn; pattern n; apply natlike_ind; [| | exact Hn]; [rewrite Z.pow_0_r, Z.mul_1_r; lia |].
  intros x Hx IH; rewrite Z.pow_succ_r, Z.mul_assoc, (Z.mul_comm a 2), <- Z.mul_assoc by lia.
  replace (Z_size a + Z.succ x) with (Z_size (a * 2 ^ x) + 1) by lia.
  assert (a * 2 ^ x > 0) by (pose proof (Z.pow_pos_nonneg 2 x); nia).
  destruct (a * 2 ^ x) eqn:?; try lia; change (2 * Z.pos p) with (Z.pos p~0); cbv [Z_size]; cbn [Pos.size]; rewrite Pos2Z.inj_succ; lia.
Qed.

Lemma Z_size_le (n x : Z) : 0 <= n -> 0 <= x < 2^n -> Z_size x <= n.
Proof.
  intros Hn Hx; destruct x as [| p | p]; [cbv [Z_size]; lia | | lia]; cbn [Z_size].
  pose proof (Pos.size_le p) as Hle; apply Pos2Z.pos_le_pos in Hle.
  rewrite (Pos2Z.inj_pow 2 (Pos.size p)), (Pos2Z.inj_xO p) in Hle; change (Z.pos 2) with 2 in Hle.
  assert (2 ^ Z.pos (Pos.size p) < 2 ^ Z.succ n) by (rewrite (Z.pow_succ_r 2 n) by lia; lia).
  rewrite <- (Z.pow_lt_mono_r_iff 2) in H by lia; lia.
Qed.

Lemma Z_size_nonneg (x : Z) : 0 <= Z_size x.
Proof. destruct x; cbv [Z_size]; lia. Qed.

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

Lemma lctz_even_min63 (default z : Z) :
  0 <= default -> z > 0 -> (z / 2 ^ Z.min (lctz default z) 63) mod 2 = 0 ->
  Z.min (lctz default z) 63 = 63.
Proof.
  intros; pose proof (lctz_ge_0 default z H).
  destruct (Z_lt_ge_dec (lctz default z) 63); [|rewrite Z.min_r by lia; reflexivity].
  rewrite Z.min_l in H1 by lia; destruct (lctz_spec default z ltac:(lia)) as [k [Hk Hz]].
  pattern z at 1 in H1; rewrite Hz, Z.div_mul in H1 by (apply Z.pow_nonzero; lia); congruence.
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
  - rewrite Z.pow_0_r, Z.mul_1_l; reflexivity.
  - intros x Hx IH; rewrite Z.pow_succ_r, <- Z.mul_assoc, gcd_double_l by lia; exact IH.
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

Lemma bound_OO_to_OO_shifted (X X_old Y_old M k_old k_new s : Z) :
  0 <= M -> 0 <= k_old -> 1 <= s -> k_old + s <= k_new ->
  2 * X_old <= (3 + k_old) * M -> 2 * Y_old <= (3 + k_old) * M ->
  X * 2^s <= X_old + Y_old + (2^s - 1) * M ->
  2 * X <= (3 + k_new) * M.
Proof.
  intros; pose proof (pow2_bound_OO s k_old ltac:(lia) ltac:(lia)).
  replace (2 ^ (s + 1)) with (2 * 2 ^ s) in * by (rewrite Z.pow_add_r by lia; lia); nia.
Qed.

Lemma bound_OO_to_OE_shifted (X X_old Y_old M k_old k_new : Z) :
  0 <= M -> k_old + 4 <= k_new ->
  2 * X_old <= (3 + k_old) * M -> 2 * Y_old <= (3 + k_old) * M ->
  X * 2^63 <= X_old + Y_old + (2^63 - 1) * M ->
  2^63 * X <= (2^63 + k_new - 2) * M.
Proof. intros; nia. Qed.

Lemma bound_OE_to_OO (X3 X4 Z_new M k_old k_new : Z) :
  0 <= M -> k_old <= 513 -> k_old <= k_new -> Z_new <= X3 + X4 ->
  2^63 * X3 <= (2^63 + k_old - 2) * M -> 2 * X4 <= (2 + k_old - 2) * M ->
  2 * Z_new <= (3 + k_new) * M.
Proof. intros; nia. Qed.

Lemma bound_OE_to_OO_shifted (X X_old M k_old k_new s : Z) :
  0 <= M -> 0 <= k_old -> 1 <= s -> k_old <= k_new ->
  2^63 * X_old <= (2^63 + k_old - 2) * M ->
  X * 2^s <= X_old + (2^s - 1) * M ->
  2 * X <= (3 + k_new) * M.
Proof.
  intros; assert (2 <= 2^s) by (transitivity (2^1); [lia | apply Z.pow_le_mono_r; lia]); nia.
Qed.

Lemma bound_OE_to_OE_shifted (X X_old M k_old k_new : Z) :
  0 <= M -> 0 <= k_old -> k_old <= 512 -> k_old + 3 <= k_new ->
  2^63 * X_old <= (2^63 + k_old - 2) * M ->
  X * 2^63 <= X_old + (2^63 - 1) * M ->
  2^63 * X <= (2^63 + k_new - 2) * M.
Proof. intros; nia. Qed.

Lemma bound_OE_to_OE_sum (X3 X4 Z_new M k_old k_new : Z) :
  0 <= M -> k_old <= 512 -> k_old + 3 <= k_new -> Z_new <= X3 + X4 ->
  2^63 * X3 <= (2^63 + k_old - 2) * M -> 2 * X4 <= (2 + k_old - 2) * M ->
  2 * Z_new <= (2 + k_new - 2) * M.
Proof. intros; nia. Qed.

Lemma bound_unchanged (Y Y_old M c_old c_new : Z) :
  0 <= M -> c_old <= c_new -> Y <= Y_old -> 2 * Y_old <= c_old * M -> 2 * Y <= c_new * M.
Proof. intros; nia. Qed.

Definition xy_inv (a_ b_ x y M k : Z) : Prop :=
  if b_ =? 0 then True
  else if andb (a_ mod 2 =? 1) (b_ mod 2 =? 1) then
    0 <= 2 * x <= (3 + k) * M /\ 0 <= 2 * y <= (3 + k) * M
  else if andb (a_ mod 2 =? 1) (b_ mod 2 =? 0) then
    0 <= 2^63 * x <= (2^63 + k - 2) * M /\ 0 <= 2 * y <= (2 + k - 2) * M
  else
    0 <= 2^63 * y <= (2^63 + k - 2) * M /\ 0 <= 2 * x <= (2 + k - 2) * M.

Lemma xy_inv_swap (a_ b_ x y M k : Z) :
  a_ > 0 -> b_ > 0 -> (a_ mod 2 = 1 \/ b_ mod 2 = 1) ->
  xy_inv a_ b_ x y M k -> xy_inv b_ a_ y x M k.
Proof.
  intros Ha Hb Hodd; cbv [xy_inv].
  destruct (b_ =? 0) eqn:Eb0; [rewrite Z.eqb_eq in Eb0; lia |].
  destruct (a_ =? 0) eqn:Ea0; [rewrite Z.eqb_eq in Ea0; lia |].
  destruct (mod2_cases a_) as [Ha_m | Ha_m], (mod2_cases b_) as [Hb_m | Hb_m];
  rewrite Ha_m, Hb_m in *; cbn [Z.eqb Pos.eqb andb]; tauto || lia.
Qed.

Lemma xy_inv_sum_lt_320 (a_ b_ x y M k : Z) :
  b_ <> 0 -> 0 <= M < 2^256 -> 0 <= k <= 512 ->
  (a_ mod 2 = 1 \/ b_ mod 2 = 1) ->
  xy_inv a_ b_ x y M k ->
  x + y < 2^320.
Proof.
  intros Hb0 HM Hk Hodd Hinv; cbv [xy_inv] in Hinv.
  destruct (b_ =? 0) eqn:Eb; [rewrite Z.eqb_eq in Eb; lia |].
  destruct (mod2_cases a_) as [Ha | Ha], (mod2_cases b_) as [Hb | Hb];
  rewrite Ha, Hb in *; cbn [Z.eqb Pos.eqb andb] in Hinv; revert Hinv HM Hk; clear; intros; nia.
Qed.

Lemma le_mul_pow2_r (a b : Z) : 0 <= a -> 0 <= b -> a <= a * 2 ^ b.
Proof. intros; assert (1 <= 2^b) by (pose proof (Z.pow_pos_nonneg 2 b); lia); clear H0; nia. Qed.

Lemma xy_inv_step (v w v' w' u z u' z' s_v s_w M k_old k_new : Z) :
  1 <= v <= w -> 0 <= M -> 0 <= k_old <= 512 ->
  (v mod 2 = 1 \/ w mod 2 = 1) ->
  xy_inv v w z u M k_old ->
  s_v = Z.min (lctz 64 v) 63 -> v' * 2^s_v = v -> 0 <= u' -> u' * 2^s_v <= u + (2^s_v - 1) * M ->
  s_w = Z.min (lctz 64 (w - v)) 63 -> w' * 2^s_w = w - v -> 0 <= z' -> z' * 2^s_w <= z + u + (2^s_w - 1) * M ->
  k_old + (Z_size v + Z_size w) - (Z_size v' + Z_size w') <= k_new ->
  0 <= v' /\ 0 <= w' ->
  1 <= v' <= v /\ 0 <= w' < w /\ k_old <= k_new /\
  Z.gcd v' w' = Z.gcd v w /\
  (w' <> 0 -> (v' mod 2 = 1 \/ w' mod 2 = 1) /\ xy_inv v' w' z' u' M k_new).
Proof.
  intros Hvw HM Hk Hodd Hinv Hsv Hv' Hu'0 Hu' Hsw Hw' Hz'0 Hz' Hknew [Hv'0 Hw'0_ge].
  assert (Hsv0 : 0 <= s_v) by (subst s_v; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hsw0 : 0 <= s_w) by (subst s_w; apply Z.min_glb; [apply lctz_ge_0 |]; lia).
  assert (Hv'_le : v' <= v) by (rewrite <- Hv'; apply le_mul_pow2_r; lia).
  assert (Hw'_le : w' <= w - v) by (rewrite <- Hw'; apply le_mul_pow2_r; lia).
  assert (Hv'_ge1 : 1 <= v') by (destruct (Z.eq_dec v' 0) as [-> | ?]; [rewrite Z.mul_0_l in Hv'; lia | lia]).
  assert (Hsz_v : Z_size v' + s_v = Z_size v) by (rewrite <- Hv', Z_size_mul_pow2 by lia; lia).
  assert (Hsz_w : Z_size w' <= Z_size w).
  { destruct (Z.eq_dec w' 0) as [-> | ?]; [pose proof (Z_size_nonneg w); cbn [Z_size]; lia |].
    transitivity (Z_size (w - v)); [rewrite <- Hw', Z_size_mul_pow2 by lia; lia | apply Z_size_sub; lia]. }
  assert (Hk_le : k_old <= k_new) by lia.
  cbv [xy_inv] in Hinv |- *.
  destruct (w =? 0) eqn:Ew0; [rewrite Z.eqb_eq in Ew0; lia |].
  assert (Hsub_gcd : Z.gcd v (w - v) = Z.gcd v w) by apply Z.gcd_sub_diag_r.
  destruct (mod2_cases v) as [Hv_m | Hv_m], (mod2_cases w) as [Hw_m | Hw_m];
    [lia | | |]; rewrite Hv_m, Hw_m in *; cbn [Z.eqb Pos.eqb andb] in Hinv; destruct Hinv as [[? ?] [? ?]].
  - (* Case 1: v even (0), w odd (1) -> w - v is odd (1) *)
    assert (Hwv_odd : (w - v) mod 2 = 1) by (Z.push_mod; rewrite Hv_m, Hw_m; reflexivity).
    assert (Hsw_eq0 : s_w = 0) by (subst s_w; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsw_eq0, Z.pow_0_r, !Z.mul_1_r in Hw', Hz'.
    assert (Hw'_odd : w' mod 2 = 1) by congruence.
    assert (Hgcd : Z.gcd v' w' = Z.gcd v w) by (rewrite <- (gcd_pow2_l s_v), Hv', Hw' by lia; exact Hsub_gcd).
    assert (Hsv_ge1 : 1 <= s_v) by (subst s_v; apply Z.min_glb; [apply lctz_ge_1 |]; lia).
    do 4 (split; [lia |]).
    intros Hw'0; destruct (w' =? 0) eqn:Ew'0; [rewrite Z.eqb_eq in Ew'0; lia |].
    split; [right; exact Hw'_odd |].
    destruct (mod2_cases v') as [Hv'_m | Hv'_m]; rewrite Hv'_m, Hw'_odd; cbn [Z.eqb Pos.eqb andb].
    + (* v' even: s_v = 63 *)
      assert (Hs63 : s_v = 63) by (subst s_v; apply lctz_even_min63; try lia; replace (v / 2 ^ Z.min (lctz 64 v) 63) with v' by (eapply Zdiv_unique with (r := 0); lia); exact Hv'_m).
      rewrite Hs63 in *; repeat split; try lia;
      [ eapply bound_OE_to_OE_shifted with (X_old := u) (k_old := k_old); try eassumption; lia
      | eapply bound_OE_to_OE_sum with (X3 := u) (X4 := z) (k_old := k_old); try eassumption; lia ].
    + (* v' odd *)
      repeat split; try lia;
      [ eapply bound_OE_to_OO with (X3 := u) (X4 := z) (k_old := k_old); try eassumption; lia
      | eapply bound_OE_to_OO_shifted with (X_old := u) (k_old := k_old) (s := s_v); try eassumption; lia ].
  - (* Case 2: v odd (1), w even (0) -> v' = v (odd), w' = w - v (odd) *)
    assert (Hwv_odd : (w - v) mod 2 = 1) by (Z.push_mod; rewrite Hv_m, Hw_m; reflexivity).
    assert (Hsv_eq0 : s_v = 0) by (subst s_v; rewrite lctz_odd by lia; reflexivity).
    assert (Hsw_eq0 : s_w = 0) by (subst s_w; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsv_eq0 in Hv', Hu'; rewrite Hsw_eq0 in Hw', Hz';
    rewrite Z.pow_0_r, !Z.mul_1_r in Hv', Hw', Hu', Hz'.
    subst v' w'; do 4 (split; [lia |]).
    intros Hw'0; destruct (w - v =? 0) eqn:Ew'0; [rewrite Z.eqb_eq in Ew'0; lia |].
    rewrite Hv_m, Hwv_odd; cbn [Z.eqb Pos.eqb andb]; split; [left; reflexivity | repeat split; try lia].
    + eapply bound_OE_to_OO with (X3 := z) (X4 := u) (k_old := k_old); try eassumption; lia.
    + eapply bound_unchanged with (Y_old := u) (c_old := 2 + k_old - 2); try eassumption; lia.
  - (* Case 3: v odd (1), w odd (1) -> v' = v (odd), w - v is even (0) *)
    assert (Hwv_even : (w - v) mod 2 = 0) by (Z.push_mod; rewrite Hv_m, Hw_m; reflexivity).
    assert (Hsv_eq0 : s_v = 0) by (subst s_v; rewrite lctz_odd by lia; reflexivity).
    rewrite Hsv_eq0, Z.pow_0_r, !Z.mul_1_r in Hv', Hu'; subst v'.
    assert (Hgcd : Z.gcd v w' = Z.gcd v w) by (rewrite <- (gcd_pow2_r s_w), Hw' by lia; exact Hsub_gcd).
    do 4 (split; [lia |]).
    intros Hw'0; destruct (w' =? 0) eqn:Ew'0; [rewrite Z.eqb_eq in Ew'0; lia |].
    assert (Hwv_pos : w - v > 0) by lia.
    assert (Hsw_ge1 : 1 <= s_w) by (subst s_w; apply Z.min_glb; [apply lctz_ge_1 |]; lia).
    assert (Hsz_w' : Z_size w' + s_w <= Z_size w) by (transitivity (Z_size (w - v)); [rewrite <- Hw', Z_size_mul_pow2 by lia; lia | apply Z_size_sub; lia]).
    split; [left; exact Hv_m |].
    destruct (mod2_cases w') as [Hw'_m | Hw'_m]; rewrite Hv_m, Hw'_m; cbn [Z.eqb Pos.eqb andb].
    + (* w' even: s_w = 63 *)
      assert (Hs63 : s_w = 63) by (subst s_w; apply lctz_even_min63; try lia; replace ((w - v) / 2 ^ Z.min (lctz 64 (w - v)) 63) with w' by (eapply Zdiv_unique with (r := 0); lia); exact Hw'_m).
      rewrite Hs63 in *; repeat split; try lia;
      [ eapply bound_OO_to_OE_shifted with (X_old := z) (Y_old := u) (k_old := k_old); try eassumption; lia
      | eapply bound_unchanged with (Y_old := u) (c_old := 3 + k_old); try eassumption; lia ].
    + (* w' odd *)
      repeat split; try lia;
      [ eapply bound_OO_to_OO_shifted with (X_old := z) (Y_old := u) (k_old := k_old) (s := s_w); try eassumption; lia
      | eapply bound_unchanged with (Y_old := u) (c_old := 3 + k_old); try eassumption; lia ].
Qed.

Lemma xy_inv_0 a_ x y M k : xy_inv a_ 0 x y M k.
Proof. exact I. Qed.
Opaque xy_inv.

(** Complete loop-body invariant preservation for BOTH branches (a_ <=? b_ = true and false) *)
Lemma helper_loop_step_complete
  (a0 b0 M a_ b_ x y a_mid b_mid x_mid y_mid a' b' x' y' s_a s_b : Z) :
  M > 1 -> M mod 2 = 1 ->
  (0 <= Z_size a0 <= 256 /\ 0 <= Z_size b0 <= 256 /\ 0 <= Z_size a_ /\ 0 <= Z_size b_) ->
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
  - (* Branch 1: a_ <= b_ *)
    destruct (xy_inv_step a_ b_ a' b' y x y' x' s_a s_b M
                ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_))
                ((Z_size a0 + Z_size b0) - (Z_size a' + Z_size b')))
      as (Ha'r & Hb'r & Hkle & Hgcd' & Hrest); try assumption; try lia.
    destruct (Z.eq_dec b' 0) as [-> | Hb'nz].
    + assert (b_ = a_) by (rewrite Z.mul_0_l in Hb'; lia).
      assert (a_ mod 2 = 1) by (subst b_; tauto).
      assert (Hs0 : s_a = 0) by (subst s_a; rewrite lctz_odd by lia; reflexivity).
      rewrite Hs0, Z.pow_0_r, Z.mul_1_r in Ha'; subst a'.
      assert (xy_inv a_ 0 x' y' M (Z_size a0 + Z_size b0 - (Z_size a_ + Z_size 0))) by apply xy_inv_0.
      repeat split; try assumption; try lia; try tauto; try congruence.
    + destruct (Hrest Hb'nz) as [Hodd' Hinv']; repeat split; try assumption; try lia; try congruence.
  - (* Branch 2: b_ < a_ -> apply xy_inv_step to (b_, a_) via xy_inv_swap *)
    assert (Hinv_sw : xy_inv b_ a_ y x M ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_)))
      by (apply xy_inv_swap; lia || tauto).
    destruct (xy_inv_step b_ a_ b' a' x y x' y' s_b s_a M
                ((Z_size a0 + Z_size b0) - (Z_size a_ + Z_size b_))
                ((Z_size a0 + Z_size b0) - (Z_size a' + Z_size b')))
      as (Hb'r & Ha'r & Hkle & Hgcd' & Hrest); try assumption; try lia; try tauto.
    assert (Ha'nz : a' <> 0) by (intros ->; rewrite Z.mul_0_l in Ha'; lia).
    destruct (Hrest Ha'nz) as [Hodd' Hinv'].
    repeat split; try assumption; try lia; try tauto.
    + apply xy_inv_swap; try lia; tauto.
    + rewrite Z.gcd_comm, Hgcd', Z.gcd_comm; exact Hgcd.
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
    { repeat straightline; intuition try ecancel_assumption; rewrite ?H12, ?H14, ?H15; try ZnWords.
      {
        Transparent xy_inv. unfold xy_inv.
        rewrite <- Z.eqb_eq, H10 in *.
        destruct (eval b =? 0) eqn:Hb0; [exact I |].
        destruct (mod2_cases (eval b)) as [Hb | Hb]; rewrite Hb; cbn [Z.eqb Pos.eqb andb]; split; lia.
        Opaque xy_inv.
      }
      { Z.push_pull_mod. rewrite Z.mul_0_l, Z.sub_0_r, Z_mod_same, Z.mod_small by lia; eauto. }
      { Z.push_pull_mod. rewrite Z.mul_1_l. eauto. }
    }
    {
      intros; repeat (straightline || straightline_call).
      1,2,3,4: ssplit; try ecancel_assumption; eauto.
      all:
        destruct (eval x2 =? 0) eqn:Hx20;
            try solve [exfalso; revert H18 H25; keep_length_equations; intros; ZnWords ].
      all: assert (Hsz : 0 <= Z_size (eval a) <= 256 /\ 0 <= Z_size (eval b) <= 256 /\ 0 <= Z_size (eval x1) /\ 0 <= Z_size (eval x2))
        by (repeat split; try apply Z_size_nonneg; apply Z_size_le; try (clear H16; lia); keep_length_equations; bigZnWords).
      {
        rewrite ?Z.eqb_neq in Hx20.
        assert (Hmod : 0 <= eval MOD < 2^256) by (keep_length_equations; bigZnWords).
        assert (Hk_range : 0 <= (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2)) <= 512)
          by (clear H16 Hmod; lia).
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
          by (repeat split; try (clear H16 H47 H49 H50 H53 H55 H56; lia); keep_length_equations; bigZnWords).
        assert (Hsub : if eval x1 <=? eval x2
                       then eval x11 = eval x1 /\ eval x13 = eval x2 - eval x1 /\ eval x15 = eval x4 /\ eval x14 = eval x3 + eval x4
                       else eval x13 = eval x2 /\ eval x11 = eval x1 - eval x2 /\ eval x14 = eval x3 /\ eval x15 = eval x3 + eval x4)
          by (destruct (eval x1 <=? eval x2); destruct H43 as (-> & ? & -> & ?); repeat split; assumption).
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
        cbv [c] in *. rewrite Z.gcd_comm, <- H62.
        rewrite bits.unsigned_1 in * by lia.
        destruct (eval x2 =? 1) eqn: Hx2.
        {
            rewrite Z.eqb_eq in *.
            split; [ | split]; eauto.
            all:
                assert (Hx8 : Zmod.unsigned x8 = 0) by (lists_into_elements; cbv [eval] in *; ZnWords);
                rewrite Hx8, Z.mul_0_r, Z.sub_0_r, H70, H67, H49 in *.
            {
                Z.push_pull_mod.
                rewrite Z.mul_sub_distr_r in *.
                Z.push_mod_step.
                rewrite Z_mod_mult', Z.sub_0_l.
                Z.push_pull_mod. rewrite Z.sub_0_l, <- H63, Hx2, Z.mod_1_l; ZnWords.
            }
            {
                assert (0 <= eval x5 mod (eval MOD) < (eval MOD)).
                { eapply Z.mod_pos_bound; lia. }

                split; try lia.
                destruct (eval x5 mod (eval MOD) =? 0) eqn :Hx5; try lia.
                rewrite Z.eqb_eq in Hx5. rewrite Hx5 in *.
                rewrite Hx2 in *.
                exfalso. rewrite Z.mod_1_l, <- Z.sub_0_l, <-Zminus_mod_idemp_r, <-Zmult_mod_idemp_l, Hx5, Z.mul_0_l, Zmod_0_l in H63 by lia. lia.
            }
        }
        {
            eapply word.eqb_ne in H65.
            rewrite H65 in *. contradiction.
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
        cbv [c] in *. rewrite Z.gcd_comm, <- H62.
        destruct (eval x2 =? 1) eqn: Hx2; eauto.
        (* Contradiction *)
        rewrite Z.eqb_eq, Hx2, bits.unsigned_1 in * by lia.
        eapply Zmod.eqb_eq in H65.
        rewrite H65 in *. discriminate.
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

