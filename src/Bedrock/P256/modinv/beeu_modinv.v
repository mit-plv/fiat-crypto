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

Lemma lxor_range : forall a b z : Z,
      0 <= a < 2 ^ z ->
      0 <= b < 2 ^ z ->
      0 <= Z.lxor a b < 2 ^ z.
Proof.
    intros * [? ?] [? ?].
    destruct (Z_lt_le_dec z 0) as [? | ?].
    { rewrite Z.pow_neg_r in * by lia. lia. }
    destruct (Z.eq_dec z 0) as [-> | ?].
    { rewrite Z.pow_0_r in *.
    assert (a = 0) by lia.
    assert (b = 0) by lia.
    subst.
    rewrite Z.lxor_0_l.
    lia. }
    assert (0 <= Z.lxor a b).
    { apply Z.lxor_nonneg; lia. }
    split; [lia |].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [-> | ?].
    { assert (0 < 2 ^ z) by (apply Z.pow_pos_nonneg; lia).
    lia. }
    { rewrite Z.log2_lt_pow2 by lia.
    assert (Z.log2 (Z.lxor a b) <= Z.max (Z.log2 a) (Z.log2 b)).
    { apply Z.log2_lxor; lia. }
    assert (Z.log2 a < z).
    { destruct (Z.eq_dec a 0) as [-> | ?].
        { rewrite Z.log2_nonpos; lia. }
        { apply Z.log2_lt_pow2; lia. } }
    assert (Z.log2 b < z).
    { destruct (Z.eq_dec b 0) as [-> | ?].
        { rewrite Z.log2_nonpos; lia. }
        { apply Z.log2_lt_pow2; lia. } }
    lia. }
Qed.

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
        rewrite ?Zmod.of_Z_0 in contra. repeat rewrite word.lor_0_iff in contra.
        repeat destruct contra as [contra ?].
        ZnWords_pre. pose proof (lxor_range w0 w1 64 ltac:(assumption) ltac:(assumption)).
        rewrite !Z.mod_small in * by lia.
        eapply Hn. rewrite Z.lxor_eq_0_iff in contra; lia.
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

Definition Z_size (z : Z) : Z :=
    match z with
    | Z.pos p => Zpos (Pos.size p)
    | 0 => 0
    | Z.neg p => Zpos (Pos.size p)
    end.

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

Lemma lctz_ge_0 (default : Z) (x : Z) : 0 <= default ->
    0 <= lctz default x.
Proof.
    intros H. destruct x; cbv [lctz]; try lia.
Qed.

Lemma le_mul_1 (a b : Z) : (0 <= a) -> (0 <= b) -> 1 <= a * b -> 1 <= a.
Proof. lia. Qed.

Lemma lctz_odd (default a : Z) : a >= 0 -> a mod 2 = 1 -> lctz default a = 0.
Proof.
    intros H_ge H_mod.
    destruct a as [ | p | p ].
    { cbn in H_mod; discriminate. }
    { destruct p as [ p' | p' | ]; [ reflexivity | | reflexivity ].
    rewrite Pos2Z.pos_xO, Z.mul_comm, Z.mod_mul in H_mod by lia.
    discriminate. }
    { lia. }
Qed.

Lemma gcd_odd_iff (a b : Z) : Z.gcd a b mod 2 = 1 <-> a mod 2 = 1 \/ b mod 2 = 1.
Proof.
    split; intros H.
    {   destruct (mod2_cases a), (mod2_cases b);
        match goal with
        | [H : ?a mod 2 = 1 |- ?a mod 2 = 1 \/ _] => left; assumption
        | [H : ?b mod 2 = 1 |- _ \/ ?b mod 2 = 1] => right; assumption
        | [H1 : ?a mod 2 = 0, H2 : ?b mod 2 = 0, H : Z.gcd ?a ?b mod 2 = 1 |- _] =>
            rewrite Z.mod_divide in H1,H2 by lia;
            rewrite (Z.cong_iff_ex _ 1) in H by lia; destruct H as [n Hn];
            pose proof (H' := Z.gcd_greatest _ _ _ H1 H2); destruct H' as [z Hz];
            lia
        end.
    }
    {
        destruct (mod2_cases (Z.gcd a b)) as [Hgcd | Hgcd]; trivial.
        rewrite Z.mod_divide, Z.gcd_divide_iff in Hgcd by lia.
        rewrite ?(Z.cong_iff_ex _ 1) in H.
        destruct H as [ [? ?] | [? ?]], Hgcd as [[? ?] [? ?]];
        lia.
    }
Qed.

Lemma gcd_double_l (a b : Z) : b mod 2 = 1 -> Z.gcd (2 * a) b = Z.gcd a b.
Proof.
    intros H; destruct a as [ | p | p], b as [| p' | p'];
    try (discriminate || reflexivity);
    (* Trivial cases and contradictions *)
    rewrite <- ?Pos2Z.pos_xO, <- ?Pos2Z.neg_xO;
    destruct p' as [p' | p' | ];
    try match goal with
    | [H : _ (xO ?p) mod 2 = 1 |- _] =>
        rewrite ?(Pos2Z.pos_xO p), ?(Pos2Z.neg_xO p),
                Z_mod_mult' in H
    | [H : _ (xH) mod 2 = 1 |- _] =>
        rewrite ?(Z.gcd_comm _ 1), ?(Z.gcd_comm _ (-1))
    end;
    discriminate || reflexivity.
Qed.

Lemma gcd_double_r (a b : Z) : a mod 2 = 1 -> Z.gcd a (2 * b) = Z.gcd a b.
Proof.
    intros H; rewrite !(Z.gcd_comm a); eapply gcd_double_l; assumption.
Qed.

Lemma gcd_pow2_l (n a b : Z) : n >= 0 -> b mod 2 = 1 -> Z.gcd (a * (2 ^ n)) b = Z.gcd a b.
Proof.
    intros Hn Hb.
    rewrite Z.mul_comm.
    assert (0 <= n) as Hle by lia.
    revert Hn.
    pattern n; apply natlike_ind; [ | | exact Hle ].
    { intros _.
    rewrite Z.pow_0_r, Z.mul_1_l.
    reflexivity. }
    { intros x Hx IH _.
    rewrite Z.pow_succ_r by lia.
    rewrite <- Z.mul_assoc.
    rewrite gcd_double_l by assumption.
    apply IH; lia. }
Qed.

Lemma gcd_pow2_r (n a b : Z) : n >= 0 -> a mod 2 = 1 -> Z.gcd a (b * 2 ^ n) = Z.gcd a b.
Proof.
    intros Hn Ha.
    rewrite !(Z.gcd_comm a).
    eapply gcd_pow2_l; assumption.
Qed.

(* --- Helper Lemmas for Pos.size --- *)

Lemma Pos_size_nat_size (p : positive) :
    Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof.
    induction p as [ p IH | p IH | ]; cbn [Pos.size Pos.size_nat]; auto.
    { rewrite Pos2Nat.inj_succ, IH. reflexivity. }
    { rewrite Pos2Nat.inj_succ, IH. reflexivity. }
Qed.

Lemma Pos_size_monotone (p q : positive) :
    (p <= q)%positive -> (Pos.size p <= Pos.size q)%positive.
Proof.
    intros Hle.
    apply Pos2Nat.inj_le.
    rewrite !Pos_size_nat_size.
    destruct (Pos.lt_total p q) as [Hlt | [Heq | Hgt]].
    { apply Pos.size_nat_monotone; assumption. }
    { subst; reflexivity. }
    { lia. }
Qed.

(* --- Lemma 1: Z_size (a - b) <= Z_size a --- *)

Lemma Z_size_sub (a b : Z) :
    a >= 0 -> b >= 0 -> b <= a -> Z_size (a - b) <= Z_size a.
Proof.
    intros Ha Hb Hba.
    destruct (Z.eq_dec (a - b) 0) as [Heq | Hneq].
    { rewrite Heq.
    cbv [Z_size].
    destruct a as [ | pa | pa ]; lia. }
    { assert (0 < a - b) by lia.
    assert (0 < a) by lia.
    destruct (a - b) as [ | pd | pd ] eqn:Eab; [ lia | | lia ].
    destruct a as [ | pa | pa ] eqn:Ea; [ lia | | lia ].
    cbv [Z_size].
    assert (Hle : (pd <= pa)%positive) by lia.
    apply Pos_size_monotone in Hle.
    lia. }
Qed.

(* --- Helper Lemmas for Z_size (2 * z) --- *)

Lemma Z_size_pos_double (p : positive) :
    Z_size (2 * Z.pos p) = Z_size (Z.pos p) + 1.
Proof.
    change (2 * Z.pos p) with (Z.pos (p~0)).
    cbv [Z_size].
    cbn [Pos.size].
    rewrite Pos2Z.inj_succ.
    lia.
Qed.

Lemma Z_size_double (z : Z) :
    z > 0 -> Z_size (2 * z) = Z_size z + 1.
Proof.
    intros Hz.
    destruct z as [ | p | p ]; [ lia | | lia ].
    apply Z_size_pos_double.
Qed.

(* --- Lemma 2: Z_size (a * 2^n) = Z_size a + n --- *)

Lemma Z_size_mul_pow2 (a n : Z) :
    a > 0 -> 0 <= n -> Z_size (a * (2 ^ n)) = Z_size a + n.
Proof.
    intros Ha Hn.
    pattern n; apply natlike_ind; [ | | exact Hn ].
    { rewrite Z.pow_0_r, Z.mul_1_r. lia. }
    { intros x Hx IH.
    rewrite Z.pow_succ_r by lia.
    replace (a * (2 * 2 ^ x)) with (2 * (a * 2 ^ x)) by ring.
    assert (Hpos : a * 2 ^ x > 0) by nia.
    rewrite Z_size_double by exact Hpos.
    rewrite IH.
    lia. }
Qed.

Lemma mul_le_mono_diag_r (a b : Z) : 0 <= a -> 1 <= b -> a <= a * b.
Proof.
    intros Ha Hb.
    nia.
Qed.

Lemma le_mul_pow2_r (a b : Z) : 0 <= a -> 0 <= b -> a <= a * (2 ^ b).
Proof.
    intros Ha Hb.
    apply mul_le_mono_diag_r; [ exact Ha | ].
    pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) Hb).
    lia.
Qed.

Lemma mod_pow2_inv (m a b n : Z) : m > 1 -> m mod 2 = 1 -> n >= 0 ->
    a * 2^n mod m = b * 2^n mod m -> a mod m = b mod m.
Proof.
    intros.
    assert (Z.coprime (2^n) m).
    {
        cbv [Z.coprime].
        rewrite <- (Z.mul_1_l (2^n)), gcd_pow2_l, Z.gcd_1_l by lia.
        eauto.
    }
    rewrite <- (Z.mul_1_r a), <- (Z.mul_1_r b). Z.push_mod.
    rewrite <- (Z.invmod_coprime (2^n) m) by (try lia; assumption).
    Z.push_pull_mod. rewrite !(Z.mul_comm _ (2^n)), !Z.mul_assoc. Z.push_mod_step. rewrite H2.
    Z.pull_mod. eauto.
Qed.

Lemma Z_size_le : forall n x,
    0 <= n ->
    0 <= x < 2^n ->
    Z_size x <= n.
Proof.
    intros n x Hn Hx.
    destruct x as [ | p | p ].
    { (* x = 0 *)
    simpl.
    lia. }
    { (* x = Z.pos p *)
    simpl.
    pose proof (Pos.size_le p) as Hle.
    apply Pos2Z.pos_le_pos in Hle.
    rewrite (Pos2Z.inj_pow 2 (Pos.size p)) in Hle.
    rewrite (Pos2Z.inj_xO p) in Hle.
    change (Z.pos 2) with 2 in Hle.
    assert (Hsucc : 2 ^ (Z.pos (Pos.size p)) < 2 ^ (Z.succ n)).
    { rewrite (Z.pow_succ_r 2 n) by lia.
        lia. }
    rewrite <- (Z.pow_lt_mono_r_iff 2) in Hsucc by lia.
    lia. }
    { (* x = Z.neg p *)
    lia. }
Qed.

Lemma Z_size_nonneg : forall x, 0 <= Z_size x.
Proof. destruct x; cbv [Z_size]; lia. Qed.

Lemma pow2_bound_OO : forall s k : Z,
  0 <= k -> 1 <= s ->
  2 ^ (s + 1) + 2 * k + 4 <= 2 ^ s * (3 + k + s).
Proof.
  intros s k Hk Hs.
  assert (Hs_cases : s = 1 \/ 2 <= s) by lia.
  destruct Hs_cases as [Hs1 | Hs2].
  { subst s. replace (1 + 1) with 2 by lia.
    change (2 ^ 2) with 4. change (2 ^ 1) with 2. lia. }
  { assert (Hpow_step : 2 ^ (s + 1) = 2 * 2 ^ s).
    { replace (s + 1) with (1 + s) by lia. rewrite Z.pow_add_r; [|lia|lia].
      change (2 ^ 1) with 2. lia. }
    rewrite Hpow_step.
    assert (2 * k + 4 <= 2 ^ s * (1 + k + s)).
    { assert (2 <= 2 ^ s).
      { transitivity (2 ^ 1); [lia|].
        apply Z.pow_le_mono_r; lia. }
      assert (2 * k <= 2 ^ s * k) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (H4 : 4 <= 2 ^ s * (1 + s)).
      { assert (4 <= 2 ^ s).
        { transitivity (2 ^ 2); [lia|].
          apply Z.pow_le_mono_r; lia. }
        assert (1 <= 1 + s) by lia.
        rewrite <- (Z.mul_1_r 4) at 1.
        apply Z.mul_le_mono_nonneg; lia. }
      replace (2 ^ s * (1 + k + s)) with (2 ^ s * k + 2 ^ s * (1 + s)) by ring.
      lia. }
    replace (2 ^ s * (3 + k + s)) with (2 * 2 ^ s + 2 ^ s * (1 + k + s)) by ring.
    lia. }
Qed.

(** ** Transition Group 1: OO -> OO (Odd/Odd Division Step) *)

Lemma bound_OO_to_OO_shifted : forall X X_old Y_old M k_old k_new s : Z,
  0 <= M -> 0 <= k_old -> 1 <= s -> k_old + s <= k_new ->
  2 * X_old <= (3 + k_old) * M ->
  2 * Y_old <= (3 + k_old) * M ->
  X * 2^s <= X_old + Y_old + (2^s - 1) * M ->
  2 * X <= (3 + k_new) * M.
Proof.
  intros X X_old Y_old M k_old k_new s HM Hk0 Hs Hks HX_old HY_old HX.
  assert (Hsum : 2 * (X_old + Y_old) <= 2 * (3 + k_old) * M) by lia.
  assert (Hscale : 2 * (X * 2^s) <= 2 * (X_old + Y_old) + 2 * (2^s - 1) * M) by lia.
  assert (HX2 : 2 * X * 2^s <= (2 * (3 + k_old) + 2 * (2^s - 1)) * M).
  { replace (2 * X * 2^s) with (2 * (X * 2^s)) by ring.
    replace ((2 * (3 + k_old) + 2 * (2^s - 1)) * M) with (2 * (3 + k_old) * M + 2 * (2^s - 1) * M) by ring.
    lia. }
  assert (Hfactor : 2 * (3 + k_old) + 2 * (2^s - 1) <= 2^s * (3 + k_new)).
  { assert (Hpow_step : 2 * (3 + k_old) + 2 * (2^s - 1) = 2^(s+1) + 2*k_old + 4).
    { assert (2 * (2^s - 1) = 2^(s+1) - 2).
      { replace (s + 1) with (1 + s) by lia. rewrite Z.pow_add_r; [|lia|lia].
        change (2^1) with 2. lia. }
      lia. }
    rewrite Hpow_step.
    assert (Hpow : 2^(s+1) + 2*k_old + 4 <= 2^s * (3 + k_old + s)) by (apply pow2_bound_OO; lia).
    assert (3 + k_old + s <= 3 + k_new) by lia.
    assert (2^s * (3 + k_old + s) <= 2^s * (3 + k_new)).
    { apply Z.mul_le_mono_nonneg_l; [|lia].
      apply Z.pow_nonneg. lia. }
    lia. }
  assert (2 * X * 2^s <= (3 + k_new) * M * 2^s).
  { assert (Hmul : (2 * (3 + k_old) + 2 * (2^s - 1)) * M <= (2^s * (3 + k_new)) * M).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    replace ((2^s * (3 + k_new)) * M) with ((3 + k_new) * M * 2^s) in Hmul by ring.
    lia. }
  assert (Hpos : 0 < 2^s) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.mul_le_mono_pos_r (2 * X) ((3 + k_new) * M) (2^s) Hpos) in H.
  exact H.
Qed.

Lemma bound_OO_to_OO_unchanged : forall Y Y_old M k_old k_new : Z,
  0 <= M ->
  k_old <= k_new ->
  Y <= Y_old ->
  2 * Y_old <= (3 + k_old) * M ->
  2 * Y <= (3 + k_new) * M.
Proof.
  intros Y Y_old M k_old k_new HM Hk HY HY_old.
  assert (2 * Y <= (3 + k_old) * M) by lia.
  assert ((3 + k_old) * M <= (3 + k_new) * M).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

(** ** Transition Group 2: OO -> OE and OO -> EO (Entering Mixed Parity) *)

Lemma bound_OO_to_OE_shifted : forall X X_old Y_old M k_old k_new : Z,
  0 <= M ->
  k_old + 4 <= k_new ->
  2 * X_old <= (3 + k_old) * M ->
  2 * Y_old <= (3 + k_old) * M ->
  2^63 * X <= X_old + Y_old + (2^63 - 1) * M ->
  2^63 * X <= (2^63 + k_new - 2) * M.
Proof.
  intros X X_old Y_old M k_old k_new HM Hk HX_old HY_old HX.
  assert (Hsum : 2 * (X_old + Y_old) <= 2 * (3 + k_old) * M) by lia.
  assert (Hsum_div : X_old + Y_old <= (3 + k_old) * M) by lia.
  assert (Hbound : 2^63 * X <= (2^63 + k_old + 2) * M).
  { replace ((2^63 + k_old + 2) * M) with ((3 + k_old) * M + (2^63 - 1) * M) by ring.
    lia. }
  assert (Hmono : (2^63 + k_old + 2) * M <= (2^63 + k_new - 2) * M).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma bound_OO_to_OE_unchanged : forall Y Y_old M k_old k_new : Z,
  0 <= M ->
  k_old + 3 <= k_new ->
  Y <= Y_old ->
  2 * Y_old <= (3 + k_old) * M ->
  2 * Y <= (2 + k_new - 2) * M.
Proof.
  intros Y Y_old M k_old k_new HM Hk HY HY_old.
  assert (2 * Y <= (3 + k_old) * M) by lia.
  assert ((3 + k_old) * M <= (2 + k_new - 2) * M).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma bound_OO_to_EO_shifted : forall Y X_old Y_old M k_old k_new : Z,
  0 <= M ->
  k_old + 4 <= k_new ->
  2 * X_old <= (3 + k_old) * M ->
  2 * Y_old <= (3 + k_old) * M ->
  2^63 * Y <= X_old + Y_old + (2^63 - 1) * M ->
  2^63 * Y <= (2^63 + k_new - 2) * M.
Proof.
  intros Y X_old Y_old M k_old k_new HM Hk HX_old HY_old HY.
  apply bound_OO_to_OE_shifted with (X_old := X_old) (Y_old := Y_old) (k_old := k_old); assumption.
Qed.

Lemma bound_OO_to_EO_unchanged : forall X X_old M k_old k_new : Z,
  0 <= M ->
  k_old + 3 <= k_new ->
  X <= X_old ->
  2 * X_old <= (3 + k_old) * M ->
  2 * X <= (2 + k_new - 2) * M.
Proof.
  intros X X_old M k_old k_new HM Hk HX HX_old.
  apply bound_OO_to_OE_unchanged with (Y_old := X_old) (k_old := k_old); assumption.
Qed.

(** ** Transition Group 3: OE -> OO and EO -> OO (Returning to Odd/Odd) *)

Lemma bound_OE_to_OO : forall X3 X4 M k_old k_new : Z,
  0 <= M ->
  k_old <= 2^62 + 2 ->
  k_old <= k_new ->
  2^63 * X3 <= (2^63 + k_old - 2) * M ->
  2 * X4 <= (2 + k_old - 2) * M ->
  2 * (X3 + X4) <= (3 + k_new) * M.
Proof.
  intros X3 X4 M k_old k_new HM Hk_max Hkn HX3 HX4.
  assert (Hpos : 0 < 2^62) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.mul_le_mono_pos_l (2 * (X3 + X4)) ((3 + k_new) * M) (2^62) Hpos).
  replace (2^62 * (2 * (X3 + X4))) with (2^63 * X3 + 2^62 * (2 * X4)) by ring.
  replace (2^62 * ((3 + k_new) * M)) with ((2^63 + 2^62 + 2^62 * k_new) * M) by ring.
  assert (Hsum : 2^63 * X3 + 2^62 * (2 * X4) <= (2^63 + k_old - 2 + 2^62 * (2 + k_old - 2)) * M).
  { replace ((2^63 + k_old - 2 + 2^62 * (2 + k_old - 2)) * M)
      with ((2^63 + k_old - 2) * M + 2^62 * ((2 + k_old - 2) * M)) by ring.
    assert (Hscaled4 : 2^62 * (2 * X4) <= 2^62 * ((2 + k_old - 2) * M)).
    { apply Z.mul_le_mono_nonneg_l; [lia | exact HX4]. }
    lia. }
  etransitivity; [exact Hsum |].
  apply Z.mul_le_mono_nonneg_r; [exact HM |].
  replace (2^63 + k_old - 2 + 2^62 * (2 + k_old - 2))
    with (2^63 + 2^62 * k_old + (k_old - 2)) by ring.
  replace (2^63 + 2^62 + 2^62 * k_new)
    with (2^63 + 2^62 * k_old + (2^62 + 2^62 * (k_new - k_old))) by ring.
  assert (0 <= 2^62 * (k_new - k_old)).
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma bound_OE_to_OO_shifted : forall X X_old M k_old k_new s : Z,
  0 <= M ->
  0 <= k_old ->
  1 <= s ->
  k_old <= k_new ->
  2^63 * X_old <= (2^63 + k_old - 2) * M ->
  X * 2^s <= X_old + (2^s - 1) * M ->
  2 * X <= (3 + k_new) * M.
Proof.
  intros X X_old M k_old k_new s HM Hk0 Hs Hkn HX_old HX.
  assert (Hpos_s : 0 < 2^s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos_63 : 0 < 2^63) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpos : 0 < 2^63 * 2^s) by (apply Z.mul_pos_pos; lia).
  apply (Z.mul_le_mono_pos_r (2 * X) ((3 + k_new) * M) (2^63 * 2^s) Hpos).
  assert (Hscale : (2 * X) * (2^63 * 2^s) <= 2 * (2^63 * X_old) + 2 * 2^63 * (2^s - 1) * M).
  { assert (Hstep : (2 * 2^63) * (X * 2^s) <= (2 * 2^63) * (X_old + (2^s - 1) * M)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    replace ((2 * X) * (2^63 * 2^s)) with ((2 * 2^63) * (X * 2^s)) by ring.
    replace (2 * (2^63 * X_old) + 2 * 2^63 * (2^s - 1) * M)
      with ((2 * 2^63) * (X_old + (2^s - 1) * M)) by ring.
    exact Hstep. }
  etransitivity; [exact Hscale |].
  assert (Hsum : 2 * (2^63 * X_old) + 2 * 2^63 * (2^s - 1) * M <= (2 * 2^63 * 2^s + 2 * k_old - 4) * M).
  { replace ((2 * 2^63 * 2^s + 2 * k_old - 4) * M)
      with (2 * ((2^63 + k_old - 2) * M) + 2 * 2^63 * (2^s - 1) * M) by ring.
    lia. }
  etransitivity; [exact Hsum |].
  replace ((3 + k_new) * M * (2^63 * 2^s))
    with ((2^63 * 2^s * (3 + k_new)) * M) by ring.
  apply Z.mul_le_mono_nonneg_r; [exact HM |].
  assert (Hpow_s : 2 <= 2^s).
  { transitivity (2^1); [lia |].
    apply Z.pow_le_mono_r; lia. }
  assert (Hk_scale : 2 * k_old <= (2^63 * 2^s) * k_new).
  { assert (2 * k_old <= 2 * k_new) by lia.
    assert (2 * k_new <= (2^63 * 2^s) * k_new).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia. }
  replace (2^63 * 2^s * (3 + k_new))
    with (2 * 2^63 * 2^s + 2^63 * 2^s + (2^63 * 2^s) * k_new) by ring.
  lia.
Qed.

Lemma bound_OE_to_OO_unchanged : forall X4 M k_old k_new : Z,
  0 <= M ->
  k_old <= k_new ->
  2 * X4 <= (2 + k_old - 2) * M ->
  2 * X4 <= (3 + k_new) * M.
Proof.
  intros X4 M k_old k_new HM Hkn HX4.
  assert (2 * X4 <= k_old * M) by lia.
  assert (k_old * M <= (3 + k_new) * M).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma bound_EO_to_OO : forall X3 X4 M k_old k_new : Z,
  0 <= M ->
  k_old <= 2^62 + 2 ->
  k_old <= k_new ->
  2 * X3 <= (2 + k_old - 2) * M ->
  2^63 * X4 <= (2^63 + k_old - 2) * M ->
  2 * (X3 + X4) <= (3 + k_new) * M.
Proof.
  intros X3 X4 M k_old k_new HM Hk_max Hkn HX3 HX4.
  rewrite Z.add_comm.
  apply bound_OE_to_OO with (k_old := k_old); assumption.
Qed.

Lemma bound_EO_to_OO_unchanged : forall X3 M k_old k_new : Z,
  0 <= M ->
  k_old <= k_new ->
  2 * X3 <= (2 + k_old - 2) * M ->
  2 * X3 <= (3 + k_new) * M.
Proof.
  intros X3 M k_old k_new HM Hkn HX3.
  apply bound_OE_to_OO_unchanged with (k_old := k_old); assumption.
Qed.

(** ** Transition Group 4: OE -> OE and EO -> EO (Remaining in Mixed Parity) *)

Lemma bound_OE_to_OE_shifted : forall X X_old M k_old k_new : Z,
  0 <= M ->
  0 <= k_old ->
  k_old <= 2^63 + 2 ->
  k_old + 3 <= k_new ->
  2^63 * X_old <= (2^63 + k_old - 2) * M ->
  2^63 * X <= X_old + (2^63 - 1) * M ->
  2^63 * X <= (2^63 + k_new - 2) * M.
Proof.
  intros X X_old M k_old k_new HM Hk0 Hk_max Hstep HX_old HX.
  assert (Hpos : 0 < 2^63) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.mul_le_mono_pos_l (2^63 * X) ((2^63 + k_new - 2) * M) (2^63) Hpos).
  assert (Hscale : 2^63 * (2^63 * X) <= 2^63 * X_old + 2^63 * (2^63 - 1) * M).
  { assert (Hstep2 : 2^63 * (2^63 * X) <= 2^63 * (X_old + (2^63 - 1) * M)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    replace (2^63 * (X_old + (2^63 - 1) * M))
      with (2^63 * X_old + 2^63 * (2^63 - 1) * M) in Hstep2 by ring.
    exact Hstep2. }
  etransitivity; [exact Hscale |].
  assert (Hsum : 2^63 * X_old + 2^63 * (2^63 - 1) * M <= (2^63 + k_old - 2 + 2^63 * (2^63 - 1)) * M).
  { replace ((2^63 + k_old - 2 + 2^63 * (2^63 - 1)) * M)
      with ((2^63 + k_old - 2) * M + 2^63 * (2^63 - 1) * M) by ring.
    lia. }
  etransitivity; [exact Hsum |].
  replace (2^63 * ((2^63 + k_new - 2) * M))
    with ((2^63 * (2^63 + k_new - 2)) * M) by ring.
  apply Z.mul_le_mono_nonneg_r; [exact HM |].
  replace (2^63 + k_old - 2 + 2^63 * (2^63 - 1))
    with (2^63 * 2^63 + (k_old - 2)) by ring.
  replace (2^63 * (2^63 + k_new - 2))
    with (2^63 * 2^63 + 2^63 * (k_new - 2)) by ring.
  assert (k_old - 2 <= 2^63 * (k_new - 2)).
  { assert (1 <= k_new - 2) by lia.
    assert (2^63 <= 2^63 * (k_new - 2)).
    { rewrite <- (Z.mul_1_r (2^63)) at 1.
      apply Z.mul_le_mono_nonneg_l; lia. }
    lia. }
  lia.
Qed.

Lemma bound_OE_to_OE_sum : forall X3 X4 M k_old k_new : Z,
  0 <= M ->
  k_old <= 2^62 + 2 ->
  k_old + 3 <= k_new ->
  2^63 * X3 <= (2^63 + k_old - 2) * M ->
  2 * X4 <= (2 + k_old - 2) * M ->
  2 * (X3 + X4) <= (2 + k_new - 2) * M.
Proof.
  intros X3 X4 M k_old k_new HM Hk_max Hstep HX3 HX4.
  assert (Hpos : 0 < 2^62) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.mul_le_mono_pos_l (2 * (X3 + X4)) ((2 + k_new - 2) * M) (2^62) Hpos).
  replace (2^62 * (2 * (X3 + X4))) with (2^63 * X3 + 2^62 * (2 * X4)) by ring.
  replace (2^62 * ((2 + k_new - 2) * M)) with ((2^62 * k_new) * M) by ring.
  assert (Hsum : 2^63 * X3 + 2^62 * (2 * X4) <= (2^63 + k_old - 2 + 2^62 * (2 + k_old - 2)) * M).
  { replace ((2^63 + k_old - 2 + 2^62 * (2 + k_old - 2)) * M)
      with ((2^63 + k_old - 2) * M + 2^62 * ((2 + k_old - 2) * M)) by ring.
    assert (Hscaled4 : 2^62 * (2 * X4) <= 2^62 * ((2 + k_old - 2) * M)).
    { apply Z.mul_le_mono_nonneg_l; [lia | exact HX4]. }
    lia. }
  etransitivity; [exact Hsum |].
  apply Z.mul_le_mono_nonneg_r; [exact HM |].
  replace (2^63 + k_old - 2 + 2^62 * (2 + k_old - 2))
    with (2^63 + 2^62 * k_old + (k_old - 2)) by ring.
  replace (2^62 * k_new)
    with (2^63 + 2^62 * k_old + 2^62 * (k_new - k_old - 2)) by ring.
  assert (Hpow : 2^62 <= 2^62 * (k_new - k_old - 2)).
  { rewrite <- (Z.mul_1_r (2^62)) at 1.
    apply Z.mul_le_mono_nonneg_l; lia. }
  lia.
Qed.

Lemma bound_EO_to_EO_shifted : forall Y Y_old M k_old k_new : Z,
  0 <= M ->
  0 <= k_old ->
  k_old <= 2^63 + 2 ->
  k_old + 3 <= k_new ->
  2^63 * Y_old <= (2^63 + k_old - 2) * M ->
  2^63 * Y <= Y_old + (2^63 - 1) * M ->
  2^63 * Y <= (2^63 + k_new - 2) * M.
Proof.
  intros Y Y_old M k_old k_new HM Hk0 Hk_max Hstep HY_old HY.
  apply bound_OE_to_OE_shifted with (X_old := Y_old) (k_old := k_old); assumption.
Qed.

Lemma bound_EO_to_EO_sum : forall X3 X4 M k_old k_new : Z,
  0 <= M ->
  k_old <= 2^62 + 2 ->
  k_old + 3 <= k_new ->
  2 * X3 <= (2 + k_old - 2) * M ->
  2^63 * X4 <= (2^63 + k_old - 2) * M ->
  2 * (X3 + X4) <= (2 + k_new - 2) * M.
Proof.
  intros X3 X4 M k_old k_new HM Hk_max Hstep HX3 HX4.
  rewrite Z.add_comm.
  apply bound_OE_to_OE_sum with (k_old := k_old); assumption.
Qed.

Lemma lctz_even_min63 (default z : Z) :
    0 <= default ->
    z > 0 ->
    (z / 2 ^ (Z.min (lctz default z) 63)) mod 2 = 0 ->
    Z.min (lctz default z) 63 = 63.
Proof.
    intros Hdef Hz Heven.
    assert (Hlctz_ge : 0 <= lctz default z) by (apply lctz_ge_0; lia).
    assert (Hlctz_cases : lctz default z < 63 \/ 63 <= lctz default z) by lia.
    destruct Hlctz_cases as [Hlt | Hge].
    { rewrite (Z.min_l _ 63) in Heven by lia.
        destruct (lctz_spec default z Hz) as [k [Hk Hz_eq]].
        pattern z at 1 in Heven.
        rewrite Hz_eq in Heven.
        rewrite Z.div_mul in Heven by (apply Z.pow_nonzero; lia).
        rewrite Hk in Heven.
        discriminate. }
    { rewrite (Z.min_r _ 63) by lia.
        reflexivity. }
Qed.

Lemma lctz_ge_1 (default z : Z) :
    0 <= default ->
    z > 0 -> z mod 2 = 0 -> 1 <= lctz default z.
  Proof.
    intros Hdef Hz Heven.
    assert (Hlctz_cases : lctz default z = 0 \/ 1 <= lctz default z).
    { pose proof (lctz_ge_0 default z Hdef). lia. }
    destruct Hlctz_cases as [H0 | Hge]; [|assumption].
    destruct (lctz_spec default z Hz) as [k [Hk Hz_eq]].
    rewrite H0, Z.pow_0_r, Z.mul_1_r in Hz_eq.
    rewrite Hz_eq in Heven. rewrite Hk in Heven. discriminate.
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
                    (((eval a_) mod 2 = 1 /\ (eval b_ mod 2 = 1)) \/ ((eval a_) mod 2 = 1 /\ (eval b_ mod 2 = 0)) \/
                    ((eval a_) mod 2 = 0 /\ (eval b_ mod 2 = 1))) /\
                    (* x, y range invariants *)
                    (if (eval b_ =? 0) then True else (if (andb ((eval a_) mod 2 =? 1) ((eval b_) mod 2 =? 1)) then
                        0 <= 2 * (eval x) <= (3 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_)))) * (eval MOD) /\  0 <= 2 * (eval y) <= (3 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_)))) * (eval MOD) else
                    if (andb ((eval a_) mod 2 =? 1) ((eval b_) mod 2 =? 0)) then
                        0 <= (2^63) * (eval x) <= (2^63 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_))) - 2) * (eval MOD) /\
                        0 <= 2 * (eval y) <= (2 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_))) - 2) * (eval MOD)
                    else
                        0 <= (2^63) * (eval y) <= (2^63 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_))) - 2) * (eval MOD) /\
                        0 <= 2 * (eval x) <= (2 + ((Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval a_) + Z_size (eval b_))) - 2) * (eval MOD)))/\
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
        rewrite <- Z.eqb_eq, H10 in *.
        destruct (eval b =? 0) eqn: Hb0; eauto; destruct (mod2_cases (eval b)) as [Hb | Hb];
        rewrite Z.eqb_eq, Hb in *; cbn [Z.eqb Pos.eqb andb] in *; ssplit; lia.
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
      (* derive from H29 *)
      {
        repeat match goal with
        | [H : context [Z_size ?a] |- _] =>
            assert_fails (assert (0 <= Z_size a <= 256) by assumption);
            assert (0 <= Z_size a <= 256) by
                (split; [ eapply Z_size_nonneg | eapply Z_size_le ]; try lia; keep_length_equations; bigZnWords)
        end.
        destruct (mod2_cases (eval x1)) as [Hxm1 | Hxm1],
            (mod2_cases (eval x2)) as [Hxm2 | Hxm2];
                destruct H28 as [[? ?] | [[? ?] | [? ?]]];
                try lia; rewrite Hxm1, Hxm2 in *;
                cbn [Z.eqb Pos.eqb andb] in *; destruct H29 as [Hcx3 Hcx4];
                remember ((Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))) as k eqn: Heqk;
                assert (Hmod : 0 <= eval MOD < 2^256) by (keep_length_equations; bigZnWords);
                assert (Hk : 0 <= k <= 512) by lia;
                revert Hcx3 Hcx4 Hk Hmod; prune_unused; nia.
      }
      {
        eexists _, _,_,_,_,_; ssplit; repeat straightline.
        {
            split. 1: try ecancel_assumption.
            clear_old_memory_hyps.
            do 4 try split; eauto.
            cbv [x21 x18] in *. clear x18 x21.
            destruct (eval x1 <=? eval x2) eqn:Hcmp; destruct H43 as [Hx1 [ Hx21 [Hx4 Hx34]]];
            rewrite Hx1, Hx21, Hx4, Hx34 in *; subst;
            try clear dependent x11;
            try clear dependent x13;
            try clear dependent x14;
            try clear dependent x15;
            destruct H28 as [ [Hxm1 Hxm2] | [[Hxm1 Hxm2] | [Hxm1 Hxm2]]];
                rewrite Hxm1, Hxm2 in *;
                cbn [Z.eqb Pos.eqb andb] in *;
                match goal with
                | [H : ?a <=? ?b = true, Ha : ?a mod 2 = ?c, Hb : ?b mod 2 = ?d |- _] =>
                    let m := eval cbv in ((d - c) mod 2) in
                        assert (Hdif : (b - a) mod 2 = m) by
                            (
                                Z.push_mod; rewrite Ha, Hb in *; eauto
                            ); clear Hb
                | [H : ?a <=? ?b = false, Ha : ?a mod 2 = ?c, Hb : ?b mod 2 = ?d |- _] =>
                    let m := eval cbv in ((d - c) mod 2) in
                        assert (Hdif : (a - b) mod 2 = m) by
                            (
                                Z.push_mod; rewrite Ha, Hb in *;
                                eauto
                            ); clear Ha
                end;
                (* Simplify lctz and min for odd variables *)
                repeat match goal with
                | [H : context [lctz 64 ?a], H' : ?a mod 2 = 1 |- _] =>
                    progress rewrite (lctz_odd 64 a), Z.min_l, Z.pow_0_r, Z.mul_1_r, Z.sub_diag, Z.mul_0_l, Z.add_0_r in * by lia; rewrite H in *; clear H
                end;
                repeat match goal with
                | [H : context [lctz 64 ?a], H' : 0 <= Z.min (lctz 64 ?a) 63 |- _] => fail 1
                | [H : context [lctz 64 ?a] |- _] =>
                    assert (0 <= Z.min (lctz 64 a) 63) by
                        (eapply Z.min_glb; try eapply lctz_ge_0; lia)
                end;
                repeat match goal with
                | [H : (?a * (2^?b)) = ?c, H' : (?a <= ?c) |- _ ] => fail 1
                | [H : ?a * (2^?b) = ?c |- _] =>
                    assert (a <= c) by (rewrite <- H; eapply le_mul_pow2_r; try lia; try (keep_length_equations; bigZnWords))
                end;
                ssplit; try eauto; try lia;
                try (keep_length_equations; bigZnWords);
                (* Parity constraints *)
                try solve [match goal with
                | [ Ha : (?a mod 2) = _, Hb : (?b mod 2) = _ |- (((?a mod 2) = _) /\ ((?b mod 2) = _)) \/ _] =>
                    intuition
                | [ Ha : (?a mod 2) = _ |- (((?a mod 2) = _) /\ (?b mod 2 = _)) \/ _] =>
                    destruct (mod2_cases b); intuition
                | [ Hb : (?b mod 2) = _ |- (((?a mod 2) = _) /\ (?b mod 2 = _)) \/ _] =>
                    destruct (mod2_cases a); intuition
                end].
                (* GCD goals *)
                all: repeat match goal with
                | [H : Z.gcd _ _ = Z.gcd ?a ?b |- Z.gcd _ _ = Z.gcd ?a ?b] =>
                    rewrite <- H in *; clear H
                | [ H : (?a * (2^?c)) = _ |- Z.gcd ?a _ = Z.gcd _ _] =>
                    rewrite <- (gcd_pow2_l c), -> H by lia; clear H
                | [ H : (?a * (2^?c)) = ?b |- Z.gcd _ ?a = Z.gcd _ _] =>
                    rewrite <- (gcd_pow2_r c), -> H by lia; clear H
                | [ |- Z.gcd (?a - ?b) ?b = Z.gcd ?a ?b] =>
                    rewrite !(Z.gcd_comm _ b), Z.gcd_sub_diag_r;
                    eauto
                | [ |- Z.gcd ?b (?a - ?b) = Z.gcd ?b ?a] =>
                    rewrite Z.gcd_sub_diag_r;
                    eauto
                end.
                (* Mod goals *)
                all: try solve [Z.push_pull_mod; Z.push_mod; rewrite ?H32, ?H33, ?H55, ?H49; Z.push_pull_mod; f_equal; lia].
                all: try solve [
                    eapply mod_pow2_inv with (n := Z.min (lctz 64 (eval x2 - eval x1)) 63); try lia;
                    rewrite <- Z.mul_assoc, (Z.mul_comm (eval b)), Z.mul_assoc;
                    rewrite ?H47; Z.push_mod_step; Z.push_mod_step; rewrite ?H32, ?H33, ?H49; Z.push_pull_mod; f_equal; lia
                ].
                all: try solve [
                    eapply mod_pow2_inv with (n := Z.min (lctz 64 (eval x1)) 63); try lia;
                    Z.push_pull_mod;
                    rewrite Z.mul_sub_distr_r, Z.mul_0_l, <- Z.mul_assoc, (Z.mul_comm (eval b)), Z.mul_assoc;
                    rewrite ?H53;
                    Z.push_mod_step; Z.push_mod_step; rewrite ?H32, ?H33, ?H55; Z.push_pull_mod; eauto
                ].
                all: try solve [
                    eapply mod_pow2_inv with (n := Z.min (lctz 64 (eval x1 - eval x2)) 63); try lia;
                    Z.push_pull_mod; rewrite Z.mul_sub_distr_r, Z.mul_0_l, <- Z.mul_assoc, (Z.mul_comm (eval b)), Z.mul_assoc;
                    rewrite ?H53; Z.push_mod_step; Z.push_mod_step; Z.push_mod_step; rewrite ?H32, ?H33, ?H55; Z.push_pull_mod;
                    f_equal; lia
                ].
                all: try solve [
                    eapply mod_pow2_inv with (n := Z.min (lctz 64 (eval x2)) 63); try lia;
                    Z.push_pull_mod; rewrite <- Z.mul_assoc, (Z.mul_comm (eval b)), Z.mul_assoc;
                    rewrite ?H47; Z.push_mod_step; rewrite ?H32, ?H33, ?H49; Z.push_pull_mod; f_equal; lia
                ].
                all: repeat match goal with
                | [ H : context [ Z.gcd _ _ ] |- _ ] => clear H
                | [ H : context [_ mod (fold_right _ _ ?MOD)] |- _] => clear H
                end.
                all: repeat match goal with
                | [H : context [Z_size ?a] |- _] =>
                    assert_fails (assert (0 <= Z_size a <= 256) by assumption);
                    assert (0 <= Z_size a <= 256) by
                        (split; [ eapply Z_size_nonneg | eapply Z_size_le ]; try lia; keep_length_equations; bigZnWords)
                end.

                2: {
                    assert (Z_size (eval x16) <= Z_size (eval x2)).
                    {
                        destruct (eval x16 =? 0) eqn:Hx16;
                        [ rewrite Z.eqb_eq in Hx16; rewrite Hx16 in *; cbn [Z_size Pos.size]; lia | ].
                        eapply Z.le_trans with (m := Z_size (eval x2 - eval x1));
                        [ rewrite <- H47, Z_size_mul_pow2 | eapply Z_size_sub ]; lia.
                    }
                    lia.
                }
                3: {
                    assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                    lia.
                }
                4: {
                    assert (Z_size (eval x19) <= Z_size (eval x1)).
                    {
                        destruct (eval x19 =? 0) eqn:Hx19;
                        [rewrite Z.eqb_eq in Hx19; rewrite Hx19 in *; cbn [Z_size Pos.size]; lia | ].
                        rewrite <- H53, Z_size_mul_pow2; lia.
                    }
                    assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                    lia.
                }
                5: {
                    assert (Z_size (eval x19) <= Z_size (eval x1)).
                    {
                        destruct (eval x19 =? 0) eqn: Hx19;
                        [ rewrite Z.eqb_eq in Hx19; rewrite Hx19 in *; cbn [Z_size Pos.size]; lia | ].
                        eapply Z.le_trans with (m := Z_size (eval x1 - eval x2));
                        [rewrite <- H53, Z_size_mul_pow2 | eapply Z_size_sub]; lia.
                    }
                    lia.
                }
                6: {
                    assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                    assert (Z_size (eval x16) <= Z_size (eval x2)).
                    {
                        destruct (eval x16 =? 0) eqn:Hx16;
                        [rewrite Z.eqb_eq in Hx16; rewrite Hx16 in *; cbn [Z_size Pos.size]; lia |].
                        rewrite <- H47, Z_size_mul_pow2; lia.
                    }
                    lia.
                }
                7: {
                    assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                    lia.
                }
                (* x,y range invariants *)
                {
                    destruct (eval x16 =? 0) eqn : Hx016; try lia.
                    destruct (mod2_cases (eval x16)) as [Hx16 | Hx16];
                    rewrite Hxm1, Hx16 in *;
                    cbn [Z.eqb andb Pos.eqb] in *; ssplit; try (keep_length_equations; bigZnWords).
                    {
                        assert (Z.min (lctz 64 (eval x2 - eval x1)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x2 - eval x1) / (2^(Z.min (lctz 64 (eval x2 - eval x1)) 63))) with (eval x16);
                              revert Hx16 H47 H; prune_unused; intros; try assumption.
                              eapply Zdiv_unique with (r := 0); try lia.
                        }
                        rewrite H19 in *.
                        eapply bound_OO_to_OE_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))) (X_old := (eval x3)) (Y_old := (eval x4)).
                        1: keep_length_equations; bigZnWords.
                        all: destruct H29.
                        2,3,4: lia.

                        assert (Z_size (eval x16) + 63 = Z_size (eval x2 - eval x1)).
                        {
                            rewrite <- H47. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                    {
                        assert (Z.min (lctz 64 (eval x2 - eval x1)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x2 - eval x1) / (2^(Z.min (lctz 64 (eval x2 - eval x1)) 63))) with (eval x16);
                              revert Hx16 H47 H; prune_unused; intros; try assumption.
                              eapply Zdiv_unique with (r := 0); try lia.
                        }
                        rewrite H19 in *.
                        eapply bound_OO_to_EO_unchanged with (k_old := (Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval x1) + Z_size (eval x2))) (X_old := (eval x4));
                        try lia; try (keep_length_equations; bigZnWords).
                        assert (Z_size (eval x16) + 63 = Z_size (eval x2 - eval x1)).
                        {
                            rewrite <- H47. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                    {
                        eapply bound_OO_to_OO_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))).
                        1: keep_length_equations; bigZnWords.
                        6: eassumption.
                        1,4,5: lia.
                        {
                            eapply Z.min_glb; try lia.
                            eapply lctz_ge_1; lia.
                        }
                        remember (Z.min (lctz 64 (eval x2 - eval x1)) 63) as s.
                        assert (Z_size (eval x16) + s = Z_size (eval x2 - eval x1)).
                        {
                            rewrite <- H47. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                    {
                        destruct H29.
                        eapply bound_OO_to_OO_unchanged with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))) (Y_old := eval x4).
                        1: keep_length_equations; bigZnWords.
                        2,3: lia.
                        remember (Z.min (lctz 64 (eval x2 - eval x1)) 63) as s.
                        assert (Z_size (eval x16) + s = Z_size (eval x2 - eval x1)).
                        {
                            rewrite <- H47. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                }
                {
                    rewrite Hxm1, Hdif in *.
                    cbn [Z.eqb andb Pos.eqb] in *; ssplit; try (keep_length_equations; bigZnWords).
                    destruct (eval x2 - eval x1 =? 0); try eauto.
                    ssplit; try (keep_length_equations; bigZnWords).
                    {
                        destruct H29 as [[? ?] [? ?]]. eapply Z.le_trans with (m := 2 * (eval x3 + eval x4)); try lia.
                        eapply bound_OE_to_OO. 1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]]. eapply Z.le_trans with (m := 2* (eval x4)); try lia.
                        eapply bound_OE_to_OO_unchanged.
                        1: keep_length_equations; bigZnWords.
                        2:eassumption.

                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)).
                        {
                            eapply Z_size_sub; lia.
                        }
                        lia.
                    }
                }
                {
                    destruct (eval x2 - eval x1 =? 0); try eauto.
                    destruct (eval x19 =? 0) eqn: Hx019; try lia.
                    destruct (mod2_cases (eval x19)) as [Hx19 | Hx19]; rewrite Hx19, Hdif in *;
                    cbn [Z.eqb Pos.eqb andb] in *; ssplit; try (keep_length_equations; bigZnWords).
                    {
                        destruct H29 as [[? ?] [? ?]].
                        assert (Z.min (lctz 64 (eval x1)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x1) / (2^(Z.min (lctz 64 (eval x1)) 63))) with (eval x19);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); try lia.
                        }
                        rewrite H31 in *.
                        eapply bound_EO_to_EO_shifted.
                        1: keep_length_equations; bigZnWords.
                        4: eassumption.
                        1,4: lia.
                        1: lia.
                        assert (Z_size (eval x19) + 63 = Z_size (eval x1)).
                        {
                            rewrite <- H53. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?][? ?]].
                        assert (Z.min (lctz 64 (eval x1)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x1) / (2^(Z.min (lctz 64 (eval x1)) 63))) with (eval x19);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); try lia.
                        }
                        rewrite H31 in *.
                        eapply Z.le_trans with (m := 2 * (eval x3 + eval x4)); try lia.
                        eapply bound_EO_to_EO_sum.
                        1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        assert (Z_size (eval x19) + 63 = Z_size (eval x1)).
                        {
                            rewrite <- H53. symmetry. eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]].
                        eapply Z.le_trans with (m := 2 * (eval x3 + eval x4)); try lia.
                        eapply bound_EO_to_OO.
                        1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        remember (Z.min (lctz 64 (eval x1)) 63) as s.
                        assert (Z_size (eval x19) + s = Z_size (eval x1)).
                        {
                            rewrite <- H53. symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]].
                        eapply bound_OE_to_OO_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2)))
                        (X_old := eval x4).
                        1: keep_length_equations; bigZnWords.
                        1: lia.
                        4: eassumption.
                        {
                            eapply Z.min_glb; try lia.
                            eapply lctz_ge_1; try lia.
                        }
                        2: eassumption.
                        remember (Z.min (lctz 64 (eval x1)) 63) as s.
                        assert (Z_size (eval x19) + s = Z_size (eval x1)).
                        {
                            rewrite <- H53. symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x2 - eval x1) <= Z_size (eval x2)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                }
                {
                    destruct (eval x2 =? 0) eqn: Hx2; try eauto.
                    destruct (eval x19 =? 0) eqn: Hx019; try lia.
                    destruct (mod2_cases (eval x19)) as [Hx19 | Hx19]; rewrite Hx19, Hxm2 in *;
                    cbn [Z.eqb Pos.eqb andb] in *; ssplit; try (keep_length_equations; bigZnWords).
                    {
                        destruct H29 as [[? ?] [? ?]].
                        assert (Z.min (lctz 64 (eval x1 - eval x2)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x1 - eval x2) / (2^(Z.min (lctz 64 (eval x1 - eval x2)) 63))) with (eval x19);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); try lia.
                        }
                        rewrite H31 in *.
                        eapply bound_OO_to_OE_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))) (X_old := (eval x3)) (Y_old := (eval x4)).
                        1: keep_length_equations; bigZnWords.
                        2,3,4: lia.
                        assert (Z_size (eval x19) + 63 = Z_size (eval x1 - eval x2)) by (rewrite <- H53; symmetry; eapply Z_size_mul_pow2; lia).
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]].
                        assert (Z.min (lctz 64 (eval x1 - eval x2)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x1 - eval x2) / (2^(Z.min (lctz 64 (eval x1 - eval x2)) 63))) with (eval x19);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); try lia.
                        }

                        rewrite H31 in *.
                        eapply bound_OO_to_EO_unchanged with (k_old := (Z_size (eval a) + (Z_size (eval b))) - (Z_size (eval x1) + Z_size (eval x2))) (X_old := (eval x3));
                        try lia; try (keep_length_equations; bigZnWords).
                        assert (Z_size (eval x19) + 63 = Z_size (eval x1 - eval x2)) by (rewrite <- H53; symmetry; eapply Z_size_mul_pow2; lia).
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29.
                        eapply bound_OO_to_OO_unchanged with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))) (Y_old := eval x3).
                        1: keep_length_equations; bigZnWords.
                        2,3: lia.
                        remember (Z.min (lctz 64 (eval x1 - eval x2)) 63) as s.
                        assert (Z_size (eval x19) + s = Z_size (eval x1 - eval x2)) by (rewrite <- H53; symmetry; eapply Z_size_mul_pow2; lia).
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {

                        eapply bound_OO_to_OO_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2))).
                        1: keep_length_equations; bigZnWords.
                        6: eassumption.
                        1,4,5: lia.
                        {
                            eapply Z.min_glb; try lia.
                            eapply lctz_ge_1; lia.
                        }
                        remember (Z.min (lctz 64 (eval x1 - eval x2)) 63) as s.
                        assert (Z_size (eval x19) + s = Z_size (eval x1 - eval x2)) by (rewrite <- H53; symmetry; eapply Z_size_mul_pow2; lia).
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                }
                {
                    destruct (eval x16 =? 0); try eauto.
                    destruct (mod2_cases (eval x16)) as [Hx16 | Hx16];
                    rewrite Hx16, Hdif in *; cbn [Z.eqb Pos.eqb andb] in *; ssplit; try (keep_length_equations; bigZnWords).
                    {
                        destruct H29 as [[? ?] [? ?]].
                        assert (Z.min (lctz 64 (eval x2)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x2) / (2^(Z.min (lctz 64 (eval x2)) 63))) with (eval x16);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); lia.
                        }
                        rewrite H31 in *.
                        eapply bound_EO_to_EO_shifted.
                        1: keep_length_equations; bigZnWords.
                        4: eassumption.
                        1,4: lia.
                        1: lia.
                        assert (Z_size (eval x16) + 63 = Z_size (eval x2)).
                        {
                            rewrite <- H47; symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?][? ?]].
                        assert (Z.min (lctz 64 (eval x2)) 63 = 63). {
                            eapply lctz_even_min63; try lia.
                            replace ((eval x2) / (2^(Z.min (lctz 64 (eval x2)) 63))) with (eval x16);
                            try assumption.
                            eapply Zdiv_unique with (r := 0); lia.
                        }
                        rewrite H31 in *.
                        eapply Z.le_trans with (m := 2 * (eval x3 + eval x4)); try lia.
                        eapply bound_OE_to_OE_sum.
                        1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        assert (Z_size (eval x16) + 63 = Z_size (eval x2)).
                        {
                            rewrite <- H47; symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]].
                        eapply bound_OE_to_OO_shifted with (k_old := (Z_size (eval a) + Z_size (eval b)) - (Z_size (eval x1) + Z_size (eval x2)))
                        (X_old := eval x3).
                        1: keep_length_equations; bigZnWords.
                        1: lia.
                        4: eassumption.
                        {
                            eapply Z.min_glb; try lia.
                            eapply lctz_ge_1; try lia.
                        }
                        2: eassumption.
                        remember (Z.min (lctz 64 (eval x2)) 63) as s.
                        assert (Z_size (eval x16) + s = Z_size (eval x2)).
                        {
                            rewrite <- H47; symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]].
                        eapply Z.le_trans with (m := 2 * (eval x3 + eval x4)); try lia.
                        eapply bound_OE_to_OO.
                        1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        remember (Z.min (lctz 64 (eval x2)) 63) as s.
                        assert (Z_size (eval x16) + s = Z_size (eval x2)).
                        {
                            rewrite <- H47; symmetry; eapply Z_size_mul_pow2; lia.
                        }
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                }
                {
                    destruct (eval x2 =? 0); try eauto.
                    rewrite Hxm2, Hdif in *.
                    cbn [Z.eqb andb Pos.eqb] in *; ssplit; try (keep_length_equations; bigZnWords);
                    ssplit; try (keep_length_equations; bigZnWords).
                    {
                        destruct H29 as [[? ?] [? ?]]. eapply Z.le_trans with (m := 2 * eval x3); try lia.
                        eapply bound_EO_to_OO_unchanged. 1: keep_length_equations; bigZnWords.
                        2: eassumption.
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                    {
                        destruct H29 as [[? ?] [? ?]]. eapply Z.le_trans with (m := 2* (eval x3 + eval x4)); try lia.
                        eapply bound_EO_to_OO.
                        1: keep_length_equations; bigZnWords.
                        3,4: eassumption.
                        1: lia.
                        assert (Z_size (eval x1 - eval x2) <= Z_size (eval x1)) by (eapply Z_size_sub; lia).
                        lia.
                    }
                }
        }
        {
            eexists; repeat straightline.
            2:
            eexists _,_,_,_; ssplit; try ecancel_assumption; eauto.
            cbv [v x21 x18] in *.

            repeat match goal with
            | [ H : context [lctz 64 ?a] |- _ ] =>
                assert_fails (assert (0 <= Z.min (lctz 64 a) 63) by assumption);
                assert (0 <= Z.min (lctz 64 a) 63) by
                    (eapply Z.min_glb; try eapply lctz_ge_0; lia)
            end;
            repeat match goal with
            | [H : ?a * (2^?b) = ?c |- _] =>
                assert (a <= c) by (rewrite <- H; eapply le_mul_pow2_r; try lia; try (keep_length_equations; bigZnWords)); clear H
            end.
            ssplit.
            1: (keep_length_equations; bigZnWords).

            destruct (eval x1 <=? eval x2) eqn : Hcmp; destruct H43 as [? [? [? ?]]];
            subst; lia.
        }
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

