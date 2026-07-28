From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2.NotationsCustomEntry bedrock2Examples.full_add bedrock2Examples.full_mul bedrock2.ZnWords.
Import coqutil.Tactics.Tactics.
From coqutil Require Import WithBaseName.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** * Specification *)

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

Local Instance spec_of_u320_muladd : spec_of "u320_muladd" := 
    fnspec! "u320_muladd" (p_v p_m c_prime : word) / (v m : list word) R ~> c,
    {
        requires t m' := 
            m' =* array p_v v ⋆ array p_m m ⋆ R 
            /\ length v = 5%nat /\ length m = 4%nat;
        ensures T M := T = t /\ 
            exists (r : list word), M =* array p_v r ⋆ array p_m m ⋆ R /\ length r = 5%nat /\
                2^320 * c + eval r = eval v + c_prime * (eval m) 
    }.

(** * Implementation *)

Definition u320_muladd := func! (p_v, p_m, c_prime) ~> c {
    carry_add = $0;
    carry_mul = $0;

    unpack! lo, hi = br_full_mul (c_prime, load(p_m));
    unpack! s0, carry_add = br_full_add (load(p_v), lo, $0);
    carry_mul = hi;

    unpack! lo, hi = br_full_mul (c_prime, load(p_m + $8));
    unpack! t1, carry_t = br_full_add (lo, carry_mul, $0);
    unpack! s1, carry_add = br_full_add (load(p_v + $8), t1, carry_add);
    carry_mul = hi + carry_t;

    unpack! lo, hi = br_full_mul (c_prime, load(p_m + $8 + $8));
    unpack! t2, carry_t = br_full_add (lo, carry_mul, $0);
    unpack! s2, carry_add = br_full_add (load(p_v + $8 + $8), t2, carry_add);
    carry_mul = hi + carry_t;

    unpack! lo, hi = br_full_mul (c_prime, load(p_m + $8 + $8 + $8));
    unpack! t3, carry_t = br_full_add (lo, carry_mul, $0);
    unpack! s3, carry_add = br_full_add (load(p_v + $8 + $8 + $8), t3, carry_add);
    carry_mul = hi + carry_t;

    unpack! t4, carry_t = br_full_add ($0, carry_mul, $0);
    unpack! s4, carry_add = br_full_add (load(p_v + $8 + $8 + $8 + $8), t4, carry_add);

    store(p_v, s0);
    store(p_v + $8, s1);
    store(p_v + $8 + $8, s2);
    store(p_v + $8 + $8 + $8, s3);
    store(p_v + $8 + $8 + $8 + $8, s4);

    c = carry_t + carry_add
}.

(** * Proof *)

Local Existing Instance spec_of_full_add.
Local Existing Instance spec_of_full_mul.

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [(*nil*)|x l]; inversion H; clear H end.

Lemma lt_word_prod (w1 w2 : word) : w1 * w2 <= (2^64 - 1) * (2^64 - 1).
Proof.
    eapply Zorder.Zmult_le_compat; ZnWords.
Qed.

Lemma u320_muladd_correct : program_logic_goal_for_function! u320_muladd.
Proof. repeat straightline. lists_into_elements. unfold array in *.
        repeat (straightline || straightline_call || ZnWords).
        eexists [_ ; _; _ ; _ ; _ ]. intuition try ecancel_assumption.
        cbn [eval carry_mul carry_mul'2 carry_mul'1 c] in *.
        assert (c_prime * m1 <= (2^64 - 1) * (2^64 - 1)) by 
            (eapply Zorder.Zmult_le_compat; ZnWords).
        assert (c_prime * m2 <= (2^64 - 1) * (2^64 - 1)) by
            (eapply Zorder.Zmult_le_compat; ZnWords).
        assert (c_prime * m3 <= (2^64 - 1) * (2^64 - 1)) by 
            (eapply Zorder.Zmult_le_compat; ZnWords).
        ZnWords.
Qed.

(** * Linking Proof *)
Definition u320_muladd_funcs := &[, u320_muladd; br_full_add; br_full_mul].

Lemma link_full_muladd : spec_of_u320_muladd (Interface.map.of_list u320_muladd_funcs).
Proof. apply u320_muladd_correct; try apply full_add_ok; try apply full_mul_ok; trivial. Qed.
