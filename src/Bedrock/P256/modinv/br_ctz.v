From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2Examples.full_sub.
From coqutil Require Import Tactics.Tactics WithBaseName Z.CountTrailingZeros.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

From Coq Require Import ZArith Lia.

Lemma lctz_word_slu (w : word) : (w > 0) -> lctz 64 (word.slu w (word.of_Z 1)) = 1 + lctz 64 w.
Proof.
    intros H. ZnWords_pre.
    replace (2^1) with 2 by lia.
    remember ((w0 * 2) mod 2^64) as a.
    destruct (Z.eq_dec a 0) as [e | ne]; subst.
    { 
        rewrite e. apply Z_div_exact_full_2 in e; try lia.
        assert (w0 * 2 / 2^64 <= 1).
        {
            apply Zlt_succ_le.
            replace (2^64) with (2^63 * 2 ^1) by (rewrite <- Z.pow_add_r; lia).
            replace (2^1) with 2 by lia.
            rewrite Zdiv_mult_cancel_r by lia.
            eapply Z.div_lt_upper_bound; lia.
        }
        assert (0 < w0 * 2 / 2^64) by (eapply Z.div_str_pos; split; lia).
        replace (w0 * 2 / 2^64) with 1 in e by lia.
        replace w0 with (2^63%nat) by lia.
        eauto.
    }
    { 
        subst. replace 64 with (Z.of_nat 64%nat) by lia.
        assert (w0 > 0) by (destruct (Z.eq_dec w0 0); lia).
        rewrite lctz_pos_modpow2 by lia.
        rewrite Z.mul_comm, lctz_pos_double; lia.
    }
Qed.


(** * Specification *)

#[export] Instance spec_of_br_ctz : spec_of "br_ctz" := 
    fnspec! "br_ctz" (value : word) ~> count,
    {
        requires t m := value > 0;
        ensures T M := T = t /\ M = m /\ count = word.of_Z (lctz 64 value)
    }.

(** * Implementation *)
Definition br_ctz := func! (value) ~> count {
    tmp = value;
    count = $0;

    while tmp {
        count = count + $1;
        tmp = tmp << $1
    };
    count = $64 - count
}.

(** * Specification Proof *)
Lemma br_ctz_ok : program_logic_goal_for_function! br_ctz.
Proof.
    repeat straightline.
    refine ((Loops.tailrec
    (* types of ghost variables*) 
        (HList.polymorphic_list.nil)
    (* program variables *) (["value";"count";"tmp"] : list String.string))
    (fun v t m value_ count tmp => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned count /\ word.unsigned tmp = (word.unsigned value * 2^count) mod 2^64 /\ lctz 64 (word.unsigned tmp) = lctz 64 (word.unsigned value) + (word.unsigned count) /\ value = value_)
    (fun T M VALUE COUNT TMP => (* postcondition *)
      T = t /\ M = m /\ 64 = lctz 64 (word.unsigned value) + word.unsigned COUNT))
    (fun n m => m < n <= 64) (* well_founded relation *)
    _ _ _ _ _ ); Loops.loop_simpl.

    { repeat straightline. }
    { eapply Z.gt_wf. }
    { 
        repeat straightline; cbv [count]; ssplit.
        all: intuition try ZnWords.
        rewrite Properties.word.unsigned_of_Z_0, Z.pow_0_r. ZnWords.
    }
    { 
        repeat straightline; try eexists _;
        repeat straightline; ssplit; try split;
        repeat straightline; 
        try match goal with 
            | [H1 : ?x = 0 , H2 : lctz 64 ?x = _ |- _ ] => erewrite H1 in H2
            end; eauto; try ZnWords.
        all: assert (Htmp : lctz 64 tmp = lctz 64 x1 + 1) by (cbv [tmp]; rewrite lctz_word_slu; ZnWords).
        all: assert (0 <= lctz 64 x1 < 64%nat) by (eapply lctz_pos_lt; ZnWords).
        all: assert (0 <= lctz 64 x < 64%nat) by (eapply lctz_pos_lt; ZnWords).
        all: try ZnWords.
        { 
            ZnWords_pre.
            match goal with 
            | [H1 : ?a = (?b * 2^?c) mod ?d |- _] => rewrite H1 by ZnWords
            end.
            rewrite Z.mul_mod_idemp_l by ZnWords.
            f_equal. rewrite_strat bottomup Z.mod_small. 
            all: idtac + rewrite ?Z.pow_add_r; ZnWords.
        }
    }
    { repeat straightline. ZnWords. }
Qed.