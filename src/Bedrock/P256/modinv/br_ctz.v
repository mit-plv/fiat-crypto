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
    intros H.
    rewrite Properties.word.unsigned_slu_shamtZ by lia.
    cbv [word.wrap].
    rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
    match goal with |- context [lctz _ ?x] => destr (x =? 0) end.
    { pose proof (Properties.word.unsigned_range w).
        apply Z.mod_divide in E; [|lia].
        destruct E.
        replace (word.unsigned w) with (2^63) by lia.
        reflexivity. }
    { rewrite lctz_eq_mod_pow2 with (n := 64%nat) by lia.
        rewrite Z.mul_comm, lctz_double by lia.
        reflexivity. }
Qed.

Lemma word_lctz_range (w : word) : 0 <= lctz 64 w <= 64%nat.
Proof.
    destruct (word.eqb w (word.of_Z 0)) eqn: Heq.
    {
        eapply Properties.word.eqb_true in Heq. rewrite Heq in *; 
        simpl; lia.
    }
    {
        eapply Properties.word.eqb_false in Heq. 
        pose proof (lctz_range 64 w 64).
        ZnWords.
    }
Qed.



(** * Specification *)

#[export] Instance spec_of_br_ctz : spec_of "br_ctz" := 
    fnspec! "br_ctz" (value : word) ~> count,
    {
        requires t m := True;
        ensures T M := T = t /\ M = m /\ word.unsigned count = (lctz 64 value)
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
      (
        v = word.unsigned count /\ word.unsigned tmp = (word.unsigned value * 2^count) mod 2^64 /\ 
      lctz 64 (word.unsigned tmp) = lctz 64 (word.unsigned value) + (word.unsigned count) /\ value = value_)
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
        all: assert (0 <= lctz 64 x1 < 64%nat) by (eapply lctz_range; ZnWords).
        all: assert (0 <= lctz 64 x < 64%nat) by (eapply lctz_range; ZnWords).
        all: try ZnWords.
        ZnWords_pre.
        match goal with 
        | [H1 : ?a = (?b * 2^?c) mod ?d |- _] => rewrite H1 by ZnWords
        end.
        rewrite Z.mul_mod_idemp_l by ZnWords.
        f_equal. rewrite_strat bottomup Z.mod_small. 
        all: idtac + rewrite ?Z.pow_add_r; ZnWords.
    }
    { repeat straightline. pose proof (word_lctz_range value). ZnWords. }
Qed.

