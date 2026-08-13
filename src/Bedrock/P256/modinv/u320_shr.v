From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic.
Require Import bedrock2.NotationsCustomEntry bedrock2.ZnWords Coq.ZArith.ZArith Lia.
From coqutil Require Import WithBaseName.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** * Specification *)

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation eval_bool := (fold_right (fun (a : word) (s : Z) => Z.lor a (Z.shiftl s 64)) 0).
Local Notation array := (array scalar (word.of_Z 8)).

#[export] Instance spec_of_u320_shr : spec_of "u320_shr" := 
fnspec! "u320_shr" (p_x carry shift : word) / (x r : list word) (s : word) R,
{
    requires t m := 
        m =* array p_x x ⋆ R /\
            length x = 5%nat /\ length r = 5%nat /\ 
            0%nat < shift < 64%nat /\ carry < 2;
    ensures T M := 
        T = t /\ exists (r : list word) , M =* array p_x r ⋆ R /\
            length r = 5%nat /\ eval r = Z.shiftr (eval (x ++ [carry])) shift
}.

(** * Implementation *)

Definition u320_shr := func! (p_x, carry, shift) 
{
    sr0 = load(p_x) >> shift | load(p_x + $8) << ($64 - shift);
    sr1 = load(p_x + $8) >> shift | load(p_x + $8 + $8) << ($64 - shift);
    sr2 = load(p_x + $8 + $8) >> shift | load(p_x + $8 + $8 + $8) << ($64 - shift);
    sr3 = load(p_x + $8 + $8 + $8) >> shift | load(p_x + $8 + $8 + $8 + $8) << ($64 - shift);
    sr4 = (load(p_x + $8 + $8 + $8 + $8) >> shift) | (carry << ($64 - shift));

    store(p_x, sr0);
    store(p_x + $8, sr1);
    store(p_x + $8 + $8, sr2);
    store(p_x + $8 + $8 + $8, sr3);
    store(p_x + $8 + $8 + $8 + $8, sr4)
}.

(** * Proof *)

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [(*nil*)|x l]; inversion H; clear H end.

Lemma eval_eval_bool (w : list word) : eval w = eval_bool w.
Proof.
    induction w; trivial.
    unfold fold_right. fold (eval w).
    fold (eval_bool w).
    rewrite IHw, Z.shiftl_mul_pow2 by lia.
    rewrite BitOps.or_to_plus; try lia.
    rewrite <-Z.shiftl_mul_pow2 by lia.
    apply Z.bits_inj'; intros.
    rewrite ?Z.land_spec.
    rewrite ?bitblast.Z.shiftl_spec'.
    rewrite Z.bits_0.
    destruct (Z_lt_le_dec n 64).
    - rewrite (Z.testbit_neg_r _ (n - 64)) by ZnWords.
      rewrite ?Bool.andb_false_r. trivial.
    - rewrite (@prove_Zeq_bitwise.testbit_above 64 a) by ZnWords.
      trivial.
Qed.
    

Lemma u320_shr_correct : program_logic_goal_for_function! u320_shr.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_ ; _; _; _; _]. intuition try ecancel_assumption.
    rewrite !eval_eval_bool.
    cbv [fold_right v sr1 sr2 sr3 sr4 app].

    (* Arithmetic proof starts here *)
    repeat rewrite !word.unsigned_or, !word.unsigned_slu, !word.unsigned_sub, !word.unsigned_sru, !word.unsigned_of_Z by ZnWords.
    cbv [word.wrap].
    rewrite Z.shiftl_0_l, !Z.lor_0_r.
    rewrite !(Z.mod_small 64), !(Z.mod_small (64 - shift)) by lia.

    apply Z.bits_inj'; intros; 
    repeat rewrite
    <-?Z.shiftr_div_pow2, ?Z.testbit_mod_pow2,
    ?bitblast.Z.shiftr_spec', ?bitblast.Z.shiftl_spec', ?Z.land_spec, ?Z.lor_spec,
    ?Z.testbit_mod_pow2
    by (lia || ZnWords).

    repeat (trivial; case Z.ltb_spec; intros; try lia;
    repeat rewrite
      ?Z.add_sub_swap,
      ?Z.sub_sub_distr,
      ?Z.add_sub_assoc,
      ?Bool.andb_true_r, ?Bool.andb_true_l,
      ?Bool.andb_false_r, ?Bool.andb_false_l,
      ?Bool.orb_true_r, ?Bool.orb_true_l,
      ?Bool.orb_false_r, ?Bool.orb_false_l;
    repeat match goal with |- context [Z.testbit ?a ?b] => rewrite (Z.testbit_neg_r a b) by ZnWords end;
    repeat match goal with |- context [Z.testbit ?a ?b] => rewrite (@prove_Zeq_bitwise.testbit_above 64 a) by ZnWords end;
    repeat match goal with |- context [Z.testbit ?a ?b] => rewrite (@prove_Zeq_bitwise.testbit_above 1 a) by ZnWords end).
Qed.
