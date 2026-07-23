From Stdlib Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Require Import bedrock2Examples.full_sub.
From coqutil Require Import Tactics.Tactics WithBaseName.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

(** * Specification *)

#[export] Instance spec_of_u320_sub : spec_of "u320_sub" := 
    fnspec! "u320_sub" (p_r p_x p_y : word) / (x y r : list word) R ~> b,
    {
        requires t m := 
            m =* array p_x x ⋆ array p_y y ⋆ array p_r r ⋆ R /\
            length x = 5%nat /\ length y = 5%nat /\ length r = 5%nat;
        ensures T M := T = t /\ exists (r : list word), 
            M =* array p_x x ⋆ array p_y y ⋆ array p_r r ⋆ R /\
            length r = 5%nat /\ eval r - 2^320*b = eval x - eval y
    }.

(** * Implementation *)
Definition u320_sub := func! (p_r, p_x, p_y) ~> b {
    b = $0;
    unpack! d0, b = br_full_sub(load(p_x) , load(p_y), b);
    unpack! d1, b = br_full_sub(load(p_x + $8), load(p_y + $8) , b);
    unpack! d2, b = br_full_sub(load(p_x + $8 + $8) , load(p_y + $8 + $8) , b);
    unpack! d3, b = br_full_sub(load(p_x + $8 + $8 + $8) , load(p_y + $8 + $8 + $8) , b);
    unpack! d4, b = br_full_sub(load(p_x + $8 + $8 + $8 + $8) , load(p_y + $8 + $8 + $8 + $8) , b);

    store(p_r, d0);
    store(p_r + $8, d1);
    store(p_r + $8 + $8, d2);
    store(p_r + $8 + $8 + $8, d3);
    store(p_r + $8 + $8 + $8 + $8, d4)
}.

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [|x l]; inversion H; clear H end.

Lemma u320_sub_correct : program_logic_goal_for_function! u320_sub.
Proof.
    repeat straightline. lists_into_elements. cbv [array] in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_ ; _ ; _ ; _ ; _]. intuition try ecancel_assumption. cbn [fold_right]. ZnWords.
Qed.

(** * Linking Proof *)
Definition u320_sub_funcs := &[, u320_sub; br_full_sub].

Lemma link_full_sub : spec_of_u320_sub (Interface.map.of_list u320_sub_funcs).
Proof. apply u320_sub_correct; try apply full_sub_ok; trivial. Qed.
