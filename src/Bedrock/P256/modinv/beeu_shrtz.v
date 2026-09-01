From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
From coqutil Require Import Tactics.Tactics WithBaseName.
From coqutil Require Import CountTrailingZeros.
Local Open Scope string_scope. Local Open Scope Z_scope.
Require Import br_ctz u320_muladd u320_shr.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

(** * Specification *)

#[local] Instance spec_of_u256_shr : spec_of "u256_shr" :=
fnspec! "u320_shr" (p_x shift : word) / (x : list word) (s : word) R,
{
    requires t m :=
        m =* array p_x x ⋆ R /\
            length x = 4%nat /\
            0%nat < shift < 64%nat;
    ensures T M :=
        T = t /\ exists (r : list word) , M =* array p_x r ⋆ R /\
            length r = 4%nat /\ eval r = Z.shiftr (eval x) shift
}.


#[export] Instance spec_of_beeu_shrtz : spec_of "beeu_shrtz" :=
    fnspec! "u320_sub" (p_a p_y p_m inv_m : word) / (a y MOD : list word) R,
    {
        requires t m :=
            m =* array p_a a ⋆ array p_y y ⋆ array p_m MOD ⋆ R /\
            (eval MOD) mod 2 = 1 /\ inv_m * (eval MOD) mod (2^64) = 2^64 - 1 /\
            length a = 4%nat /\ length y = 5%nat /\ length MOD = 4%nat;
        ensures T M := T = t /\ exists (a' y' : list word) (s : Z),
            M =* array p_a a' ⋆ array p_y y' ⋆ array p_m MOD ⋆ R /\
            length a' = 4%nat /\ length y' = 5%nat /\
            (eval a' * (2^s) = eval a) /\ (s = Z.min (lctz 64 (eval a)) 63) /\
            (eval y' * (2^s) mod (eval MOD) = eval y mod (eval MOD)) /\
            (eval y' * (2^s) <= (eval y + (2^s - 1) * (eval MOD)))
    }.

(** * Implementation *)
Definition beeu_shrtz := func! (p_a, p_y, p_m, inv_m) {
    unpack! shift = br_ctz(load(p_a) | ($1 << $63));

    if $0 < shift {
        u256_shr(p_a, shift);
        mask = ($1 << shift) - $1;
        c_prime = (load(p_y) * inv_m) & mask;
        unpack! carry = u320_muladd(p_y, p_m, c_prime);
        u320_shr(p_y, shift, carry)
    }
}.

Lemma beeu_shrtz_ok : program_logic_goal_for_function! beeu_shrtz.
Proof.
    repeat straightline.

