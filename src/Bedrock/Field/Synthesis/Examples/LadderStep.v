Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Require Import Crypto.Spec.ModularArithmetic.
Definition F := F (2^255 - 19).
Definition a24 : F := F.of_Z _ 121665.

(* Gallina specification *)
Definition ladderstep_gallina
           (X1 : F) (P1 P2 : F * F) : F * F * (F * F) :=
  @MxDH.ladderstep F F.add F.sub F.mul a24 X1 P1 P2.

Existing Instances
         default_parameters default_parameters_ok
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.

Local Notation n := X25519_64.n.
Local Notation s := X25519_64.s.
Local Notation c := X25519_64.c.
Local Notation M := (UnsaturatedSolinas.m s c).
Local Notation word := BasicC64Semantics.word.
Local Notation mem := BasicC64Semantics.mem.
Local Notation weight :=
  (ModOps.weight (QArith_base.Qnum
                    (UnsaturatedSolinasHeuristics.limbwidth n s c))
                 (Z.pos (QArith_base.Qden
                           (UnsaturatedSolinasHeuristics.limbwidth n s c)))).
Local Notation eval := (Positional.eval weight n).
Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

Existing Instances
  curve25519_bedrock2_scmul121665_func
  curve25519_bedrock2_scmul121665_spec
  curve25519_bedrock2_scmul121665_correctness.
Require Import bedrock2.NotationsCustomEntry.

Definition ladderstep : Syntax.func :=
  let mul := "curve25519_carry_mul" in
  let square := "curve25519_carry_square" in
  let add := "curve25519_add" in
  let sub := "curve25519_sub" in
  let scmul121665 := "curve25519_carry_scmul_const121665" in
  ("ladderstep",
   (["X1"; "X2"; "Z2"; "X3"; "Z3";
       "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"], [],
    (* store results back in P1 (X2, Z2) and P2 (X3, Z3) *)
    bedrock_func_body:(
      $add (A, X2, Z2) ;     (* llet A  := X2+Z2 in *)
      $square (AA, A) ;      (* llet AA := A^2 in *)
      $sub (B, X2, Z2) ;     (* llet B  := X2-Z2 in *)
      $square (BB, B) ;      (* llet BB := B^2 in *)
      $sub (E, AA, BB) ;     (* llet E  := AA-BB in *)
      $add (C, X3, Z3) ;     (* llet C  := X3+Z3 in *)
      $sub (D, X3, Z3) ;     (* llet D  := X3-Z3 in *)
      $mul (DA, D, A) ;      (* llet DA := D*A in *)
      $mul (CB, C, B) ;      (* llet CB := C*B in *)
      $add (X3, DA, CB) ;    (* llet X3 := (DA+CB)^2 in *)
      $square (X3, X3) ;
      $sub (Z3, DA, CB) ;    (* llet Z3 := X1*(DA-CB)^2 in *)
      $square (Z3, Z3) ;
      $mul (Z3, X1, Z3) ;
      $mul (X2, AA, BB) ;    (* llet X2 := AA*BB in *)
      $scmul121665 (Z2, E) ; (* llet Z2 := E*(AA + a24*E) in *)
      $add (Z2, AA, Z2) ;
      $mul (Z2, E, Z2)        (* pair4 X2 Z2 X3 Z3 *)
  ))).

Instance spec_of_ladderstep : spec_of ladderstep :=
  fun functions =>
    forall (X1 X2 Z2 X3 Z3 A AA B BB E C D DA CB : list word)
           (pX1 pX2 pZ2 pX3 pZ3
                pA pAA pB pBB pE pC pD pDA pCB : word)
           t m (R : Interface.map.rep (map:=mem) -> Prop),
      (* inputs must be bounded by loose_bounds *)
      let X1z := map word.unsigned X1 in
      let X2z := map word.unsigned X2 in
      let Z2z := map word.unsigned Z2 in
      let X3z := map word.unsigned X3 in
      let Z3z := map word.unsigned Z3 in
      list_Z_bounded_by tight_bounds X1z ->
      list_Z_bounded_by tight_bounds X2z ->
      list_Z_bounded_by tight_bounds Z2z ->
      list_Z_bounded_by tight_bounds X3z ->
      list_Z_bounded_by tight_bounds Z3z ->
      (Bignum n pX1 X1
       * Bignum n pX2 X2
       * Bignum n pZ2 Z2
       * Bignum n pX3 X3
       * Bignum n pZ3 Z3
       * Bignum n pA A
       * Bignum n pAA AA
       * Bignum n pB B
       * Bignum n pBB BB
       * Bignum n pE E
       * Bignum n pC C
       * Bignum n pD D
       * Bignum n pDA DA
       * Bignum n pCB CB)%sep m ->
      WeakestPrecondition.call
        functions ladderstep t m
        [pX1; pX2; pZ2; pX3; pZ3; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
        (fun t' m' rets =>
           t = t' /\
           rets = []%list /\
           exists X4 Z4 X5 Z5 (* output values *)
                  A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
                  : list word,
             let X4z := map word.unsigned X4 in
             let Z4z := map word.unsigned Z4 in
             let X5z := map word.unsigned X5 in
             let Z5z := map word.unsigned Z5 in
             let toF := fun x => F.of_Z (2^255 - 19) (eval x) in
             ladderstep_gallina
               (toF X1z) (toF X2z, toF Z2z) (toF X3z, toF Z3z) =
             ((toF X4z, toF Z4z), (toF X5z, toF Z5z))
             /\ list_Z_bounded_by tight_bounds X4z
             /\ list_Z_bounded_by tight_bounds Z4z
             /\ list_Z_bounded_by tight_bounds X5z
             /\ list_Z_bounded_by tight_bounds Z5z
             /\ (Bignum n pX1 X1
                 * Bignum n pX2 X4
                 * Bignum n pZ2 Z4
                 * Bignum n pX3 X5
                 * Bignum n pZ3 Z5
                 * Bignum n pA A'
                 * Bignum n pAA AA'
                 * Bignum n pB B'
                 * Bignum n pBB BB'
                 * Bignum n pE E'
                 * Bignum n pC C'
                 * Bignum n pD D'
                 * Bignum n pDA DA'
                 * Bignum n pCB CB')%sep m').

Instance spec_of_curve25519_carry_mul :
  spec_of "curve25519_carry_mul" := spec_of_carry_mul.
Instance spec_of_curve25519_carry_square :
  spec_of "curve25519_carry_square" := spec_of_carry_square.
Instance spec_of_curve25519_add :
  spec_of "curve25519_add" := spec_of_add.
Instance spec_of_curve25519_sub :
  spec_of "curve25519_sub" := spec_of_sub.
Instance spec_of_curve25519_carry_scmul_const121665 :
  spec_of "curve25519_carry_scmul_const121665"
  := @spec_of_carry_scmul_const _ curve25519_bedrock2_scmul121665_spec.

Ltac prove_bounds :=
  lazymatch goal with
  | H : list_Z_bounded_by tight_bounds ?x
    |- list_Z_bounded_by loose_bounds ?x =>
    apply UnsaturatedSolinas.relax_valid; apply H
  | H : list_Z_bounded_by ?b ?x |- list_Z_bounded_by ?b ?x =>
    apply H
  end.
Ltac prove_length :=
  match goal with
  | |- length (map _ _) = _ => rewrite ?map_length; assumption
  | |- length _ = X25519_64.n =>
    apply bounded_by_loose_bounds_length
      with (s:=X25519_64.s) (c:=X25519_64.c); prove_bounds
  end.
Ltac prove_preconditions :=
  lazymatch goal with
  | |- length _ = _ => prove_length
  | |- list_Z_bounded_by _ _ => prove_bounds
  end.

(* tactics for solving the final arithmetic equivalence *)
Ltac push_FtoZ :=
  cbv [F.sub];
  repeat first [ rewrite ModularArithmeticTheorems.F.to_Z_add
               | rewrite ModularArithmeticTheorems.F.to_Z_mul
               | rewrite ModularArithmeticTheorems.F.to_Z_opp
               | rewrite ModularArithmeticTheorems.F.of_Z_to_Z
               | rewrite ModularArithmeticTheorems.F.to_Z_of_Z
               ].
Ltac rewrite_field_postconditions :=
  repeat lazymatch goal with
         | H : eval (map word.unsigned ?x) mod M = _
           |- context [map word.unsigned ?x] =>
           autorewrite with push_Zmod in H;
           rewrite H
         end.
Ltac solve_F_eq :=
  apply ModularArithmeticTheorems.F.eq_of_Z_iff;
  push_FtoZ; change (Z.pos (2^255 - 19)) with M; pull_Zmod;
  let LHS := fresh "LHS" in
  match goal with |- ?lhs = _ =>
                  set (LHS := lhs) end;
  rewrite_field_postconditions; pull_Zmod;
  subst LHS; try reflexivity.

Ltac t := repeat straightline; handle_call; [ prove_preconditions .. | ].

Lemma ladderstep_correct :
  program_logic_goal_for_function! ladderstep.
Proof.
  straightline_init_with_change.
  Time
  repeat t.

  (* now prove postcondition *)
  repeat split; try reflexivity.
  repeat lazymatch goal with
         | |- exists _, _ => eexists
         | |- _ /\ _ => split
         end;
    lazymatch goal with
    | |- sep _ _ _ => clear_old_seps; ecancel_assumption
    | _ => idtac
    end.
  all: try prove_bounds.
  cbv [ladderstep_gallina MxDH.ladderstep].
  repeat match goal with
           |- (_ , _) = (_ , _) => apply f_equal2
         end.
  all:solve_F_eq.
Qed.
