Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Specs.Field.
Local Open Scope Z_scope.

Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representaton : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_felem_copy
           spec_of_felem_small_literal.
  Hint Resolve relax_bounds : compiler.

  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1: F M_pos) (P1 P2: point)  : (point * point) :=
      let '(X2, Z2) := P1 in
      let '(X3, Z3) := P2 in
      let/d A := X2+Z2 in
      let/d AA := A^2 in
      let/d B := X2-Z2 in
      let/d BB := B^2 in
      let/d E := AA-BB in
      let/d C := X3+Z3 in
      let/d D := X3-Z3 in
      let/d DA := D*A in
      let/d CB := C*B in
      let/d X5 := (DA+CB)^2 in
      let/d Z5 := X1*(DA-CB)^2 in
      let/d X4 := AA*BB in
      let/dZ4 := E*(AA + a24*E) in
      ((X4, Z4), (X5, Z5)).
  End Gallina.

  (* single predicate for all ladderstep end-state information *)
  (* N.B. it's important to leave the associativity of the predicate so that the
     emp is separated from the rest. This way, sepsimpl can easily pull it
     out. If sepsimpl is improved to handle very nested emps, this will not be
     necessary. *)
  Definition LadderStepResult
             (X1 X2 Z2 X3 Z3 : felem)
             (pX1 pX2 pZ2 pX3 pZ3 : Semantics.word)
             (pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
             (result : point * point)
    : list word -> Semantics.mem -> Prop :=
    fun _ =>
      (liftexists X4 Z4 X5 Z5 (* output values *)
                  A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
       : felem,
         (emp (result = ((feval X4, feval Z4), (feval X5, feval Z5))
               /\ bounded_by tight_bounds X4
               /\ bounded_by tight_bounds Z4
               /\ bounded_by tight_bounds X5
               /\ bounded_by tight_bounds Z5)
          * (FElem pX1 X1 * FElem pX2 X4 * FElem pZ2 Z4
             * FElem pX3 X5 * FElem pZ3 Z5
             * FElem pA A' * FElem pAA AA'
             * FElem pB B' * FElem pBB BB'
             * FElem pE E' * FElem pC C' * FElem pD D'
             * FElem pDA DA' * FElem pCB CB'))%sep).

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    forall! (X1 X2 Z2 X3 Z3 : felem)
          (pX1 pX2 pZ2 pX3 pZ3
               pA pAA pB pBB pE pC pD pDA pCB : Semantics.word),
      (fun R m =>
        bounded_by tight_bounds X1
        /\ bounded_by tight_bounds X2
        /\ bounded_by tight_bounds Z2
        /\ bounded_by tight_bounds X3
        /\ bounded_by tight_bounds Z3
        /\ (FElem pX1 X1
            * FElem pX2 X2 * FElem pZ2 Z2
            * FElem pX3 X3 * FElem pZ3 Z3
            * Placeholder pA * Placeholder pAA
            * Placeholder pB * Placeholder pBB
            * Placeholder pE * Placeholder pC
            * Placeholder pD * Placeholder pDA
            * Placeholder pCB * R)%sep m)
        ===>
        "ladderstep" @ [pX1; pX2; pZ2; pX3; pZ3; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
        ===>
        (LadderStepResult
           X1 X2 Z2 X3 Z3 pX1 pX2 pZ2 pX3 pZ3
           pA pAA pB pBB pE pC pD pDA pCB
           (ladderstep_gallina
              (feval X1) (feval X2, feval Z2)
              (feval X3, feval Z3))).

    Lemma compile_ladderstep :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        (locals_ok : Semantics.locals -> Prop)
        tr retvars R R' functions T (pred: T -> _ -> _ -> Prop)
        x1 x2 z2 x3 z3
        X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
        X3 X3_ptr X3_var Z3 Z3_ptr Z3_var
        A_ptr A_var AA_ptr AA_var B_ptr B_var BB_ptr BB_var
        E_ptr E_var C_ptr C_var D_ptr D_var
        DA_ptr DA_var CB_ptr CB_var
        k k_impl,
        spec_of_ladderstep functions ->
        feval X1 = x1 ->
        feval X2 = x2 ->
        feval Z2 = z2 ->
        feval X3 = x3 ->
        feval Z3 = z3 ->
        bounded_by tight_bounds X1 ->
        bounded_by tight_bounds X2 ->
        bounded_by tight_bounds Z2 ->
        bounded_by tight_bounds X3 ->
        bounded_by tight_bounds Z3 ->
        (FElem X1_ptr X1
         * FElem X2_ptr X2 * FElem Z2_ptr Z2
         * FElem X3_ptr X3 * FElem Z3_ptr Z3
         * Placeholder A_ptr * Placeholder AA_ptr
         * Placeholder B_ptr * Placeholder BB_ptr
         * Placeholder E_ptr * Placeholder C_ptr
         * Placeholder D_ptr * Placeholder DA_ptr
         * Placeholder CB_ptr * R')%sep mem ->
        map.get locals X1_var = Some X1_ptr ->
        map.get locals X2_var = Some X2_ptr ->
        map.get locals Z2_var = Some Z2_ptr ->
        map.get locals X3_var = Some X3_ptr ->
        map.get locals Z3_var = Some Z3_ptr ->
        map.get locals A_var = Some A_ptr ->
        map.get locals AA_var = Some AA_ptr ->
        map.get locals B_var = Some B_ptr ->
        map.get locals BB_var = Some BB_ptr ->
        map.get locals E_var = Some E_ptr ->
        map.get locals C_var = Some C_ptr ->
        map.get locals D_var = Some D_ptr ->
        map.get locals DA_var = Some DA_ptr ->
        map.get locals CB_var = Some CB_ptr ->
        let v := ladderstep_gallina x1 (x2, z2) (x3, z3) in
        (let head := v in
         forall m,
           (LadderStepResult
             X1 X2 Z2 X3 Z3 X1_ptr X2_ptr Z2_ptr X3_ptr
             Z3_ptr A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr
             CB_ptr head [] * R')%sep m ->
           (find k_impl
            implementing (pred (k head))
            and-returning retvars
            and-locals-post locals_ok
            with-locals locals
            and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] "ladderstep"
                           [ expr.var X1_var; expr.var X2_var;
                               expr.var Z2_var; expr.var X3_var;
                                 expr.var Z3_var; expr.var A_var;
                                   expr.var AA_var; expr.var B_var;
                                     expr.var BB_var; expr.var E_var;
                                       expr.var C_var; expr.var D_var;
                                         expr.var DA_var; expr.var CB_var ])

                 k_impl)
         implementing (pred (dlet head k))
         and-returning retvars
         and-locals-post locals_ok
         with-locals locals
         and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | sepsimpl ].
      repeat straightline'. subst. eauto.
    Qed.

  Ltac ladderstep_compile_custom :=
    repeat compile_compose_step;
    field_compile_step; [ repeat compile_step .. | ];
    (* if the output we selected was one of the inputs, need to write the
       Placeholder back into a FElem for the arguments precondition *)
    lazymatch goal with
    | |- sep _ _ _ =>
      seprewrite FElem_from_bytes;
      solve [repeat compile_step]
    | _ => idtac
    end;
    [ solve [repeat compile_step] .. | intros ].

  Ltac compile_custom ::= ladderstep_compile_custom.

  Derive ladderstep_body SuchThat
         (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3";
                         "A"; "AA"; "B"; "BB"; "E"; "C";
                           "D"; "DA"; "CB"] in
          let ladderstep := ("ladderstep", (args, [], ladderstep_body)) in
          program_logic_goal_for
            ladderstep
            (ltac:(let x := program_logic_goal_for_function
                              ladderstep [mul;add;sub;square;scmula24] in
                   exact x)))
    As ladderstep_body_correct.
  Proof.
    cbv [program_logic_goal_for spec_of_ladderstep].
    setup.
    repeat safe_compile_step.

    (* by now, we're out of Placeholders; need to decide (manually for now)
       where output gets stored *)
    free pX3; repeat safe_compile_step.
    free pZ3; repeat safe_compile_step.
    free pX2; repeat safe_compile_step.
    free pZ2; repeat safe_compile_step.

    (* sanity-check that compilation is done *)
    lazymatch goal with
    | |- context [dlet.dlet] => fail
    | _ => idtac
    end.

    (* done! now just prove postcondition *)
    compile_done. cbv [LadderStepResult].
    repeat lazymatch goal with
           | |- Lift1Prop.ex1 _ _ => eexists
           | |- sep _ _ _ =>
             first [ progress sepsimpl
                   | ecancel_assumption ]
          end.
    all:lazymatch goal with
        | |- bounded_by _ _ => solve [auto with compiler]
        | _ => idtac
        end.
    congruence.
  Qed.
End __.

Local Coercion expr.var : string >-> Syntax.expr.
Local Unset Printing Coercions.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
