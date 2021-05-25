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
  Hint Resolve relax_bounds : compiler.

  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1: F M_pos) (P1 P2: point)  : (point * point) :=
      let '(X2, Z2) := P1 in
      let '(X3, Z3) := P2 in
      let/n A := X2+Z2 in
      let/n AA := A^2 in
      let/n B := X2-Z2 in
      let/n BB := B^2 in
      let/n E := AA-BB in
      let/n C := X3+Z3 in
      let/n D := X3-Z3 in
      let/n DA := D*A in
      let/n CB := C*B in
      (* store X5 under X3 pointer *)
      let/n X3 := (DA+CB) in
      let/n X3 := X3^2 in
      (* store Z5 under Z3 pointer *)
      let/n Z3 := (DA-CB) in
      let/n Z3 := Z3^2 in
      let/n Z3 := X1*Z3 in
      (* store X4 under X2 pointer *)
      let/n X2 := AA*BB in
      (* store Z4 under Z2 pointer *)
      let/n Z2 := a24*E in
      let/n Z2:= (AA+Z2) in
      let/n Z2 := E*Z2 in
      (* ((X4, Z4), (X5, Z5)) *)
      ((X2, Z2), (X3, Z3)).
  End Gallina.

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pZ2 pX3 pZ3
               pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
          / (X1 X2 Z2 X3 Z3 A AA B BB E C D DA CB : felem) R,
    { requires tr mem :=
        bounded_by tight_bounds X1
        /\ bounded_by tight_bounds X2
        /\ bounded_by tight_bounds Z2
        /\ bounded_by tight_bounds X3
        /\ bounded_by tight_bounds Z3
        /\ (FElem pX1 X1
            * FElem pX2 X2 * FElem pZ2 Z2
            * FElem pX3 X3 * FElem pZ3 Z3
            * FElem pA A * FElem pAA AA
            * FElem pB B * FElem pBB BB
            * FElem pE E * FElem pC C
            * FElem pD D * FElem pDA DA
            * FElem pCB CB * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists X4 Z4 X5 Z5 (* output values *)
               A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
               : felem,
          (ladderstep_gallina
             (feval X1) (feval X2, feval Z2)
             (feval X3, feval Z3)
           = ((feval X4, feval Z4), (feval X5, feval Z5)))
          /\ bounded_by tight_bounds X4
          /\ bounded_by tight_bounds Z4
          /\ bounded_by tight_bounds X5
          /\ bounded_by tight_bounds Z5
          /\ (FElem pX1 X1 * FElem pX2 X4 * FElem pZ2 Z4
              * FElem pX3 X5 * FElem pZ3 Z5
              * FElem pA A' * FElem pAA AA'
              * FElem pB B' * FElem pBB BB'
              * FElem pE E' * FElem pC C' * FElem pD D'
              * FElem pDA DA' * FElem pCB CB' * R)%sep mem'}.

  Lemma compile_ladderstep {tr mem locals functions}
        (x1 x2 z2 x3 z3 : F M_pos) :
    let v := ladderstep_gallina x1 (x2, z2) (x3, z3) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
           X3 X3_ptr X3_var Z3 Z3_ptr Z3_var
           A A_ptr A_var AA AA_ptr AA_var
           B B_ptr B_var BB BB_ptr BB_var
           E E_ptr E_var C C_ptr C_var
           D D_ptr D_var DA DA_ptr DA_var
           CB CB_ptr CB_var,

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
       * FElem A_ptr A * FElem AA_ptr AA
       * FElem B_ptr B * FElem BB_ptr BB
       * FElem E_ptr E * FElem C_ptr C
       * FElem D_ptr D * FElem DA_ptr DA
       * FElem CB_ptr CB * Rout)%sep mem ->

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

        (let v := v in
         forall (X4 Z4 X5 Z5 (* output values *)
                    A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
                 : felem) m
                (Heq : ladderstep_gallina
                         (feval X1) (feval X2, feval Z2)
                         (feval X3, feval Z3)
                       = ((feval X4, feval Z4), (feval X5, feval Z5))),
          bounded_by tight_bounds X4 ->
          bounded_by tight_bounds Z4 ->
          bounded_by tight_bounds X5 ->
          bounded_by tight_bounds Z5 ->
          (FElem X1_ptr X1 * FElem X2_ptr X4 * FElem Z2_ptr Z4
           * FElem X3_ptr X5 * FElem Z3_ptr Z5
           * FElem A_ptr A' * FElem AA_ptr AA'
           * FElem B_ptr B' * FElem BB_ptr BB'
           * FElem E_ptr E' * FElem C_ptr C' * FElem D_ptr D'
           * FElem DA_ptr DA' * FElem CB_ptr CB' * Rout)%sep m ->
           (<{ Trace := tr;
               Memory := m;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.call [] "ladderstep"
                    [ expr.var X1_var; expr.var X2_var;
                        expr.var Z2_var; expr.var X3_var;
                          expr.var Z3_var; expr.var A_var;
                            expr.var AA_var; expr.var B_var;
                              expr.var BB_var; expr.var E_var;
                                expr.var C_var; expr.var D_var;
                                  expr.var DA_var; expr.var CB_var ])
          k_impl
        <{ pred (nlet_eq
                   [X1_var; X2_var; Z2_var; X3_var; Z3_var]
                   v k) }>.
    Proof.
      repeat straightline'.
      handle_call;
        lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => solve [eauto]
        end.
    Qed.

  Ltac ladderstep_compile_custom :=
    simple apply compile_nlet_as_nlet_eq;
    field_compile_step; [ repeat compile_step .. | intros ];
    eauto with compiler;
    (* rewrite results in terms of feval to match lemmas *)
    repeat lazymatch goal with
           | H : feval _ = ?x |- context [?x] =>
             is_var x; rewrite <-H
           end.

  Ltac compile_custom ::= ladderstep_compile_custom.

  Derive ladderstep_body SuchThat
         (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3";
                         "A"; "AA"; "B"; "BB"; "E"; "C";
                         "D"; "DA"; "CB"] in
          ltac:(
            let proc := constr:(("ladderstep",
                                 (args, [], ladderstep_body))
                                : Syntax.func) in
            let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                          proc [mul;add;sub;square;scmula24] in
            exact (__rupicola_program_marker ladderstep_gallina -> goal)))
         As ladderstep_correct.
  Proof.
    compile_setup.

    repeat compile_step.
  Qed.
End __.

Existing Instance spec_of_ladderstep.

Local Coercion expr.var : string >-> Syntax.expr.
Local Unset Printing Coercions.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
