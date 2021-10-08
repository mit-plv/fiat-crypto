
Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.SeparationLogicImpl.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Local Open Scope Z_scope.


Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representaton : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.
  
  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1 X2 Z2 X3 Z3: F M_pos) : F M_pos * F M_pos * F M_pos * F M_pos :=
      let/n A := alloc (X2+Z2) in
      let/n AA := alloc (A^2) in
      let/n B := alloc (X2-Z2) in
      let/n BB := alloc (B^2) in
      let/n E := alloc (AA-BB) in
      let/n C := alloc (X3+Z3) in
      let/n D := alloc (X3-Z3) in
      let/n DA := alloc (D*A) in
      let/n CB := alloc (C*B) in
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
      (X2, Z2, X3, Z3).
  End Gallina.

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pZ2 pX3 pZ3 : word)
          / (X1 X2 Z2 X3 Z3 : F M_pos) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
            * FElem (Some tight_bounds) pX2 X2
            * FElem (Some tight_bounds) pZ2 Z2
            * FElem (Some tight_bounds) pX3 X3
            * FElem (Some tight_bounds) pZ3 Z3 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists X4 Z4 X5 Z5 (* output values *)
                  : F M_pos,
          (ladderstep_gallina X1 X2 Z2 X3 Z3
           = (X4, Z4, X5, Z5))
          /\ (FElem (Some tight_bounds) pX1 X1
              * FElem (Some tight_bounds) pX2 X4
              * FElem (Some tight_bounds) pZ2 Z4
              * FElem (Some tight_bounds) pX3 X5
              * FElem (Some tight_bounds) pZ3 Z5 * R)%sep mem'}.

  Lemma compile_ladderstep {tr m l functions}
        (x1 x2 z2 x3 z3 : F M_pos) :
    let v := ladderstep_gallina x1 x2 z2 x3 z3 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1_ptr X1_var X2_ptr X2_var Z2_ptr Z2_var
           X3_ptr X3_var Z3_ptr Z3_var,

      spec_of_ladderstep functions ->

      (FElem (Some tight_bounds) X1_ptr x1
       * FElem (Some tight_bounds) X2_ptr x2 * FElem (Some tight_bounds) Z2_ptr z2
       * FElem (Some tight_bounds) X3_ptr x3 * FElem (Some tight_bounds) Z3_ptr z3 * Rout)%sep m ->

        map.get l X1_var = Some X1_ptr ->
        map.get l X2_var = Some X2_ptr ->
        map.get l Z2_var = Some Z2_ptr ->
        map.get l X3_var = Some X3_ptr ->
        map.get l Z3_var = Some Z3_ptr ->

        (let v := v in
         forall X4 Z4 X5 Z5 (* output values *) m'
                (Heq : ladderstep_gallina x1 x2 z2 x3 z3
                       = (X4, Z4, X5, Z5)),
          (FElem (Some tight_bounds) X1_ptr x1
           * FElem (Some tight_bounds) X2_ptr X4
           * FElem (Some tight_bounds) Z2_ptr Z4
           * FElem (Some tight_bounds) X3_ptr X5
           * FElem (Some tight_bounds) Z3_ptr Z5 * Rout)%sep m' ->
           (<{ Trace := tr;
               Memory := m';
               Locals := l;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->

        <{ Trace := tr;
           Memory := m;
           Locals := l;
           Functions := functions }>
        cmd.seq
          (cmd.call [] "ladderstep"
                    [ expr.var X1_var; expr.var X2_var;
                        expr.var Z2_var; expr.var X3_var;
                          expr.var Z3_var])
          k_impl
        <{ pred (nlet_eq
                   [X2_var; Z2_var; X3_var; Z3_var]
                   v k) }>.
  Proof.
      repeat straightline'.
      handle_call;
        lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => solve [eauto]
        end.
  Qed.
  
  Lemma relax_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some tight_bounds) x_ptr x)
                      (FElem (Some loose_bounds) x_ptr x).
  Proof.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.
  
  Lemma drop_bounds_FElem x_ptr x bounds
    : Lift1Prop.impl1 (FElem bounds x_ptr x)
                      (FElem None x_ptr x).
  Proof.
    unfold FElem.
    intros m H.
    sepsimpl.
    exists x0.
    sepsimpl; simpl in *; eauto using relax_bounds.
  Qed.

  (*TODO: move to pred_sep if deemed useful*)
    Lemma merge_pred_sep A (a : A) R1 R2 pred tr m l
    : pred_sep (R1*R2)%sep pred a tr m l ->
      pred_sep R1 (pred_sep R2 pred) a tr m l.
    Proof.
    unfold pred_sep; simpl.
    unfold Basics.flip; simpl.
    repeat change (fun x => ?h x) with h.
    intros; ecancel_assumption.
    Qed.

    
    Hint Immediate relax_bounds_FElem : ecancel_impl.
    Hint Immediate drop_bounds_FElem : ecancel_impl.


    Ltac ecancel_assumption ::=  ecancel_assumption_impl.

  Ltac ladderstep_compile_custom :=
    try simple apply compile_nlet_as_nlet_eq;
    field_compile_step; [ repeat compile_step .. | intros ];
    eauto with compiler;
    (* rewrite results in terms of feval to match lemmas *)
    repeat lazymatch goal with
           | H : feval _ = ?x |- context [?x] =>
             is_var x; rewrite <-H
           end.

  Ltac compile_custom ::= ladderstep_compile_custom.

  Hint Extern 1 (spec_of _) => (simple refine (@spec_of_BinOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.
  Hint Extern 1 (spec_of _) => (simple refine (@spec_of_UnOp _ _ _ _ _ _ _ _ _ _)) : typeclass_instances.
  
  Derive ladderstep_body SuchThat
         (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3"] in
          ltac:(
            let proc := constr:(("ladderstep",
                                 (args, [], ladderstep_body))
                                : Syntax.func) in
            let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                          proc [mul;add;sub;square;scmula24] in
            exact (__rupicola_program_marker ladderstep_gallina -> goal)))
         As ladderstep_correct.
  Proof. compile. Qed.

End __.

Existing Instance spec_of_ladderstep.

Import Syntax.
Local Unset Printing Coercions.
Set Printing Depth 70.
Print ladderstep_body.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
(*TODO: should I set it back?*)
Set Printing Depth 50.
