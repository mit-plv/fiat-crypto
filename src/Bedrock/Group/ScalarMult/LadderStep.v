Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Specs.Field.
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

  Section Gallina.
    Local Open Scope F_scope.

    Definition ladderstep_gallina
               (X1 X2 Z2 X3 Z3: F M_pos) : F M_pos * F M_pos * F M_pos * F M_pos :=
      let/n A := felem_alloc (X2+Z2) in
      let/n AA := felem_alloc (A^2) in
      let/n B := felem_alloc (X2-Z2) in
      let/n BB := felem_alloc (B^2) in
      let/n E := felem_alloc (AA-BB) in
      let/n C := felem_alloc (X3+Z3) in
      let/n D := felem_alloc (X3-Z3) in
      let/n DA := felem_alloc (D*A) in
      let/n CB := felem_alloc (C*B) in
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
          (pX1 pX2 pZ2 pX3 pZ3 : Semantics.word)
          / (X1 X2 Z2 X3 Z3 : felem) R,
    { requires tr mem :=
        bounded_by tight_bounds X1
        /\ bounded_by tight_bounds X2
        /\ bounded_by tight_bounds Z2
        /\ bounded_by tight_bounds X3
        /\ bounded_by tight_bounds Z3
        /\ (FElem pX1 X1
            * FElem pX2 X2 * FElem pZ2 Z2
            * FElem pX3 X3 * FElem pZ3 Z3 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists X4 Z4 X5 Z5 (* output values *)
                  : felem,
          (ladderstep_gallina
             (feval X1) (feval X2) (feval Z2)
             (feval X3) (feval Z3)
           = (feval X4, feval Z4, feval X5, feval Z5))
          /\ bounded_by tight_bounds X4
          /\ bounded_by tight_bounds Z4
          /\ bounded_by tight_bounds X5
          /\ bounded_by tight_bounds Z5
          /\ (FElem pX1 X1 * FElem pX2 X4 * FElem pZ2 Z4
              * FElem pX3 X5 * FElem pZ3 Z5 * R)%sep mem'}.

  Lemma compile_ladderstep {tr mem locals functions}
        (x1 x2 z2 x3 z3 : F M_pos) :
    let v := ladderstep_gallina x1 x2 z2 x3 z3 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
           X3 X3_ptr X3_var Z3 Z3_ptr Z3_var,

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
       * FElem X3_ptr X3 * FElem Z3_ptr Z3 * Rout)%sep mem ->

        map.get locals X1_var = Some X1_ptr ->
        map.get locals X2_var = Some X2_ptr ->
        map.get locals Z2_var = Some Z2_ptr ->
        map.get locals X3_var = Some X3_ptr ->
        map.get locals Z3_var = Some Z3_ptr ->

        (let v := v in
         forall (X4 Z4 X5 Z5 (* output values *)
                 : felem) m
                (Heq : ladderstep_gallina
                         (feval X1) (feval X2) (feval Z2)
                         (feval X3) (feval Z3)
                       = (feval X4, feval Z4, feval X5, feval Z5)),
          bounded_by tight_bounds X4 ->
          bounded_by tight_bounds Z4 ->
          bounded_by tight_bounds X5 ->
          bounded_by tight_bounds Z5 ->
          (FElem X1_ptr X1 * FElem X2_ptr X4 * FElem Z2_ptr Z4
           * FElem X3_ptr X5 * FElem Z3_ptr Z5 * Rout)%sep m ->
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
         (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3"] in
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
  {
    unfold pred_sep; simpl.
    unfold Basics.flip; simpl.
    repeat change (fun x => ?h x) with h.
    unfold map.getmany_of_list.
    simpl.
    {
      eapply Proper_sep_impl1;
        [ eapply FElem_to_bytes | | ecancel_assumption].
      clear H29 m16.
      repeat (intros m16 H29;
      eapply Proper_sep_impl1;
        [ eapply FElem_to_bytes | | ecancel_assumption];
        clear H29 m16).
      intros m16 H29.
      exists [].
      repeat compile_step.
      do 4 eexists.
      intuition.
      ecancel_assumption.
    }
  }
Qed.
  
  
End __.

Existing Instance spec_of_ladderstep.

Import Syntax.
Local Unset Printing Coercions.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
