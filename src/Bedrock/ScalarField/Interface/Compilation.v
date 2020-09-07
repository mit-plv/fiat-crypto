Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {scalar_field_parameters : ScalarFieldParameters}.
  Context {scalar_representaton : ScalarRepresentation}.
  Existing Instance spec_of_sctestbit.

  Lemma compile_sctestbit :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R R' functions
           T (pred: T -> list word -> Semantics.mem -> Prop)
      x x_ptr x_var i wi i_var k k_impl var,
      spec_of_sctestbit functions ->
      (Scalar x_ptr x * R')%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals i_var = Some wi ->
      word.unsigned wi = Z.of_nat i ->
      let v := Z.testbit (F.to_Z (sceval x)) (Z.of_nat i) in
      (let head := v in
       forall m,
         (Scalar x_ptr x * R')%sep m ->
         (find k_impl
          implementing (pred (k head))
          and-returning retvars
          and-locals-post locals_ok
          with-locals (map.put locals var (word.of_Z (Z.b2z head)))
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [var] sctestbit [expr.var x_var; expr.var i_var])
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    handle_call; [ solve [eauto] ..
                 | cbv [dlet.dlet] in *|-; sepsimpl ].
    cbn [length] in *. destruct_lists_of_known_length.
    subst_lets_in_goal. subst.
    match goal with H : word.unsigned _ = Z.of_nat _ |- _ =>
                    rewrite H in *
    end.
    repeat straightline'; eauto.
  Qed.
End Compile.

Ltac scfield_compile_step := simple eapply compile_sctestbit.
