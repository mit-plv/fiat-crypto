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

  Lemma compile_sctestbit {tr mem locals functions} x i:
    let v := Z.testbit (F.to_Z (sceval x)) (Z.of_nat i) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R x_ptr x_var wi i_var out_var,

      spec_of_sctestbit functions ->
      (Scalar x_ptr x * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      map.get locals i_var = Some wi ->
      word.unsigned wi = Z.of_nat i ->

      (let v := v in
       forall m,
         (Scalar x_ptr x * R)%sep m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var
                               (word.of_Z (Z.b2z v));
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [out_var] sctestbit [expr.var x_var; expr.var i_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
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
