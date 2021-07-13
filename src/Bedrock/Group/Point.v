Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.

Section Gallina.
  Definition point {field_parameters : FieldParameters} : Type
    := (F M_pos * F M_pos).
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Lemma compile_point_assign :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R functions T (pred: T -> _ -> _ -> Prop)
      (x y : F M_pos) k k_impl,
      let v := (x, y) in
      (let _ := 0 in (* placeholder *)
       find k_impl
       implementing (pred (dlet x
                                (fun x => dlet y
                                               (fun y => k (x, y)))))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.
End Compile.
