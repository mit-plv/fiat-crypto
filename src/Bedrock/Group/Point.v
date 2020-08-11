Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.

Section Gallina.
  Definition point : Type := (Z * Z).
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {bignum_representation : BignumRepresentation}.

  Lemma compile_point_assign :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R functions T (pred: T -> _ -> _ -> Prop)
      (x y : Z) k k_impl,
      let v := (x mod M, y mod M)%Z in
      (let __ := 0 in (* placeholder *)
       find k_impl
       implementing (pred (dlet (x mod M)%Z
                                (fun x => dlet (y mod M)%Z
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
