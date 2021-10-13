Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.

Section Gallina.
  Definition point {field_parameters : FieldParameters} : Type
    := (F M_pos * F M_pos).
End Gallina.

Section Compile.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  (* TODO: uses removed notation.
     Find out whether anything still uses this file
  Lemma compile_point_assign :
    forall (l: locals) (mem: mem)
           (locals_ok : locals -> Prop)
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
       with-locals l and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals l and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.
   *)
End Compile.
