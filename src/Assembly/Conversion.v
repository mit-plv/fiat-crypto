
Require Export Language.

Module Type Conversion (A B: Language).

  Parameter convertProgram: forall (x: A.Params) (y: B.Params),
    A.Program x -> option (B.Program y).
  Parameter convertState: forall (x: A.Params) (y: B.Params),
    B.State y -> option (A.State x).

  Axiom convert_spec: forall pa pb a a' b b' prog prog',
    convertProgram pa pb prog = Some prog' ->
    convertState pa pb a = Some a' ->
    convertState pa pb b = Some b' ->
    A.evaluatesTo pa prog a' b' ->
    B.evaluatesTo pb prog' a b.

End Conversion.
