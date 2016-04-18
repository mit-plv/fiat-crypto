
Require Export Language.

Module Type Conversion (A B: Language).

  Parameter convertProgram: A.Program -> option B.Program.
  Parameter convertState: B.State -> option A.State.

  Axiom convert_spec: forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    B.evaluatesTo prog' a b <-> A.evaluatesTo prog a' b'.

End Conversion.
