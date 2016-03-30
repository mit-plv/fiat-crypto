
Require Export Language.

Module Type Conversion (A B: Language).

  Parameter convertProgram: A.Program -> option B.Program.
  Parameter convertState: B.State -> option A.State.

  Axiom convert_spec: forall st' prog,
    match ((convertProgram prog), (convertState st')) with
    | (Some prog', Some st) =>
      match (B.eval prog' st') with
      | Some st'' => A.eval prog st = (convertState st'')
      | _ => True
      end
    | _ => True
    end.

End Conversion.
