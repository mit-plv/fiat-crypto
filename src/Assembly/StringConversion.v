Require Export Qhasm Language Conversion.
Require Export String.

Module QhasmString <: Language.
  Definition Program := string.
  Definition State := unit.

  Definition eval (p: Program) (s: State): option State := Some tt.
End QhasmString.

Module StringConversion <: Conversion Qhasm QhasmString.

  Definition convertState (st: QhasmString.State): option Qhasm.State := None.

  (* TODO (rsloan): Actually implement string conversion *)
  Definition convertProgram (prog: Qhasm.Program): option string :=
    Some EmptyString.

  Lemma convert_spec: forall st' prog,
    match ((convertProgram prog), (convertState st')) with
    | (Some prog', Some st) =>
      match (QhasmString.eval prog' st') with
      | Some st'' => Qhasm.eval prog st = (convertState st'')
      | _ => True
      end
    | _ => True
    end.
  Admitted.

End StringConversion.
