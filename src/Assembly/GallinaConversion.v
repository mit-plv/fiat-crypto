
Require Export Language Conversion.
Require Export AlmostQhasm QhasmCommon.
Require Export Bedrock.Word.
Require Export List.
Require Vector.

Module Type GallinaFunction <: Language.
  Parameter len: nat.
  Definition Vec := Vector.t (word 32) len.

  Definition Program := Vec -> Vec.
  Definition State := Vec.

  Definition eval (p: Program) (s: Vec) := Some (p s).
End GallinaFunction.

Module GallinaConversion (S: GallinaFunction) <: Conversion S AlmostQhasm.
  Import QhasmCommon AlmostQhasm.
  Import ListNotations.
  Import S.

  Fixpoint convertState' (st: AlmostQhasm.State) (rem: nat): list (word 32) :=
    match rem with
    | O => []
    | S m =>
      match (getStack (stack32 rem) st) with
      | Some e => e
      | None => (wzero 32) 
      end :: (convertState' st m)
    end.

  Lemma convertState'_len: forall st rem, length (convertState' st rem) = rem.
  Proof.
    intros; induction rem; simpl; intuition.
  Qed.

  Definition convertState (st: AlmostQhasm.State): option S.State.
    unfold State, Vec.
    replace len with (length (convertState' st len))
      by abstract (apply convertState'_len).
    refine (Some (Vector.of_list (convertState' st len))).
  Defined.

  (* TODO (rsloan): implement conversion *)
  Definition convertProgram (prog: S.Program): option AlmostQhasm.Program :=
    Some ASkip.

  Lemma convert_spec: forall st' prog,
    match ((convertProgram prog), (convertState st')) with
    | (Some prog', Some st) =>
      match (AlmostQhasm.eval prog' st') with
      | Some st'' => S.eval prog st = (convertState st'')
      | _ => True
      end
    | _ => True
    end.
  Admitted.

End GallinaConversion.
