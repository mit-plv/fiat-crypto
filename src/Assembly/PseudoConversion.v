
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export AlmostQhasm Pseudo State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Vector.

Module PseudoConversion (M: PseudoMachine).
  Import QhasmCommon AlmostQhasm State Util.
  Import ListNotations.

  Module P := Pseudo M.

  Fixpoint take {A} (n: nat) (lst: list A) :=
    match n with
    | O => []
    | S m =>
      match lst with
      | [] => []
      | l :: ls => l :: (take m ls)
      end
    end.

  Module Conv <: Conversion P AlmostQhasm.
    Import P M.

    Definition activeRegisters := 6.
    Definition overflowReg := ireg 6.

    Definition convertState (st: AlmostQhasm.State): P.State :=
      match st with
      | fullState _ stackState _ =>
        take vars (map (fun x => NToWord width (snd x))
                       (NatM.elements stackState))
      end.

    Definition dec_lt (a b: nat): {(a < b)%nat} + {(a >= b)%nat}.
      assert ({(a <? b)%nat = true} + {(a <? b)%nat <> true})
        by abstract (destruct (a <? b)%nat; intuition);
        destruct H.

      - left; abstract (apply Nat.ltb_lt in e; intuition).

      - right; abstract (rewrite Nat.ltb_lt in n; intuition).
    Defined.

    Inductive Mapping :=
      | regM: forall (r: IReg width) (v: nat), v = getIRegIndex r -> Mapping
      | stackM: forall (r: Stack width) (v: nat), v = getStackIndex r -> Mapping.

    Definition natM (x: nat): Mapping.
      refine (
        let N := activeRegisters in
        let r := (ireg x) in
        let s := (stack (x - N)) in

        if (dec_lt x N)
        then (regM r (getIRegIndex r) _)
        else (stackM s (getStackIndex s) _));
      abstract intuition.
    Defined.

    Definition freshN (cur: list nat): nat :=
      let range := (fix f (x: nat) :=
        match x with
        | O => []
        | S x' => cons ((length cur) - x) (f x')
        end) in

      let curRange := (range (length cur)) in

      let notInCur := fun x =>
        negb (proj1_sig (bool_of_sumbool
          (in_dec Nat.eq_dec x cur))) in

      let options := filter notInCur curRange in

      match options with
      | cons x xs => x
      | nil => O (* will never happen. TODO (rsloan): False_rec this *)
      end.

    Fixpoint convertProgram' {n m} (prog: Pseudo n m) (mapping: list nat): option AlmostQhasm.Program :=
      let option_map' := fun x f => option_map f x in
      match prog with
      | PVar n i =>
        option_map' (nth_error mapping n) (fun v =>
          match (natM v) with
          | regM r v _ =>
            AAssign (ARegRegInt width (ireg 0) r)
          | stackM s v _ =>
            AAssign (ARegStackInt width (ireg 0) s)
          end)

      | PConst n c =>
        Some (AAssign (AConstInt width (ireg 0) (iconst c)))

      | PBin n m o a b =>
        option_map' (nth_error mapping n) (fun v =>
          match (natM v) with
          | regM r v _ =>
            AAssign (ARegRegInt width (ireg 0) r)
          | stackM s v _ =>
            AAssign (ARegStackInt width (ireg 0) s)
          end)

      | PNat n o v => None

      | PShift n o a x => None

      | PLet n k m f g => None

      | PComp n k m f g => None

      | PComb n a b f g => None

      | PIf n m o i0 i1 l r => None

      | PFunExp n f e => None

      end.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      AlmostQhasm.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End Conv.
End PseudoConversions.
