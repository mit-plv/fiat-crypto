Require Import QhasmEvalCommon QhasmUtil.
Require Import Language.
Require Import List.

Module Type PseudoMachine.
  Parameter width: nat.
  Parameter vars: nat.
  Parameter width_spec: ISize width.
End PseudoMachine.

Module Pseudo (M: PseudoMachine) <: Language.
  Import ListNotations State Util M.

  Definition const: Type := word width.

  Definition width_dec: {width = 32} + {width = 64}.
    destruct width_spec.
    - left; abstract intuition.
    - right; abstract intuition.
  Defined.

  Definition ireg (x: nat): IReg width :=
    match width_spec with
    | I32 => regInt32 x
    | I64 => regInt64 x
    end.

  Definition iconst (x: word width): IConst width.
    refine (
      if width_dec
      then (convert constInt32 _) x
      else (convert constInt64 _) x);
    abstract (rewrite _H; intuition).
  Defined.

  Definition stack (x: nat): Stack width :=
    match width_spec with
    | I32 => stack32 x
    | I64 => stack64 (2 * x)
    end.

  (* Program Types *)
  Definition State := list const.

  Inductive WBinOp: Set :=
    | Wplus: WBinOp    | Wminus: WBinOp   | Wand: WBinOp.

  Inductive WDualOp: Set :=
    | Wmult: WDualOp.

  Inductive WNatOp: Set :=
    | Wones: WNatOp    | Wzeros: WNatOp.

  Inductive WShiftOp: Set :=
    | Wshl: WShiftOp   | Wshr: WShiftOp.

  Inductive Pseudo: nat -> nat -> Type :=
    | PVar: forall n, Index n -> Pseudo n 1
    | PConst: forall n, const -> Pseudo n 1

    | PBin: forall n, WBinOp -> Pseudo n 2 -> Pseudo n 1
    | PNat: forall n, WNatOp -> Index width -> Pseudo n 1
    | PDual: forall n, WDualOp -> Pseudo n 2 -> Pseudo n 2
    | PShift: forall n, WShiftOp -> Index width -> Pseudo n 1 -> Pseudo n 1

    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComp: forall n k m, Pseudo n k -> Pseudo k m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)

    | PIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PFunExp: forall n, Pseudo n n -> nat -> Pseudo n n.

  Hint Constructors Pseudo.

  Definition Program := Pseudo vars vars.

  Definition applyBin (op: WBinOp) (a b: word width): const :=
    match op with
    | Wplus => wplus a b
    | Wminus => wminus a b
    | Wand => wand a b
    end.

  Definition applyDual (op: WDualOp) (a b: word width): list const :=
    match op with
    | Wmult =>
      let wres := natToWord (width + width)
        (N.to_nat ((wordToN a) * (wordToN b))) in
      [split1 _ _ wres; split2 _ _ wres]
    end.

  Definition applyNat (op: WNatOp) (v: Index width): const.
    refine match op with
    | Wones => convert (zext (wones v) (width - v)) _
    | Wzeros => wzero width
    end; abstract (
      destruct v; simpl;
      replace (x + (width - x)) with width;
      intuition ).
  Defined.

  Definition applyShift (op: WShiftOp) (v: const) (n: Index width): const.
    refine match op with
    | Wshl => convert (Word.combine (wzero n) (split1 (width - n) n (convert v _))) _
    | Wshr => convert (Word.combine (split2 n (width - n) (convert v _)) (wzero n)) _
    end; abstract (
      unfold const;
      destruct n; simpl;
      replace (width - x + x) with width;
      replace (x + (width - x)) with width;
      intuition ).
  Defined.

  Fixpoint pseudoEval {n m} (prog: Pseudo n m) (st: State): option State :=
    let option_map' := fun {A B: Type} (x: option A) (f: A -> option B) =>
      match x with
      | Some x' =>
        match (f x') with
        | Some res => Some res
        | None => None
        end
      | _ => None
      end in

    match prog with
    | PVar n i => option_map' (nth_error st i) (fun x => Some [x])
    | PConst n c => Some ([c])
    | PNat n o i => Some [applyNat o i]

    | PBin n o p =>
      option_map' (pseudoEval p st) (fun sp =>
        match sp with
        | [wa; wb] => Some [applyBin o wa wb]
        | _ => None
        end)

    | PDual n o p =>
      option_map' (pseudoEval p st) (fun sp =>
        match sp with
        | [wa; wb] => Some (applyDual o wa wb)
        | _ => None
        end)

    | PShift n o a x =>
      option_map' (pseudoEval x st) (fun sx =>
        match sx with
        | [wx] => Some [applyShift o wx a]
        | _ => None
        end)

    | PLet n k m f g =>
      option_map' (pseudoEval f st) (fun sf =>
        option_map' (pseudoEval g (st ++ sf))
          (fun sg => Some sg))

    | PComp n k m f g => 
      option_map' (pseudoEval f st) (fun sf =>
        option_map' (pseudoEval g sf)
          (fun sg => Some sg))

    | PComb n a b f g =>
      option_map' (pseudoEval f st) (fun sf =>
        option_map' (pseudoEval g st) (fun sg =>
          Some (sf ++ sg)))

    | PIf n m t i0 i1 l r =>
      option_map' (nth_error st i0) (fun v0 =>
        option_map' (nth_error st i1) (fun v1 =>
          if (evalTest t v0 v1)
          then pseudoEval l st
          else pseudoEval r st ))

    | PFunExp n p e =>
      (fix funexpseudo (e': nat) (st': State) := 
        match e' with
        | O => Some st'
        | S e'' =>
          option_map' (pseudoEval p st') (fun st'' =>
            funexpseudo e'' st'')
        end) e st
    end.

  Definition evaluatesTo := fun (p: Program) (st st': State) => (pseudoEval p st = Some st').

  (* world peace *)
End Pseudo.

Module PseudoUnary32 <: PseudoMachine.
  Definition width := 32.
  Definition vars := 1.
  Definition width_spec := I32.
  Definition const: Type := word width.
End PseudoUnary32.

Module PseudoUnary64 <: PseudoMachine.
  Definition width := 64.
  Definition vars := 1.
  Definition width_spec := I64.
  Definition const: Type := word width.
End PseudoUnary64.
 