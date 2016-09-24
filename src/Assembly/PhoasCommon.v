Require Export Coq.ZArith.BinInt.
Require Export Coq.NArith.BinNat.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.

Require Export Bedrock.Word Bedrock.Nomega.

Require Export Crypto.Util.GlobalSettings.
Require Export Crypto.Util.Tactics.
Require Export Crypto.Util.Notations.
Require Export Crypto.Tactics.VerdiTactics.

Require Export Crypto.Assembly.Evaluables.

Section Definitions.
  Context {T: Type} {E: Evaluable T}.

  Inductive type := TT | Prod : type -> type -> type.

  Fixpoint interp_type (t:type): Type :=
    match t with
    | TT => T
    | Prod a b => prod (interp_type a) (interp_type b)
    end.

  Inductive binop : type -> type -> type -> Type :=
    | OPadd    : binop TT TT TT
    | OPsub    : binop TT TT TT
    | OPmul    : binop TT TT TT
    | OPand    : binop TT TT TT
    | OPshiftr : binop TT TT TT.
    (* TODO: should [Pair] be a [binop]? *)

  Definition interp_binop {t1 t2 t} (op:binop t1 t2 t) : interp_type t1 -> interp_type t2 -> interp_type t :=
    match op with
    | OPadd    => @eadd T E
    | OPsub    => @esub T E
    | OPmul    => @emul T E
    | OPand    => @eand T E
    | OPshiftr => @eshiftr T E
    end.
End Definitions.
