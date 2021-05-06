Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Bedrock.Field.Synthesis.New.Signature.
Require Import Crypto.Language.API.
Import API.Compilers.

Record computed_op
      {p : Types.parameters} {t}
      {op : Pipeline.ErrorT (API.Expr t)}
      {name : String.string}
      {insizes outsizes inlengths}
  :=
  { res : API.Expr t;
    b2_func : func;
    res_eq : op = ErrorT.Success res;
    func_eq :
      b2_func = make_bedrock_func
                  name insizes outsizes inlengths res;
  }.
Global Arguments computed_op {_} {_}.

Ltac make_computed_op :=
  eapply Build_computed_op;
  lazymatch goal with
  | |- _ = ErrorT.Success _ => vm_compute; reflexivity
  | _ => idtac
  end;
  vm_compute; reflexivity.
