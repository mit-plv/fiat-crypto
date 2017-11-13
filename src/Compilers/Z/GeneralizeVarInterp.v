Require Import Coq.ZArith.BinInt.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.GeneralizeVarInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.GeneralizeVar.

Definition InterpGeneralizeVar
           {interp_base_type}
           {interp_op}
      {t} (e : Expr t)
      (Hwf : Wf e)
      e'
      (He' : GeneralizeVar (e _) = Some e')
  : forall v, Compilers.Syntax.Interp (interp_base_type:=interp_base_type) interp_op e' v
              = Compilers.Syntax.Interp interp_op e v
  := @InterpGeneralizeVar
       base_type op base_type_beq internal_base_type_dec_bl
       internal_base_type_dec_lb
       (fun _ t => Op (OpConst 0%Z) TT)
       interp_base_type
       interp_op
       t e Hwf e' He'.
