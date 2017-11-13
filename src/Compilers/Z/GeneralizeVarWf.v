Require Import Coq.ZArith.BinInt.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.GeneralizeVarWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.GeneralizeVar.

Definition Wf_GeneralizeVar
           {t} (e1 : expr base_type op t)
           e'
           (He' : GeneralizeVar e1 = Some e')
  : Wf e'
  := @Wf_GeneralizeVar
       base_type op base_type_beq internal_base_type_dec_bl
       internal_base_type_dec_lb
       (fun _ t => Op (OpConst 0%Z) TT)
       t e1 e' He'.

Definition Wf_GeneralizeVar_arrow
           {s d} (e : expr base_type op (Arrow s d))
           e'
           (He' : GeneralizeVar e = Some e')
  : Wf e'
  := @Wf_GeneralizeVar_arrow
       base_type op base_type_beq internal_base_type_dec_bl
       internal_base_type_dec_lb
       (fun _ t => Op (OpConst 0%Z) TT)
       s d e e' He'.

Hint Resolve Wf_GeneralizeVar Wf_GeneralizeVar_arrow : wf.
