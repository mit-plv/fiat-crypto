Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Notations.

Infix ">>" := Z.shiftr : Z_scope.
Infix "<<" := Z.shiftl : Z_scope.
Infix "&'" := Z.land : Z_scope.
