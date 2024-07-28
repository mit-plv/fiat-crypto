From Coq Require Import FMapInterface.
From Coq Require Import Equalities.
From Coq Require Import Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Orders.

Module Type UsualWS <: WS.
  Declare Module E : UsualDecidableTypeOrig.
  Include WSfun E.
End UsualWS.

Module Type UsualS <: S.
  Declare Module E : UsualOrderedTypeOrig.
  Include Sfun E.
End UsualS.
