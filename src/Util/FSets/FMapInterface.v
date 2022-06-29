Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
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
