Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.FSets.FMapFlip.
Require Import Crypto.Util.FSets.FMapSum.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.OrdersEx.

Local Set Implicit Arguments.

Module NegativeMap <: UsualS := FlipUsualMap PositiveMap.
Module SumNegNMap <: UsualS := SumUsualMap NegativeMap NMap.

Module ZMap <: UsualS := IsoS SumNegNMap ZIsoSumNegNOrig.
