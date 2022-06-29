Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.NArith.NArith.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.FSets.FMapOption.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.OrdersEx.

Local Set Implicit Arguments.

Module OptionPositiveMap <: UsualS := OptionUsualMap PositiveMap.

Module NMap <: UsualS := IsoS OptionPositiveMap NIsoOptionPositiveOrig.
