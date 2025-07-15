From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import OrderedType.
From Coq Require Import FMapInterface.
From Coq Require Import FMapPositive.
From Coq Require Import NArith.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.FSets.FMapOption.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.OrdersEx.

Local Set Implicit Arguments.

Module OptionPositiveMap <: UsualS := OptionUsualMap PositiveMap.

Module NMap <: UsualS := IsoS OptionPositiveMap NIsoOptionPositiveOrig.
