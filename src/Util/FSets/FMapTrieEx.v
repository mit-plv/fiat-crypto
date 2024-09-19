From Coq Require Import OrderedTypeEx.
From Coq Require Import FMapPositive.
From Coq Require Import FMapInterface.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapTrie.
Require Import Crypto.Util.FSets.FMapTrie.ShapeEx.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.FSets.FMapZ.
Require Import Crypto.Util.Structures.OrdersEx.

Module ListPositiveMap <: UsualS := ListUsualMap PositiveMap PositiveMapTrieInd.
Module ListNMap <: UsualS := ListUsualMap NMap NMapTrieInd.
Module ListZMap <: UsualS := ListUsualMap ZMap ZMapTrieInd.
