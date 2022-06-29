Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapTrie.
Require Import Crypto.Util.FSets.FMapTrie.ShapeEx.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.FSets.FMapZ.
Require Import Crypto.Util.Structures.OrdersEx.

Module ListPositiveMap <: UsualS := ListUsualMap PositiveMap PositiveMapTrieInd.
Module ListNMap <: UsualS := ListUsualMap NMap NMapTrieInd.
Module ListZMap <: UsualS := ListUsualMap ZMap ZMapTrieInd.
