(** * Context made from an associative list *)
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Compilers.Named.FMapContext.

Module WeakListContext (E : DecidableType).
  Module WL := FMapWeakList.Make E.
  Module Context := FMapContext WL.
  Include Context.
End WeakListContext.
