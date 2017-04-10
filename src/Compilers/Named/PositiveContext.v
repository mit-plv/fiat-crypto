Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Compilers.Named.FMapContext.

Module PositiveContext := FMapContext PositiveMap.
Notation PositiveContext := PositiveContext.FMapContext.
Notation PositiveContext_nd := PositiveContext.FMapContext_nd.
Definition PositiveContextOk := PositiveContext.FMapContextOk (fun x y pf => pf).
Global Existing Instance PositiveContextOk.
