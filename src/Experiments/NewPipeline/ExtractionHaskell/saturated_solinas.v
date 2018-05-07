Require Import Crypto.Experiments.NewPipeline.StandaloneHaskellMain.

(*Redirect "/tmp/saturated_solinas.hs"*) Recursive Extraction SaturatedSolinas.main.
(* cat /tmp/solinas.hs.out | sed -f haskell.sed  > ../../solinas.hs *)
