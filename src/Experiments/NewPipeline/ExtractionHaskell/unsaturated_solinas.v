Require Import Crypto.Experiments.NewPipeline.StandaloneHaskellMain.

(*Redirect "/tmp/unsaturated_solinas.hs" *)Recursive Extraction UnsaturatedSolinas.main.
(* cat /tmp/solinas.hs.out | sed -f haskell.sed  > ../../solinas.hs *)
