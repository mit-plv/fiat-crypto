Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/saturated_solinas.hs"*) Recursive Extraction SaturatedSolinas.main.
(* cat /tmp/saturated_solinas.hs.out | sed -f haskell.sed  > ../../saturated_solinas.hs *)
