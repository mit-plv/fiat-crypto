Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/unsaturated_solinas.hs" *)Recursive Extraction UnsaturatedSolinas.main.
(* cat /tmp/unsaturated_solinas.hs.out | sed -f haskell.sed  > ../../unsaturated_solinas.hs *)
