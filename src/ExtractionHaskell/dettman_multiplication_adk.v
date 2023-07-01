Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/dettman_multiplication_adk.hs"*) Recursive Extraction DettmanMultiplicationADK.main.
(* cat /tmp/dettman_multiplication_adk.hs.out | sed -f haskell.sed  > ../../dettman_multiplication_adk.hs *)
