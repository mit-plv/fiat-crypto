Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/dettman_multiplication.hs"*) Recursive Extraction DettmanMultiplication.main.
(* cat /tmp/dettman_multiplication.hs.out | sed -f haskell.sed  > ../../dettman_multiplication.hs *)
