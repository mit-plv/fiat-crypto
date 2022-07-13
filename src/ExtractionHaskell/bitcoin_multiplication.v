Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/bitcoin_multiplication.hs"*) Recursive Extraction BitcoinMultiplication.main.
(* cat /tmp/bitcoin_multiplication.hs.out | sed -f haskell.sed  > ../../bitcoin_multiplication.hs *)
