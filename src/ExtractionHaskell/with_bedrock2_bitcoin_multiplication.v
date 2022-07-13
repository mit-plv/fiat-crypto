Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2Later.

(*Redirect "/tmp/bedrock2_bitcoin_multiplication.hs"*) Recursive Extraction BitcoinMultiplication.main.
(* cat /tmp/bedrock2_bitcoin_multiplication.hs.out | sed -f haskell.sed  > ../../bedrock2_bitcoin_multiplication.hs *)
