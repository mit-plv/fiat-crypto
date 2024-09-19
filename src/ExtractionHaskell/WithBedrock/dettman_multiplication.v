Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2Later.

(*Redirect "/tmp/bedrock2_dettman_multiplication.hs"*) Recursive Extraction DettmanMultiplication.main.
(* cat /tmp/bedrock2_dettman_multiplication.hs.out | sed -f haskell.sed  > ../../bedrock2_dettman_multiplication.hs *)
