Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2First.

(*Redirect "/tmp/bedrock2_dettman_multiplication_adk.hs"*) Recursive Extraction DettmanMultiplicationADK.main.
(* cat /tmp/bedrock2_dettman_multiplication_adk.hs.out | sed -f haskell.sed  > ../../bedrock2_dettman_multiplication_adk.hs *)
