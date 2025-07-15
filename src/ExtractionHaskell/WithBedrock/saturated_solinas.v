Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2Later.

(*Redirect "/tmp/bedrock2_saturated_solinas.hs"*) Recursive Extraction SaturatedSolinas.main.
(* cat /tmp/bedrock2_saturated_solinas.hs.out | sed -f haskell.sed  > ../../bedrock2_saturated_solinas.hs *)
