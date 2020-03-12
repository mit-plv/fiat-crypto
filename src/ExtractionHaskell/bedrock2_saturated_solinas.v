Require Import Crypto.Bedrock.StandaloneHaskellMain.

(*Redirect "/tmp/bedrock2_saturated_solinas.hs"*) Recursive Extraction SaturatedSolinas.main.
(* cat /tmp/bedrock2_saturated_solinas.hs.out | sed -f haskell.sed  > ../../bedrock2_saturated_solinas.hs *)
