Require Import Crypto.Bedrock.StandaloneHaskellMain.

(*Redirect "/tmp/bedrock2_unsaturated_solinas.hs" *)Recursive Extraction UnsaturatedSolinas.main.
(* cat /tmp/bedrock2_unsaturated_solinas.hs.out | sed -f haskell.sed  > ../../bedrock2_unsaturated_solinas.hs *)
