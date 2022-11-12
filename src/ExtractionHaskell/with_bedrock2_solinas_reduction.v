Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2Later.

(*Redirect "/tmp/bedrock2_solinas_reduction.hs"*) Recursive Extraction SolinasReduction.main.
(* cat /tmp/bedrock2_solinas_reduction.hs.out | sed -f haskell.sed  > ../../bedrock2_solinas_reduction.hs *)
