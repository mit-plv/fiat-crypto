Require Import Crypto.Bedrock.StandaloneHaskellMain.

(*Redirect "/tmp/bedrock2_base_conversion.hs"*) Recursive Extraction BaseConversion.main.
(* cat /tmp/bedrock2_base_conversion.hs.out | sed -f haskell.sed  > ../../bedrock2_base_conversion.hs *)
