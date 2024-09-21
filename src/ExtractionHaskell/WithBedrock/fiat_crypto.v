Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.
Import Bedrock2Later.

(*Redirect "/tmp/bedrock2_fiat_crypto.hs" *)Recursive Extraction FiatCrypto.main.
(* cat /tmp/bedrock2_fiat_crypto.hs.out | sed -f haskell.sed  > ../../bedrock2_fiat_crypto.hs *)
