Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/fiat_crypto.hs" *)Recursive Extraction FiatCrypto.main.
(* cat /tmp/fiat_crypto.hs.out | sed -f haskell.sed  > ../../fiat_crypto.hs *)
