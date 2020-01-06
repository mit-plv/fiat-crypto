Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/base_conversion.hs"*) Recursive Extraction BaseConversion.main.
(* cat /tmp/base_conversion.hs.out | sed -f haskell.sed  > ../../base_conversion.hs *)
