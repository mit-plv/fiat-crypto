Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/barrett.hs" *)Recursive Extraction Barrett.main.
(* cat /tmp/barrett.hs.out | sed -f haskell.sed  > ../../barrett.hs *)
