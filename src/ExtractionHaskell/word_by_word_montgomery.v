Require Import Crypto.StandaloneHaskellMain.

(*Redirect "/tmp/word_by_word_montgomery.hs" *)Recursive Extraction WordByWordMontgomery.main.
(* cat /tmp/word_by_word_montgomery.hs.out | sed -f haskell.sed  > ../../word_by_word_montgomery.hs *)
