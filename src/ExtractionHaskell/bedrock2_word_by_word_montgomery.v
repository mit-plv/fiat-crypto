Require Import Crypto.Bedrock.StandaloneHaskellMain.

(*Redirect "/tmp/bedrock2_word_by_word_montgomery.hs" *)Recursive Extraction WordByWordMontgomery.main.
(* cat /tmp/bedrock2_word_by_word_montgomery.hs.out | sed -f haskell.sed  > ../../bedrock2_word_by_word_montgomery.hs *)
