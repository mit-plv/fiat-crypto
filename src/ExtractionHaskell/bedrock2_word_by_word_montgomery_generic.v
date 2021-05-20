Require Import Crypto.Bedrock.Standalone.StandaloneHaskellMain.

(*Redirect "/tmp/bedrock2_word_by_word_montgomery_generic.hs" *)Recursive Extraction WordByWordMontgomeryGeneric.main.
(* cat /tmp/bedrock2_word_by_word_montgomery_generic.hs.out | sed -f haskell.sed  > ../../bedrock2_word_by_word_montgomery_generic.hs *)
