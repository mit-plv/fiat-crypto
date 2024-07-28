(* This is mostly for testing the performance of [Search] for Coq's bench *)
From Coq Require Import ZArith.
Time Require Import Crypto.Everything.
#[local] Set Search Output Name Only.
Time Redirect "log" SearchPattern _.
#[local] Unset Search Output Name Only.
Time Redirect "log" SearchPattern _.
