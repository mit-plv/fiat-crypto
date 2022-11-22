(* This is mostly for testing the performance of [Search] for Coq's bench *)
Require Import Coq.ZArith.ZArith.
Time Require Import Crypto.Everything.
#[local] Set Search Output Name Only.
Time Redirect "log" Search -"____".
Time Redirect "log" Search Z.
#[local] Unset Search Output Name Only.
Time Redirect "log" Search -"____".
Time Redirect "log" Search Z.
