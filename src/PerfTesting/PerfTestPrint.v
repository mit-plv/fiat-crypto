(* This is mostly for testing the performance of variations of [Print] for Coq's bench, a la what company-coq uses *)
From Coq Require Import ZArith.
Time Require Import Crypto.Everything.
Time Redirect "log" Print Grammar tactic.
Time Redirect "log" Print Grammar constr.
Time Redirect "log" Print Ltac Signatures.
Time Redirect "log" Print LoadPath.
