(** Quick test: does [vectorized_add] produce valid assembly? *)
From Coq Require Import ZArith List String.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Vectorize.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Util.Strings.Show.
Import ListNotations.
Local Open Scope string_scope.

(** Generate 5-limb vectorized add assembly *)
Definition test_add_lines : Lines :=
  vectorized_add "fiat_25519_add" 5.

(** Convert to string lines *)
Definition test_add_strings : list string :=
  show_lines test_add_lines.

(** Evaluate to see the output *)
Eval compute in test_add_strings.
