Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Local Open Scope string_scope.

Global Instance show_zrange : Show zrange
  := fun _ r
     => "[" ++ Hex.show_Z false (lower r) ++ " ~> " ++ Hex.show_Z false (upper r) ++ "]".
