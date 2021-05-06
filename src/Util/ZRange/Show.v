Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Local Open Scope string_scope.

Global Instance show_zrange : Show zrange
  := fun r
     => "[" ++ Hex.show_Z (lower r) ++ " ~> " ++ Hex.show_Z (upper r) ++ "]".
Global Instance show_lvl_zrange : ShowLevel zrange := show_zrange.
