Require Import Coq.MSets.MSetPositive.
Require Import Crypto.Util.MSets.Show.
Require Import Crypto.Util.Strings.Show.

Module Import ShowMSetPositive := ShowWSets PositiveSet.

Global Instance show_PositiveSet : Show PositiveSet.t := _.
Global Instance show_lvl_PositiveSet : ShowLevel PositiveSet.t := _.
Global Instance show_lines_PositiveSet : ShowLines PositiveSet.t := let _ := @ShowLines_of_Show PositiveSet.elt in _.
