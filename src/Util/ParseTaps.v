Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Notations.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition tap := (Z * Z)%type.
Definition taps := list tap.
Delimit Scope tap_scope with tap.
Delimit Scope taps_scope with taps.
Bind Scope tap_scope with tap.
Bind Scope taps_scope with taps.

Coercion Z_to_tap (v : Z) : tap := (v, 0).
Coercion tap_to_taps (v : tap) : taps := [v].
Definition make_tap (b e : Z) : tap := (b, e).

Definition scmul_tap (c : Z) (t : tap) : tap
  := let '(c', e) := t in (c * c', e).
Definition neg_tap (t : tap) : tap
  := let '(c, e) := t in (-c, e).
Definition add_taps : taps -> taps -> taps := @List.app _.

Notation "b ^ e" := (make_tap (Z.log2 b) e) : tap_scope.
Notation "2 ^ e" := [(1, e%Z)] (only printing) : tap_scope.
Notation "x * y" := (scmul_tap x y) : tap_scope.
Notation "- a" := (neg_tap a) : tap_scope.

Notation "b ^ e" := (b^e)%tap (only printing) : taps_scope.
Notation "x * y" := (x * y)%tap (only printing) : taps_scope.
Notation "- a" := (-a)%tap (only printing) : taps_scope.
Notation "b ^ e" := (tap_to_taps (b ^ e)) : taps_scope.
Notation "x * y" := (tap_to_taps (x * y)) : taps_scope.
Notation "- a" := (tap_to_taps (-a)) : taps_scope.

Notation "a + b" := (add_taps a b) : taps_scope.
Notation "a - b" := (add_taps a (neg_tap (Z_to_tap (Zpos b)))) : taps_scope.
Notation "a - b" := (add_taps a (- b)) : taps_scope.
