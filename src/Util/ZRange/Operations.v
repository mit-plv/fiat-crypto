Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Notations.

Module ZRange.
  Local Open Scope zrange_scope.

  Local Notation eta v := r[ lower v ~> upper v ].

  Definition flip (v : zrange) : zrange
    := r[ upper v ~> lower v ].

  Definition union (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       let (ly, uy) := eta y in
       r[ Z.min lx ly ~> Z.max ux uy ].

  Definition normalize (v : zrange) : zrange
    := r[ Z.min (lower v) (upper v) ~> Z.max (upper v) (lower v) ].

  Definition normalize' (v : zrange) : zrange
    := union v (flip v).

  Lemma normalize'_eq : normalize = normalize'. Proof. reflexivity. Defined.

  Definition abs (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ 0 ~> Z.max (Z.abs l) (Z.abs u) ].

  Definition map (f : Z -> Z) (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ f l ~> f u ].

  Definition two_corners (f : Z -> Z) (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ Z.min (f l) (f u) ~> Z.max (f u) (f l) ].

  Definition two_corners' (f : Z -> Z) (v : zrange) : zrange
    := normalize' (map f v).

  Lemma two_corners'_eq : two_corners = two_corners'. Proof. reflexivity. Defined.

  Definition four_corners (f : Z -> Z -> Z) (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       union (two_corners (f lx) y)
             (two_corners (f ux) y).

  Definition eight_corners (f : Z -> Z -> Z -> Z) (x y z : zrange) : zrange
    := let (lx, ux) := eta x in
       union (four_corners (f lx) y z)
             (four_corners (f ux) y z).
End ZRange.
