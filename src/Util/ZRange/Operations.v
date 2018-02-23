Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Notations.

Module ZRange.
  Local Open Scope Z_scope.
  Local Open Scope zrange_scope.

  Local Notation eta v := r[ lower v ~> upper v ].

  Definition flip (v : zrange) : zrange
    := r[ upper v ~> lower v ].

  Definition union (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       let (ly, uy) := eta y in
       r[ Z.min lx ly ~> Z.max ux uy ].

  Definition intersection (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       let (ly, uy) := eta y in
       r[ Z.max lx ly ~> Z.min ux uy ].

  Definition normalize (v : zrange) : zrange
    := r[ Z.min (lower v) (upper v) ~> Z.max (upper v) (lower v) ].

  Definition normalize' (v : zrange) : zrange
    := union v (flip v).

  Lemma normalize'_eq : normalize = normalize'. Proof. reflexivity. Defined.

  Definition abs (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ 0 ~> Z.max (Z.abs l) (Z.abs u) ].

  Definition opp (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ -u ~> -l ].

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

  Definition upper_lor_land_bounds (x y : BinInt.Z) : BinInt.Z
    := 2^(1 + Z.log2_up (Z.max x y)).
  Definition extreme_lor_land_bounds (x y : zrange) : zrange
    := let mx := ZRange.upper (ZRange.abs x) in
       let my := ZRange.upper (ZRange.abs y) in
       {| lower := -upper_lor_land_bounds mx my ; upper := upper_lor_land_bounds mx my |}.
  Definition extremization_bounds (f : zrange -> zrange -> zrange) (x y : zrange) : zrange
    := let (lx, ux) := x in
       let (ly, uy) := y in
       if ((lx <? 0) || (ly <? 0))%Z%bool
       then extreme_lor_land_bounds x y
       else f x y.
  Definition land_bounds : zrange -> zrange -> zrange
    := extremization_bounds
         (fun x y
          => let (lx, ux) := x in
             let (ly, uy) := y in
             {| lower := Z.min 0 (Z.min lx ly) ; upper := Z.max 0 (Z.min ux uy) |}).

  Definition split_bounds (r : zrange) (split_at : BinInt.Z) : zrange * zrange :=
    if upper r <? split_at
    then if (0 <=? lower r)%Z
         then (r, {| lower := 0; upper := 0 |})
         else ( {| lower := 0; upper := split_at - 1 |},
                {| lower := 0; upper := Z.max ( -(lower r / split_at)) (upper r / split_at) |} )
    else ( {| lower := 0; upper := split_at - 1 |},
           {| lower := 0; upper := Z.max ( -(lower r / split_at)) (upper r / split_at) |} ).
End ZRange.
