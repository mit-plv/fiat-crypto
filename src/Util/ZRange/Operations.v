Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.

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

  Definition size (v : zrange) : Z := upper (normalize v) - lower (normalize v).

  Definition abs (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ 0 ~> Z.max (Z.abs l) (Z.abs u) ].

  Definition opp (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ -u ~> -l ].

  Definition map (f : Z -> Z) (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ f l ~> f u ].

  Definition split_range_at_0 (x : zrange) : option zrange (* < 0 *) * option zrange (* = 0 *) * option zrange (* > 0 *)
    := let (l, u) := eta x in
       (if (0 <=? l)%Z
        then None
        else Some r[l ~> Z.min u (-1)],
        if ((0 <? l)%Z || (u <? 0)%Z)%bool
        then None
        else Some r[0 ~> 0],
        if (u <=? 0)%Z
        then None
        else Some r[Z.max 1 l ~> u]).

  Definition apply_to_split_range (f : zrange -> zrange) (v : zrange) : zrange
    := match split_range_at_0 v with
       | (Some n, Some z, Some p) => union (union (f n) (f p)) (f z)
       | (Some v1, Some v2, None) | (Some v1, None, Some v2) | (None, Some v1, Some v2) => union (f v1) (f v2)
       | (Some v, None, None) | (None, Some v, None) | (None, None, Some v) => f v
       | (None, None, None) => f v
       end.

  Definition apply_to_range (f : BinInt.Z -> zrange) (v : zrange) : zrange
    := let (l, u) := eta v in
       union (f l) (f u).

  Definition apply_to_each_split_range (f : BinInt.Z -> zrange) (v : zrange) : zrange
    := apply_to_split_range (apply_to_range f) v.

  Definition constant (v : Z) : zrange := r[v ~> v].

  Fixpoint nary_T (A B : Type) (n : nat) :=
    match n with
    | O => B
    | S n => A -> nary_T A B n
    end.

  Fixpoint under_args {A B B'} (F : B -> B') {n : nat} : nary_T A B n -> nary_T A B' n
    := match n with
       | O => F
       | S n => fun f x => @under_args A B B' F n (f x)
       end.

  Fixpoint under_args2 {A B B' B''} (F : B -> B' -> B'') {n : nat} : nary_T A B n -> nary_T A B' n -> nary_T A B'' n
    := match n with
       | O => F
       | S n => fun f g x => @under_args2 A B B' B'' F n (f x) (g x)
       end.

  Definition apply_to_range_under_args {A} {n} (f : Z -> nary_T A zrange n) (v : zrange) : nary_T A zrange n
    := let (l, u) := eta v in
       under_args2 union (f l) (f u).

  Definition apply_to_split_range_under_args {A} {n} (f : zrange -> nary_T A zrange n) (v : zrange) : nary_T A zrange n
    := match split_range_at_0 v with
       | (Some n, Some z, Some p) => under_args2 union (under_args2 union (f n) (f p)) (f z)
       | (Some v1, Some v2, None) | (Some v1, None, Some v2) | (None, Some v1, Some v2) => under_args2 union (f v1) (f v2)
       | (Some v, None, None) | (None, Some v, None) | (None, None, Some v) => f v
       | (None, None, None) => f v
       end.

  Definition apply_to_each_split_range_under_args {A} {n} (f : BinInt.Z -> nary_T A zrange n) (v : zrange) : nary_T A zrange n
    := apply_to_split_range_under_args (apply_to_range_under_args f) v.

  Fixpoint nary_is_bounded_by {n : nat} : nary_T Z Z n -> nary_T zrange zrange n -> Prop
    := match n return nary_T Z Z n -> nary_T zrange zrange n -> Prop with
       | O => fun z r => is_bounded_by_bool z r = true
       | S n
         => fun (f : Z -> nary_T Z Z n) (fb : zrange -> nary_T zrange zrange n)
            => forall z r, is_bounded_by_bool z r = true -> nary_is_bounded_by (f z) (fb r)
       end.

  Fixpoint n_corners {n : nat} : nary_T Z Z n -> nary_T zrange zrange n
    := match n with
       | O => constant
       | S n
         => fun (f : Z -> nary_T Z Z n) (v : zrange)
            => apply_to_range_under_args (fun x => n_corners (f x)) v
       end.

  Fixpoint n_corners_and_zero {n : nat} : nary_T Z Z n -> nary_T zrange zrange n
    := match n with
       | O => constant
       | S n
         => fun (f : Z -> nary_T Z Z n) (v : zrange)
            => apply_to_each_split_range_under_args (fun x => n_corners_and_zero (f x)) v
       end.

  Fixpoint apply_to_n_split_range {n : nat} : nary_T zrange zrange n -> nary_T zrange zrange n
    := match n with
       | O => fun x => x
       | S n
         => fun (f : zrange -> nary_T zrange zrange n) (v : zrange)
            => apply_to_n_split_range (apply_to_split_range_under_args f v)
       end.

  Definition two_corners (f : Z -> Z) (v : zrange) : zrange
    := apply_to_range (fun x => constant (f x)) v.
  Definition four_corners (f : Z -> Z -> Z) (x y : zrange) : zrange
    := apply_to_range (fun x => two_corners (f x) y) x.
  Definition eight_corners (f : Z -> Z -> Z -> Z) (x y z : zrange) : zrange
    := apply_to_range (fun x => four_corners (f x) y z) x.

  Definition two_corners_and_zero (f : Z -> Z) (v : zrange) : zrange
    := apply_to_each_split_range (fun x => constant (f x)) v.
  Definition four_corners_and_zero (f : Z -> Z -> Z) (x y : zrange) : zrange
    := apply_to_split_range (apply_to_range (fun x => two_corners_and_zero (f x) y)) x.
  Definition eight_corners_and_zero (f : Z -> Z -> Z -> Z) (x y z : zrange) : zrange
    := apply_to_split_range (apply_to_range (fun x => four_corners_and_zero (f x) y z)) x.

  Definition split_range_one (f : zrange -> zrange) : zrange -> zrange
    := apply_to_n_split_range (n := 1) f.
  Definition split_range_two (f : zrange -> zrange -> zrange) : zrange -> zrange -> zrange
    := apply_to_n_split_range (n := 2) f.

  Definition two_corners' (f : Z -> Z) (v : zrange) : zrange
    := normalize' (map f v).

  Lemma two_corners'_eq x y : two_corners x y = two_corners' x y.
  Proof.
    cbv [two_corners two_corners' normalize' map union apply_to_range constant flip].
    cbn [lower upper].
    rewrite Z.max_comm; reflexivity.
  Qed.

  Definition extend_land_lor_bounds (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ Z.min 0 l ~> Z.max (-1) u ].

  Definition land_lor_bounds (f : BinInt.Z -> BinInt.Z -> BinInt.Z) (x y : zrange) : zrange
    := four_corners_and_zero (fun x y => f (Z.round_lor_land_bound x) (Z.round_lor_land_bound y))
                             (extend_land_lor_bounds x) (extend_land_lor_bounds y).
  Definition lor_bounds : zrange -> zrange -> zrange := land_lor_bounds Z.lor.

  (* N.B. the bounds here for negative numbers are fairly loose *)
  Definition land_bounds (x y : zrange) : zrange
    :=
      let low := if ((lower x <? 0) && (lower y <? 0))%bool
                 then
                   let logx := Z.log2_up (-lower x) in
                   let logy := Z.log2_up (-lower y) in
                   - 2 ^ (Z.max logx logy)
                 else 0 in
      let high := if ((0 <=? lower x)%Z && (0 <=? lower y)%Z)%bool
                  then (* both arguments must be positive *)
                    if ((0 <=? upper x)%Z && (0 <=? upper y)%Z)%bool
                    then Z.min (upper x) (upper y)
                    else (* only get here if upper < lower *)
                      Z.max (Z.max (lower x) (upper x))
                            (Z.max (lower y) (upper y))
                  else if ((upper x <? 0) && (upper y <? 0))%bool
                       then 0 (* both arguments must be negative *)
                       else Z.max (upper x) (upper y) in
      r[low~>high].


  Definition split_bounds_pos (r : zrange) (split_at : BinInt.Z) : zrange * zrange :=
    if upper r <? split_at
    then if (0 <=? lower r)%Z
         then (r, {| lower := 0; upper := 0 |})
         else ( {| lower := 0; upper := split_at - 1 |},
                {| lower := lower r / split_at; upper := (upper r / split_at) |} )
    else ( {| lower := 0; upper := split_at - 1 |},
           {| lower := lower r / split_at; upper := (upper r / split_at) |} ).
  Definition split_bounds (r : zrange) (split_at : BinInt.Z) : zrange * zrange :=
    if (0 <? split_at)%Z
    then split_bounds_pos r split_at
    else if (split_at =? 0)%Z
         then (ltac:(match eval hnf in (1 mod 0) with | 0 => exact {| lower := 0; upper := 0 |} | _ => exact r end), {| lower := 0; upper := 0 |})
         else let '(q, r) := split_bounds_pos (opp r) (-split_at) in
              (opp q, r).

  Definition good (r : zrange) : Prop
    := lower r <= upper r.
  Definition goodb (r : zrange) : bool
    := (lower r <=? upper r)%Z.
  Definition covers (rs : list zrange) (r : zrange)
    := forall z, is_bounded_by_bool z r = true -> exists r', is_bounded_by_bool z r' = true /\ List.In r' rs.

  Notation log2 := (ZRange.two_corners Z.log2).
  Notation log2_up := (ZRange.two_corners Z.log2_up).
  Notation add := (ZRange.four_corners Z.add).
  Notation sub := (ZRange.four_corners Z.sub).
  Notation mul := (ZRange.four_corners Z.mul).
  Notation div := (ZRange.four_corners_and_zero Z.div).
  Notation shiftr := (ZRange.four_corners_and_zero Z.shiftr).
  Notation shiftl := (ZRange.four_corners_and_zero Z.shiftl).
  Notation land := land_bounds.
  Notation lor := lor_bounds.
  Notation cc_m s := (ZRange.two_corners (Z.cc_m s)).

  Module Export ZRangeNotations.
    Notation "- x" := (opp x) : zrange_scope.
    Infix "+" := add : zrange_scope.
    Infix "-" := sub : zrange_scope.
    Infix "*" := mul : zrange_scope.
    Infix "/" := div : zrange_scope.
    Infix ">>" := shiftr : zrange_scope.
    Infix "<<" := shiftl : zrange_scope.
    Infix "&'" := land : zrange_scope.
    (* enable pairing to show up in arguments bound to zrange_scope *)
    Notation "( x , y , .. , z )" := (pair .. (pair x%zrange y%zrange) .. z%zrange) : zrange_scope.
  End ZRangeNotations.
End ZRange.

Export ZRange.ZRangeNotations.
