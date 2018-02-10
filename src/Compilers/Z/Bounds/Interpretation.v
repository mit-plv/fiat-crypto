Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Tactics.DestructHead.
Export Compilers.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Notation bounds := zrange.
Delimit Scope bounds_scope with bounds.
Local Open Scope Z_scope.

Module Import Bounds.
  Definition t := bounds.
  Bind Scope bounds_scope with t.
  Local Coercion Z.of_nat : nat >-> Z.
  Definition interp_base_type (ty : base_type) : Set := t.

  Section ops.
    (** Generic helper definitions *)
    Definition t_map1 (f : Z -> Z) : t -> t
      := fun x => ZRange.two_corners f x.
    Definition t_map2 (f : Z -> Z -> Z) : t -> t -> t
      := fun x y => ZRange.four_corners f x y.
    Definition t_map3 (f : Z -> Z -> Z -> Z) : t -> t -> t -> t
      := fun x y z => ZRange.eight_corners f x y z.
    (** Definitions of the actual bounds propogation *)
    (** Rules for adding new operations:

        - Use [t_mapn] to if the underlying operation on [Z] is
          monotonic in all [n] of its arguments ([t_mapn] handles both
          monotonic non-increasing and monotonic non-decreasing) *)

    Definition add : t -> t -> t := t_map2 Z.add.
    Definition sub : t -> t -> t := t_map2 Z.sub.
    Definition mul : t -> t -> t := t_map2 Z.mul.
    Definition shl : t -> t -> t := t_map2 Z.shiftl.
    Definition shr : t -> t -> t := t_map2 Z.shiftr.
    Definition max_abs_bound (x : t) : Z
      := upper (ZRange.abs x).
    Definition upper_lor_and_bounds (x y : Z) : Z
      := 2^(1 + Z.log2_up (Z.max x y)).
    Definition extreme_lor_land_bounds (x y : t) : t
      := let mx := max_abs_bound x in
         let my := max_abs_bound y in
         {| lower := -upper_lor_and_bounds mx my ; upper := upper_lor_and_bounds mx my |}.
    Definition extremization_bounds (f : t -> t -> t) (x y : t) : t
      := let (lx, ux) := x in
         let (ly, uy) := y in
         if ((lx <? 0) || (ly <? 0))%Z%bool
         then extreme_lor_land_bounds x y
         else f x y.
    Definition land : t -> t -> t
      := extremization_bounds
           (fun x y
            => let (lx, ux) := x in
               let (ly, uy) := y in
               {| lower := Z.min 0 (Z.min lx ly) ; upper := Z.max 0 (Z.min ux uy) |}).
    Definition lor : t -> t -> t
      := extremization_bounds
           (fun x y
            => let (lx, ux) := x in
               let (ly, uy) := y in
               {| lower := Z.max lx ly;
                  upper := 2^(Z.max (Z.log2_up (ux+1)) (Z.log2_up (uy+1))) - 1 |}).
    Definition opp : t -> t := t_map1 Z.opp.
    Definition zselect' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition zselect (c r1 r2 : t) : t
      := zselect' r1 r2.
    Definition add_with_carry : t -> t -> t -> t
      := t_map3 Z.add_with_carry.
    Definition sub_with_borrow : t -> t -> t -> t
      := t_map3 Z.sub_with_borrow.
    Definition modulo_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            {| lower := if l / d =? u / d then Z.min (l mod d) (u mod d) else Z.min 0 (d + 1);
               upper := if l / d =? u / d then Z.max (l mod d) (u mod d) else Z.max 0 (d - 1) |}.
    Definition div_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            {| lower := l / d ; upper := u / d |}.
    Definition opp_div_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            {| lower := -(u / d) ; upper := -(l / d) |}.
    Definition neg (int_width : Z) : t -> t
      := fun v
         => let (lb, ub) := v in
            let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
            let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
            if must_be_one
            then {| lower := Z.ones int_width ; upper := Z.ones int_width |}
            else if might_be_one
                 then {| lower := Z.min 0 (Z.ones int_width) ; upper := Z.max 0 (Z.ones int_width) |}
                 else {| lower := 0 ; upper := 0 |}.
    Definition cmovne' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovne (x y r1 r2 : t) : t
      := cmovne' r1 r2.
    Definition cmovle' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovle (x y r1 r2 : t) : t
      := cmovle' r1 r2.

    Definition id_with_alt {T1 T2 Tout} (x : interp_base_type T1) (y : interp_base_type T2)
      : interp_base_type Tout
      := match T1, T2, Tout with
         | TZ, TZ, TZ => y
         | _, _, _ => x
         end.
  End ops.
  Section ops_with_carry.
    Context (carry_boundary_bit_width : Z).
    Definition get_carry : t -> t * t
      := fun v =>
           (modulo_pow2_constant carry_boundary_bit_width v,
            div_pow2_constant carry_boundary_bit_width v).
    Definition get_borrow : t -> t * t
      := fun v =>
           (modulo_pow2_constant carry_boundary_bit_width v,
            opp_div_pow2_constant carry_boundary_bit_width v).
    Definition add_with_get_carry  : t -> t -> t -> t * t
      := fun c x y
         => get_carry (add_with_carry c x y).
    Definition sub_with_get_borrow : t -> t -> t -> t * t
      := fun c x y
         => get_borrow (sub_with_borrow c x y).
    Definition mul_split : t -> t -> t * t
      := fun x y => get_carry (mul x y).
  End ops_with_carry.

  Module Export Notations.
    Export Util.ZRange.Notations.
    Infix "+" := add : bounds_scope.
    Infix "-" := sub : bounds_scope.
    Infix "*" := mul : bounds_scope.
    Infix "<<" := shl : bounds_scope.
    Infix ">>" := shr : bounds_scope.
    Infix "&'" := land : bounds_scope.
    Notation "- x" := (opp x) : bounds_scope.
  End Notations.

  Definition log_bit_width_of_base_type ty : option nat
    := match ty with
       | TZ => None
       | TWord logsz => Some logsz
       end.

  Definition bit_width_of_base_type ty : option Z
    := option_map (fun logsz => 2^Z.of_nat logsz)%Z (log_bit_width_of_base_type ty).

  Definition truncation_bounds' bit_width (b : t)
    := match bit_width with
       | Some bit_width => if ((0 <=? lower b) && (upper b <? 2^bit_width))%bool
                           then b
                           else {| lower := 0 ; upper := 2^bit_width - 1 |}
       | None => b
       end.
  Definition truncation_bounds ty : interp_base_type ty -> interp_base_type ty
    := truncation_bounds' (bit_width_of_base_type ty).

  Definition interp_op {src dst} (f : op src dst)
             (x : interp_flat_type interp_base_type src)
    : interp_flat_type interp_base_type dst
    := SmartVarfMap
         truncation_bounds
         (match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
          | OpConst T v => fun _ => {| lower := v ; upper := v |}
          | Add _ _ T => fun xy => add (fst xy) (snd xy)
          | Sub _ _ T => fun xy => sub (fst xy) (snd xy)
          | Mul _ _ T => fun xy => mul (fst xy) (snd xy)
          | Shl _ _ T => fun xy => shl (fst xy) (snd xy)
          | Shr _ _ T => fun xy => shr (fst xy) (snd xy)
          | Land _ _ T => fun xy => land (fst xy) (snd xy)
          | Lor _ _ T => fun xy => lor (fst xy) (snd xy)
          | Opp _ T => fun x => opp x
          | IdWithAlt _ _ T => fun xy => id_with_alt (fst xy) (snd xy)
          | Zselect _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in zselect c x y
          | MulSplit carry_boundary_bit_width _ _ T1 T2
            => fun xy => mul_split carry_boundary_bit_width (fst xy) (snd xy)
          | AddWithCarry _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in add_with_carry c x y
          | AddWithGetCarry carry_boundary_bit_width _ _ _ T1 T2
            => fun cxy => let '(c, x, y) := eta3 cxy in
                          add_with_get_carry carry_boundary_bit_width c x y
          | SubWithBorrow _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in sub_with_borrow c x y
          | SubWithGetBorrow carry_boundary_bit_width _ _ _ T1 T2
            => fun cxy => let '(c, x, y) := eta3 cxy in
                          sub_with_get_borrow carry_boundary_bit_width c x y
          end%bounds x).

  Definition of_Z (z : Z) : t := ZToZRange z.

  Definition of_interp t (z : Syntax.interp_base_type t) : interp_base_type t
    := ZToZRange (interpToZ z).

  Definition smallest_logsz
             (round_up : nat -> option nat)
             (b : t)
    : option nat
    := if (0 <=? lower b)%Z
       then Some (Z.to_nat (Z.log2_up (Z.log2_up (1 + upper b))))
       else None.
  Definition actual_logsz
             (round_up : nat -> option nat)
             (b : t)
    : option nat
    := if (0 <=? lower b)%Z
       then let smallest_lgsz := (Z.to_nat (Z.log2_up (Z.log2_up (1 + upper b)))) in
            let lgsz := round_up smallest_lgsz in
            match lgsz with
            | Some lgsz
              => if Nat.leb smallest_lgsz lgsz
                 then Some lgsz
                 else None
            | None => None
            end
       else None.
  Definition bounds_to_base_type
             {round_up : nat -> option nat}
             (T : base_type)
             (b : interp_base_type T)
    : base_type
    := match T with
       | TZ => match actual_logsz round_up b with
               | Some lgsz => TWord lgsz
               | None => TZ
               end
       | TWord _
         => match smallest_logsz round_up b with
            | Some lgsz => TWord lgsz
            | None => TZ
            end
       end.

  Definition option_min (a : nat) (b : option nat)
    := match b with
       | Some b => Nat.min a b
       | None => a
       end.

  Definition round_up_to_in_list (allowable_lgsz : list nat)
             (lgsz : nat)
    : option nat
    := let good_lgsz := List.filter (Nat.leb lgsz) allowable_lgsz in
       List.fold_right (fun a b => Some (option_min a b)) None good_lgsz.

  Definition ComputeBounds {t} (e : Expr t)
             (input_bounds : interp_flat_type interp_base_type (domain t))
    : interp_flat_type interp_base_type (codomain t)
    := Compilers.Syntax.Interp (@interp_op) e input_bounds.

  Definition is_tighter_thanb' {T} : interp_base_type T -> interp_base_type T -> bool
    := is_tighter_than_bool.

  Definition is_bounded_by' {T} : interp_base_type T -> Syntax.interp_base_type T -> Prop
    := fun bounds val => is_bounded_by' (bit_width_of_base_type T) bounds (interpToZ val).

  Definition is_tighter_thanb {T} : interp_flat_type interp_base_type T -> interp_flat_type interp_base_type T -> bool
    := interp_flat_type_relb_pointwise (@is_tighter_thanb').

  Definition is_bounded_by {T} : interp_flat_type interp_base_type T -> interp_flat_type Syntax.interp_base_type T -> Prop
    := interp_flat_type_rel_pointwise (@is_bounded_by').

  Local Arguments interp_base_type !_ / .
  Global Instance dec_eq_interp_flat_type : forall {T}, DecidableRel (@eq (interp_flat_type interp_base_type T)) | 10.
  Proof.
    induction T; destruct_head base_type; simpl; exact _.
  Defined.
End Bounds.
