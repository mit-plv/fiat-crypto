Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.DestructHead.
Export Reflection.Syntax.Notations.

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
  Section with_bitwidth.
    Context (bit_width : option Z).
    Definition four_corners (f : Z -> Z -> Z) : t -> t -> t
      := fun x y
         => let (lx, ux) := x in
            let (ly, uy) := y in
            {| lower := Z.min (f lx ly) (Z.min (f lx uy) (Z.min (f ux ly) (f ux uy)));
               upper := Z.max (f lx ly) (Z.max (f lx uy) (Z.max (f ux ly) (f ux uy))) |}.
    Definition truncation_bounds (b : t)
      := match bit_width with
         | Some bit_width => if ((0 <=? lower b) && (upper b <? 2^bit_width))%bool
                             then b
                             else {| lower := 0 ; upper := 2^bit_width - 1 |}
         | None => b
         end.
    Definition BuildTruncated_bounds (l u : Z) : t
      := truncation_bounds {| lower := l ; upper := u |}.
    Definition t_map1 (f : bounds -> bounds) (x : t)
      := truncation_bounds (f x).
    Definition t_map2 (f : Z -> Z -> Z) : t -> t -> t
      := fun x y => truncation_bounds (four_corners f x y).
    Definition t_map4 (f : bounds -> bounds -> bounds -> bounds -> bounds) (x y z w : t)
      := truncation_bounds (f x y z w).
    Definition add : t -> t -> t := t_map2 Z.add.
    Definition sub : t -> t -> t := t_map2 Z.sub.
    Definition mul : t -> t -> t := t_map2 Z.mul.
    Definition shl : t -> t -> t := t_map2 Z.shiftl.
    Definition shr : t -> t -> t := t_map2 Z.shiftr.
    Definition extreme_lor_land_bounds (x y : t) : t
      := let (lx, ux) := x in
         let (ly, uy) := y in
         let lx := Z.abs lx in
         let ly := Z.abs ly in
         let ux := Z.abs ux in
         let uy := Z.abs uy in
         let max := Z.max (Z.max lx ly) (Z.max ux uy) in
         {| lower := -2^(1 + Z.log2_up max) ; upper := 2^(1 + Z.log2_up max) |}.
    Definition extermization_bounds (f : t -> t -> t) (x y : t) : t
      := truncation_bounds
           (let (lx, ux) := x in
            let (ly, uy) := y in
            if ((lx <? 0) || (ly <? 0))%Z%bool
            then extreme_lor_land_bounds x y
            else f x y).
    Definition land : t -> t -> t
      := extermization_bounds
           (fun x y
            => let (lx, ux) := x in
               let (ly, uy) := y in
               {| lower := Z.min 0 (Z.min lx ly) ; upper := Z.max 0 (Z.min ux uy) |}).
    Definition lor : t -> t -> t
      := extermization_bounds
           (fun x y
            => let (lx, ux) := x in
               let (ly, uy) := y in
               {| lower := Z.max lx ly;
                  upper := 2^(Z.max (Z.log2_up (ux+1)) (Z.log2_up (uy+1))) - 1 |}).
    Definition neg' (int_width : Z) : t -> t
      := fun v
         => let (lb, ub) := v in
            let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
            let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
            if must_be_one
            then {| lower := Z.ones int_width ; upper := Z.ones int_width |}
            else if might_be_one
                 then {| lower := Z.min 0 (Z.ones int_width) ; upper := Z.max 0 (Z.ones int_width) |}
                 else {| lower := 0 ; upper := 0 |}.
    Definition neg (int_width : Z) : t -> t
      := fun v
         => truncation_bounds (neg' int_width v).
    Definition cmovne' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovne (x y r1 r2 : t) : t
      := truncation_bounds (cmovne' r1 r2).
    Definition cmovle' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovle (x y r1 r2 : t) : t
      := truncation_bounds (cmovle' r1 r2).
  End with_bitwidth.

  Module Export Notations.
    Export Util.ZRange.Notations.
    Infix "+" := (add _) : bounds_scope.
    Infix "-" := (sub _) : bounds_scope.
    Infix "*" := (mul _) : bounds_scope.
    Infix "<<" := (shl _) : bounds_scope.
    Infix ">>" := (shr _) : bounds_scope.
    Infix "&'" := (land _) : bounds_scope.
  End Notations.

  Definition interp_base_type (ty : base_type) : Set := t.

  Definition bit_width_of_base_type ty : option Z
    := match ty with
       | TZ => None
       | TWord logsz => Some (2^Z.of_nat logsz)%Z
       end.

  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | OpConst T v => fun _ => BuildTruncated_bounds (bit_width_of_base_type T) v v
       | Add _ _ T => fun xy => add (bit_width_of_base_type T) (fst xy) (snd xy)
       | Sub _ _ T => fun xy => sub (bit_width_of_base_type T) (fst xy) (snd xy)
       | Mul _ _ T => fun xy => mul (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shl _ _ T => fun xy => shl (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shr _ _ T => fun xy => shr (bit_width_of_base_type T) (fst xy) (snd xy)
       | Land _ _ T => fun xy => land (bit_width_of_base_type T) (fst xy) (snd xy)
       | Lor _ _ T => fun xy => lor (bit_width_of_base_type T) (fst xy) (snd xy)
       | Neg _ T int_width => fun x => neg (bit_width_of_base_type T) int_width x
       | Cmovne _ _ _ _ T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne (bit_width_of_base_type T) x y z w
       | Cmovle _ _ _ _ T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle (bit_width_of_base_type T) x y z w
       end%bounds.

  Definition of_Z (z : Z) : t := ZToZRange z.

  Definition of_interp t (z : Syntax.interp_base_type t) : interp_base_type t
    := ZToZRange (interpToZ z).

  Definition bounds_to_base_type (b : t) : base_type
    := if (0 <=? lower b)%Z
       then TWord (Z.to_nat (Z.log2_up (Z.log2_up (1 + upper b))))
       else TZ.

  Definition ComputeBounds {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type interp_base_type (domain t))
    : interp_flat_type interp_base_type (codomain t)
    := Interp (@interp_op) e input_bounds.

  Definition is_tighter_thanb' {T} : interp_base_type T -> interp_base_type T -> bool
    := is_tighter_than_bool.

  Definition is_bounded_by' {T} : interp_base_type T -> Syntax.interp_base_type T -> Prop
    := fun bounds val => is_bounded_by' (bit_width_of_base_type T) bounds (interpToZ val).

  Definition is_tighter_thanb {T} : interp_flat_type interp_base_type T -> interp_flat_type interp_base_type T -> bool
    := interp_flat_type_relb_pointwise (@is_tighter_thanb').

  Definition is_bounded_by {T} : interp_flat_type interp_base_type T -> interp_flat_type Syntax.interp_base_type T -> Prop
    := interp_flat_type_rel_pointwise (@is_bounded_by').

  Local Arguments interp_base_type !_ / .
  Global Instance dec_eq_interp_flat_type {T} : DecidableRel (@eq (interp_flat_type interp_base_type T)) | 10.
  Proof.
    induction T; destruct_head base_type; simpl; exact _.
  Defined.
End Bounds.
