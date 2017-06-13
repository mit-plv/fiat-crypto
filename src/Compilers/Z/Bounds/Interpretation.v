Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
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

  Section with_bitwidth.
    Context (bit_width : option Z).
    Definition two_corners (f : Z -> Z) : t -> t
      := fun x
         => let (lx, ux) := x in
            {| lower := Z.min (f lx) (f ux);
               upper := Z.max (f lx) (f ux) |}.
    Definition four_corners (f : Z -> Z -> Z) : t -> t -> t
      := fun x y
         => let (lx, ux) := x in
            let (lfl, ufl) := two_corners (f lx) y in
            let (lfu, ufu) := two_corners (f ux) y in
            {| lower := Z.min lfl lfu;
               upper := Z.max ufl ufu |}.
    Definition eight_corners (f : Z -> Z -> Z -> Z) : t -> t -> t -> t
      := fun x y z
         => let (lx, ux) := x in
            let (lfl, ufl) := four_corners (f lx) y z in
            let (lfu, ufu) := four_corners (f ux) y z in
            {| lower := Z.min lfl lfu;
               upper := Z.max ufl ufu |}.
    Definition truncation_bounds (b : t)
      := match bit_width with
         | Some bit_width => if ((0 <=? lower b) && (upper b <? 2^bit_width))%bool
                             then b
                             else {| lower := 0 ; upper := 2^bit_width - 1 |}
         | None => b
         end.
    Definition BuildTruncated_bounds (l u : Z) : t
      := truncation_bounds {| lower := l ; upper := u |}.
    Definition t_map1 (f : Z -> Z) (x : t)
      := truncation_bounds (two_corners f x).
    Definition t_map2' (f : Z -> Z -> Z) : t -> t -> t
      := fun x y => four_corners f x y.
    Definition t_map2 (f : Z -> Z -> Z) : t -> t -> t
      := fun x y => truncation_bounds (four_corners f x y).
    Definition t_map3' (f : Z -> Z -> Z -> Z) : t -> t -> t -> t
      := fun x y z => eight_corners f x y z.
    Definition t_map3 (f : Z -> Z -> Z -> Z) : t -> t -> t -> t
      := fun x y z => truncation_bounds (eight_corners f x y z).
    Definition t_map4 (f : bounds -> bounds -> bounds -> bounds -> bounds) (x y z w : t)
      := truncation_bounds (f x y z w).
    Definition add : t -> t -> t := t_map2 Z.add.
    Definition sub : t -> t -> t := t_map2 Z.sub.
    Definition mul : t -> t -> t := t_map2 Z.mul.
    Definition mul' : t -> t -> t := t_map2' Z.mul.
    Definition shl : t -> t -> t := t_map2 Z.shiftl.
    Definition shr : t -> t -> t := t_map2 Z.shiftr.
    Definition max_abs_bound (x : t) : Z
      := Z.max (Z.abs (lower x)) (Z.abs (upper x)).
    Definition upper_lor_and_bounds (x y : Z) : Z
      := 2^(1 + Z.log2_up (Z.max x y)).
    Definition extreme_lor_land_bounds (x y : t) : t
      := let mx := max_abs_bound x in
         let my := max_abs_bound y in
         {| lower := -upper_lor_and_bounds mx my ; upper := upper_lor_and_bounds mx my |}.
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
    Definition opp : t -> t := t_map1 Z.opp.
    Definition zselect' (r1 r2 : t) : t
      := let (lr1, ur1) := r1 in
         let (lr2, ur2) := r2 in
         {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition zselect (c r1 r2 : t) : t
      := truncation_bounds (zselect' r1 r2).
    Definition add_with_carry' : t -> t -> t -> t
      := t_map3' Z.add_with_carry.
    Definition add_with_carry : t -> t -> t -> t
      := t_map3 Z.add_with_carry.
    Definition sub_with_borrow' : t -> t -> t -> t
      := t_map3' Z.sub_with_borrow.
    Definition sub_with_borrow : t -> t -> t -> t
      := t_map3 Z.sub_with_borrow.
    Definition modulo_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            truncation_bounds {| lower := if l / d =? u / d then Z.min (l mod d) (u mod d) else Z.min 0 (d + 1);
                                 upper := if l / d =? u / d then Z.max (l mod d) (u mod d) else Z.max 0 (d - 1) |}.
    Definition div_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            truncation_bounds {| lower := l / d ; upper := u / d |}.
    Definition opp_div_pow2_constant : Z -> t -> t
      := fun e x
         => let d := 2^e in
            let (l, u) := (lower x, upper x) in
            truncation_bounds {| lower := -(u / d) ; upper := -(l / d) |}.
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

    Definition id_with_alt {T1 T2 Tout} (x : interp_base_type T1) (y : interp_base_type T2)
      : interp_base_type Tout
      := truncation_bounds match T1, T2, Tout with
                           | TZ, TZ, TZ => y
                           | _, _, _ => x
                           end.
  End with_bitwidth.
  Section with_bitwidth2.
    Context (bit_width1 bit_width2 : option Z)
            (carry_boundary_bit_width : Z).
    Definition get_carry : t -> t * t
      := fun v =>
           (modulo_pow2_constant bit_width1 carry_boundary_bit_width v,
            div_pow2_constant bit_width2 carry_boundary_bit_width v).
    Definition get_borrow : t -> t * t
      := fun v =>
           (modulo_pow2_constant bit_width1 carry_boundary_bit_width v,
            opp_div_pow2_constant bit_width2 carry_boundary_bit_width v).
    Definition add_with_get_carry  : t -> t -> t -> t * t
      := fun c x y
         => get_carry (add_with_carry' c x y).
    Definition sub_with_get_borrow : t -> t -> t -> t * t
      := fun c x y
         => get_borrow (sub_with_borrow' c x y).
    Definition mul_split : t -> t -> t * t
      := fun x y => get_carry (mul' x y).
  End with_bitwidth2.

  Module Export Notations.
    Export Util.ZRange.Notations.
    Infix "+" := (add _) : bounds_scope.
    Infix "-" := (sub _) : bounds_scope.
    Infix "*" := (mul _) : bounds_scope.
    Infix "<<" := (shl _) : bounds_scope.
    Infix ">>" := (shr _) : bounds_scope.
    Infix "&'" := (land _) : bounds_scope.
    Notation "- x" := (opp _ x) : bounds_scope.
  End Notations.

  Definition log_bit_width_of_base_type ty : option nat
    := match ty with
       | TZ => None
       | TWord logsz => Some logsz
       end.

  Definition bit_width_of_base_type ty : option Z
    := option_map (fun logsz => 2^Z.of_nat logsz)%Z (log_bit_width_of_base_type ty).

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
       | Opp _ T => fun x => opp (bit_width_of_base_type T) x
       | IdWithAlt _ _ T => fun xy => id_with_alt (bit_width_of_base_type T) (fst xy) (snd xy)
       | Zselect _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in zselect (bit_width_of_base_type T) c x y
       | MulSplit carry_boundary_bit_width _ _ T1 T2
         => fun xy => mul_split (bit_width_of_base_type T1) (bit_width_of_base_type T2) carry_boundary_bit_width (fst xy) (snd xy)
       | AddWithCarry _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in add_with_carry (bit_width_of_base_type T) c x y
       | AddWithGetCarry carry_boundary_bit_width _ _ _ T1 T2
         => fun cxy => let '(c, x, y) := eta3 cxy in
                       add_with_get_carry (bit_width_of_base_type T1) (bit_width_of_base_type T2) carry_boundary_bit_width c x y
       | SubWithBorrow _ _ _ T => fun cxy => let '(c, x, y) := eta3 cxy in sub_with_borrow (bit_width_of_base_type T) c x y
       | SubWithGetBorrow carry_boundary_bit_width _ _ _ T1 T2
         => fun cxy => let '(c, x, y) := eta3 cxy in
                       sub_with_get_borrow (bit_width_of_base_type T1) (bit_width_of_base_type T2) carry_boundary_bit_width c x y
       end%bounds.

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
  Global Instance dec_eq_interp_flat_type : forall {T}, DecidableRel (@eq (interp_flat_type interp_base_type T)) | 10.
  Proof.
    induction T; destruct_head base_type; simpl; exact _.
  Defined.
End Bounds.
