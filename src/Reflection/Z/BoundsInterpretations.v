Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bounds.
Require Import Crypto.Util.Tactics.DestructHead.
Export Reflection.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Module Import Bounds.
  Definition t := option bounds. (* TODO?: Separate out the bounds computation from the overflow computation? e.g., have [safety := in_bounds | overflow] and [t := bounds * safety]? *)
  Bind Scope bounds_scope with t.
  Local Coercion Z.of_nat : nat >-> Z.
  Section with_bitwidth.
    Context (bit_width : option Z).
    Definition SmartBuildBounds (l u : Z)
      := if ((0 <=? l) && (match bit_width with Some bit_width => u <? 2^bit_width | None => true end))%Z%bool
         then Some {| lower := l ; upper := u |}
         else None.
    Definition SmartRebuildBounds (b : t) : t
      := match b with
         | Some b => SmartBuildBounds (lower b) (upper b)
         | None => None
         end.
    Definition t_map1 (f : bounds -> bounds) (x : t)
      := match x with
         | Some x
           => match f x with
              | Build_bounds l u
                => SmartBuildBounds l u
              end
         | _ => None
         end%Z.
    Definition t_map2 (f : bounds -> bounds -> bounds) (x y : t)
      := match x, y with
         | Some x, Some y
           => match f x y with
              | Build_bounds l u
                => SmartBuildBounds l u
              end
         | _, _ => None
         end%Z.
    Definition t_map4 (f : bounds -> bounds -> bounds -> bounds -> bounds) (x y z w : t)
      := match x, y, z, w with
         | Some x, Some y, Some z, Some w
           => match f x y z w with
              | Build_bounds l u
                => SmartBuildBounds l u
              end
         | _, _, _, _ => None
         end%Z.
    Definition add' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx + ly ; upper := ux + uy |}.
    Definition add : t -> t -> t := t_map2 add'.
    Definition sub' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx - uy ; upper := ux - ly |}.
    Definition sub : t -> t -> t := t_map2 sub'.
    Definition mul' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx * ly ; upper := ux * uy |}.
    Definition mul : t -> t -> t := t_map2 mul'.
    Definition shl' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := Z.shiftl lx ly ; upper := Z.shiftl ux uy |}.
    Definition shl : t -> t -> t := t_map2 shl'.
    Definition shr' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := Z.shiftr lx uy ; upper := Z.shiftr ux ly |}.
    Definition shr : t -> t -> t := t_map2 shr'.
    Definition land' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := 0 ; upper := Z.min ux uy |}.
    Definition land : t -> t -> t := t_map2 land'.
    Definition lor' : bounds -> bounds -> bounds
      := fun x y => let (lx, ux) := x in let (ly, uy) := y in
                                         {| lower := Z.max lx ly;
                                            upper := 2^(Z.max (Z.log2_up (ux+1)) (Z.log2_up (uy+1))) - 1 |}.
    Definition lor : t -> t -> t := t_map2 lor'.
    Definition neg' (int_width : Z) : bounds -> bounds
      := fun v
         => let (lb, ub) := v in
            let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
            let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
            if must_be_one
            then {| lower := Z.ones int_width ; upper := Z.ones int_width |}
            else if might_be_one
                 then {| lower := 0 ; upper := Z.ones int_width |}
                 else {| lower := 0 ; upper := 0 |}.
    Definition neg (int_width : Z) : t -> t
      := fun v
         => if ((0 <=? int_width) (*&& (int_width <=? WordW.bit_width)*))%Z%bool
            then t_map1 (neg' int_width) v
            else None.
    Definition cmovne' (r1 r2 : bounds) : bounds
      := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovne (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovne') x y r1 r2.
    Definition cmovle' (r1 r2 : bounds) : bounds
      := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovle (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovle') x y r1 r2.
  End with_bitwidth.

  Module Export Notations.
    Export Util.Bounds.Notations.
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
       | OpConst TZ v => fun _ => SmartBuildBounds None v v
       | OpConst (TWord _ as T) v => fun _ => SmartBuildBounds (bit_width_of_base_type T) ((*FixedWordSizes.wordToZ*) v) ((*FixedWordSizes.wordToZ*) v)
       | Add T => fun xy => add (bit_width_of_base_type T) (fst xy) (snd xy)
       | Sub T => fun xy => sub (bit_width_of_base_type T) (fst xy) (snd xy)
       | Mul T => fun xy => mul (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shl T => fun xy => shl (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shr T => fun xy => shr (bit_width_of_base_type T) (fst xy) (snd xy)
       | Land T => fun xy => land (bit_width_of_base_type T) (fst xy) (snd xy)
       | Lor T => fun xy => lor (bit_width_of_base_type T) (fst xy) (snd xy)
       | Neg T int_width => fun x => neg (bit_width_of_base_type T) int_width x
       | Cmovne T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne (bit_width_of_base_type T) x y z w
       | Cmovle T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle (bit_width_of_base_type T) x y z w
       | Cast _ T => fun x => SmartRebuildBounds (bit_width_of_base_type T) x
       end%bounds.

  Definition of_Z (z : Z) : t := Some (ZToBounds z).

  Definition of_interp t (z : Syntax.interp_base_type t) : interp_base_type t
    := Some (ZToBounds (match t return Syntax.interp_base_type t -> Z with
                        | TZ => fun z => z
                        | TWord logsz => fun z => z (*FixedWordSizes.wordToZ*)
                        end z)).

  Definition bounds_to_base_type' (b : bounds) : base_type
    := if (0 <=? lower b)%Z
       then TWord (Z.to_nat (Z.log2_up (Z.log2_up (1 + upper b))))
       else TZ.
  Definition bounds_to_base_type (b : t) : base_type
    := match b with
       | None => TZ
       | Some b' => bounds_to_base_type' b'
       end.

  Definition ComputeBounds {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type interp_base_type (domain t))
    : interp_flat_type interp_base_type (codomain t)
    := Interp (@interp_op) e input_bounds.

  Definition bound_is_goodb : forall t, interp_base_type t -> bool
    := fun t bs
       => match bs with
          | Some bs
            => (*let l := lower bs in
               let u := upper bs in
               let bit_width := bit_width_of_base_type t in
               ((0 <=? l) && (match bit_width with Some bit_width => Z.log2 u <? bit_width | None => true end))%Z%bool*)
            true
          | None => false
          end.
  Definition bound_is_good : forall t, interp_base_type t -> Prop
    := fun t v => bound_is_goodb t v = true.
  Definition bounds_are_good : forall {t}, interp_flat_type interp_base_type t -> Prop
    := (@interp_flat_type_rel_pointwise1 _ _ bound_is_good).

  Definition is_bounded_byb {T} : Syntax.interp_base_type T -> interp_base_type T -> bool
    := fun val bound
       => match bound with
          | Some bounds'
            => Util.Bounds.is_bounded_byb (bit_width_of_base_type T) bounds' val
          | None => true
          end%bool%Z.
  Definition is_bounded_by' {T} : Syntax.interp_base_type T -> interp_base_type T -> Prop
    := fun val bound => is_bounded_byb val bound = true.

  Definition is_bounded_by {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type interp_base_type T -> Prop
    := interp_flat_type_rel_pointwise (@is_bounded_by').
  Definition is_bounded_by_bool {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type interp_base_type T -> bool
    := interp_flat_type_relb_pointwise (@is_bounded_byb).

  Local Arguments interp_base_type !_ / .
  Global Instance dec_eq_interp_flat_type {T} : DecidableRel (@eq (interp_flat_type interp_base_type T)) | 10.
  Proof.
    induction T; destruct_head base_type; simpl; exact _.
  Defined.
End Bounds.
