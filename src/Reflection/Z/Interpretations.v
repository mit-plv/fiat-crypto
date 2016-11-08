(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Crypto.Util.Tuple.
Require Crypto.Util.HList.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import Crypto.Util.WordUtil.
Export Reflection.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Module Z.
  Definition interp_base_type (t : base_type) : Type := interp_base_type t.
  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := interp_op src dst f.
End Z.

Module LiftOption.
  Section lift_option.
    Context (T : Type).

    Definition interp_flat_type (t : flat_type base_type)
      := option (interp_flat_type (fun _ => T) t).

    Definition interp_base_type' (t : base_type)
      := match t with
         | TZ => option T
         end.

    Definition of' {t} : Syntax.interp_flat_type interp_base_type' t -> interp_flat_type t
      := @smart_interp_flat_map
           base_type
           interp_base_type' interp_flat_type
           (fun t => match t with TZ => fun x => x end)
           (fun _ _ x y => match x, y with
                           | Some x', Some y' => Some (x', y')
                           | _, _ => None
                           end)
           t.

    Fixpoint to' {t} : interp_flat_type t -> Syntax.interp_flat_type interp_base_type' t
      := match t return interp_flat_type t -> Syntax.interp_flat_type interp_base_type' t with
         | Tbase TZ => fun x => x
         | Prod A B => fun x => (@to' A (option_map (@fst _ _) x),
                                 @to' B (option_map (@snd _ _) x))
         end.

    Definition lift_relation {interp_base_type2}
               (R : forall t, T -> interp_base_type2 t -> Prop)
      : forall t, interp_base_type' t -> interp_base_type2 t -> Prop
      := fun t x y => match of' (t:=Tbase t) x with
                      | Some x' => R t x' y
                      | None => True
                      end.

    Definition Some {t} (x : T) : interp_base_type' t
      := match t with
         | TZ => Some x
         end.
  End lift_option.
  Global Arguments of' {T t} _.
  Global Arguments to' {T t} _.
  Global Arguments Some {T t} _.
  Global Arguments lift_relation {T _} R _ _ _.

  Section lift_option2.
    Context (T U : Type).
    Definition lift_relation2 (R : T -> U -> Prop)
      : forall t, interp_base_type' T t -> interp_base_type' U t -> Prop
      := fun t x y => match of' (t:=Tbase t) x, of' (t:=Tbase t) y with
                      | Datatypes.Some x', Datatypes.Some y' => R x' y'
                      | None, None => True
                      | _, _ => False
                      end.
  End lift_option2.
  Global Arguments lift_relation2 {T U} R _ _ _.
End LiftOption.

Module Word64.
  Definition bit_width : nat := 64.
  Definition word64 := word bit_width.
  Delimit Scope word64_scope with word64.
  Bind Scope word64_scope with word64.

  Definition word64ToZ (x : word64) : Z
    := Z.of_N (wordToN x).
  Definition ZToWord64 (x : Z) : word64
    := NToWord _ (Z.to_N x).

  Ltac fold_Word64_Z :=
    repeat match goal with
           | [ |- context G[NToWord bit_width (Z.to_N ?x)] ]
             => let G' := context G [ZToWord64 x] in change G'
           | [ |- context G[Z.of_N (wordToN ?x)] ]
             => let G' := context G [word64ToZ x] in change G'
           | [ H : context G[NToWord bit_width (Z.to_N ?x)] |- _ ]
             => let G' := context G [ZToWord64 x] in change G' in H
           | [ H : context G[Z.of_N (wordToN ?x)] |- _ ]
             => let G' := context G [word64ToZ x] in change G' in H
           end.

  Create HintDb push_word64ToZ discriminated.
  Hint Extern 1 => progress autorewrite with push_word64ToZ in * : push_word64ToZ.

  Lemma bit_width_pos : (0 < Z.of_nat bit_width)%Z.
  Proof. simpl; omega. Qed.
  Local Hint Resolve bit_width_pos : zarith.

  Ltac arith := solve [ omega | auto using bit_width_pos with zarith ].

  Lemma word64ToZ_bound w : (0 <= word64ToZ w < 2^Z.of_nat bit_width)%Z.
  Proof.
    pose proof (wordToNat_bound w) as H.
    apply Nat2Z.inj_lt in H.
    rewrite Zpow_pow2, Z2Nat.id in H by (apply Z.pow_nonneg; omega).
    unfold word64ToZ.
    rewrite wordToN_nat, nat_N_Z; omega.
  Qed.

  Lemma word64ToZ_log_bound w : (0 <= word64ToZ w /\ Z.log2 (word64ToZ w) < Z.of_nat bit_width)%Z.
  Proof.
    pose proof (word64ToZ_bound w) as H.
    destruct (Z_zerop (word64ToZ w)) as [H'|H'].
    { rewrite H'; simpl; omega. }
    { split; [ | apply Z.log2_lt_pow2 ]; try omega. }
  Qed.

  Lemma ZToWord64_word64ToZ (x : word64) : ZToWord64 (word64ToZ x) = x.
  Proof.
    unfold ZToWord64, word64ToZ.
    rewrite N2Z.id, NToWord_wordToN.
    reflexivity.
  Qed.
  Hint Rewrite ZToWord64_word64ToZ : push_word64ToZ.

  Lemma word64ToZ_ZToWord64 (x : Z) : (0 <= x < 2^Z.of_nat bit_width)%Z -> word64ToZ (ZToWord64 x) = x.
  Proof.
    unfold ZToWord64, word64ToZ; intros [H0 H1].
    pose proof H1 as H1'; apply Z2Nat.inj_lt in H1'; [ | omega.. ].
    rewrite <- Z.pow_Z2N_Zpow in H1' by omega.
    replace (Z.to_nat 2) with 2%nat in H1' by reflexivity.
    rewrite wordToN_NToWord_idempotent, Z2N.id by (omega || auto using bound_check_nat_N).
    reflexivity.
  Qed.
  Hint Rewrite word64ToZ_ZToWord64 using arith : push_word64ToZ.

  Definition add : word64 -> word64 -> word64 := @wplus _.
  Definition sub : word64 -> word64 -> word64 := @wminus _.
  Definition mul : word64 -> word64 -> word64 := @wmult _.
  Definition shl : word64 -> word64 -> word64 := @wordBin N.shiftl _.
  Definition shr : word64 -> word64 -> word64 := @wordBin N.shiftr _.
  Definition land : word64 -> word64 -> word64 := @wand _.
  Definition lor : word64 -> word64 -> word64 := @wor _.
  Definition neg : word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y => ZToWord64 (ModularBaseSystemListZOperations.neg (word64ToZ x) (word64ToZ y)).
  Definition cmovne : word64 -> word64 -> word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y z w => ZToWord64 (ModularBaseSystemListZOperations.cmovne (word64ToZ x) (word64ToZ y) (word64ToZ z) (word64ToZ w)).
  Definition cmovle : word64 -> word64 -> word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y z w => ZToWord64 (ModularBaseSystemListZOperations.cmovl (word64ToZ x) (word64ToZ y) (word64ToZ z) (word64ToZ w)).
  Definition conditional_subtract (pred_limb_count : nat) : word64 -> Tuple.tuple word64 (S pred_limb_count) -> Tuple.tuple word64 (S pred_limb_count) -> Tuple.tuple word64 (S pred_limb_count)
    := fun x y z => Tuple.map ZToWord64 (@ModularBaseSystemListZOperations.conditional_subtract_modulus
                                           (S pred_limb_count) (word64ToZ x) (Tuple.map word64ToZ y) (Tuple.map word64ToZ z)).
  Infix "+" := add : word64_scope.
  Infix "-" := sub : word64_scope.
  Infix "*" := mul : word64_scope.
  Infix "<<" := shl : word64_scope.
  Infix ">>" := shr : word64_scope.
  Infix "&'" := land : word64_scope.

  (*Local*) Hint Resolve <- Z.log2_lt_pow2_alt : zarith.
  Local Hint Resolve eq_refl : zarith.
  Local Ltac w64ToZ_t :=
    intros;
    try match goal with
        | [ |- ?wordToZ ?op = _ ]
          => let op' := head op in
             cbv [wordToZ op'] in *
        end;
    autorewrite with push_Zto_N push_Zof_N push_wordToN; try reflexivity.
  Local Ltac w64ToZ_extra_t :=
    repeat first [ reflexivity
                 | progress cbv [ModularBaseSystemListZOperations.neg ModularBaseSystemListZOperations.cmovne ModularBaseSystemListZOperations.cmovl (*ModularBaseSystemListZOperations.conditional_subtract_modulus*)] in *
                 | progress break_match
                 | progress fold_Word64_Z
                 | progress intros
                 | progress autorewrite with push_Zto_N push_Zof_N push_wordToN push_word64ToZ ].

  Local Notation bounds_statement wop Zop
    := ((0 <= Zop -> Z.log2 Zop < Z.of_nat bit_width -> word64ToZ wop = Zop)%Z).
  Local Notation bounds_statement_tuple wop Zop
    := ((HList.hlist (fun v => 0 <= v /\ Z.log2 v < Z.of_nat bit_width) Zop -> Tuple.map word64ToZ wop = Zop)%Z).
  Local Notation bounds_2statement wop Zop
    := (forall x y,
           bounds_statement (wop x y) (Zop (word64ToZ x) (word64ToZ y))).
  Local Notation bounds_1_tuple2_statement wop Zop
    := (forall x y z,
           bounds_statement_tuple (wop x y z) (Zop (word64ToZ x) (Tuple.map word64ToZ y) (Tuple.map word64ToZ z))).
  Local Notation bounds_4statement wop Zop
    := (forall x y z w,
           bounds_statement (wop x y z w) (Zop (word64ToZ x) (word64ToZ y) (word64ToZ z) (word64ToZ w))).

  Lemma word64ToZ_add : bounds_2statement add Z.add. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_sub : bounds_2statement sub Z.sub. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_mul : bounds_2statement mul Z.mul. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_shl : bounds_2statement shl Z.shiftl.
  Proof. w64ToZ_t. admit. Admitted.
  Lemma word64ToZ_shr : bounds_2statement shr Z.shiftr.
  Proof. admit. Admitted.
  Lemma word64ToZ_land : bounds_2statement land Z.land.
  Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_lor : bounds_2statement lor Z.lor.
  Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_neg : bounds_2statement neg ModularBaseSystemListZOperations.neg.
  Proof. w64ToZ_t; w64ToZ_extra_t. Qed.
  Lemma word64ToZ_cmovne : bounds_4statement cmovne ModularBaseSystemListZOperations.cmovne.
  Proof. w64ToZ_t; w64ToZ_extra_t. Qed.
  Lemma word64ToZ_cmovle : bounds_4statement cmovle ModularBaseSystemListZOperations.cmovl.
  Proof. w64ToZ_t; w64ToZ_extra_t. Qed.
  Lemma word64ToZ_conditional_subtract pred_limb_count
    : bounds_1_tuple2_statement (@conditional_subtract pred_limb_count)
                                (@ModularBaseSystemListZOperations.conditional_subtract_modulus (S pred_limb_count)).
  Proof.
    w64ToZ_t; unfold conditional_subtract; w64ToZ_extra_t.
    repeat first [ progress w64ToZ_extra_t
                 | rewrite Tuple.map_map
                 | rewrite HList.Tuple.map_id_ext
                 | match goal with
                   | [ H : HList.hlist _ _ |- HList.hlist _ _ ]
                     => revert H; apply HList.hlist_impl
                   end
                 | apply HList.const ].
  Qed.

  Definition interp_base_type (t : base_type) : Type
    := match t with
       | TZ => word64
       end.
  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | Add => fun xy => fst xy + snd xy
       | Sub => fun xy => fst xy - snd xy
       | Mul => fun xy => fst xy * snd xy
       | Shl => fun xy => fst xy << snd xy
       | Shr => fun xy => fst xy >> snd xy
       | Land => fun xy => land (fst xy) (snd xy)
       | Lor => fun xy => lor (fst xy) (snd xy)
       | Neg => fun xy => neg (fst xy) (snd xy)
       | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
       | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
       | ConditionalSubtract pred_n
         => fun xyz => let '(x, y, z) := eta3 xyz in
                       flat_interp_untuple' (T:=Tbase TZ) (@conditional_subtract pred_n x (flat_interp_tuple y) (flat_interp_tuple z))
       end%word64.

  Definition of_Z ty : Z.interp_base_type ty -> interp_base_type ty
    := match ty return Z.interp_base_type ty -> interp_base_type ty with
       | TZ => ZToWord64
       end.
  Definition to_Z ty : interp_base_type ty -> Z.interp_base_type ty
    := match ty return interp_base_type ty -> Z.interp_base_type ty with
       | TZ => word64ToZ
       end.

  Module Export Rewrites.
    Ltac word64_util_arith := omega.

    Hint Rewrite word64ToZ_add using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_add using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_sub using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_sub using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_mul using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_mul using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_shl using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_shl using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_shr using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_shr using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_land using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_land using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_lor using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_lor using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_neg using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_neg using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_cmovne using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_cmovne using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_cmovle using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_cmovle using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_conditional_subtract using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_conditional_subtract using word64_util_arith : pull_word64ToZ.
  End Rewrites.
End Word64.

Module ZBounds.
  Record bounds := { lower : Z ; upper : Z }.
  Bind Scope bounds_scope with bounds.
  Definition t := option bounds. (* TODO?: Separate out the bounds computation from the overflow computation? e.g., have [safety := in_bounds | overflow] and [t := bounds * safety]? *)
  Bind Scope bounds_scope with t.
  Local Coercion Z.of_nat : nat >-> Z.
  Definition word64ToBounds (x : Word64.word64) : t
    := let v := Word64.word64ToZ x in Some {| lower := v ; upper := v |}.
  Definition SmartBuildBounds (l u : Z)
    := if ((0 <=? l) && (Z.log2 u <? Word64.bit_width))%Z%bool
       then Some {| lower := l ; upper := u |}
       else None.
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
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx << ly ; upper := ux << uy |}.
  Definition shl : t -> t -> t := t_map2 shl'.
  Definition shr' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx >> uy ; upper := ux >> ly |}.
  Definition shr : t -> t -> t := t_map2 shr'.
  Definition land' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := 0 ; upper := Z.min ux uy |}.
  Definition land : t -> t -> t := t_map2 land'.
  Definition lor' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in
                                       {| lower := Z.max lx ly;
                                          upper := 2^(Z.max (Z.log2 (ux+1)) (Z.log2 (uy+1))) - 1 |}.
  Definition lor : t -> t -> t := t_map2 lor'.
  Definition neg' : bounds -> bounds -> bounds
    := fun int_width v
       => let (lint_width, uint_width) := int_width in
          let (lb, ub) := v in
          let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
          let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
          if must_be_one
          then {| lower := Z.ones lint_width ; upper := Z.ones uint_width |}
          else if might_be_one
               then {| lower := 0 ; upper := Z.ones uint_width |}
               else {| lower := 0 ; upper := 0 |}.
  Definition neg : t -> t -> t
    := fun int_width v
       => match int_width, v with
          | Some (Build_bounds lint_width uint_width as int_width), Some (Build_bounds lb ub as v)
            => if ((0 <=? lint_width) && (uint_width <=? Word64.bit_width))%Z%bool
               then Some (neg' int_width v)
               else None
          | _, _ => None
          end.
  Definition cmovne' (r1 r2 : bounds) : bounds
    := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
  Definition cmovne (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovne') x y r1 r2.
  Definition cmovle' (r1 r2 : bounds) : bounds
    := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
  Definition cmovle (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovle') x y r1 r2.
  (** TODO(jadep): Check that this is correct; it computes the bounds,
      conditional on the assumption that the entire calculation is
      valid.  Currently, it says that each limb is upper-bounded by
      either the original value less the modulus, or by the smaller of
      the original value and the modulus (in the case that the
      subtraction is negative).  Feel free to substitute any other
      bounds you'd like here. *)
  Definition conditional_subtract' (pred_n : nat) (int_width : bounds)
             (modulus value : Tuple.tuple bounds (S pred_n))
    : Tuple.tuple bounds (S pred_n)
    := Tuple.map2
         (fun modulus_bounds value_bounds : bounds
          => let (ml, mu) := modulus_bounds in
             let (vl, vu) := value_bounds in
             {| lower := 0 ; upper := Z.max (Z.min vu mu) (vu - ml) |})
         modulus value.
  (** TODO(jadep): Fill me in.  This should check that the modulus and
      value fit within int_width, that the modulus is of the right
      form, and that the value is small enough. *)
  Axiom check_conditional_subtract_bounds
    : forall (pred_n : nat) (int_width : bounds)
             (modulus value : Tuple.tuple bounds (S pred_n)), bool.
  Definition conditional_subtract (pred_n : nat) (int_width : t)
             (modulus value : Tuple.tuple t (S pred_n))
    : Tuple.tuple t (S pred_n)
    := Tuple.push_option
         match int_width, Tuple.lift_option modulus, Tuple.lift_option value with
         | Some int_width, Some modulus, Some value
           => if check_conditional_subtract_bounds pred_n int_width modulus value
              then Some (conditional_subtract' pred_n int_width modulus value)
              else None
         | _, _, _ => None
         end.

  Module Export Notations.
    Delimit Scope bounds_scope with bounds.
    Notation "b[ l ~> u ]" := {| lower := l ; upper := u |} : bounds_scope.
    Infix "+" := add : bounds_scope.
    Infix "-" := sub : bounds_scope.
    Infix "*" := mul : bounds_scope.
    Infix "<<" := shl : bounds_scope.
    Infix ">>" := shr : bounds_scope.
    Infix "&'" := land : bounds_scope.
  End Notations.

  Definition interp_base_type (ty : base_type) : Type
    := LiftOption.interp_base_type' bounds ty.
  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | Add => fun xy => fst xy + snd xy
       | Sub => fun xy => fst xy - snd xy
       | Mul => fun xy => fst xy * snd xy
       | Shl => fun xy => fst xy << snd xy
       | Shr => fun xy => fst xy >> snd xy
       | Land => fun xy => land (fst xy) (snd xy)
       | Lor => fun xy => lor (fst xy) (snd xy)
       | Neg => fun xy => neg (fst xy) (snd xy)
       | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
       | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
       | ConditionalSubtract pred_n
         => fun xyz => let '(x, y, z) := eta3 xyz in
                       flat_interp_untuple' (T:=Tbase TZ) (@conditional_subtract pred_n x (flat_interp_tuple y) (flat_interp_tuple z))
       end%bounds.

  Definition of_word64 ty : Word64.interp_base_type ty -> interp_base_type ty
    := match ty return Word64.interp_base_type ty -> interp_base_type ty with
       | TZ => word64ToBounds
       end.

  Ltac inversion_bounds :=
    let lower := (eval cbv [lower] in (fun x => lower x)) in
    let upper := (eval cbv [upper] in (fun y => upper y)) in
    repeat match goal with
           | [ H : _ = _ :> bounds |- _ ]
             => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
                cbv beta iota in *
           | [ H : _ = _ :> t |- _ ]
             => unfold t in H; inversion_option
           end.
End ZBounds.

Module BoundedWord64.
  Local Notation is_bounded_by value lower upper
    := ((0 <= lower /\ lower <= Word64.word64ToZ value <= upper /\ Z.log2 upper < Z.of_nat Word64.bit_width)%Z)
         (only parsing).
  Record BoundedWord :=
    { lower : Z ; value : Word64.word64 ; upper : Z ;
      in_bounds : is_bounded_by value lower upper }.
  Bind Scope bounded_word_scope with BoundedWord.
  Definition t := option BoundedWord.
  Bind Scope bounded_word_scope with t.
  Local Coercion Z.of_nat : nat >-> Z.

  Ltac inversion_BoundedWord :=
    repeat match goal with
           | _ => progress subst
           | [ H : _ = _ :> BoundedWord |- _ ]
             => pose proof (f_equal lower H);
                pose proof (f_equal upper H);
                pose proof (f_equal value H);
                clear H
           end.

  Definition interp_base_type (ty : base_type)
    := LiftOption.interp_base_type' BoundedWord ty.

  Definition word64ToBoundedWord (x : Word64.word64) : t.
  Proof.
    refine (let v := Word64.word64ToZ x in
            match Sumbool.sumbool_of_bool (0 <=? v)%Z, Sumbool.sumbool_of_bool (Z.log2 v <? Z.of_nat Word64.bit_width)%Z with
            | left Hl, left Hu
              => Some {| lower := Word64.word64ToZ x ; value := x ; upper := Word64.word64ToZ x |}
            | _, _ => None
            end).
    subst v.
    abstract (Z.ltb_to_lt; repeat split; (assumption || reflexivity)).
  Defined.

  Definition boundedWordToWord64 (x : t) : Word64.word64
    := match x with
       | Some x' => value x'
       | None => Word64.ZToWord64 0
       end.

  Definition of_word64 ty : Word64.interp_base_type ty -> interp_base_type ty
    := match ty return Word64.interp_base_type ty -> interp_base_type ty with
       | TZ => word64ToBoundedWord
       end.
  Definition to_word64 ty : interp_base_type ty -> Word64.interp_base_type ty
    := match ty return interp_base_type ty -> Word64.interp_base_type ty with
       | TZ => boundedWordToWord64
       end.

  (** XXX FIXME(jgross) This is going to break horribly if we need to support any types other than [Z] *)
  Definition to_word64' ty : BoundedWord -> Word64.interp_base_type ty
    := match ty return BoundedWord -> Word64.interp_base_type ty with
       | TZ => fun x => boundedWordToWord64 (Some x)
       end.

  Definition to_Z' ty : BoundedWord -> Z.interp_base_type ty
    := fun x => Word64.to_Z _ (to_word64' _ x).

  Definition of_Z ty : Z.interp_base_type ty -> interp_base_type ty
    := fun x => of_word64 _ (Word64.of_Z _ x).
  Definition to_Z ty : interp_base_type ty -> Z.interp_base_type ty
    := fun x => Word64.to_Z _ (to_word64 _ x).

  Definition BoundedWordToBounds (x : BoundedWord) : ZBounds.bounds
    := {| ZBounds.lower := lower x ; ZBounds.upper := upper x |}.

  Definition to_bounds' : t -> ZBounds.t
    := option_map BoundedWordToBounds.

  Definition to_bounds ty : interp_base_type ty -> ZBounds.interp_base_type ty
    := match ty return interp_base_type ty -> ZBounds.interp_base_type ty with
       | TZ => to_bounds'
       end.

  Definition t_map2
             (opW : Word64.word64 -> Word64.word64 -> Word64.word64)
             (opB : ZBounds.t -> ZBounds.t -> ZBounds.t)
             (pf : forall x y l u,
                 opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                 = Some {| ZBounds.lower := l ; ZBounds.upper := u |}
                 -> let val :=  opW (value x) (value y) in
                    is_bounded_by val l u)
    : t -> t -> t
    := fun x y : t
       => match x, y with
          | Some x, Some y
            => match opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                     as bop return opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = bop -> t
               with
               | Some (ZBounds.Build_bounds l u)
                 => fun Heq => Some {| lower := l ; value := opW (value x) (value y) ; upper := u;
                                       in_bounds := pf _ _ _ _ Heq |}
               | None => fun _ => None
               end eq_refl
          | _, _ => None
          end.

  Definition t_map4
             (opW : Word64.word64 -> Word64.word64 -> Word64.word64 -> Word64.word64 -> Word64.word64)
             (opB : ZBounds.t -> ZBounds.t -> ZBounds.t -> ZBounds.t -> ZBounds.t)
             (pf : forall x y z w l u,
                 opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                 = Some {| ZBounds.lower := l ; ZBounds.upper := u |}
                 -> let val :=  opW (value x) (value y) (value z) (value w) in
                    is_bounded_by val l u)
    : t -> t -> t -> t -> t
    := fun x y z w : t
       => match x, y, z, w with
          | Some x, Some y, Some z, Some w
            => match opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                         (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                     as bop return opB _ _ _ _ = bop -> t
               with
               | Some (ZBounds.Build_bounds l u)
                 => fun Heq => Some {| lower := l ; value := opW (value x) (value y) (value z) (value w) ; upper := u;
                                       in_bounds := pf _ _ _ _ _ _ Heq |}
               | None => fun _ => None
               end eq_refl
          | _, _, _, _ => None
          end.

  Definition t_map1_tuple2 {n}
             (opW : Word64.word64 -> Tuple.tuple Word64.word64 (S n) -> Tuple.tuple Word64.word64 (S n) -> Tuple.tuple Word64.word64 (S n))
             (opB : ZBounds.t -> Tuple.tuple ZBounds.t (S n) -> Tuple.tuple ZBounds.t (S n) -> Tuple.tuple ZBounds.t (S n))
             (pf : forall x y z bs,
                 Tuple.lift_option
                   (opB (Some (BoundedWordToBounds x)) (Tuple.push_option (Some (Tuple.map BoundedWordToBounds y)))
                        (Tuple.push_option (Some (Tuple.map BoundedWordToBounds z))))
                 = Some bs
                 -> let val := opW (value x) (Tuple.map value y) (Tuple.map value z) in
                    HList.hlist
                      (fun vlu => let v := fst vlu in
                                  let lu : ZBounds.bounds := snd vlu in
                                  is_bounded_by v (ZBounds.lower lu) (ZBounds.upper lu))
                      (Tuple.map2 (fun v (lu : ZBounds.bounds) => (v, lu))
                                  val bs))
    : t -> Tuple.tuple t (S n) -> Tuple.tuple t (S n) -> Tuple.tuple t (S n)
    := fun (x : t) (y z : Tuple.tuple t (S n))
       => Tuple.push_option
            match x, Tuple.lift_option y, Tuple.lift_option z with
            | Some x, Some y, Some z
              => match Tuple.lift_option (opB (Some (BoundedWordToBounds x))
                                              (Tuple.push_option (Some (Tuple.map BoundedWordToBounds y)))
                                              (Tuple.push_option (Some (Tuple.map BoundedWordToBounds z))))
                       as bop return Tuple.lift_option _ = bop -> option (Tuple.tuple _ (S n)) with
                 | Some bs
                   => fun Heq
                      => let v
                             := HList.mapt
                                  (fun (vlu : Word64.word64 * ZBounds.bounds) pf
                                   => {| lower := ZBounds.lower (snd vlu) ; value := fst vlu ; upper := ZBounds.upper (snd vlu) ;
                                         in_bounds := pf |})
                                  (pf _ _ _ _ Heq) in
                         Some v
                 | None => fun _ => None
                 end eq_refl
            | _, _, _ => None
            end.

  Axiom proof_admitted : False.
  Local Opaque Word64.bit_width.
  Hint Resolve Z.ones_nonneg : zarith.
  Local Ltac t_start :=
    repeat first [ match goal with
                   | [ |- forall x y l u, ?opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = Some _ -> let val := ?opW (value x) (value y) in _ ]
                     => try unfold opB; try unfold opW
                   | [ |- forall x y z w l u, ?opB _ _ _ _ = Some _ -> let val := ?opW (value x) (value y) (value z) (value w) in _ ]
                     => try unfold opB; try unfold opW
                   | [ |- appcontext[ZBounds.t_map2 ?op] ] => unfold op
                   | [ |- appcontext[?op (ZBounds.Build_bounds _ _) (ZBounds.Build_bounds _ _)] ] => unfold op
                   end
                 | progress cbv [BoundedWordToBounds ZBounds.SmartBuildBounds cmovne cmovl ModularBaseSystemListZOperations.neg] in *
                 | progress break_match
                 | progress break_match_hyps
                 | progress intros
                 | progress subst
                 | progress ZBounds.inversion_bounds
                 | progress inversion_option
                 | progress Word64.fold_Word64_Z
                 | progress autorewrite with bool_congr_setoid in *
                 | progress destruct_head' and
                 | progress Z.ltb_to_lt
                 | assumption
                 | progress destruct_head' BoundedWord; simpl in *
                 | progress autorewrite with push_word64ToZ
                 | progress repeat apply conj
                 | solve [ Word64.arith ]
                 | match goal with
                   | [ |- appcontext[Z.min ?x ?y] ]
                     => apply (Z.min_case_strong x y)
                   | [ |- appcontext[Z.max ?x ?y] ]
                     => apply (Z.max_case_strong x y)
                   end
                 | progress destruct_head' or ].

  Tactic Notation "admit" := abstract case proof_admitted.


  (** TODO(jadep): Use the bounds lemma here to prove that if each
      component of [ret_val] is [Some (l, v, u)], then we can fill in
      [pf] and return the tuple of [{| lower := l ; value := v ; upper
      := u ; in_bounds := pf |}]. *)
  Lemma conditional_subtract_bounded
        (pred_n : nat) (x : BoundedWord)
        (y z : Tuple.tuple BoundedWord (S pred_n))
        (H : ZBounds.check_conditional_subtract_bounds
               pred_n (BoundedWordToBounds x)
               (Tuple.map BoundedWordToBounds y) (Tuple.map BoundedWordToBounds z) = true)
    : HList.hlist
        (fun vlu : Word64.word64 * ZBounds.bounds =>
           (0 <= ZBounds.lower (snd vlu))%Z /\
           (ZBounds.lower (snd vlu) <= Word64.word64ToZ (fst vlu) <= ZBounds.upper (snd vlu))%Z /\
           (Z.log2 (ZBounds.upper (snd vlu)) < Word64.bit_width)%Z)
        (Tuple.map2 (fun v lu => (v, lu))
                    (Word64.conditional_subtract
                       pred_n (value x) (Tuple.map value y) (Tuple.map value z))
                    (ZBounds.conditional_subtract'
                       pred_n (BoundedWordToBounds x)
                       (Tuple.map BoundedWordToBounds y) (Tuple.map BoundedWordToBounds z))).
  Proof. Admitted.


  Definition add : t -> t -> t.
  Proof.
    refine (t_map2 Word64.add ZBounds.add _); t_start; admit.
  Defined.

  Definition sub : t -> t -> t.
  Proof.
    refine (t_map2 Word64.sub ZBounds.sub _); t_start;
      admit.
  Defined.

  Definition mul : t -> t -> t.
  Proof.
    refine (t_map2 Word64.mul ZBounds.mul _); t_start;
      admit.
  Defined.

  Definition shl : t -> t -> t.
  Proof.
    refine (t_map2 Word64.shl ZBounds.shl _); t_start;
      admit.
  Defined.

  Definition shr : t -> t -> t.
  Proof.
    refine (t_map2 Word64.shr ZBounds.shr _); t_start;
      admit.
  Defined.

  Definition land : t -> t -> t.
  Proof.
    refine (t_map2 Word64.land ZBounds.land _); t_start;
      admit.
  Defined.

  Definition lor : t -> t -> t.
  Proof.
    refine (t_map2 Word64.lor ZBounds.lor _); t_start;
      admit.
  Defined.

  Definition neg : t -> t -> t.
  Proof. refine (t_map2 Word64.neg ZBounds.neg _); abstract t_start. Defined.

  Definition cmovne : t -> t -> t -> t -> t.
  Proof. refine (t_map4 Word64.cmovne ZBounds.cmovne _); abstract t_start. Defined.

  Definition cmovle : t -> t -> t -> t -> t.
  Proof. refine (t_map4 Word64.cmovle ZBounds.cmovle _); abstract t_start. Defined.

  Definition conditional_subtract (pred_n : nat)
    : forall (int_width : t) (modulus val : Tuple.tuple t (S pred_n)),
      Tuple.tuple t (S pred_n).
  Proof.
    refine (@t_map1_tuple2 pred_n (@Word64.conditional_subtract _) (@ZBounds.conditional_subtract _) _).
    abstract (
        repeat first [ progress unfold ZBounds.conditional_subtract
                     | rewrite !Tuple.lift_push_option
                     | progress break_match
                     | congruence
                     | progress subst
                     | progress inversion_option
                     | intro
                     | solve [ auto using conditional_subtract_bounded ] ]
      ).
  Defined.

  Local Notation binop_correct op opW opB :=
    (forall x y v, op (Some x) (Some y) = Some v
                   -> value v = opW (value x) (value y)
                      /\ Some (BoundedWordToBounds v) = opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)))
      (only parsing).

  Local Notation op4_correct op opW opB :=
    (forall x y z w v, op (Some x) (Some y) (Some z) (Some w) = Some v
                       -> value v = opW (value x) (value y) (value z) (value w)
                          /\ Some (BoundedWordToBounds v) = opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                                                                (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w)))
      (only parsing).

  Local Notation op1_tuple2_correct op opW opB :=
    (forall x y z v,
        Tuple.lift_option (op (Some x) (Tuple.push_option (Some y)) (Tuple.push_option (Some z))) = Some v
        -> Tuple.map value v = opW (value x) (Tuple.map value y) (Tuple.map value z)
           /\ Some (Tuple.map BoundedWordToBounds v)
              = Tuple.lift_option
                  (opB (Some (BoundedWordToBounds x))
                       (Tuple.push_option (Some (Tuple.map BoundedWordToBounds y)))
                       (Tuple.push_option (Some (Tuple.map BoundedWordToBounds z)))))
      (only parsing).

  Lemma t_map2_correct opW opB pf
    : binop_correct (t_map2 opW opB pf) opW opB.
  Proof.
    intros ??? H.
    unfold t_map2 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
      unfold BoundedWordToBounds in *;
      inversion_option; subst; simpl.
    eauto.
  Qed.

  Lemma t_map4_correct opW opB pf
    : op4_correct (t_map4 opW opB pf) opW opB.
  Proof.
    intros ????? H.
    unfold t_map4 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
      unfold BoundedWordToBounds in *;
      inversion_option; subst; simpl.
    eauto.
  Qed.

  (* TODO: Automate this proof more *)
  Lemma t_map1_tuple2_correct {n} opW opB pf
    : op1_tuple2_correct (t_map1_tuple2 (n:=n) opW opB pf) opW opB.
  Proof.
    intros ???? H.
    unfold t_map1_tuple2 in H; unfold BoundedWordToBounds in *.
    rewrite !Tuple.lift_push_option in H.
    convoy_destruct_in H; [ | congruence ].
    rewrite_hyp *.
    inversion_option.
    symmetry in H.
    pose proof (f_equal (Tuple.map value) H) as H0'.
    pose proof (f_equal (Tuple.map BoundedWordToBounds) H) as H1'.
    unfold BoundedWordToBounds in *.
    rewrite_hyp !*.
    rewrite !HList.map_mapt; simpl @lower; simpl @upper; simpl @value.
    rewrite <- !HList.map_is_mapt.
    rewrite !Tuple.map_map2; simpl @fst; simpl @snd.
    rewrite !Tuple.map2_fst, !Tuple.map2_snd, Tuple.map_id, Tuple.map_id_ext
      by (intros [? ?]; reflexivity).
    eauto.
  Qed.

  Local Notation binop_correct_None op opW opB :=
    (forall x y, op (Some x) (Some y) = None -> opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = None)
      (only parsing).

  Local Notation op4_correct_None op opW opB :=
    (forall x y z w, op (Some x) (Some y) (Some z) (Some w) = None
                     -> opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                            (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                        = None)
      (only parsing).

  Local Notation op1_tuple2_correct_None op opW opB :=
    (forall x y z,
        Tuple.lift_option (op (Some x) (Tuple.push_option (Some y)) (Tuple.push_option (Some z))) = None
        -> Tuple.lift_option
             (opB (Some (BoundedWordToBounds x))
                  (Tuple.push_option (Some (Tuple.map BoundedWordToBounds y)))
                  (Tuple.push_option (Some (Tuple.map BoundedWordToBounds z))))
           = None)
      (only parsing).

  Lemma t_map2_correct_None opW opB pf
    : binop_correct_None (t_map2 opW opB pf) opW opB.
  Proof.
    intros ?? H.
    unfold t_map2 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
      unfold BoundedWordToBounds in *;
      inversion_option; subst; simpl.
    eauto.
  Qed.

  Lemma t_map4_correct_None opW opB pf
    : op4_correct_None (t_map4 opW opB pf) opW opB.
  Proof.
    intros ???? H.
    unfold t_map4 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
      unfold BoundedWordToBounds in *;
      inversion_option; subst; simpl.
    eauto.
  Qed.

  Lemma t_map1_tuple2_correct_None {n} opW opB pf
    : op1_tuple2_correct_None (t_map1_tuple2 (n:=n) opW opB pf) opW opB.
  Proof.
    intros ??? H.
    unfold t_map1_tuple2 in H; unfold BoundedWordToBounds in *.
    rewrite !Tuple.lift_push_option in H.
    convoy_destruct_in H; congruence.
  Qed.

  Module Export Notations.
    Delimit Scope bounded_word_scope with bounded_word.
    Notation "b[ l ~> u ]" := {| lower := l ; upper := u |} : bounded_word_scope.
    Infix "+" := add : bounded_word_scope.
    Infix "-" := sub : bounded_word_scope.
    Infix "*" := mul : bounded_word_scope.
    Infix "<<" := shl : bounded_word_scope.
    Infix ">>" := shr : bounded_word_scope.
    Infix "&'" := land : bounded_word_scope.
  End Notations.

  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | Add => fun xy => fst xy + snd xy
       | Sub => fun xy => fst xy - snd xy
       | Mul => fun xy => fst xy * snd xy
       | Shl => fun xy => fst xy << snd xy
       | Shr => fun xy => fst xy >> snd xy
       | Land => fun xy => land (fst xy) (snd xy)
       | Lor => fun xy => lor (fst xy) (snd xy)
       | Neg => fun xy => neg (fst xy) (snd xy)
       | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
       | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
       | ConditionalSubtract pred_n
         => fun xyz => let '(x, y, z) := eta3 xyz in
                       flat_interp_untuple' (T:=Tbase TZ) (@conditional_subtract pred_n x (flat_interp_tuple y) (flat_interp_tuple z))
     end%bounded_word.
End BoundedWord64.

Module ZBoundsTuple.
  Definition interp_flat_type (t : flat_type base_type)
    := LiftOption.interp_flat_type ZBounds.bounds t.

  Definition of_ZBounds {ty} : Syntax.interp_flat_type ZBounds.interp_base_type ty -> interp_flat_type ty
    := @LiftOption.of' ZBounds.bounds ty.
  Definition to_ZBounds {ty} : interp_flat_type ty -> Syntax.interp_flat_type ZBounds.interp_base_type ty
    := @LiftOption.to' ZBounds.bounds ty.
End ZBoundsTuple.

Module BoundedWord64Tuple.
  Definition interp_flat_type (t : flat_type base_type)
    := LiftOption.interp_flat_type BoundedWord64.BoundedWord t.

  Definition of_BoundedWord64 {ty} : Syntax.interp_flat_type BoundedWord64.interp_base_type ty -> interp_flat_type ty
    := @LiftOption.of' BoundedWord64.BoundedWord ty.
  Definition to_BoundedWord64 {ty} : interp_flat_type ty -> Syntax.interp_flat_type BoundedWord64.interp_base_type ty
    := @LiftOption.to' BoundedWord64.BoundedWord ty.
End BoundedWord64Tuple.
