(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
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
    := fun x y z w => ZToWord64 (ModularBaseSystemListZOperations.cmovne (word64ToZ x) (word64ToZ x) (word64ToZ z) (word64ToZ w)).
  Definition cmovle : word64 -> word64 -> word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y z w => ZToWord64 (ModularBaseSystemListZOperations.cmovl (word64ToZ x) (word64ToZ x) (word64ToZ z) (word64ToZ w)).
  Definition conditional_subtract (pred_limb_count : nat) : word64 -> Tuple.tuple word64 (S pred_limb_count) -> Tuple.tuple word64 (S pred_limb_count) -> Tuple.tuple word64 (S pred_limb_count)
    := fun x y z => Tuple.map ZToWord64 (@ModularBaseSystemListZOperations.conditional_subtract_modulus
                                           (S pred_limb_count) (word64ToZ x) (Tuple.map word64ToZ y) (Tuple.map word64ToZ z)).
  Infix "+" := add : word64_scope.
  Infix "-" := sub : word64_scope.
  Infix "*" := mul : word64_scope.
  Infix "<<" := shl : word64_scope.
  Infix ">>" := shr : word64_scope.
  Infix "&'" := land : word64_scope.

  Local Ltac w64ToZ_t :=
    intros;
    try match goal with
        | [ |- ?wordToZ (?op ?x ?y) = _ ]
          => cbv [wordToZ op] in *
        end;
    autorewrite with push_Zto_N push_Zof_N push_wordToN; try reflexivity.

  Local Notation bounds_2statement wop Zop
    := (forall x y,
           (0 <= Zop (word64ToZ x) (word64ToZ y)
            -> Z.log2 (Zop (word64ToZ x) (word64ToZ y)) < Z.of_nat bit_width
            -> word64ToZ (wop x y) = (Zop (word64ToZ x) (word64ToZ y)))%Z).

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
  Definition cmovne (x y r1 r2 : t) : t := t_map2 cmovne' r1 r2.
  Definition cmovle' (r1 r2 : bounds) : bounds
    := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
  Definition cmovle (x y r1 r2 : t) : t := t_map2 cmovle' r1 r2.
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
      form, and that the value is small enough.  If not, it should
      [None]; otherwise, it should delegate to
      [conditional_subtract']. *)
  Axiom conditional_subtract_o
    : forall (pred_n : nat) (int_width : bounds)
             (modulus value : Tuple.tuple bounds (S pred_n)), option (Tuple.tuple bounds (S pred_n)).
  Definition conditional_subtract (pred_n : nat) (int_width : t)
             (modulus value : Tuple.tuple t (S pred_n))
    : Tuple.tuple t (S pred_n)
    := Tuple.push_option
         match int_width, Tuple.lift_option modulus, Tuple.lift_option value with
         | Some int_width, Some modulus, Some value
           => conditional_subtract_o pred_n int_width modulus value
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
  Record BoundedWord :=
    { lower : Z ; value : Word64.word64 ; upper : Z ;
      in_bounds : (0 <= lower /\ lower <= Word64.word64ToZ value <= upper /\ Z.log2 upper < Z.of_nat Word64.bit_width)%Z }.
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

  Definition to_bounds' := BoundedWordToBounds.

  Definition to_bounds ty : interp_base_type ty -> ZBounds.interp_base_type ty
    := match ty return interp_base_type ty -> ZBounds.interp_base_type ty with
       | TZ => option_map to_bounds'
       end.

  Local Ltac build_binop word_op bounds_op :=
    refine (fun x y : t
            => match x, y with
               | Some x, Some y
                 => match bounds_op (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                          as bop return bounds_op (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = bop -> t
                    with
                    | Some (ZBounds.Build_bounds l u)
                      => let pff := _ in
                         fun pf => Some {| lower := l ; value := word_op (value x) (value y) ; upper := u;
                                           in_bounds := pff pf |}
                    | None => fun _ => None
                    end eq_refl
               | _, _ => None
               end);
    try unfold bounds_op; try unfold word_op;
    repeat match goal with
           | [ |- appcontext[ZBounds.t_map2 ?op] ] => unfold op
           | [ |- appcontext[?op (ZBounds.Build_bounds _ _) (ZBounds.Build_bounds _ _)] ] => unfold op
           | _ => progress cbv [ZBounds.t_map2 BoundedWordToBounds ZBounds.SmartBuildBounds ModularBaseSystemListZOperations.neg]
           end.

  Local Ltac build_4op word_op bounds_op :=
    refine (fun x y z w : t
            => match x, y, z, w with
               | Some x, Some y, Some z, Some w
                 => match bounds_op (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                                    (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                          as bop return bounds_op (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                                                  (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                                        = bop -> t
                    with
                    | Some (ZBounds.Build_bounds l u)
                      => let pff := _ in
                         fun pf => Some {| lower := l ; value := word_op (value x) (value y) (value z) (value w) ; upper := u;
                                           in_bounds := pff pf |}
                    | None => fun _ => None
                    end eq_refl
               | _, _, _, _ => None
               end);
    try unfold bounds_op; try unfold word_op;
    repeat match goal with
           | [ |- appcontext[ZBounds.t_map2 ?op] ] => unfold op
           | [ |- appcontext[?op (ZBounds.Build_bounds _ _) (ZBounds.Build_bounds _ _)] ] => unfold op
           | _ => progress cbv [ZBounds.t_map2 BoundedWordToBounds ZBounds.SmartBuildBounds cmovne cmovl]
           end.

  Axiom proof_admitted : False.
  Local Opaque Word64.bit_width.
  Hint Resolve Z.ones_nonneg : zarith.
  Local Ltac t_start :=
    repeat first [ progress break_match
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

  Definition add : t -> t -> t.
  Proof.
    build_binop Word64.add ZBounds.add; t_start;
      admit.
  Defined.

  Definition sub : t -> t -> t.
  Proof.
    build_binop Word64.sub ZBounds.sub; t_start;
      admit.
  Defined.

  Definition mul : t -> t -> t.
  Proof.
    build_binop Word64.mul ZBounds.mul; t_start;
      admit.
  Defined.

  Definition shl : t -> t -> t.
  Proof.
    build_binop Word64.shl ZBounds.shl; t_start;
      admit.
  Defined.

  Definition shr : t -> t -> t.
  Proof.
    build_binop Word64.shr ZBounds.shr; t_start;
      admit.
  Defined.

  Definition land : t -> t -> t.
  Proof.
    build_binop Word64.land ZBounds.land; t_start;
      admit.
  Defined.

  Definition lor : t -> t -> t.
  Proof.
    build_binop Word64.lor ZBounds.lor; t_start;
      admit.
  Defined.

  Definition neg : t -> t -> t.
  Proof. build_binop Word64.neg ZBounds.neg; abstract t_start. Defined.

  Definition cmovne : t -> t -> t -> t -> t.
  Proof. build_4op Word64.cmovne ZBounds.cmovne; abstract t_start. Defined.

  Definition cmovle : t -> t -> t -> t -> t.
  Proof. build_4op Word64.cmovle ZBounds.cmovle; abstract t_start. Defined.

  Definition conditional_subtract (pred_n : nat) (int_width : t)
             (modulus val : Tuple.tuple t (S pred_n))
    : Tuple.tuple t (S pred_n).
  Proof.
    refine (match int_width, Tuple.lift_option modulus, Tuple.lift_option val with
            | Some int_width, Some modulus, Some val
              => let boundsv := Tuple.push_option
                                  (ZBounds.conditional_subtract_o
                                     pred_n (BoundedWordToBounds int_width)
                                     (Tuple.map BoundedWordToBounds modulus)
                                     (Tuple.map BoundedWordToBounds val)) in
                 let wordv := (Word64.conditional_subtract
                                 pred_n (value int_width)
                                 (Tuple.map value modulus)
                                 (Tuple.map value val)) in
                 let ret_val := Tuple.map2
                                  (fun bs val
                                   => option_map (fun bs' : ZBounds.bounds
                                                  => let (l, u) := bs' in
                                                     (l, val, u)) bs)
                                  boundsv wordv in
                 _
            | _, _, _ => Tuple.push_option None
            end).
    (** TODO(jadep): Use the bounds lemma here to prove that if each
        component of [ret_val] is [Some (l, v, u)], then we can fill
        in [pf] and return the tuple of [{| lower := l ; value := v ;
        upper := u ; in_bounds := pf |}]. *)
    admit.
  Defined.


  Local Notation binop_correct op opW opB :=
    (forall x y v, op (Some x) (Some y) = Some v -> value v = opW (value x) (value y)
                                                    /\ BoundedWordToBounds v = opB (BoundedWordToBounds x) (BoundedWordToBounds y))
      (only parsing).

  Local Notation op4_correct op opW opB :=
    (forall x y z w v, op (Some x) (Some y) (Some z) (Some w) = Some v
                       -> value v = opW (value x) (value y) (value z) (value w)
                          /\ BoundedWordToBounds v = opB (BoundedWordToBounds x) (BoundedWordToBounds y) (BoundedWordToBounds z) (BoundedWordToBounds w))
      (only parsing).

  Local Ltac convoy_destruct_in H :=
    match type of H with
    | context G[match ?e with Some x => @?S x | None => ?N end eq_refl]
      => let e' := fresh in
         let H' := fresh in
         pose e as e';
         pose (eq_refl : e = e') as H';
         let G' := context G[match e' with Some x => S x | None => N end H'] in
         change G' in H;
         clearbody H' e'; destruct e'
    end.
  Local Arguments ZBounds.SmartBuildBounds _ _ / .
  Local Arguments BoundedWordToBounds _ / .
  Local Ltac invert_t_step :=
    match goal with
    | _ => progress intros
    | [ |- ?x = ?x ] => reflexivity
    | [ H : context[match _ with _ => _ end eq_refl] |- _ ] => convoy_destruct_in H
    | _ => progress destruct_head' BoundedWord
    | _ => progress destruct_head' ZBounds.bounds
    | _ => progress inversion_option
    | _ => progress ZBounds.inversion_bounds
    | _ => progress inversion_BoundedWord
    | _ => progress simpl in *
    | _ => progress break_match_hyps
    | [ |- _ /\ _ ] => split
    end.
  Local Ltac invert_t := repeat invert_t_step.
  Definition invert_add : binop_correct add Word64.add ZBounds.add'.
  Proof. invert_t. Qed.
  Definition invert_sub : binop_correct sub Word64.sub ZBounds.sub'.
  Proof. invert_t. Qed.
  Definition invert_mul : binop_correct mul Word64.mul ZBounds.mul'.
  Proof. invert_t. Qed.
  Definition invert_shl : binop_correct shl Word64.shl ZBounds.shl'.
  Proof. invert_t. Qed.
  Definition invert_shr : binop_correct shr Word64.shr ZBounds.shr'.
  Proof. invert_t. Qed.
  Definition invert_land : binop_correct land Word64.land ZBounds.land'.
  Proof. invert_t. Qed.
  Definition invert_lor : binop_correct lor Word64.lor ZBounds.lor'.
  Proof. invert_t. Qed.
  Definition invert_neg : binop_correct neg Word64.neg ZBounds.neg'.
  Proof. invert_t. Qed.
  Definition invert_cmovne : op4_correct cmovne Word64.cmovne (fun _ _ => ZBounds.cmovne').
  Proof. invert_t. Qed.
  Definition invert_cmovle : op4_correct cmovle Word64.cmovle (fun _ _ => ZBounds.cmovle').
  Proof. invert_t. Qed.
  (** TODO(jadep): Fill me in *)
  Definition invert_conditional_subtract : False.
  Proof. Admitted.

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
