(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Bedrock.Nomega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.WordUtil.
Require Import Bedrock.Word.
Require Import Crypto.Assembly.WordizeUtil.
Require Import Crypto.Assembly.Evaluables.
Require Import Crypto.Assembly.QhasmUtil.
Export Reflection.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Module Z.
  Definition interp_base_type (t : base_type) : Type := interp_base_type t.
  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := interp_op src dst f.
End Z.

Module Word64.
  Definition bit_width : nat := 64.
  Definition word64 := word bit_width.
  Delimit Scope word64_scope with word64.
  Bind Scope word64_scope with word64.

  Definition word64ToZ (x : word64) : Z
    := Z.of_N (wordToN x).
  Definition ZToWord64 (x : Z) : word64
    := NToWord _ (Z.to_N x).

  Create HintDb push_word64ToZ discriminated.
  Hint Extern 1 => progress autorewrite with push_word64ToZ in * : push_word64ToZ.

  Definition w64plus : word64 -> word64 -> word64 := @wplus _.
  Definition w64minus : word64 -> word64 -> word64 := @wminus _.
  Definition w64mul : word64 -> word64 -> word64 := @wmult _.
  Definition w64shl : word64 -> word64 -> word64
    := fun x y => NToWord _ (Z.to_N (Z.shiftl (Z.of_N (wordToN x)) (Z.of_N (wordToN y)))).
  Definition w64shr : word64 -> word64 -> word64
    := fun x y => NToWord _ (Z.to_N (Z.shiftr (Z.of_N (wordToN x)) (Z.of_N (wordToN y)))).
  Definition w64land : word64 -> word64 -> word64 := @wand _.
  Definition w64lor : word64 -> word64 -> word64 := @wor _.
  Definition w64neg : word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y => NToWord _ (Z.to_N (ModularBaseSystemListZOperations.neg (Z.of_N (wordToN x)) (Z.of_N (wordToN x)))).
  Definition w64cmovne : word64 -> word64 -> word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y z w => NToWord _ (Z.to_N (ModularBaseSystemListZOperations.cmovne (Z.of_N (wordToN x)) (Z.of_N (wordToN x)) (Z.of_N (wordToN z)) (Z.of_N (wordToN w)))).
  Definition w64cmovle : word64 -> word64 -> word64 -> word64 -> word64 (* TODO: FIXME? *)
    := fun x y z w => NToWord _ (Z.to_N (ModularBaseSystemListZOperations.cmovl (Z.of_N (wordToN x)) (Z.of_N (wordToN x)) (Z.of_N (wordToN z)) (Z.of_N (wordToN w)))).
  Infix "+" := w64plus : word64_scope.
  Infix "-" := w64minus : word64_scope.
  Infix "*" := w64mul : word64_scope.
  Infix "<<" := w64shl : word64_scope.
  Infix ">>" := w64shr : word64_scope.
  Infix "&'" := w64land : word64_scope.

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

  Require Import Crypto.Assembly.WordizeUtil.

  Lemma word64ToZ_w64plus : bounds_2statement w64plus Z.add. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_w64minus : bounds_2statement w64minus Z.sub. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_w64mul : bounds_2statement w64mul Z.mul. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_w64land : bounds_2statement w64land Z.land. Proof. w64ToZ_t. Qed.
  Lemma word64ToZ_w64lor : bounds_2statement w64lor Z.lor. Proof. w64ToZ_t. Qed.

  Lemma word64ToZ_w64shl : bounds_2statement w64shl Z.shiftl.
  Proof.
    intros x y H H0.
    w64ToZ_t.

    destruct (N.eq_dec (Z.to_N (Z.of_N (wordToN x) << Z.of_N (wordToN y))) 0%N) as [e|e]; [
      rewrite e; rewrite wordToN_NToWord; [|apply Npow2_gt0];
      rewrite <- e; rewrite Z2N.id; [reflexivity|assumption]
    | apply N.neq_0_lt_0 in e].

    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z.shiftl_spec; [|assumption].
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite wordToN_NToWord.

    - rewrite <- N2Z.inj_testbit.
      rewrite (Z2N.id k); [|assumption].
      rewrite Z2N.id; [|assumption].
      rewrite Z.shiftl_spec; [reflexivity|assumption].

    - rewrite Npow2_N.
      apply N.log2_lt_pow2; [assumption|].
      apply N2Z.inj_lt.
      rewrite nat_N_Z.
      refine (Z.le_lt_trans _ _ _ _ H0).
      rewrite log2_conv; reflexivity.
  Qed.

  Lemma word64ToZ_w64shr : bounds_2statement w64shr Z.shiftr.
  Proof.
    intros x y H H0.
    w64ToZ_t.

    destruct (N.eq_dec (Z.to_N (Z.of_N (wordToN x) >> Z.of_N (wordToN y))) 0%N) as [e|e]; [
      rewrite e; rewrite wordToN_NToWord; [|apply Npow2_gt0];
      rewrite <- e; rewrite Z2N.id; [reflexivity|assumption]
    | apply N.neq_0_lt_0 in e].

    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z.shiftr_spec; [|assumption].
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite wordToN_NToWord.

    - rewrite <- N2Z.inj_testbit.
      rewrite (Z2N.id k); [|assumption].
      rewrite Z2N.id; [|assumption].
      rewrite Z.shiftr_spec; [reflexivity|assumption].

    - rewrite Npow2_N.
      apply N.log2_lt_pow2; [assumption|].
      apply N2Z.inj_lt.
      rewrite nat_N_Z.
      refine (Z.le_lt_trans _ _ _ _ H0).
      rewrite log2_conv; reflexivity.
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
       | Land => fun xy => w64land (fst xy) (snd xy)
       | Lor => fun xy => w64lor (fst xy) (snd xy)
       | Neg => fun xy => w64neg (fst xy) (snd xy)
       | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in w64cmovne x y z w
       | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in w64cmovle x y z w
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

    Hint Rewrite word64ToZ_w64plus using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64plus using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64minus using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64minus using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64mul using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64mul using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64shl using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64shl using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64shr using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64shr using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64land using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64land using word64_util_arith : pull_word64ToZ.
    Hint Rewrite word64ToZ_w64lor using word64_util_arith : push_word64ToZ.
    Hint Rewrite <- word64ToZ_w64lor using word64_util_arith : pull_word64ToZ.
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
  Definition t_map2 (f : Z -> Z -> Z -> Z -> bounds) (x y : t)
    := match x, y with
       | Some (Build_bounds lx ux), Some (Build_bounds ly uy)
         => match f lx ly ux uy with
            | Build_bounds l u
              => SmartBuildBounds l u
            end
       | _, _ => None
       end%Z.

  Definition add : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := lx + ly ; upper := ux + uy |}).
  Definition sub : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := lx - uy ; upper := ux - ly |}).
  Definition mul : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := lx * ly ; upper := ux * uy |}).
  Definition shl : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := lx << ly ; upper := ux << uy |}).
  Definition shr : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := lx >> uy ; upper := ux >> ly |}).
  Definition land : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := 0 ;
                                     upper := 2^(Z.succ (Z.min (Z.log2 ux) (Z.log2 uy))) |}).
  Definition lor : t -> t -> t
    := t_map2 (fun lx ly ux uy => {| lower := Z.max lx ly;
                                     upper := 2^(Z.succ (Z.max (Z.log2 ux) (Z.log2 uy))) |}).
  Definition neg : t -> t -> t
    := t_map2 (fun lint_width lb uint_width ub
               => let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
                  let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
                  if must_be_one
                  then {| lower := Z.ones lint_width ; upper := Z.ones uint_width |}
                  else if might_be_one
                       then {| lower := 0 ; upper := Z.ones uint_width |}
                       else {| lower := 0 ; upper := 0 |}).
  Definition cmovne (x y r1 r2 : t) : t
    := match x, y with
       | Some (Build_bounds lx ux), Some (Build_bounds ly uy)
         => let must_be_equal := ((lx =? ux) && (ly =? uy) && (lx =? ly))%Z%bool in
            let might_be_equal := ((lx <=? uy) && (ly <=? ux))%Z%bool in
            if must_be_equal
            then r1
            else if negb might_be_equal
                 then r2
                 else t_map2 (fun lr1 lr2 ur1 ur2 => {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}) r1 r2
       | _, _ => None
       end%Z.
  Definition cmovle (x y r1 r2 : t) : t
    := match x, y with
       | Some (Build_bounds lx ux), Some (Build_bounds ly uy)
         => let must_be_le := (ux <=? ly)%Z in
            let might_be_le := (lx <=? uy)%Z in
            if must_be_le
            then r1
            else if negb might_be_le
                 then r2
                 else t_map2 (fun lr1 lr2 ur1 ur2 => {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}) r1 r2
       | _, _ => None
       end%Z.

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
    := match ty with
       | TZ => t
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

  Definition interp_base_type (ty : base_type) : Type
    := match ty with
       | TZ => t
       end.


  Definition word64ToBoundedWord (x : Word64.word64) : t.
  Proof.
    refine (let v := Word64.word64ToZ x in
            (if (0 <=? v)%Z as Hl return (0 <=? v)%Z = Hl -> t
             then (if (Z.log2 v <? Z.of_nat Word64.bit_width)%Z as Hu return (Z.log2 v <? Z.of_nat Word64.bit_width)%Z = Hu -> _ -> t
                   then fun Hu Hl => Some {| lower := Word64.word64ToZ x ; value := x ; upper := Word64.word64ToZ x |}
                   else fun _ _ => None) eq_refl
             else fun _ => None) eq_refl).
    subst v.
    abstract (Z.ltb_to_lt; repeat split; (assumption || reflexivity)).
  Defined.

  Definition of_word64 ty : Word64.interp_base_type ty -> interp_base_type ty
    := match ty return Word64.interp_base_type ty -> interp_base_type ty with
       | TZ => word64ToBoundedWord
       end.

  Definition BoundedWordToBounds (x : BoundedWord) : ZBounds.bounds
    := {| ZBounds.lower := lower x ; ZBounds.upper := upper x |}.

  Definition to_bounds ty : interp_base_type ty -> ZBounds.interp_base_type ty
    := match ty return interp_base_type ty -> ZBounds.interp_base_type ty with
       | TZ => option_map BoundedWordToBounds
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
    try unfold word_op; try unfold bounds_op;
    cbv [ZBounds.t_map2 BoundedWordToBounds ZBounds.SmartBuildBounds].

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
    try unfold word_op; try unfold bounds_op;
    cbv [ZBounds.t_map2 BoundedWordToBounds ZBounds.SmartBuildBounds].

  Local Ltac t_start :=
    repeat first [ progress break_match
                 | progress intros
                 | progress subst
                 | progress ZBounds.inversion_bounds
                 | progress inversion_option
                 | progress autorewrite with bool_congr_setoid in *
                 | progress destruct_head' and
                 | progress Z.ltb_to_lt
                 | assumption
                 | progress destruct_head' BoundedWord; simpl in *
                 | progress autorewrite with push_word64ToZ
                 | progress repeat apply conj ].

  Ltac ktrans k := do k (etransitivity; [|eassumption]); assumption.
  Ltac trans' := first [ assumption | ktrans ltac:1 | ktrans ltac:2 ].

  Definition add : t -> t -> t.
  Proof.
    Ltac add_mono :=
      etransitivity;
      [apply Z.add_le_mono_l | apply Z.add_le_mono_r];
      trans'.

    build_binop Word64.w64plus ZBounds.add; t_start;
      unfold Word64.word64ToZ; rewrite wordToN_wplus; abstract first
    [ add_mono
    | transitivity (lower1 + lower0)%Z; [assumption|]; add_mono
    | eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; add_mono ].
  Defined.

  Definition sub : t -> t -> t.
  Proof.
    Ltac sub_mono :=
      etransitivity;
      [| apply Z.sub_le_mono_r; eassumption]; first
      [ apply Z.sub_le_mono_l; assumption
      | apply Z.le_add_le_sub_l; etransitivity;
          [|eassumption]; repeat rewrite Z.add_0_r; assumption].

    build_binop Word64.w64minus ZBounds.sub; t_start;
      unfold Word64.word64ToZ; rewrite wordToN_wminus;
      apply Z.le_add_le_sub_l in H; abstract first
    [ sub_mono
    | transitivity (lower1 - lower0)%Z; [assumption|]; sub_mono
    | eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; sub_mono ].
  Defined.

  Definition mul : t -> t -> t.
  Proof.
    Ltac mul_mono :=
      etransitivity;
      [apply Z.mul_le_mono_nonneg_l | apply Z.mul_le_mono_nonneg_r];
      trans'.

    build_binop Word64.w64mul ZBounds.mul; t_start;
      unfold Word64.word64ToZ; rewrite wordToN_wmult; abstract first
    [ mul_mono
    | transitivity (lower1 * lower0)%Z; [assumption|]; mul_mono
    | eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; mul_mono ].
  Defined.

  Definition shl : t -> t -> t.
  Proof.
    Ltac shl_mono := etransitivity;
      [apply Z.mul_le_mono_nonneg_l | apply Z.mul_le_mono_nonneg_r].

    build_binop Word64.w64shl ZBounds.shl; t_start; abstract (
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite Z.shiftl_mul_pow2 in *;
      repeat match goal with
      | [|- (0 <= 2 ^ _)%Z ] => apply Z.pow_nonneg
      | [|- (0 <= _ * _)%Z ] => apply Z.mul_nonneg_nonneg
      | [|- (2 ^ _ <= 2 ^ _)%Z ] => apply Z.pow_le_mono_r
      | [|- context[(?a << ?b)%Z]] => rewrite Z.shiftl_mul_pow2
      | [|- (_ < Npow2 _)%N] => 
        apply N2Z.inj_lt, Z.log2_lt_cancel; simpl;
        eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; rewrite Z2N.id

      | _ => progress shl_mono
      | _ => progress trans'
      | _ => progress omega
      end).
  Defined.

  Definition shr : t -> t -> t.
  Proof.
    Ltac shr_mono := etransitivity;
      [apply Z.div_le_compat_l | apply Z.div_le_mono].

    assert (forall x, (0 <= x)%Z -> (0 < 2^x)%Z) as gt0. {
      intros; rewrite <- (Z2Nat.id x); [|assumption].
      induction (Z.to_nat x) as [|n]; [cbv; auto|].
      eapply Z.lt_le_trans; [eassumption|rewrite Nat2Z.inj_succ].
      apply Z.pow_le_mono_r; [cbv; auto|omega].
    }

    build_binop Word64.w64shr ZBounds.shr; t_start; abstract (
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite Z.shiftr_div_pow2 in *;
      repeat match goal with
      | [|- _ /\ _ ] => split
      | [|- (0 <= 2 ^ _)%Z ] => apply Z.pow_nonneg
      | [|- (0 < 2 ^ ?X)%Z ] => apply gt0
      | [|- (0 <= _ / _)%Z ] => apply Z.div_le_lower_bound; [|rewrite Z.mul_0_r]
      | [|- (2 ^ _ <= 2 ^ _)%Z ] => apply Z.pow_le_mono_r
      | [|- context[(?a >> ?b)%Z]] => rewrite Z.shiftr_div_pow2 in *
      | [|- (_ < Npow2 _)%N] => 
        apply N2Z.inj_lt, Z.log2_lt_cancel; simpl;
        eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; rewrite Z2N.id

      | _ => progress shr_mono
      | _ => progress trans'
      | _ => progress omega
      end).
  Defined.

  Definition land : t -> t -> t.
  Proof.
    build_binop Word64.w64land ZBounds.land; t_start; [apply N2Z.is_nonneg|];
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite wordize_and.

    destruct (Z_ge_dec upper1 upper0) as [g|g].

    - rewrite Z.min_r; [|abstract (apply Z.log2_le_mono; omega)].
      abstract (
        rewrite (land_intro_ones (wordToN value0));
        rewrite N.land_assoc;
        etransitivity; [apply N2Z.inj_le; apply N.lt_le_incl; apply land_lt_Npow2|];
        rewrite N2Z.inj_pow;
        apply Z.pow_le_mono; [abstract (split; cbn; [omega|reflexivity])|];
        unfold getBits; rewrite N2Z.inj_succ;
        apply -> Z.succ_le_mono;
        rewrite <- (N2Z.id (wordToN value0)), <- log2_conv;
        apply Z.log2_le_mono;
        etransitivity; [eassumption|reflexivity]).

    - rewrite Z.min_l; [|abstract (apply Z.log2_le_mono; omega)].
      abstract (
        rewrite (land_intro_ones (wordToN value1));
        rewrite <- N.land_comm, N.land_assoc;
        etransitivity; [apply N2Z.inj_le; apply N.lt_le_incl; apply land_lt_Npow2|];
        rewrite N2Z.inj_pow;
        apply Z.pow_le_mono; [abstract (split; cbn; [omega|reflexivity])|];
        unfold getBits; rewrite N2Z.inj_succ;
        apply -> Z.succ_le_mono;
        rewrite <- (N2Z.id (wordToN value1)), <- log2_conv;
        apply Z.log2_le_mono;
        etransitivity; [eassumption|reflexivity]).
  Defined.

  Definition lor : t -> t -> t.
  Proof.
    build_binop Word64.w64lor ZBounds.lor; t_start;
      unfold Word64.word64ToZ in *; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite wordize_or.

    - transitivity (Z.max (Z.of_N (wordToN value1)) (Z.of_N (wordToN value0)));
      [ abstract (destruct
          (Z_ge_dec lower1 lower0) as [l|l],
          (Z_ge_dec (Z.of_N (& value1)%w) (Z.of_N (& value0)%w)) as [v|v];
        [ rewrite Z.max_l, Z.max_l | rewrite Z.max_l, Z.max_r
        | rewrite Z.max_r, Z.max_l | rewrite Z.max_r, Z.max_r ];
        
        try (omega || assumption))
      | ].

      rewrite <- N2Z.inj_max.
      apply Z2N.inj_le; [apply N2Z.is_nonneg|apply N2Z.is_nonneg|].
      repeat rewrite N2Z.id.

      abstract (
        destruct (N.max_dec (wordToN value1) (wordToN value0)) as [v|v];
        rewrite v;
        apply N.ldiff_le, N.bits_inj_iff; intros k;
        rewrite N.ldiff_spec, N.lor_spec;
        induction (N.testbit (wordToN value1)), (N.testbit (wordToN value0)); simpl;
        reflexivity).

    - apply Z.lt_le_incl, Z.log2_lt_cancel.
      rewrite Z.log2_pow2; [| abstract (
        destruct (Z.max_dec (Z.log2 upper1) (Z.log2 upper0)) as [g|g];
        rewrite g; apply Z.le_le_succ_r, Z.log2_nonneg)].

      eapply (Z.le_lt_trans _ (Z.log2 (Z.lor _ _)) _).

      + apply Z.log2_le_mono, Z.eq_le_incl.
        apply Z.bits_inj_iff'; intros k Hpos.
        rewrite Z2N.inj_testbit, Z.lor_spec, N.lor_spec; [|assumption].
        repeat (rewrite <- Z2N.inj_testbit; [|assumption]).
        reflexivity.

      + abstract (
          rewrite Z.log2_lor; [|trans'|trans'];
          destruct
            (Z_ge_dec (Z.of_N (wordToN value1)) (Z.of_N (wordToN value0))) as [g0|g0],
            (Z_ge_dec upper1 upper0) as [g1|g1];
            [ rewrite Z.max_l, Z.max_l
            | rewrite Z.max_l, Z.max_r
            | rewrite Z.max_r, Z.max_l
            | rewrite Z.max_r, Z.max_r];
            try apply Z.log2_le_mono; try omega;
            apply Z.le_succ_l;
            apply -> Z.succ_le_mono;
            apply Z.log2_le_mono;
            assumption || (etransitivity; [eassumption|]; omega)).
  Defined.

  Axiom proof_admitted : False.
  Tactic Notation "admit" := abstract case proof_admitted.

  Definition neg : t -> t -> t.
  Proof.
    build_binop Word64.w64neg ZBounds.neg; t_start;
      admit.
  Defined.

  Definition cmovne : t -> t -> t -> t -> t.
  Proof.
    build_4op Word64.w64cmovne ZBounds.cmovne; t_start;
      admit.
  Defined.

  Definition cmovle : t -> t -> t -> t -> t.
  Proof.
    build_4op Word64.w64cmovle ZBounds.cmovle; t_start;
      admit.
  Defined.

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
       end%bounded_word.
End BoundedWord64.

Module Relations.
  Definition lift_relation {T} (R : BoundedWord64.BoundedWord -> T -> Prop) : BoundedWord64.t -> T -> Prop
    := fun x y => match x with
                  | Some _ => True
                  | None => False
                  end -> match x with
                         | Some x' => R x' y
                         | None => True
                         end.

  Definition related'_Z (x : BoundedWord64.BoundedWord) (y : Z) : Prop
    := Word64.word64ToZ (BoundedWord64.value x) = y.
  Definition related_Z : BoundedWord64.t -> Z -> Prop := lift_relation related'_Z.
  Definition related'_word64 (x : BoundedWord64.BoundedWord) (y : Word64.word64) : Prop
    := BoundedWord64.value x = y.
  Definition related_word64 : BoundedWord64.t -> Word64.word64 -> Prop := lift_relation related'_word64.
  Definition related_bounds (x : BoundedWord64.t) (y : ZBounds.t) : Prop
    := match x, y with
       | Some x, Some y
         => BoundedWord64.lower x = ZBounds.lower y /\ BoundedWord64.upper x = ZBounds.upper y
       | Some _, _
         => False
       | None, None => True
       | None, _ => False
       end.
End Relations.
