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

Module Type BitSize.
  Parameter bit_width : nat.
  Axiom bit_width_pos : (0 < Z.of_nat bit_width)%Z.
End BitSize.

Module Import Bounds.
  Record bounds := { lower : Z ; upper : Z }.
End Bounds.
Module Import BoundedWord.
  Record BoundedWordGen wordW (is_bounded_by : _ -> _ -> _ -> Prop) :=
    { lower : Z ; value : wordW ; upper : Z ;
      in_bounds : is_bounded_by value lower upper }.
  Global Arguments lower {_ _} _.
  Global Arguments value {_ _} _.
  Global Arguments upper {_ _} _.
  Global Arguments in_bounds {_ _} _.
End BoundedWord.
Module InterpretationsGen (Bit : BitSize).
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

  Module WordW.
    Include Bit.
    Definition wordW := word bit_width.
    Delimit Scope wordW_scope with wordW.
    Bind Scope wordW_scope with wordW.

    Definition wordWToZ (x : wordW) : Z
      := Z.of_N (wordToN x).
    Definition ZToWordW (x : Z) : wordW
      := NToWord _ (Z.to_N x).

    Ltac fold_WordW_Z :=
      repeat match goal with
             | [ |- context G[NToWord bit_width (Z.to_N ?x)] ]
               => let G' := context G [ZToWordW x] in change G'
             | [ |- context G[Z.of_N (wordToN ?x)] ]
               => let G' := context G [wordWToZ x] in change G'
             | [ H : context G[NToWord bit_width (Z.to_N ?x)] |- _ ]
               => let G' := context G [ZToWordW x] in change G' in H
             | [ H : context G[Z.of_N (wordToN ?x)] |- _ ]
               => let G' := context G [wordWToZ x] in change G' in H
             end.

    Create HintDb push_wordWToZ discriminated.
    Hint Extern 1 => progress autorewrite with push_wordWToZ in * : push_wordWToZ.

    Local Hint Resolve bit_width_pos : zarith.

    Ltac arith := solve [ omega | auto using bit_width_pos with zarith ].

    Lemma wordWToZ_bound w : (0 <= wordWToZ w < 2^Z.of_nat bit_width)%Z.
    Proof.
      pose proof (wordToNat_bound w) as H.
      apply Nat2Z.inj_lt in H.
      rewrite Zpow_pow2, Z2Nat.id in H by (apply Z.pow_nonneg; omega).
      unfold wordWToZ.
      rewrite wordToN_nat, nat_N_Z; omega.
    Qed.

    Lemma wordWToZ_log_bound w : (0 <= wordWToZ w /\ Z.log2 (wordWToZ w) < Z.of_nat bit_width)%Z.
    Proof.
      pose proof (wordWToZ_bound w) as H.
      destruct (Z_zerop (wordWToZ w)) as [H'|H'].
      { rewrite H'; simpl; split; auto with zarith. }
      { split; [ | apply Z.log2_lt_pow2 ]; omega. }
    Qed.

    Lemma ZToWordW_wordWToZ (x : wordW) : ZToWordW (wordWToZ x) = x.
    Proof.
      unfold ZToWordW, wordWToZ.
      rewrite N2Z.id, NToWord_wordToN.
      reflexivity.
    Qed.
    Hint Rewrite ZToWordW_wordWToZ : push_wordWToZ.

    Lemma wordWToZ_ZToWordW (x : Z) : (0 <= x < 2^Z.of_nat bit_width)%Z -> wordWToZ (ZToWordW x) = x.
    Proof.
      unfold ZToWordW, wordWToZ; intros [H0 H1].
      pose proof H1 as H1'; apply Z2Nat.inj_lt in H1'; [ | omega.. ].
      rewrite <- Z.pow_Z2N_Zpow in H1' by omega.
      replace (Z.to_nat 2) with 2%nat in H1' by reflexivity.
      rewrite wordToN_NToWord_idempotent, Z2N.id by (omega || auto using bound_check_nat_N).
      reflexivity.
    Qed.
    Hint Rewrite wordWToZ_ZToWordW using arith : push_wordWToZ.

    Definition add : wordW -> wordW -> wordW := @wplus _.
    Definition sub : wordW -> wordW -> wordW := @wminus _.
    Definition mul : wordW -> wordW -> wordW := @wmult _.
    Definition shl : wordW -> wordW -> wordW := @wordBin N.shiftl _.
    Definition shr : wordW -> wordW -> wordW := @wordBin N.shiftr _.
    Definition land : wordW -> wordW -> wordW := @wand _.
    Definition lor : wordW -> wordW -> wordW := @wor _.
    Definition neg (int_width : Z) : wordW -> wordW (* TODO: Is this right? *)
      := fun x => ZToWordW (ModularBaseSystemListZOperations.neg int_width (wordWToZ x)).
    Definition cmovne : wordW -> wordW -> wordW -> wordW -> wordW (* TODO: Is this right? *)
      := fun x y z w => ZToWordW (ModularBaseSystemListZOperations.cmovne (wordWToZ x) (wordWToZ y) (wordWToZ z) (wordWToZ w)).
    Definition cmovle : wordW -> wordW -> wordW -> wordW -> wordW (* TODO: Is this right? *)
      := fun x y z w => ZToWordW (ModularBaseSystemListZOperations.cmovl (wordWToZ x) (wordWToZ y) (wordWToZ z) (wordWToZ w)).

    Infix "+" := add : wordW_scope.
    Infix "-" := sub : wordW_scope.
    Infix "*" := mul : wordW_scope.
    Infix "<<" := shl : wordW_scope.
    Infix ">>" := shr : wordW_scope.
    Infix "&'" := land : wordW_scope.

    (*Local*) Hint Resolve <- Z.log2_lt_pow2_alt : zarith.
    Local Hint Resolve eq_refl : zarith.
    Local Ltac wWToZ_t :=
      intros;
      try match goal with
          | [ |- ?wordToZ ?op = _ ]
            => let op' := head op in
               cbv [wordToZ op'] in *
          end;
      autorewrite with push_Zto_N push_Zof_N push_wordToN; try reflexivity.
    Local Ltac wWToZ_extra_t :=
      repeat first [ reflexivity
                   | progress cbv [ModularBaseSystemListZOperations.neg ModularBaseSystemListZOperations.cmovne ModularBaseSystemListZOperations.cmovl] in *
                   | progress break_match
                   | progress fold_WordW_Z
                   | progress intros
                   | progress autorewrite with push_Zto_N push_Zof_N push_wordToN push_wordWToZ ].

    Local Notation bounds_statement wop Zop
      := ((0 <= Zop -> Z.log2 Zop < Z.of_nat bit_width -> wordWToZ wop = Zop)%Z).
    Local Notation bounds_statement_tuple wop Zop
      := ((HList.hlist (fun v => 0 <= v /\ Z.log2 v < Z.of_nat bit_width) Zop -> Tuple.map wordWToZ wop = Zop)%Z).
    Local Notation bounds_1statement wop Zop
      := (forall x,
             bounds_statement (wop x) (Zop (wordWToZ x))).
    Local Notation bounds_2statement wop Zop
      := (forall x y,
             bounds_statement (wop x y) (Zop (wordWToZ x) (wordWToZ y))).
    Local Notation bounds_4statement wop Zop
      := (forall x y z w,
             bounds_statement (wop x y z w) (Zop (wordWToZ x) (wordWToZ y) (wordWToZ z) (wordWToZ w))).

    Lemma wordWToZ_add : bounds_2statement add Z.add. Proof. wWToZ_t. Qed.
    Lemma wordWToZ_sub : bounds_2statement sub Z.sub. Proof. wWToZ_t. Qed.
    Lemma wordWToZ_mul : bounds_2statement mul Z.mul. Proof. wWToZ_t. Qed.
    Lemma wordWToZ_shl : bounds_2statement shl Z.shiftl.
    Proof.
      wWToZ_t; wWToZ_extra_t; unfold wordWToZ, wordBin.
      rewrite wordToN_NToWord_idempotent; [rewrite <- Z_inj_shiftl; reflexivity|].
      apply N2Z.inj_lt.
      rewrite Z_inj_shiftl.
      destruct (Z.lt_ge_cases 0 ((wordWToZ x) << (wordWToZ y)))%Z;
        [|eapply Z.le_lt_trans; [|apply N2Z.inj_lt, Npow2_gt0]; assumption].
      rewrite Npow2_N, N2Z.inj_pow, ?nat_N_Z.
      apply Z.log2_lt_pow2; assumption.
    Qed.

    Lemma wordWToZ_shr : bounds_2statement shr Z.shiftr.
    Proof.
      wWToZ_t; wWToZ_extra_t; unfold wordWToZ, wordBin.
      rewrite wordToN_NToWord_idempotent; [rewrite <- Z_inj_shiftr; reflexivity|].
      apply N2Z.inj_lt.
      rewrite Z_inj_shiftr.
      destruct (Z.lt_ge_cases 0 ((wordWToZ x) >> (wordWToZ y)))%Z;
        [|eapply Z.le_lt_trans; [|apply N2Z.inj_lt, Npow2_gt0]; assumption].
      rewrite Npow2_N, N2Z.inj_pow, nat_N_Z.
      apply Z.log2_lt_pow2; assumption.
    Qed.

    Lemma wordWToZ_land : bounds_2statement land Z.land.
    Proof. wWToZ_t. Qed.
    Lemma wordWToZ_lor : bounds_2statement lor Z.lor.
    Proof. wWToZ_t. Qed.
    Lemma wordWToZ_neg int_width : bounds_1statement (neg int_width) (ModularBaseSystemListZOperations.neg int_width).
    Proof. wWToZ_t; wWToZ_extra_t. Qed.
    Lemma wordWToZ_cmovne : bounds_4statement cmovne ModularBaseSystemListZOperations.cmovne.
    Proof. wWToZ_t; wWToZ_extra_t. Qed.
    Lemma wordWToZ_cmovle : bounds_4statement cmovle ModularBaseSystemListZOperations.cmovl.
    Proof. wWToZ_t; wWToZ_extra_t. Qed.

    Definition interp_base_type (t : base_type) : Type
      := match t with
         | TZ => wordW
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
         | Neg int_width => fun x => neg int_width x
         | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
         | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
         end%wordW.

    Definition of_Z ty : Z.interp_base_type ty -> interp_base_type ty
      := match ty return Z.interp_base_type ty -> interp_base_type ty with
         | TZ => ZToWordW
         end.
    Definition to_Z ty : interp_base_type ty -> Z.interp_base_type ty
      := match ty return interp_base_type ty -> Z.interp_base_type ty with
         | TZ => wordWToZ
         end.

    Module Export Rewrites.
      Ltac wordW_util_arith := omega.

      Hint Rewrite wordWToZ_add using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_add using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_sub using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_sub using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_mul using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_mul using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_shl using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_shl using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_shr using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_shr using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_land using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_land using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_lor using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_lor using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_neg using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_neg using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_cmovne using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_cmovne using wordW_util_arith : pull_wordWToZ.
      Hint Rewrite wordWToZ_cmovle using wordW_util_arith : push_wordWToZ.
      Hint Rewrite <- wordWToZ_cmovle using wordW_util_arith : pull_wordWToZ.
    End Rewrites.
  End WordW.

  Module ZBounds.
    Export Bounds.
    Definition bounds := bounds.
    Bind Scope bounds_scope with bounds.
    Definition t := option bounds. (* TODO?: Separate out the bounds computation from the overflow computation? e.g., have [safety := in_bounds | overflow] and [t := bounds * safety]? *)
    Bind Scope bounds_scope with t.
    Local Coercion Z.of_nat : nat >-> Z.
    Definition wordWToBounds (x : WordW.wordW) : t
      := let v := WordW.wordWToZ x in Some {| lower := v ; upper := v |}.
    Definition SmartBuildBounds (l u : Z)
      := if ((0 <=? l) && (Z.log2 u <? WordW.bit_width))%Z%bool
         then Some {| lower := l ; upper := u |}
         else None.
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
         => if ((0 <=? int_width) && (int_width <=? WordW.bit_width))%Z%bool
            then t_map1 (neg' int_width) v
            else None.
    Definition cmovne' (r1 r2 : bounds) : bounds
      := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovne (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovne') x y r1 r2.
    Definition cmovle' (r1 r2 : bounds) : bounds
      := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
    Definition cmovle (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovle') x y r1 r2.

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
         | Neg int_width => fun x => neg int_width x
         | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
         | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
         end%bounds.

    Definition of_wordW ty : WordW.interp_base_type ty -> interp_base_type ty
      := match ty return WordW.interp_base_type ty -> interp_base_type ty with
         | TZ => wordWToBounds
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

  Module BoundedWordW.
    Export BoundedWord.
    Local Notation is_bounded_by value lower upper
      := ((0 <= lower /\ lower <= WordW.wordWToZ value <= upper /\ Z.log2 upper < Z.of_nat WordW.bit_width)%Z)
           (only parsing).
    Definition BoundedWord := BoundedWordGen WordW.wordW (fun value lower upper => is_bounded_by value lower upper).
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

    Definition wordWToBoundedWord (x : WordW.wordW) : t.
    Proof.
      refine (let v := WordW.wordWToZ x in
              match Sumbool.sumbool_of_bool (0 <=? v)%Z, Sumbool.sumbool_of_bool (Z.log2 v <? Z.of_nat WordW.bit_width)%Z with
              | left Hl, left Hu
                => Some {| lower := WordW.wordWToZ x ; value := x ; upper := WordW.wordWToZ x |}
              | _, _ => None
              end).
      subst v.
      abstract (Z.ltb_to_lt; repeat split; (assumption || reflexivity)).
    Defined.

    Definition boundedWordToWordW (x : t) : WordW.wordW
      := match x with
         | Some x' => value x'
         | None => WordW.ZToWordW 0
         end.

    Definition of_wordW ty : WordW.interp_base_type ty -> interp_base_type ty
      := match ty return WordW.interp_base_type ty -> interp_base_type ty with
         | TZ => wordWToBoundedWord
         end.
    Definition to_wordW ty : interp_base_type ty -> WordW.interp_base_type ty
      := match ty return interp_base_type ty -> WordW.interp_base_type ty with
         | TZ => boundedWordToWordW
         end.

    (** XXX FIXME(jgross) This is going to break horribly if we need to support any types other than [Z] *)
    Definition to_wordW' ty : BoundedWord -> WordW.interp_base_type ty
      := match ty return BoundedWord -> WordW.interp_base_type ty with
         | TZ => fun x => boundedWordToWordW (Some x)
         end.

    Definition to_Z' ty : BoundedWord -> Z.interp_base_type ty
      := fun x => WordW.to_Z _ (to_wordW' _ x).

    Definition of_Z ty : Z.interp_base_type ty -> interp_base_type ty
      := fun x => of_wordW _ (WordW.of_Z _ x).
    Definition to_Z ty : interp_base_type ty -> Z.interp_base_type ty
      := fun x => WordW.to_Z _ (to_wordW _ x).

    Definition BoundedWordToBounds (x : BoundedWord) : ZBounds.bounds
      := {| Bounds.lower := lower x ; Bounds.upper := upper x |}.

    Definition to_bounds' : t -> ZBounds.t
      := option_map BoundedWordToBounds.

    Definition to_bounds ty : interp_base_type ty -> ZBounds.interp_base_type ty
      := match ty return interp_base_type ty -> ZBounds.interp_base_type ty with
         | TZ => to_bounds'
         end.

    Definition t_map1
               (opW : WordW.wordW -> WordW.wordW)
               (opB : ZBounds.t -> ZBounds.t)
               (pf : forall x l u,
                   opB (Some (BoundedWordToBounds x))
                   = Some {| Bounds.lower := l ; Bounds.upper := u |}
                   -> let val :=  opW (value x) in
                      is_bounded_by val l u)
      : t -> t
      := fun x : t
         => match x with
            | Some x
              => match opB (Some (BoundedWordToBounds x))
                       as bop return opB (Some (BoundedWordToBounds x)) = bop -> t
                 with
                 | Some (Bounds.Build_bounds l u)
                   => fun Heq => Some {| lower := l ; value := opW (value x) ; upper := u;
                                         in_bounds := pf _ _ _ Heq |}
                 | None => fun _ => None
                 end eq_refl
            | _ => None
            end.

    Definition t_map2
               (opW : WordW.wordW -> WordW.wordW -> WordW.wordW)
               (opB : ZBounds.t -> ZBounds.t -> ZBounds.t)
               (pf : forall x y l u,
                   opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                   = Some {| Bounds.lower := l ; Bounds.upper := u |}
                   -> let val :=  opW (value x) (value y) in
                      is_bounded_by val l u)
      : t -> t -> t
      := fun x y : t
         => match x, y with
            | Some x, Some y
              => match opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                       as bop return opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = bop -> t
                 with
                 | Some (Bounds.Build_bounds l u)
                   => fun Heq => Some {| lower := l ; value := opW (value x) (value y) ; upper := u;
                                         in_bounds := pf _ _ _ _ Heq |}
                 | None => fun _ => None
                 end eq_refl
            | _, _ => None
            end.

    Definition t_map4
               (opW : WordW.wordW -> WordW.wordW -> WordW.wordW -> WordW.wordW -> WordW.wordW)
               (opB : ZBounds.t -> ZBounds.t -> ZBounds.t -> ZBounds.t -> ZBounds.t)
               (pf : forall x y z w l u,
                   opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                   = Some {| Bounds.lower := l ; Bounds.upper := u |}
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
                 | Some (Bounds.Build_bounds l u)
                   => fun Heq => Some {| lower := l ; value := opW (value x) (value y) (value z) (value w) ; upper := u;
                                         in_bounds := pf _ _ _ _ _ _ Heq |}
                 | None => fun _ => None
                 end eq_refl
            | _, _, _, _ => None
            end.

    Local Opaque WordW.bit_width.
    Hint Resolve Z.ones_nonneg : zarith.
    Local Ltac t_prestart :=
      repeat first [ match goal with
                     | [ |- forall x l u, ?opB (Some (BoundedWordToBounds x)) = Some _ -> let val := ?opW (value x) in _ ]
                       => let opB' := head opB in let opW' := head opW in progress (try unfold opB'; try unfold opW')
                     | [ |- forall x y l u, ?opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = Some _ -> let val := ?opW (value x) (value y) in _ ]
                       => progress (try unfold opB; try unfold opW)
                     | [ |- forall x y z w l u, ?opB _ _ _ _ = Some _ -> let val := ?opW (value x) (value y) (value z) (value w) in _ ]
                       => progress (try unfold opB; try unfold opW)
                     | [ |- appcontext[ZBounds.t_map1 ?op] ] => let op' := head op in unfold op'
                     | [ |- appcontext[ZBounds.t_map2 ?op] ] => let op' := head op in unfold op'
                     | [ |- appcontext[?op (Bounds.Build_bounds _ _)] ] => let op' := head op in unfold op'
                     | [ |- appcontext[?op (Bounds.Build_bounds _ _) (Bounds.Build_bounds _ _)] ] => unfold op
                     end
                   | progress cbv [BoundedWordToBounds ZBounds.SmartBuildBounds cmovne cmovl ModularBaseSystemListZOperations.neg] in *
                   | progress break_match
                   | progress break_match_hyps
                   | progress intros
                   | progress subst
                   | progress ZBounds.inversion_bounds
                   | progress inversion_option
                   | progress WordW.fold_WordW_Z
                   | progress autorewrite with bool_congr_setoid in *
                   | progress destruct_head' and
                   | progress Z.ltb_to_lt
                   | assumption
                   | progress destruct_head' BoundedWord; simpl in *
                   | progress autorewrite with push_wordWToZ
                   | progress repeat apply conj
                   | solve [ WordW.arith ]
                   | progress destruct_head' or ].
    Local Ltac t_start :=
      repeat first [ progress t_prestart
                   | match goal with
                     | [ |- appcontext[Z.min ?x ?y] ]
                       => apply (Z.min_case_strong x y)
                     | [ |- appcontext[Z.max ?x ?y] ]
                       => apply (Z.max_case_strong x y)
                     end ].

    Local Hint Resolve WordW.bit_width_pos : zarith.
    Local Hint Extern 1 (Z.log2 _ < _)%Z => eapply Z.le_lt_trans; [ eapply Z.log2_le_mono; eassumption | eassumption ] : zarith.
    (* Local *) Hint Resolve <- Z.log2_lt_pow2_alt : zarith.


    Definition add : t -> t -> t.
    Proof.
      refine (t_map2 WordW.add ZBounds.add _);
        abstract (t_start; eapply add_valid_update; eauto).
    Defined.

    Definition sub : t -> t -> t.
    Proof.
      refine (t_map2 WordW.sub ZBounds.sub _);
        abstract (t_start; eapply sub_valid_update; eauto).
    Defined.

    Definition mul : t -> t -> t.
    Proof.
      refine (t_map2 WordW.mul ZBounds.mul _);
        abstract (t_start; eapply mul_valid_update; eauto).
    Defined.

    Definition land : t -> t -> t.
    Proof.
      refine (t_map2 WordW.land ZBounds.land _);
        abstract (t_prestart; eapply land_valid_update; eauto).
    Defined.

    Definition lor : t -> t -> t.
    Proof.
      refine (t_map2 WordW.lor ZBounds.lor _);
        abstract (t_prestart; eapply lor_valid_update; eauto).
    Defined.

    Definition shl : t -> t -> t.
    Proof.
      refine (t_map2 WordW.shl ZBounds.shl _);
        abstract (t_start; eapply shl_valid_update; eauto).
    Defined.

    Definition shr : t -> t -> t.
    Proof.
      refine (t_map2 WordW.shr ZBounds.shr _);
        abstract (t_start; eapply shr_valid_update; eauto).
    Defined.

    Definition neg (int_width : Z) : t -> t.
    Proof. refine (t_map1 (WordW.neg int_width) (ZBounds.neg int_width) _); abstract t_start. Defined.

    Definition cmovne : t -> t -> t -> t -> t.
    Proof. refine (t_map4 WordW.cmovne ZBounds.cmovne _); abstract t_start. Defined.

    Definition cmovle : t -> t -> t -> t -> t.
    Proof. refine (t_map4 WordW.cmovle ZBounds.cmovle _); abstract t_start. Defined.

    Local Notation unop_correct op opW opB :=
      (forall x v, op (Some x) = Some v
                   -> value v = opW (value x)
                      /\ Some (BoundedWordToBounds v) = opB (Some (BoundedWordToBounds x)))
        (only parsing).

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

    Lemma t_map1_correct opW opB pf
      : unop_correct (t_map1 opW opB pf) opW opB.
    Proof.
      intros ?? H.
      unfold t_map1 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
        unfold BoundedWordToBounds in *;
        inversion_option; subst; simpl.
      eauto.
    Qed.

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

    Local Notation unop_correct_None op opB :=
      (forall x, op (Some x) = None -> opB (Some (BoundedWordToBounds x)) = None)
        (only parsing).

    Local Notation binop_correct_None op opB :=
      (forall x y, op (Some x) (Some y) = None -> opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y)) = None)
        (only parsing).

    Local Notation op4_correct_None op opB :=
      (forall x y z w, op (Some x) (Some y) (Some z) (Some w) = None
                       -> opB (Some (BoundedWordToBounds x)) (Some (BoundedWordToBounds y))
                              (Some (BoundedWordToBounds z)) (Some (BoundedWordToBounds w))
                          = None)
        (only parsing).

    Lemma t_map1_correct_None opW opB pf
      : unop_correct_None (t_map1 opW opB pf) opB.
    Proof.
      intros ? H.
      unfold t_map1 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
        unfold BoundedWordToBounds in *;
        inversion_option; subst; simpl.
      eauto.
    Qed.

    Lemma t_map2_correct_None opW opB pf
      : binop_correct_None (t_map2 opW opB pf) opB.
    Proof.
      intros ?? H.
      unfold t_map2 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
        unfold BoundedWordToBounds in *;
        inversion_option; subst; simpl.
      eauto.
    Qed.

    Lemma t_map4_correct_None opW opB pf
      : op4_correct_None (t_map4 opW opB pf) opB.
    Proof.
      intros ???? H.
      unfold t_map4 in H; convoy_destruct_in H; destruct_head' ZBounds.bounds;
        unfold BoundedWordToBounds in *;
        inversion_option; subst; simpl.
      eauto.
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
         | Neg int_width => fun x => neg int_width x
         | Cmovne => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
         | Cmovle => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
         end%bounded_word.
  End BoundedWordW.

  Module ZBoundsTuple.
    Definition interp_flat_type (t : flat_type base_type)
      := LiftOption.interp_flat_type ZBounds.bounds t.

    Definition of_ZBounds {ty} : Syntax.interp_flat_type ZBounds.interp_base_type ty -> interp_flat_type ty
      := @LiftOption.of' ZBounds.bounds ty.
    Definition to_ZBounds {ty} : interp_flat_type ty -> Syntax.interp_flat_type ZBounds.interp_base_type ty
      := @LiftOption.to' ZBounds.bounds ty.
  End ZBoundsTuple.

  Module BoundedWordWTuple.
    Definition interp_flat_type (t : flat_type base_type)
      := LiftOption.interp_flat_type BoundedWordW.BoundedWord t.

    Definition of_BoundedWordW {ty} : Syntax.interp_flat_type BoundedWordW.interp_base_type ty -> interp_flat_type ty
      := @LiftOption.of' BoundedWordW.BoundedWord ty.
    Definition to_BoundedWordW {ty} : interp_flat_type ty -> Syntax.interp_flat_type BoundedWordW.interp_base_type ty
      := @LiftOption.to' BoundedWordW.BoundedWord ty.
  End BoundedWordWTuple.
End InterpretationsGen.
