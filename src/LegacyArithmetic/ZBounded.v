(*** Bounded ℤ-Like Types *)
(** This file specifies a ℤ-like type of bounded integers, with
    operations for Montgomery Reduction and Barrett Reduction. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.

Class ZLikeOps (small_bound smaller_bound : Z) (modulus : Z) :=
  {
    LargeT : Type;
    SmallT : Type;
    modulus_digits : SmallT;
    decode_large : LargeT -> Z;
    decode_small : SmallT -> Z;
    Mod_SmallBound : LargeT -> SmallT;
    DivBy_SmallBound : LargeT -> SmallT;
    DivBy_SmallerBound : LargeT -> SmallT;
    Mul : SmallT -> SmallT -> LargeT;
    CarryAdd : LargeT -> LargeT -> bool * LargeT;
    CarrySubSmall : SmallT -> SmallT -> bool * SmallT;
    ConditionalSubtract : bool -> SmallT -> SmallT;
    ConditionalSubtractModulus : SmallT -> SmallT
  }.

Delimit Scope small_zlike_scope with small_zlike.
Delimit Scope large_zlike_scope with large_zlike.
Local Open Scope small_zlike_scope.
Local Open Scope large_zlike_scope.
Local Open Scope Z_scope.
Bind Scope small_zlike_scope with SmallT.
Bind Scope large_zlike_scope with LargeT.
Arguments decode_large (_ _ _)%Z _ _%large_zlike.
Arguments decode_small (_ _ _)%Z _ _%small_zlike.
Arguments Mod_SmallBound (_ _ _)%Z _ _%large_zlike.
Arguments DivBy_SmallBound (_ _ _)%Z _ _%large_zlike.
Arguments DivBy_SmallerBound (_ _ _)%Z _ _%large_zlike.
Arguments Mul (_ _ _)%Z _ (_ _)%small_zlike.
Arguments CarryAdd (_ _ _)%Z _ (_ _)%large_zlike.
Arguments CarrySubSmall (_ _ _)%Z _ (_ _)%large_zlike.
Arguments ConditionalSubtract (_ _ _)%Z _ _%bool _%small_zlike.
Arguments ConditionalSubtractModulus (_ _ _)%Z _ _%small_zlike.

Infix "*" := Mul : large_zlike_scope.
Notation "x + y" := (snd (CarryAdd x y)) : large_zlike_scope.

Class ZLikeProperties {small_bound smaller_bound modulus : Z} (Zops : ZLikeOps small_bound smaller_bound modulus) :=
  {
    large_valid : LargeT -> Prop;
    medium_valid : LargeT -> Prop;
    small_valid : SmallT -> Prop;
    decode_large_valid : forall v, large_valid v -> 0 <= decode_large v < small_bound * small_bound;
    decode_medium_valid : forall v, medium_valid v -> 0 <= decode_large v < small_bound * smaller_bound;
    medium_to_large_valid : forall v, medium_valid v -> large_valid v;
    decode_small_valid : forall v, small_valid v -> 0 <= decode_small v < small_bound;
    modulus_digits_valid : small_valid modulus_digits;
    modulus_digits_correct : decode_small modulus_digits = modulus;
    Mod_SmallBound_valid : forall v, large_valid v -> small_valid (Mod_SmallBound v);
    Mod_SmallBound_correct
    : forall v, large_valid v -> decode_small (Mod_SmallBound v) = decode_large v mod small_bound;
    DivBy_SmallBound_valid : forall v, large_valid v -> small_valid (DivBy_SmallBound v);
    DivBy_SmallBound_correct
    : forall v, large_valid v -> decode_small (DivBy_SmallBound v) = decode_large v / small_bound;
    DivBy_SmallerBound_valid : forall v, medium_valid v -> small_valid (DivBy_SmallerBound v);
    DivBy_SmallerBound_correct
    : forall v, medium_valid v -> decode_small (DivBy_SmallerBound v) = decode_large v / smaller_bound;
    Mul_valid : forall x y, small_valid x -> small_valid y -> large_valid (Mul x y);
    Mul_correct
    : forall x y, small_valid x -> small_valid y -> decode_large (Mul x y) = decode_small x * decode_small y;
    CarryAdd_valid : forall x y, large_valid x -> large_valid y -> large_valid (snd (CarryAdd x y));
    CarryAdd_correct_fst
    : forall x y, large_valid x -> large_valid y -> fst (CarryAdd x y) = (small_bound * small_bound <=? decode_large x + decode_large y);
    CarryAdd_correct_snd
    : forall x y, large_valid x -> large_valid y -> decode_large (snd (CarryAdd x y)) = (decode_large x + decode_large y) mod (small_bound * small_bound);
    CarrySubSmall_valid : forall x y, small_valid x -> small_valid y -> small_valid (snd (CarrySubSmall x y));
    CarrySubSmall_correct_fst
    : forall x y, small_valid x -> small_valid y -> fst (CarrySubSmall x y) = (decode_small x - decode_small y <? 0);
    CarrySubSmall_correct_snd
    : forall x y, small_valid x -> small_valid y -> decode_small (snd (CarrySubSmall x y)) = (decode_small x - decode_small y) mod small_bound;
    ConditionalSubtract_valid : forall b x, small_valid x  -> small_valid (ConditionalSubtract b x);
    ConditionalSubtract_correct
    : forall b x, small_valid x -> decode_small (ConditionalSubtract b x)
                                 = if b then (decode_small x - decode_small modulus_digits) mod small_bound else decode_small x;
    ConditionalSubtractModulus_valid : forall x, small_valid x -> small_valid (ConditionalSubtractModulus x);
    ConditionalSubtractModulus_correct
    : forall x, small_valid x -> decode_small (ConditionalSubtractModulus x)
                                 = if (decode_small x <? decode_small modulus_digits) then decode_small x else decode_small x - decode_small modulus_digits
  }.

Arguments ZLikeProperties [small_bound smaller_bound modulus] Zops, small_bound smaller_bound modulus {Zops}.

Existing Class large_valid.
Existing Class medium_valid.
Existing Class small_valid.
Existing Instances Mod_SmallBound_valid DivBy_SmallerBound_valid DivBy_SmallBound_valid Mul_valid CarryAdd_valid CarrySubSmall_valid ConditionalSubtract_valid ConditionalSubtractModulus_valid modulus_digits_valid medium_to_large_valid.

Lemma ConditionalSubtractModulus_correct'
      {small_bound smaller_bound modulus : Z} {Zops : ZLikeOps small_bound smaller_bound modulus}
      {Zprops : ZLikeProperties Zops}
  : forall x, small_valid x -> decode_small (ConditionalSubtractModulus x)
                               = if (decode_small modulus_digits <=? decode_small x) then decode_small x - decode_small modulus_digits else decode_small x.
Proof.
  intros; rewrite ConditionalSubtractModulus_correct by assumption.
  break_match; Z.ltb_to_lt; omega.
Qed.

Lemma modulus_nonneg {small_bound smaller_bound modulus} (Zops : ZLikeOps small_bound smaller_bound modulus) {_ : ZLikeProperties Zops} : 0 <= modulus.
Proof.
  pose proof (decode_small_valid _ modulus_digits_valid) as H.
  rewrite modulus_digits_correct in H.
  omega.
Qed.

Create HintDb push_zlike_decode discriminated.
Create HintDb pull_zlike_decode discriminated.
Hint Rewrite @Mod_SmallBound_correct @DivBy_SmallBound_correct @DivBy_SmallerBound_correct @Mul_correct @CarryAdd_correct_fst @CarryAdd_correct_snd @CarrySubSmall_correct_fst @CarrySubSmall_correct_snd  @ConditionalSubtract_correct @ConditionalSubtractModulus_correct @ConditionalSubtractModulus_correct' @modulus_digits_correct using solve [ typeclasses eauto ] : push_zlike_decode.
Hint Rewrite <- @Mod_SmallBound_correct @DivBy_SmallBound_correct @DivBy_SmallerBound_correct @Mul_correct @CarryAdd_correct_fst @CarryAdd_correct_snd @CarrySubSmall_correct_fst @CarrySubSmall_correct_snd @ConditionalSubtract_correct @ConditionalSubtractModulus_correct @modulus_digits_correct using solve [ typeclasses eauto ] : pull_zlike_decode.

Ltac get_modulus :=
  match goal with
  | [ _ : ZLikeOps _ _ ?modulus |- _ ] => modulus
  end.

Ltac push_zlike_decode :=
  let modulus := get_modulus in
  repeat first [ erewrite !Mod_SmallBound_correct by typeclasses eauto
               | erewrite !DivBy_SmallBound_correct by typeclasses eauto
               | erewrite !DivBy_SmallerBound_correct by typeclasses eauto
               | erewrite !Mul_correct by typeclasses eauto
               | erewrite !CarryAdd_correct_fst by typeclasses eauto
               | erewrite !CarryAdd_correct_snd by typeclasses eauto
               | erewrite !CarrySubSmall_correct_fst by typeclasses eauto
               | erewrite !CarrySubSmall_correct_snd by typeclasses eauto
               | erewrite !ConditionalSubtract_correct by typeclasses eauto
               | erewrite !ConditionalSubtractModulus_correct by typeclasses eauto
               | erewrite !ConditionalSubtractModulus_correct' by typeclasses eauto
               | erewrite !(@modulus_digits_correct _ modulus _ _) by typeclasses eauto ].
Ltac pull_zlike_decode :=
  let modulus := get_modulus in
  repeat first [ match goal with
                 | [ |- context G[modulus] ]
                   => let G' := context G[decode_small modulus_digits] in
                      cut G'; [ rewrite !modulus_digits_correct by typeclasses eauto; exact (fun x => x) | ]
                 end
               | erewrite <- !Mod_SmallBound_correct by typeclasses eauto
               | erewrite <- !DivBy_SmallBound_correct by typeclasses eauto
               | erewrite <- !DivBy_SmallerBound_correct by typeclasses eauto
               | erewrite <- !Mul_correct by typeclasses eauto
               | erewrite <- !CarryAdd_correct_fst by typeclasses eauto
               | erewrite <- !CarryAdd_correct_snd by typeclasses eauto
               | erewrite <- !ConditionalSubtract_correct by typeclasses eauto
               | erewrite <- !CarrySubSmall_correct_fst by typeclasses eauto
               | erewrite <- !CarrySubSmall_correct_snd by typeclasses eauto
               | erewrite <- !ConditionalSubtractModulus_correct by typeclasses eauto
               | erewrite <- !ConditionalSubtractModulus_correct' by typeclasses eauto
               | erewrite <- !(@modulus_digits_correct _ modulus _ _) by typeclasses eauto ].
