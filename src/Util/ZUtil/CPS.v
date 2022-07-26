Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.Head.

Local Open Scope Z_scope.

Module Z.
  Definition eq_dec_cps {T} (x y : Z) (f : {x = y} + {x <> y} -> T) : T
    := f (Z.eq_dec x y).
  Definition eq_dec_cps_correct {T} x y f : @eq_dec_cps T x y f = f (Z.eq_dec x y)
    := eq_refl.
#[global]
  Hint Rewrite @eq_dec_cps_correct : uncps.

  Definition eqb_cps {T} (x y : Z) (f : bool -> T) : T
    := f (Z.eqb x y).
  Definition eqb_cps_correct {T} x y f : @eqb_cps T x y f = f (Z.eqb x y)
    := eq_refl.
#[global]
  Hint Rewrite @eqb_cps_correct : uncps.

  Local Ltac prove_cps_correct _ :=
    try match goal with
        | [ |- ?lhs ?f = ?f ?rhs ]
          => let l := head lhs in
             let r := head rhs in
             cbv [l r] in *
        end;
    repeat first [ reflexivity
                 | progress cbv [Decidable.dec Decidable.dec_eq_Z] in *
                 | progress Z.ltb_to_lt
                 | congruence
                 | progress autorewrite with uncps
                 | break_innermost_match_step ].

  Definition get_carry_cps {T} (bitwidth : Z) (v : Z) (f : Z * Z -> T) : T
    := f (Z.get_carry bitwidth v).
  Definition get_carry_cps_correct {T} bitwidth v f
    : @get_carry_cps T bitwidth v f = f (Z.get_carry bitwidth v)
    := eq_refl.
#[global]
  Hint Rewrite @get_carry_cps_correct : uncps.
  Definition add_with_get_carry_cps {T} (bitwidth : Z) (c : Z) (x y : Z) (f : Z * Z -> T) : T
    := f (Z.add_with_get_carry bitwidth c x y).
  Definition add_with_get_carry_cps_correct {T} bitwidth c x y f
    : @add_with_get_carry_cps T bitwidth c x y f = f (Z.add_with_get_carry bitwidth c x y)
    := eq_refl.
#[global]
  Hint Rewrite @add_with_get_carry_cps_correct : uncps.
  Definition add_get_carry_cps {T} (bitwidth : Z) (x y : Z) (f : Z * Z -> T) : T
    := f (Z.add_get_carry bitwidth x y).
  Definition add_get_carry_cps_correct {T} bitwidth x y f
    : @add_get_carry_cps T bitwidth x y f = f (Z.add_get_carry bitwidth x y)
    := eq_refl.
#[global]
  Hint Rewrite @add_get_carry_cps_correct : uncps.

  Definition get_borrow_cps {T} (bitwidth : Z) (v : Z) (f : Z * Z -> T)
    := f (Z.get_borrow bitwidth v).
  Definition get_borrow_cps_correct {T} bitwidth v f
    : @get_borrow_cps T bitwidth v f = f (Z.get_borrow bitwidth v)
    := eq_refl.
#[global]
  Hint Rewrite @get_borrow_cps_correct : uncps.
  Definition sub_with_get_borrow_cps {T} (bitwidth : Z) (c : Z) (x y : Z) (f : Z * Z -> T) : T
    := f (Z.sub_with_get_borrow bitwidth c x y).
  Definition sub_with_get_borrow_cps_correct {T} (bitwidth : Z) (c : Z) (x y : Z) (f : Z * Z -> T)
    : @sub_with_get_borrow_cps T bitwidth c x y f = f (Z.sub_with_get_borrow bitwidth c x y)
    := eq_refl.
#[global]
  Hint Rewrite @sub_with_get_borrow_cps_correct : uncps.
  Definition sub_get_borrow_cps {T} (bitwidth : Z) (x y : Z) (f : Z * Z -> T) : T
    := f (Z.sub_get_borrow bitwidth x y).
  Definition sub_get_borrow_cps_correct {T} (bitwidth : Z) (x y : Z) (f : Z * Z -> T)
    : @sub_get_borrow_cps T bitwidth x y f = f (Z.sub_get_borrow bitwidth x y)
    := eq_refl.
#[global]
  Hint Rewrite @sub_get_borrow_cps_correct : uncps.

  (* splits at [bound], not [2^bitwidth]; wrapper to make add_getcarry
  work if input is not known to be a power of 2 *)
  Definition add_get_carry_full_cps {T} (bound : Z) (x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         (2 ^ (Z.log2 bound)) bound
         (fun eqb
          => if eqb
             then add_get_carry_cps (Z.log2 bound) x y f
             else f ((x + y) mod bound, (x + y) / bound)).
  Lemma add_get_carry_full_cps_correct {T} (bound : Z) (x y : Z) (f : Z * Z -> T)
    : @add_get_carry_full_cps T bound x y f = f (Z.add_get_carry_full bound x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @add_get_carry_full_cps_correct : uncps.
  Definition add_with_get_carry_full_cps {T} (bound : Z) (c x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         (2 ^ (Z.log2 bound)) bound
         (fun eqb
          => if eqb
             then add_with_get_carry_cps (Z.log2 bound) c x y f
             else f ((c + x + y) mod bound, (c + x + y) / bound)).
  Lemma add_with_get_carry_full_cps_correct {T} (bound : Z) (c x y : Z) (f : Z * Z -> T)
    : @add_with_get_carry_full_cps T bound c x y f = f (Z.add_with_get_carry_full bound c x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @add_with_get_carry_full_cps_correct : uncps.
  Definition sub_get_borrow_full_cps {T} (bound : Z) (x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         (2 ^ (Z.log2 bound)) bound
         (fun eqb
          => if eqb
             then sub_get_borrow_cps (Z.log2 bound) x y f
             else f ((x - y) mod bound, -((x - y) / bound))).
  Lemma sub_get_borrow_full_cps_correct {T} (bound : Z) (x y : Z) (f : Z * Z -> T)
    : @sub_get_borrow_full_cps T bound x y f = f (Z.sub_get_borrow_full bound x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @sub_get_borrow_full_cps_correct : uncps.
  Definition sub_with_get_borrow_full_cps {T} (bound : Z) (c x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         (2 ^ (Z.log2 bound)) bound
         (fun eqb
          => if eqb
             then sub_with_get_borrow_cps (Z.log2 bound) c x y f
             else f ((x - y - c) mod bound, -((x - y - c) / bound))).
  Lemma sub_with_get_borrow_full_cps_correct {T} (bound : Z) (c x y : Z) (f : Z * Z -> T)
    : @sub_with_get_borrow_full_cps T bound c x y f = f (Z.sub_with_get_borrow_full bound c x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @sub_with_get_borrow_full_cps_correct : uncps.

  Definition mul_split_at_bitwidth_cps {T} (bitwidth : Z) (x y : Z) (f : Z * Z -> T) : T
    := dlet xy := x * y in
        f (if Z.geb bitwidth 0
           then Z.land xy (Z.ones bitwidth)
           else xy mod 2^bitwidth,
           if Z.geb bitwidth 0
           then Z.shiftr xy bitwidth
           else xy / 2^bitwidth).
  Definition mul_split_at_bitwidth_cps_correct {T} (bitwidth : Z) (x y : Z) (f : Z * Z -> T)
    : @mul_split_at_bitwidth_cps T bitwidth x y f = f (Z.mul_split_at_bitwidth bitwidth x y)
    := eq_refl.
#[global]
  Hint Rewrite @mul_split_at_bitwidth_cps_correct : uncps.
  Definition mul_split_cps {T} (s x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         s (2^Z.log2 s)
         (fun b
          => if b
             then mul_split_at_bitwidth_cps (Z.log2 s) x y f
             else f ((x * y) mod s, (x * y) / s)).
  Lemma mul_split_cps_correct {T} (s x y : Z) (f : Z * Z -> T)
    : @mul_split_cps T s x y f = f (Z.mul_split s x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @mul_split_cps_correct : uncps.

  Definition mul_split_cps' {T} (s x y : Z) (f : Z * Z -> T) : T
    := eqb_cps
         s (2^Z.log2 s)
         (fun b
          => if b
             then f (Z.mul_split_at_bitwidth (Z.log2 s) x y)
             else f ((x * y) mod s, (x * y) / s)).
  Lemma mul_split_cps'_correct {T} (s x y : Z) (f : Z * Z -> T)
    : @mul_split_cps' T s x y f = f (Z.mul_split s x y).
  Proof. prove_cps_correct (). Qed.
#[global]
  Hint Rewrite @mul_split_cps'_correct : uncps.
End Z.
