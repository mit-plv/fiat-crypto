(*** Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.
Local Open Scope type_scope.

Create HintDb push_decode discriminated.
Create HintDb pull_decode discriminated.
Hint Extern 1 => progress autorewrite with push_decode in * : push_decode.
Hint Extern 1 => progress autorewrite with pull_decode in * : pull_decode.

(* TODO(from jgross): Try dropping the record wrappers.  See
   https://github.com/mit-plv/fiat-crypto/pull/52#discussion_r74627992
   and
   https://github.com/mit-plv/fiat-crypto/pull/52#discussion_r74658417
   and
   https://github.com/mit-plv/fiat-crypto/pull/52#issuecomment-239536847.
   The wrappers are here to make [autorewrite] databases feasable and
   fast, based on design patterns learned from past experience.  There
   might be better ways. *)
Class decoder (n : Z) W :=
  { decode : W -> Z }.
Coercion decode : decoder >-> Funclass.
Global Arguments decode {n W _} _.

Class is_decode {n W} (decode : decoder n W) :=
  decode_range : forall x, 0 <= decode x < 2^n.

Section InstructionGallery.
  Context (n : Z) (* bit-width of width of [W] *)
          {W : Type} (* bounded type, [W] for word *)
          (Wdecoder : decoder n W).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Record load_immediate := { ldi :> imm -> W }.

  Class is_load_immediate {ldi : load_immediate}  :=
    decode_load_immediate : forall x, 0 <= x < 2^n -> decode (ldi x) = x.

  Record shift_right_doubleword_immediate := { shrd :> W -> W -> imm -> W }.

  Class is_shift_right_doubleword_immediate (shrd : shift_right_doubleword_immediate) :=
    decode_shift_right_doubleword :
      forall high low count,
        0 <= count < n
        -> decode (shrd high low count) = (((decode high << n) + decode low) >> count) mod 2^n.

  Record shift_left_immediate := { shl :> W -> imm -> W }.

  Class is_shift_left_immediate (shl : shift_left_immediate) :=
    decode_shift_left_immediate :
      forall r count, 0 <= count < n -> decode (shl r count) = (decode r << count) mod 2^n.

  Record shift_right_immediate := { shr :> W -> imm -> W }.

  Class is_shift_right_immediate (shr : shift_right_immediate) :=
    decode_shift_right_immediate :
      forall r count, 0 <= count < n -> decode (shr r count) = (decode r >> count).

  Record spread_left_immediate := { sprl :> W -> imm -> W * W (* [(low, high)] *) }.

  Class is_spread_left_immediate (sprl : spread_left_immediate) :=
    {
      decode_fst_spread_left_immediate : forall r count,
          0 <= count < n
          -> decode (fst (sprl r count)) = (decode r << count) mod 2^n;
      decode_snd_spread_left_immediate : forall r count,
        0 <= count < n
        -> decode (snd (sprl r count)) = (decode r << count) >> n;

    }.

  Definition Build_is_spread_left_immediate' (sprl : spread_left_immediate)
             (pf : forall r count, 0 <= count < n
                                   -> decode (fst (sprl r count)) = (decode r << count) mod 2^n
                                      /\ decode (snd (sprl r count)) = (decode r << count) >> n)
    := {| decode_fst_spread_left_immediate r count H := proj1 (pf r count H);
          decode_snd_spread_left_immediate r count H := proj2 (pf r count H) |}.

  Record mask_keep_low := { mkl :> W -> imm -> W }.

  Class is_mask_keep_low (mkl : mask_keep_low) :=
    decode_mask_keep_low : forall r count,
      0 <= count < n -> decode (mkl r count) = decode r mod 2^count.

  Local Notation bit b := (if b then 1 else 0).

  Record add_with_carry := { adc :> W -> W -> bool -> bool * W }.

  Class is_add_with_carry (adc : add_with_carry) :=
    {
      bit_fst_add_with_carry : forall x y c, bit (fst (adc x y c)) = (decode x + decode y + bit c) >> n;
      decode_snd_add_with_carry : forall x y c, decode (snd (adc x y c)) = (decode x + decode y + bit c) mod (2^n)
    }.

  Definition Build_is_add_with_carry' (adc : add_with_carry)
             (pf : forall x y c, bit (fst (adc x y c)) = (decode x + decode y + bit c) >> n /\ decode (snd (adc x y c)) = (decode x + decode y + bit c) mod (2^n))
    := {| bit_fst_add_with_carry x y c := proj1 (pf x y c);
          decode_snd_add_with_carry x y c := proj2 (pf x y c) |}.

  Record sub_with_carry := { subc :> W -> W -> bool -> bool * W }.

  Class is_sub_with_carry (subc:W->W->bool->bool*W) :=
    {
      fst_sub_with_carry : forall x y c, fst (subc x y c) = ((decode x - decode y - bit c) <? 0);
      decode_snd_sub_with_carry : forall x y c, decode (snd (subc x y c)) = (decode x - decode y - bit c) mod 2^n
    }.

  Definition Build_is_sub_with_carry' (subc : sub_with_carry)
             (pf : forall x y c, fst (subc x y c) = ((decode x - decode y - bit c) <? 0) /\ decode (snd (subc x y c)) = (decode x - decode y - bit c) mod 2^n)
    := {| fst_sub_with_carry x y c := proj1 (pf x y c);
          decode_snd_sub_with_carry x y c := proj2 (pf x y c) |}.

  Record multiply := { mul :> W -> W -> W }.

  Class is_mul (mul : multiply) :=
    decode_mul : forall x y, decode (mul x y) = (decode x * decode y) mod 2^n.

  Record multiply_low_low := { mulhwll :> W -> W -> W }.
  Record multiply_high_low := { mulhwhl :> W -> W -> W }.
  Record multiply_high_high := { mulhwhh :> W -> W -> W }.

  Class is_mul_low_low (w:Z) (mulhwll : multiply_low_low) :=
    decode_mul_low_low :
      forall x y, decode (mulhwll x y) = ((decode x mod 2^w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_low (w:Z) (mulhwhl : multiply_high_low) :=
    decode_mul_high_low :
      forall x y, decode (mulhwhl x y) = ((decode x >> w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_high (w:Z) (mulhwhh : multiply_high_high) :=
    decode_mul_high_high :
      forall x y, decode (mulhwhh x y) = ((decode x >> w) * (decode y >> w)) mod 2^n.

  Record select_conditional := { selc :> bool -> W -> W -> W }.

  Class is_select_conditional (selc : select_conditional) :=
    decode_select_conditional : forall b x y,
      decode (selc b x y) = if b then decode x else decode y.

  Record add_modulo := { addm :> W -> W -> W (* modulus *) -> W }.

  Class is_add_modulo (addm : add_modulo) :=
    decode_add_modulo : forall x y modulus,
      decode (addm x y modulus) = (if (decode x + decode y) <? decode modulus
                                   then (decode x + decode y)
                                   else (decode x + decode y) - decode modulus)%Z.
End InstructionGallery.

Global Arguments load_immediate : clear implicits.
Global Arguments shift_right_doubleword_immediate : clear implicits.
Global Arguments shift_left_immediate : clear implicits.
Global Arguments shift_right_immediate : clear implicits.
Global Arguments spread_left_immediate : clear implicits.
Global Arguments mask_keep_low : clear implicits.
Global Arguments add_with_carry : clear implicits.
Global Arguments sub_with_carry : clear implicits.
Global Arguments multiply : clear implicits.
Global Arguments multiply_low_low : clear implicits.
Global Arguments multiply_high_low : clear implicits.
Global Arguments multiply_high_high : clear implicits.
Global Arguments select_conditional : clear implicits.
Global Arguments add_modulo : clear implicits.
Global Arguments ldi {_ _} _.
Global Arguments shrd {_ _} _ _ _.
Global Arguments shl {_ _} _ _.
Global Arguments shr {_ _} _ _.
Global Arguments sprl {_ _} _ _.
Global Arguments mkl {_ _} _ _.
Global Arguments adc {_ _} _ _ _.
Global Arguments subc {_ _} _ _ _.
Global Arguments mul {_ _} _ _.
Global Arguments mulhwll {_ _} _ _.
Global Arguments mulhwhl {_ _} _ _.
Global Arguments mulhwhh {_ _} _ _.
Global Arguments selc {_ _} _ _ _.
Global Arguments addm {_ _} _ _ _.

Existing Class load_immediate.
Existing Class shift_right_doubleword_immediate.
Existing Class shift_left_immediate.
Existing Class shift_right_immediate.
Existing Class spread_left_immediate.
Existing Class mask_keep_low.
Existing Class add_with_carry.
Existing Class sub_with_carry.
Existing Class multiply.
Existing Class multiply_low_low.
Existing Class multiply_high_low.
Existing Class multiply_high_high.
Existing Class select_conditional.
Existing Class add_modulo.

Global Arguments is_decode {_ _} _.
Global Arguments is_load_immediate {_ _ _} _.
Global Arguments is_shift_right_doubleword_immediate {_ _ _} _.
Global Arguments is_shift_left_immediate {_ _ _} _.
Global Arguments is_shift_right_immediate {_ _ _} _.
Global Arguments is_spread_left_immediate {_ _ _} _.
Global Arguments is_mask_keep_low {_ _ _} _.
Global Arguments is_add_with_carry {_ _ _} _.
Global Arguments is_sub_with_carry {_ _ _} _.
Global Arguments is_mul {_ _ _} _.
Global Arguments is_mul_low_low {_ _ _} _ _.
Global Arguments is_mul_high_low {_ _ _} _ _.
Global Arguments is_mul_high_high {_ _ _} _ _.
Global Arguments is_select_conditional {_ _ _} _.
Global Arguments is_add_modulo {_ _ _} _.

Ltac bounded_solver_tac :=
  solve [ eassumption | typeclasses eauto | omega ].

Lemma decode_proj n W (dec : W -> Z)
  : @decode n W {| decode := dec |} = dec.
Proof. reflexivity. Qed.

Lemma decode_if_bool n W (decode : decoder n W) (b : bool) x y
  : decode (if b then x else y)
    = if b then decode x else decode y.
Proof. destruct b; reflexivity. Qed.

Lemma decode_exponent_nonnegative {n W} (decode : decoder n W) {isdecode : is_decode decode}
      (isinhabited : W)
  : 0 <= n.
Proof.
  pose proof (decode_range isinhabited).
  assert (0 < 2^n) by omega.
  destruct (Z_lt_ge_dec n 0) as [H'|]; [ | omega ].
  assert (2^n = 0) by auto using Z.pow_neg_r.
  omega.
Qed.

Hint Rewrite @decode_load_immediate @decode_shift_right_doubleword @decode_shift_left_immediate @decode_shift_right_immediate @decode_fst_spread_left_immediate @decode_snd_spread_left_immediate @decode_mask_keep_low @bit_fst_add_with_carry @decode_snd_add_with_carry @fst_sub_with_carry @decode_snd_sub_with_carry @decode_mul @decode_mul_low_low @decode_mul_high_low @decode_mul_high_high @decode_select_conditional @decode_add_modulo @decode_proj @decode_if_bool using bounded_solver_tac : push_decode.

Ltac push_decode_step :=
  first [ rewrite !decode_proj
        | rewrite !decode_if_bool
        | erewrite !decode_load_immediate by bounded_solver_tac
        | erewrite !decode_shift_right_doubleword by bounded_solver_tac
        | erewrite !decode_shift_left_immediate by bounded_solver_tac
        | erewrite !decode_shift_right_immediate by bounded_solver_tac
        | erewrite !decode_fst_spread_left_immediate by bounded_solver_tac
        | erewrite !decode_snd_spread_left_immediate by bounded_solver_tac
        | erewrite !decode_mask_keep_low by bounded_solver_tac
        | erewrite !bit_fst_add_with_carry by bounded_solver_tac
        | erewrite !decode_snd_add_with_carry by bounded_solver_tac
        | erewrite !fst_sub_with_carry by bounded_solver_tac
        | erewrite !decode_snd_sub_with_carry by bounded_solver_tac
        | erewrite !decode_mul by bounded_solver_tac
        | erewrite !decode_mul_low_low by bounded_solver_tac
        | erewrite !decode_mul_high_low by bounded_solver_tac
        | erewrite !decode_mul_high_high by bounded_solver_tac
        | erewrite !decode_select_conditional by bounded_solver_tac
        | erewrite !decode_add_modulo by bounded_solver_tac ].
Ltac pull_decode_step :=
  first [ erewrite <- !decode_load_immediate by bounded_solver_tac
        | erewrite <- !decode_shift_right_doubleword by bounded_solver_tac
        | erewrite <- !decode_shift_left_immediate by bounded_solver_tac
        | erewrite <- !decode_shift_right_immediate by bounded_solver_tac
        | erewrite <- !decode_fst_spread_left_immediate by bounded_solver_tac
        | erewrite <- !decode_snd_spread_left_immediate by bounded_solver_tac
        | erewrite <- !decode_mask_keep_low by bounded_solver_tac
        | erewrite <- !bit_fst_add_with_carry by bounded_solver_tac
        | erewrite <- !decode_snd_add_with_carry by bounded_solver_tac
        | erewrite <- !fst_sub_with_carry by bounded_solver_tac
        | erewrite <- !decode_snd_sub_with_carry by bounded_solver_tac
        | erewrite <- !decode_mul by bounded_solver_tac
        | erewrite <- !decode_mul_low_low by bounded_solver_tac
        | erewrite <- !decode_mul_high_low by bounded_solver_tac
        | erewrite <- !decode_mul_high_high by bounded_solver_tac
        | erewrite <- !decode_select_conditional by bounded_solver_tac
        | erewrite <- !decode_add_modulo by bounded_solver_tac ].
Ltac push_decode := repeat push_decode_step.
Ltac pull_decode := repeat pull_decode_step.

(* We take special care to handle the case where the decoder is
   syntactically different but the decoded expression is judgmentally
   the same; we don't want to split apart variables that should be the
   same. *)
Ltac set_decode_step check :=
  match goal with
  | [ |- context G[@Interface.decode ?n ?W ?dr ?w] ]
    => check w;
      first [ match goal with
              | [ d := @Interface.decode _ _ _ w |- _ ]
                => change (@Interface.decode n W dr w) with d
              end
            | generalize (@decode_range n W dr _ w);
              let d := fresh "d" in
              set (d := @Interface.decode n W dr w);
              intro ]
  end.
Ltac set_decode check := repeat set_decode_step check.
Ltac clearbody_decode :=
  repeat match goal with
         | [ H := @Interface.decode _ _ _ _ |- _ ] => clearbody H
         end.
Ltac generalize_decode_by check := set_decode check; clearbody_decode.
Ltac generalize_decode := generalize_decode_by ltac:(fun w => idtac).
Ltac generalize_decode_var := generalize_decode_by ltac:(fun w => is_var w).

Module fancy_machine.
  Local Notation imm := Z (only parsing).

  Class instructions (n : Z) :=
    {
      W : Type (* [n]-bit word *);
      decode :> decoder n W;
      ldi :> load_immediate W;
      shrd :> shift_right_doubleword_immediate W;
      shl :> shift_left_immediate W;
      shr :> shift_right_immediate W;
      mkl :> mask_keep_low W;
      adc :> add_with_carry W;
      subc :> sub_with_carry W;
      mulhwll :> multiply_low_low W;
      mulhwhl :> multiply_high_low W;
      mulhwhh :> multiply_high_high W;
      selc :> select_conditional W;
      addm :> add_modulo W
    }.

  Class arithmetic {n_over_two} (ops:instructions (2 * n_over_two)) :=
    {
      decode_range :> is_decode decode;
      load_immediate :> is_load_immediate ldi;
      shift_right_doubleword_immediate :> is_shift_right_doubleword_immediate shrd;
      shift_left_immediate :> is_shift_left_immediate shl;
      shift_right_immediate :> is_shift_right_immediate shr;
      mask_keep_low :> is_mask_keep_low mkl;
      add_with_carry :> is_add_with_carry adc;
      sub_with_carry :> is_sub_with_carry subc;
      multiply_low_low :> is_mul_low_low n_over_two mulhwll;
      multiply_high_low :> is_mul_high_low n_over_two mulhwhl;
      multiply_high_high :> is_mul_high_high n_over_two mulhwhh;
      select_conditional :> is_select_conditional selc;
      add_modulo :> is_add_modulo addm
    }.
End fancy_machine.
