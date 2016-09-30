(*** Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.AutoRewrite.
Require Import Crypto.Util.Notations.

Local Open Scope type_scope.
Local Open Scope Z_scope.

Class decoder (n : Z) W :=
  { decode : W -> Z }.
Coercion decode : decoder >-> Funclass.
Global Arguments decode {n W _} _.

Class is_decode {n W} (decode : decoder n W) :=
  decode_range : forall x, 0 <= decode x < 2^n.

Class bounded_in_range_cls (x y z : Z) := is_bounded_in_range : x <= y < z.
Ltac bounded_solver_tac :=
  solve [ eassumption | typeclasses eauto | omega ].
Hint Extern 0 (bounded_in_range_cls _ _ _) => unfold bounded_in_range_cls; bounded_solver_tac : typeclass_instances.
Global Arguments bounded_in_range_cls / _ _ _.
Global Instance decode_range_bound {n W} {decode : decoder n W} {H : is_decode decode}
  : forall x, bounded_in_range_cls 0 (decode x) (2^n)
  := H.

Class bounded_le_cls (x y : Z) := is_bounded_le : x <= y.
Hint Extern 0 (bounded_le_cls _ _) => unfold bounded_le_cls; bounded_solver_tac : typeclass_instances.
Global Arguments bounded_le_cls / _ _.

Inductive bounded_decode_pusher_tag := decode_tag.

Ltac push_decode_step :=
  match goal with
  | [ |- context[@decode ?n ?W ?decoder ?w] ]
    => tc_rewrite (decode_tag) (@decode n W decoder w) ->
  | [ |- context[match @fst ?A ?B ?x with true => 1 | false => 0 end] ]
    => tc_rewrite (decode_tag) (match @fst A B x with true => 1 | false => 0 end) ->
  end.
Ltac push_decode := repeat push_decode_step.
Ltac pull_decode_step :=
  match goal with
  | [ |- context[?E] ]
    => lazymatch type of E with
       | Z => idtac
       | bool => idtac
       end;
       tc_rewrite (decode_tag) <- E
  end.
Ltac pull_decode := repeat pull_decode_step.

Delimit Scope bounded_rewrite_scope with bounded_rewrite.

Infix "<~=~>" := (rewrite_eq decode_tag) : bounded_rewrite_scope.
Infix "=~>" := (rewrite_left_to_right_eq decode_tag) : bounded_rewrite_scope.
Infix "<~=" := (rewrite_right_to_left_eq decode_tag) : bounded_rewrite_scope.
Notation "x <= y" := (bounded_le_cls x y) : bounded_rewrite_scope.
Notation "x <= y < z" := (bounded_in_range_cls x y z) : bounded_rewrite_scope.

Module Import BoundedRewriteNotations.
  Infix "<~=~>" := (rewrite_eq decode_tag) : type_scope.
  Infix "=~>" := (rewrite_left_to_right_eq decode_tag) : type_scope.
  Infix "<~=" := (rewrite_right_to_left_eq decode_tag) : type_scope.
  Open Scope bounded_rewrite_scope.
End BoundedRewriteNotations.

(** This is required for typeclass resolution to be fast. *)
Typeclasses Opaque decode.

Section InstructionGallery.
  Context (n : Z) (* bit-width of width of [W] *)
          {W : Type} (* bounded type, [W] for word *)
          (Wdecoder : decoder n W).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Class load_immediate := { ldi : imm -> W }.
  Global Coercion ldi : load_immediate >-> Funclass.

  Class is_load_immediate {ldi : load_immediate}  :=
    decode_load_immediate :> forall x, 0 <= x < 2^n -> decode (ldi x) =~> x.

  Class shift_right_doubleword_immediate := { shrd : W -> W -> imm -> W }.
  Global Coercion shrd : shift_right_doubleword_immediate >-> Funclass.

  Class is_shift_right_doubleword_immediate (shrd : shift_right_doubleword_immediate) :=
    decode_shift_right_doubleword :>
      forall high low count,
        0 <= count < n
        -> decode (shrd high low count) <~=~> (((decode high << n) + decode low) >> count) mod 2^n.

  Class shift_left_immediate := { shl : W -> imm -> W }.
  Global Coercion shl : shift_left_immediate >-> Funclass.

  Class is_shift_left_immediate (shl : shift_left_immediate) :=
    decode_shift_left_immediate :>
      forall r count, 0 <= count < n -> decode (shl r count) <~=~> (decode r << count) mod 2^n.

  Class shift_right_immediate := { shr : W -> imm -> W }.
  Global Coercion shr : shift_right_immediate >-> Funclass.

  Class is_shift_right_immediate (shr : shift_right_immediate) :=
    decode_shift_right_immediate :>
      forall r count, 0 <= count < n -> decode (shr r count) <~=~> (decode r >> count).

  Class spread_left_immediate := { sprl : W -> imm -> tuple W 2 (* [(low, high)] *) }.
  Global Coercion sprl : spread_left_immediate >-> Funclass.

  Class is_spread_left_immediate (sprl : spread_left_immediate) :=
    {
      decode_fst_spread_left_immediate :> forall r count,
          0 <= count < n
          -> decode (fst (sprl r count)) =~> (decode r << count) mod 2^n;
      decode_snd_spread_left_immediate :> forall r count,
        0 <= count < n
        -> decode (snd (sprl r count)) =~> (decode r << count) >> n

    }.

  Class mask_keep_low := { mkl :> W -> imm -> W }.
  Global Coercion mkl : mask_keep_low >-> Funclass.

  Class is_mask_keep_low (mkl : mask_keep_low) :=
    decode_mask_keep_low :> forall r count,
      0 <= count < n -> decode (mkl r count) <~=~> decode r mod 2^count.

  Local Notation bit b := (if b then 1 else 0).

  Class add_with_carry := { adc : W -> W -> bool -> bool * W }.
  Global Coercion adc : add_with_carry >-> Funclass.

  Class is_add_with_carry (adc : add_with_carry) :=
    {
      bit_fst_add_with_carry :> forall x y c, bit (fst (adc x y c)) <~=~> (decode x + decode y + bit c) >> n;
      decode_snd_add_with_carry :> forall x y c, decode (snd (adc x y c)) <~=~> (decode x + decode y + bit c) mod (2^n)
    }.

  Class sub_with_carry := { subc : W -> W -> bool -> bool * W }.
  Global Coercion subc : sub_with_carry >-> Funclass.

  Class is_sub_with_carry (subc:W->W->bool->bool*W) :=
    {
      fst_sub_with_carry :> forall x y c, fst (subc x y c) <~=~> ((decode x - decode y - bit c) <? 0);
      decode_snd_sub_with_carry :> forall x y c, decode (snd (subc x y c)) <~=~> (decode x - decode y - bit c) mod 2^n
    }.

  Class multiply := { mul : W -> W -> W }.
  Global Coercion mul : multiply >-> Funclass.

  Class is_mul (mul : multiply) :=
    decode_mul :> forall x y, decode (mul x y) <~=~> (decode x * decode y).

  Class multiply_low_low := { mulhwll : W -> W -> W }.
  Global Coercion mulhwll : multiply_low_low >-> Funclass.
  Class multiply_high_low := { mulhwhl : W -> W -> W }.
  Global Coercion mulhwhl : multiply_high_low >-> Funclass.
  Class multiply_high_high := { mulhwhh : W -> W -> W }.
  Global Coercion mulhwhh : multiply_high_high >-> Funclass.
  Class multiply_double := { muldw : W -> W -> tuple W 2 }.
  Global Coercion muldw : multiply_double >-> Funclass.

  Class is_mul_low_low (w:Z) (mulhwll : multiply_low_low) :=
    decode_mul_low_low :>
      forall x y, decode (mulhwll x y) <~=~> ((decode x mod 2^w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_low (w:Z) (mulhwhl : multiply_high_low) :=
    decode_mul_high_low :>
      forall x y, decode (mulhwhl x y) <~=~> ((decode x >> w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_high (w:Z) (mulhwhh : multiply_high_high) :=
    decode_mul_high_high :>
      forall x y, decode (mulhwhh x y) <~=~> ((decode x >> w) * (decode y >> w)) mod 2^n.
  Class is_mul_double (muldw : multiply_double) :=
    {
      decode_fst_mul_double :>
        forall x y, decode (fst (muldw x y)) =~> (decode x * decode y) mod 2^n;
      decode_snd_mul_double :>
        forall x y, decode (snd (muldw x y)) =~> (decode x * decode y) >> n
    }.

  Class select_conditional := { selc : bool -> W -> W -> W }.
  Global Coercion selc : select_conditional >-> Funclass.

  Class is_select_conditional (selc : select_conditional) :=
    decode_select_conditional :> forall b x y,
      decode (selc b x y) <~=~> if b then decode x else decode y.

  Class add_modulo := { addm : W -> W -> W (* modulus *) -> W }.
  Global Coercion addm : add_modulo >-> Funclass.

  Class is_add_modulo (addm : add_modulo) :=
    decode_add_modulo :> forall x y modulus,
        decode (addm x y modulus) <~=~> (if (decode x + decode y) <? decode modulus
                                         then (decode x + decode y)
                                         else (decode x + decode y) - decode modulus).
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
Global Arguments multiply_double : clear implicits.
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
Global Arguments muldw {_ _} _ _.
Global Arguments selc {_ _} _ _ _.
Global Arguments addm {_ _} _ _ _.

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
Global Arguments is_mul_double {_ _ _} _.
Global Arguments is_select_conditional {_ _ _} _.
Global Arguments is_add_modulo {_ _ _} _.

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
