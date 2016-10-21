(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Import Bug5107WorkAround.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).

(** The list is low to high; the tuple is low to high *)
Definition tuple_decoder {n W} {decode : decoder n W} {k : nat} : decoder (k * n) (tuple W k)
  := {| decode w := BaseSystem.decode (base_from_limb_widths (repeat n k))
                                      (List.map decode (List.rev (Tuple.to_list _ w))) |}.
Global Arguments tuple_decoder : simpl never.
Hint Extern 3 (decoder _ (tuple ?W ?k)) => let kv := (eval simpl in (Z.of_nat k)) in apply (fun n decode => (@tuple_decoder n W decode k : decoder (kv * n) (tuple W k))) : typeclass_instances.

Section ripple_carry_definitions.
  (** tuple is high to low ([to_list] reverses) *)
  Fixpoint ripple_carry_tuple' {T} (f : T -> T -> bool -> bool * T) k
    : forall (xs ys : tuple' T k) (carry : bool), bool * tuple' T k
    := match k return forall (xs ys : tuple' T k) (carry : bool), bool * tuple' T k with
       | O => f
       | S k' => fun xss yss carry => dlet xss := xss in
                                      dlet yss := yss in
                                      let (xs, x) := eta xss in
                                      let (ys, y) := eta yss in
                                      dlet addv := (@ripple_carry_tuple' _ f k' xs ys carry) in
                                      let (carry, zs) := eta addv in
                                      dlet fxy := (f x y carry) in
                                      let (carry, z) := eta fxy in
                                      (carry, (zs, z))
       end.

  Definition ripple_carry_tuple {T} (f : T -> T -> bool -> bool * T) k
    : forall (xs ys : tuple T k) (carry : bool), bool * tuple T k
    := match k return forall (xs ys : tuple T k) (carry : bool), bool * tuple T k with
       | O => fun xs ys carry => (carry, tt)
       | S k' => ripple_carry_tuple' f k'
       end.
End ripple_carry_definitions.

Global Instance ripple_carry_adc
       {W} (adc : add_with_carry W) {k}
  : add_with_carry (tuple W k)
  := { adc := ripple_carry_tuple adc k }.

Global Instance ripple_carry_subc
       {W} (subc : sub_with_carry W) {k}
  : sub_with_carry (tuple W k)
  := { subc := ripple_carry_tuple subc k }.

(** constructions on [tuple W 2] *)
Section tuple2.
  Section select_conditional.
    Context {W}
            {selc : select_conditional W}.

    Definition select_conditional_double (b : bool) (x : tuple W 2) (y : tuple W 2) : tuple W 2
      := dlet x := x in
         dlet y := y in
         let (x1, x2) := eta x in
         let (y1, y2) := eta y in
         (selc b x1 y1, selc b x2 y2).

    Global Instance selc_double : select_conditional (tuple W 2)
      := { selc := select_conditional_double }.
  End select_conditional.

  Section load_immediate.
    Context (n : Z) {W}
            {ldi : load_immediate W}.

    Definition load_immediate_double (r : Z) : tuple W 2
      := (ldi (r mod 2^n), ldi (r / 2^n)).

    (** Require a [decoder] instance to aid typeclass search in
        resolving [n] *)
    Global Instance ldi_double {decode : decoder n W} : load_immediate (tuple W 2)
      := { ldi := load_immediate_double }.
  End load_immediate.

  Section bitwise_or.
    Context {W}
            {or : bitwise_or W}.

    Definition bitwise_or_double (x : tuple W 2) (y : tuple W 2) : tuple W 2
      := dlet x := x in
         dlet y := y in
         let (x1, x2) := eta x in
         let (y1, y2) := eta y in
         (or x1 y1, or x2 y2).

    Global Instance or_double : bitwise_or (tuple W 2)
      := { or := bitwise_or_double }.
  End bitwise_or.

  Section bitwise_and.
    Context {W}
            {and : bitwise_and W}.

    Definition bitwise_and_double (x : tuple W 2) (y : tuple W 2) : tuple W 2
      := dlet x := x in
         dlet y := y in
         let (x1, x2) := eta x in
         let (y1, y2) := eta y in
         (and x1 y1, and x2 y2).

    Global Instance and_double : bitwise_and (tuple W 2)
      := { and := bitwise_and_double }.
  End bitwise_and.

  Section spread_left.
    Context (n : Z) {W}
            {ldi : load_immediate W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}.

    Definition spread_left_from_shift (r : W) (count : Z) : tuple W 2
      := dlet r := r in
         (shl r count, if count =? 0 then ldi 0 else shr r (n - count)).

    (** Require a [decoder] instance to aid typeclass search in
        resolving [n] *)
    Global Instance sprl_from_shift {decode : decoder n W} : spread_left_immediate W
      := { sprl := spread_left_from_shift }.
  End spread_left.

  Section shl_shr.
    Context (n : Z) {W}
            {ldi : load_immediate W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}
            {or : bitwise_or W}.

    Definition shift_left_immediate_double (r : tuple W 2) (count : Z) : tuple W 2
      := dlet r := r in
         let (r1, r2) := eta r in
         (if count =? 0
          then r1
          else if count <? n
               then shl r1 count
               else ldi 0,
          if count =? 0
          then r2
          else if count <? n
               then or (shr r1 (n - count)) (shl r2 count)
               else shl r1 (count - n)).

    Definition shift_right_immediate_double (r : tuple W 2) (count : Z) : tuple W 2
      := dlet r := r in
         let (r1, r2) := eta r in
         (if count =? 0
          then r1
          else if count <? n
               then or (shr r1 count) (shl r2 (n - count))
               else shr r2 (count - n),
          if count =? 0
          then r2
          else if count <? n
               then shr r2 count
               else ldi 0).

    (** Require a [decoder] instance to aid typeclass search in
        resolving [n] *)
    Global Instance shl_double {decode : decoder n W} : shift_left_immediate (tuple W 2)
      := { shl := shift_left_immediate_double }.
    Global Instance shr_double {decode : decoder n W} : shift_right_immediate (tuple W 2)
      := { shr := shift_right_immediate_double }.
  End shl_shr.

  Section shrd.
    Context (n : Z) {W}
            {ldi : load_immediate W}
            {shrd : shift_right_doubleword_immediate W}.

    Definition shift_right_doubleword_immediate_double (high low : tuple W 2) (count : Z) : tuple W 2
      := dlet high := high in
         dlet low := low in
         let (high1, high2) := eta high in
         let (low1, low2) := eta low in
         (if count =? 0
          then low1
          else if count <? n
               then shrd low2 low1 count
               else if count <? 2 * n
                    then shrd high1 low2 (count - n)
                    else shrd high2 high1 (count - 2 * n),
          if count =? 0
          then low2
          else if count <? n
               then shrd high1 low2 count
               else if count <? 2 * n
                    then shrd high2 high1 (count - n)
                    else shrd (ldi 0) high2 (count - 2 * n)).

    (** Require a [decoder] instance to aid typeclass search in
        resolving [n] *)
    Global Instance shrd_double {decode : decoder n W} : shift_right_doubleword_immediate (tuple W 2)
      := { shrd := shift_right_doubleword_immediate_double }.
  End shrd.

  Section double_from_half.
    Context {half_n : Z} {W}
            {mulhwll : multiply_low_low W}
            {mulhwhl : multiply_high_low W}
            {mulhwhh : multiply_high_high W}
            {adc : add_with_carry W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}
            {ldi : load_immediate W}.

    Definition mul_double (a b : W) : tuple W 2
      := dlet a              := a in
         dlet b              := b in
         let out : tuple W 2 := (mulhwll a b, mulhwhh a b) in
         dlet out            := out in
         dlet tmp            := mulhwhl a b in
         dlet addv           := (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
         let (_, out)        := eta addv in
         dlet tmp            := mulhwhl b a in
         dlet addv           := (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
         let (_, out)        := eta addv in
         out.

    (** Require a dummy [decoder] for these instances to allow
            typeclass inference of the [half_n] argument *)
    Global Instance mul_double_multiply {decode : decoder (2 * half_n) W} : multiply_double W
      := { muldw a b := mul_double a b }.
  End double_from_half.

  Global Instance mul_double_multiply_low_low {W} {muldw : multiply_double W}
    : multiply_low_low (tuple W 2)
    := { mulhwll a b := muldw (fst a) (fst b) }.
  Global Instance mul_double_multiply_high_low {W} {muldw : multiply_double W}
    : multiply_high_low (tuple W 2)
    := { mulhwhl a b := muldw (snd a) (fst b) }.
  Global Instance mul_double_multiply_high_high {W} {muldw : multiply_double W}
    : multiply_high_high (tuple W 2)
    := { mulhwhh a b := muldw (snd a) (snd b) }.
End tuple2.

Global Arguments mul_double half_n {_ _ _ _ _ _ _} _ _.
