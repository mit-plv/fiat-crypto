(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.

Local Open Scope list_scope.
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
  Definition ripple_carry {T} (f : T -> T -> bool -> bool * T)
             (xs ys : list T) (carry : bool) : bool * list T
    := List.fold_right
         (fun x_y carry_zs => let '(x, y) := eta x_y in
                              let '(carry, zs) := eta carry_zs in
                              let '(carry, z) := eta (f x y carry) in
                              (carry, z :: zs))
         (carry, nil)
         (List.combine xs ys).

  (** tuple is high to low ([to_list] reverses) *)
  Fixpoint ripple_carry_tuple' {T} (f : T -> T -> bool -> bool * T) k
    : forall (xs ys : tuple' T k) (carry : bool), bool * tuple' T k
    := match k return forall (xs ys : tuple' T k) (carry : bool), bool * tuple' T k with
       | O => f
       | S k' => fun xss yss carry => let '(xs, x) := eta xss in
                                      let '(ys, y) := eta yss in
                                      let '(carry, zs) := eta (@ripple_carry_tuple' _ f k' xs ys carry) in
                                      let '(carry, z) := eta (f x y carry) in
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

(** constructions on [tuple W 2] *)
Section tuple2.
  Section spread_left.
    Context (n : Z) {W}
            {ldi : load_immediate W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}.

    Definition spread_left_from_shift (r : W) (count : Z) : tuple W 2
      := (shl r count, if count =? 0 then ldi 0 else shr r (n - count)).

    (** Require a [decoder] instance to aid typeclass search in
        resolving [n] *)
    Global Instance sprl_from_shift {decode : decoder n W} : spread_left_immediate W
      := { sprl := spread_left_from_shift }.
  End spread_left.

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
      := let out : tuple W 2 := (mulhwll a b, mulhwhh a b) in
         let tmp             := mulhwhl a b in
         let '(_, out)   := eta (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
         let tmp             := mulhwhl b a in
         let '(_, out)   := eta (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
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
