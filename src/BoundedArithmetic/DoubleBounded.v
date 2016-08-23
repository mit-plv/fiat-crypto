(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
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

Section generic_constructions.
  Section decode.
    Context {n W} {decode : decoder n W}.
    Section with_k.
      Context {k : nat}.
      Let limb_widths := repeat n k.
      (** The list is low to high; the tuple is low to high *)
      Local Instance tuple_decoder : decoder (k * n) (tuple W k)
        := { decode w := BaseSystem.decode (base_from_limb_widths limb_widths) (List.map decode (List.rev (Tuple.to_list _ w))) }.
    End with_k.
  End decode.

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

  Section ripple_carry_adc.
    Context {n W} {decode : decoder n W} (adc : add_with_carry W).

    Global Instance ripple_carry_adc {k} : add_with_carry (tuple W k)
      := {| Interface.adc := ripple_carry_tuple adc k |}.
  End ripple_carry_adc.

  (* TODO: Would it made sense to make generic-width shift operations here? *)

  Section tuple2.
    Section spread_left.
      Context (n : Z) {W}
              {ldi : load_immediate W}
              {shl : shift_left_immediate W}
              {shr : shift_right_immediate W}.

      Definition spread_left_from_shift (r : W) (count : Z) : tuple W 2
        := (shl r count, if count =? 0 then ldi 0 else shr r (n - count)).

      (** Require a [decode] instance to aid typeclass search in
          resolving [n] *)
      Global Instance sprl_from_shift {decode : decoder n W} : spread_left_immediate W
        := {| Interface.sprl := spread_left_from_shift |}.
    End spread_left.

    Section full_from_half.
      Context {W}
              {mulhwll : multiply_low_low W}
              {mulhwhl : multiply_high_low W}
              {mulhwhh : multiply_high_high W}
              {adc : add_with_carry W}
              {shl : shift_left_immediate W}
              {shr : shift_right_immediate W}.

      Section def.
        Context (half_n : Z).
        Definition mul_double (a b : W) : tuple W 2
          := let out : tuple W 2 := (mulhwll a b, mulhwhh a b) in
             let tmp             := mulhwhl a b in
             let '(_, out)   := eta (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
             let tmp             := mulhwhl b a in
             let '(_, out)   := eta (ripple_carry_adc adc out (shl tmp half_n, shr tmp half_n) false) in
             out.
      End def.

      Section instances.
        Context {half_n : Z}
                {ldi : load_immediate W}.

        (** Require a dummy [decoder] for these instances to allow
            typeclass inference of the [half_n] argument *)
        Global Instance mul_double_multiply_low_low {decode : decoder (2 * half_n) W}
          : multiply_low_low (tuple W 2)
          := {| Interface.mulhwll a b := mul_double half_n (fst a) (fst b) |}.
        Global Instance mul_double_multiply_high_low {decode : decoder (2 * half_n) W}
          : multiply_high_low (tuple W 2)
          := {| Interface.mulhwhl a b := mul_double half_n (snd a) (fst b) |}.
        Global Instance mul_double_multiply_high_high {decode : decoder (2 * half_n) W}
          : multiply_high_high (tuple W 2)
          := {| Interface.mulhwhh a b := mul_double half_n (snd a) (snd b) |}.
      End instances.
    End full_from_half.
  End tuple2.
End generic_constructions.

Global Arguments tuple_decoder : simpl never.

Hint Resolve (fun n W decode => (@tuple_decoder n W decode 2 : decoder (2 * n) (tuple W 2))) : typeclass_instances.
Hint Extern 3 (decoder _ (tuple ?W ?k)) => let kv := (eval simpl in (Z.of_nat k)) in apply (fun n decode => (@tuple_decoder n W decode k : decoder (kv * n) (tuple W k))) : typeclass_instances.
