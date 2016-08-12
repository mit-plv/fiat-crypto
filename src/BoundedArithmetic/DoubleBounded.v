(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).

Section generic_constructions.
  Definition ripple_carry {T} (f : T -> T -> bool -> bool * T)
             (carry : bool) (xs ys : list T) : bool * list T
    := List.fold_right
         (fun x_y carry_zs => let '(x, y) := eta x_y in
                              let '(carry, zs) := eta carry_zs in
                              let '(carry, z) := eta (f x y carry) in
                              (carry, z :: zs))
         (carry, nil)
         (List.combine xs ys).

  (* TODO: Would it made sense to make generic-width shift operations here? *)

  (* FUTURE: here go proofs about [ripple_carry] with [f] that satisfies [is_add_with_carry] *)
End generic_constructions.
