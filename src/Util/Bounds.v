Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.

Delimit Scope bounds_scope with bounds.
Record bounds := { lower : Z ; upper : Z }.
Bind Scope bounds_scope with bounds.
Local Open Scope Z_scope.

Definition ZToBounds (z : Z) : bounds := {| lower := z ; upper := z |}.

Ltac inversion_bounds :=
  let lower := (eval cbv [lower] in (fun x => lower x)) in
  let upper := (eval cbv [upper] in (fun y => upper y)) in
  repeat match goal with
         | [ H : _ = _ :> bounds |- _ ]
           => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
              cbv beta iota in *
         end.

(** All of the boundedness properties take an optional bitwidth, and
    enforce the condition that the bounds are within 0 and 2^bitwidth,
    if given. *)
Section with_bitwidth.
  Context (bitwidth : option Z).

  Definition is_bounded_byb : bounds -> Z -> bool
    := fun bound val
       => (((lower bound <=? val) && (val <=? upper bound))
             && (match bitwidth with
                 | Some sz => (0 <=? lower bound) && (upper bound <? 2^sz)
                 | None => true
                 end))%bool%Z.
  Definition is_bounded_by' : bounds -> Z -> Prop
    := fun bound val => is_bounded_byb bound val = true.

  Definition is_bounded_by {n} : Tuple.tuple bounds n -> Tuple.tuple Z n -> Prop
    := Tuple.pointwise2 is_bounded_by'.
End with_bitwidth.

Global Instance dec_eq_bounds : DecidableRel (@eq bounds) | 10.
Proof.
  intros [lx ux] [ly uy].
  destruct (dec (lx = ly)), (dec (ux = uy));
    [ left; apply f_equal2; assumption
    | abstract (right; intro H; inversion_bounds; tauto).. ].
Defined.

Module Export Notations.
  Delimit Scope bounds_scope with bounds.
  Notation "b[ l ~> u ]" := {| lower := l ; upper := u |}
                              (format "b[ l  ~>  u ]") : bounds_scope.
End Notations.
