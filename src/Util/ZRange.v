Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.

Delimit Scope zrange_scope with zrange.
Record zrange := { lower : Z ; upper : Z }.
Bind Scope zrange_scope with zrange.
Local Open Scope Z_scope.

Definition ZToZRange (z : Z) : zrange := {| lower := z ; upper := z |}.

Ltac inversion_zrange :=
  let lower := (eval cbv [lower] in (fun x => lower x)) in
  let upper := (eval cbv [upper] in (fun y => upper y)) in
  repeat match goal with
         | [ H : _ = _ :> zrange |- _ ]
           => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
              cbv beta iota in *
         | [ H : Build_zrange _ _ = _ |- _ ]
           => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
              cbv beta iota in *
         | [ H : _ = Build_zrange _ _ |- _ ]
           => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
              cbv beta iota in *
         end.

(** All of the boundedness properties take an optional bitwidth, and
    enforce the condition that the range is within 0 and 2^bitwidth,
    if given. *)
Section with_bitwidth.
  Context (bitwidth : option Z).

  Definition is_bounded_by' : zrange -> Z -> Prop
    := fun bound val
       => lower bound <= val <= upper bound
          /\ match bitwidth with
             | Some sz => 0 <= lower bound /\ upper bound < 2^sz
             | None => True
             end.

  Definition is_bounded_by {n} : Tuple.tuple zrange n -> Tuple.tuple Z n -> Prop
    := Tuple.fieldwise is_bounded_by'.
End with_bitwidth.

Definition is_tighter_than_bool (x y : zrange) : bool
  := ((lower y <=? lower x) && (upper x <=? upper y))%bool%Z.

Global Instance dec_eq_zrange : DecidableRel (@eq zrange) | 10.
Proof.
  intros [lx ux] [ly uy].
  destruct (dec (lx = ly)), (dec (ux = uy));
    [ left; apply f_equal2; assumption
    | abstract (right; intro H; inversion_zrange; tauto).. ].
Defined.

Module Export Notations.
  Delimit Scope zrange_scope with zrange.
  Notation "r[ l ~> u ]" := {| lower := l ; upper := u |} : zrange_scope.
  Infix "<=?" := is_tighter_than_bool : zrange_scope.
End Notations.
