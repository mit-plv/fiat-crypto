(** Definitions for use in pre-reified rewriter rules *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Module ident.
  Definition literal {T} (v : T) := v.
  Definition eagerly {T} (v : T) := v.
  Definition gets_inlined (real_val : bool) {T} (v : T) : bool := real_val.

  Section cast.
    Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

    Definition is_more_pos_than_neg (r : zrange) (v : BinInt.Z) : bool
      := ((Z.abs (lower r) <? Z.abs (upper r)) (* if more of the range is above 0 than below 0 *)
          || ((lower r =? upper r) && (0 <=? lower r))
          || ((Z.abs (lower r) =? Z.abs (upper r)) && (0 <=? v))).

    (** We ensure that [ident.cast] is symmetric under [Z.opp], as
            this makes some rewrite rules much, much easier to
            prove. *)
    Let cast_outside_of_range' (r : zrange) (v : BinInt.Z) : BinInt.Z
      := ((cast_outside_of_range r v - lower r) mod (upper r - lower r + 1)) + lower r.

    Definition cast (r : zrange) (x : BinInt.Z)
      := let r := ZRange.normalize r in
         if (lower r <=? x) && (x <=? upper r)
         then x
         else if is_more_pos_than_neg r x
              then cast_outside_of_range' r x
              else -cast_outside_of_range' (-r) (-x).
    Definition cast2 (r : zrange * zrange) (x : BinInt.Z * BinInt.Z)
      := (cast (Datatypes.fst r) (Datatypes.fst x),
          cast (Datatypes.snd r) (Datatypes.snd x)).
  End cast.

  Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
  Proof. exact v. Qed.

  Module Thunked.
    Definition bool_rect P (t f : Datatypes.unit -> P) (b : bool) : P
      := Datatypes.bool_rect (fun _ => P) (t tt) (f tt) b.
    Definition list_rect {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P -> P) (ls : list A) : P
      := Datatypes.list_rect (fun _ => P) (N tt) C ls.
    Definition list_case {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P) (ls : list A) : P
      := ListUtil.list_case (fun _ => P) (N tt) C ls.
    Definition nat_rect P (O_case : unit -> P) (S_case : nat -> P -> P) (n : nat) : P
      := Datatypes.nat_rect (fun _ => P) (O_case tt) S_case n.
    Definition option_rect {A} P (S_case : A -> P) (N_case : unit -> P) (o : option A) : P
      := Datatypes.option_rect (fun _ => P) S_case (N_case tt) o.
  End Thunked.
End ident.

Global Opaque ident.cast. (* This should never be unfolded except in [Language.Wf] *)
