(** * Push-Button Synthesis fancy argument definitions *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Section with_wordmax.
  Context (log2wordmax : Z) (consts : list Z).
  Let wordmax := 2 ^ log2wordmax.
  Let half_bits := log2wordmax / 2.
  Let wordmax_half_bits := 2 ^ half_bits.

  Inductive kind_of_constant := upper_half (c : BinInt.Z) | lower_half (c : BinInt.Z).

  Definition constant_to_scalar_single (const x : BinInt.Z) : option kind_of_constant :=
    if x =? (BinInt.Z.shiftr const half_bits)
    then Some (upper_half const)
    else if x =? (BinInt.Z.land const (wordmax_half_bits - 1))
         then Some (lower_half const)
         else None.

  Definition constant_to_scalar (x : BinInt.Z)
    : option kind_of_constant :=
    fold_right (fun c res => match res with
                             | Some s => Some s
                             | None => constant_to_scalar_single c x
                             end) None consts.

  Definition invert_low (v : BinInt.Z) : option BinInt.Z
    := match constant_to_scalar v with
       | Some (lower_half v) => Some v
       | _ => None
       end.

  Definition invert_high (v : BinInt.Z) : option BinInt.Z
    := match constant_to_scalar v with
       | Some (upper_half v) => Some v
       | _ => None
       end.
End with_wordmax.
