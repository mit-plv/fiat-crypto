(** * PHOAS Syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Export Syntax.Notations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive base_type := TZ.

Local Notation tZ := (Tbase TZ).

Definition interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => Z
  end.

Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| OpConst {T} (z : interp_base_type T) : op Unit (Tbase T)
| Add T : op (Tbase T * Tbase T) (Tbase T)
| Sub T : op (Tbase T * Tbase T) (Tbase T)
| Mul T : op (Tbase T * Tbase T) (Tbase T)
| Shl T : op (Tbase T * Tbase T) (Tbase T)
| Shr T : op (Tbase T * Tbase T) (Tbase T)
| Land T : op (Tbase T * Tbase T) (Tbase T)
| Lor T : op (Tbase T * Tbase T) (Tbase T)
| Neg T (int_width : Z) : op (Tbase T) (Tbase T)
| Cmovne T : op (Tbase T * Tbase T * Tbase T * Tbase T) (Tbase T)
| Cmovle T : op (Tbase T * Tbase T * Tbase T * Tbase T) (Tbase T)
| Cast T1 T2 : op (Tbase T1) (Tbase T2).

Definition interpToZ {t} : interp_base_type t -> Z
  := match t with
     | TZ => fun x => x
     end.
Definition ZToInterp {t} : Z -> interp_base_type t
  := match t return Z -> interp_base_type t with
     | TZ => fun x => x
     end.
Definition cast_const {t1 t2} (v : interp_base_type t1) : interp_base_type t2
  := ZToInterp (interpToZ v).

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Definition interp_op src dst (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
     | OpConst _ v => fun _ => v
     | Add TZ => fun xy => fst xy + snd xy
     | Sub TZ => fun xy => fst xy - snd xy
     | Mul TZ => fun xy => fst xy * snd xy
     | Shl TZ => fun xy => Z.shiftl (fst xy) (snd xy)
     | Shr TZ => fun xy => Z.shiftr (fst xy) (snd xy)
     | Land TZ => fun xy => Z.land (fst xy) (snd xy)
     | Lor TZ => fun xy => Z.lor (fst xy) (snd xy)
     | Neg TZ int_width => fun x => ModularBaseSystemListZOperations.neg int_width x
     | Cmovne TZ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
     | Cmovle TZ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovl x y z w
     | Cast _ _ => cast_const
     end%Z.
