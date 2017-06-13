(** * PHOAS Syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Word.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeUtil.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.NatUtil. (* for nat_beq for equality schemes *)
Export Syntax.Notations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive base_type := TZ | TWord (logsz : nat).

Local Notation tZ := (Tbase TZ).
Local Notation tWord logsz := (Tbase (TWord logsz)).

Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| OpConst {T} (z : Z) : op Unit (Tbase T)
| Add T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Sub T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Mul T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Shl T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Shr T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Land T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Lor T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Opp T Tout : op (Tbase T) (Tbase Tout)
| IdWithAlt T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Zselect T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| MulSplit (bitwidth : Z) T1 T2 Tout1 Tout2 : op (Tbase T1 * Tbase T2) (Tbase Tout1 * Tbase Tout2)
| AddWithCarry T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| AddWithGetCarry (bitwidth : Z) T1 T2 T3 Tout1 Tout2 : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout1 * Tbase Tout2)
| SubWithBorrow T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| SubWithGetBorrow (bitwidth : Z) T1 T2 T3 Tout1 Tout2 : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout1 * Tbase Tout2)
.

Definition interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => Z
  | TWord logsz => wordT logsz
  end.

Definition interpToZ {t} : interp_base_type t -> Z
  := match t with
     | TZ => fun x => x
     | TWord _ => wordToZ
     end.
Definition ZToInterp {t} : Z -> interp_base_type t
  := match t return Z -> interp_base_type t with
     | TZ => fun x => x
     | TWord _ => ZToWord
     end.
Definition cast_const {t1 t2} (v : interp_base_type t1) : interp_base_type t2
  := ZToInterp (interpToZ v).

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Definition lift_op {src dst}
           (srcv:=SmartValf (fun _ => base_type) (fun t => t) src)
           (dstv:=SmartValf (fun _ => base_type) (fun t => t) dst)
           (ff:=fun t0 (v : interp_flat_type _ t0) t => SmartFlatTypeMap (var':=fun _ => base_type) (fun _ _ => t) v)
           (srcf:=ff src srcv) (dstf:=ff dst dstv)
           (srcZ:=srcf TZ) (dstZ:=dstf TZ)
           (opZ : interp_flat_type interp_base_type srcZ -> interp_flat_type interp_base_type dstZ)
  : interp_flat_type interp_base_type src
    -> interp_flat_type interp_base_type dst
  := fun xy
     => SmartFlatTypeMapUnInterp
         (fun _ _ => cast_const)
         (opZ (SmartFlatTypeMapInterp2 (fun _ _ => cast_const) _ xy)).

Definition Zinterp_op src dst (f : op src dst)
           (asZ := fun t0 => SmartFlatTypeMap (var':=fun _ => base_type) (fun _ _ => TZ) (SmartValf (fun _ => base_type) (fun t => t) t0))
  : interp_flat_type interp_base_type (asZ src) -> interp_flat_type interp_base_type (asZ dst)
  := match f in op src dst return interp_flat_type interp_base_type (asZ src) -> interp_flat_type interp_base_type (asZ dst) with
     | OpConst _ v => fun _ => cast_const (t1:=TZ) v
     | Add _ _ _ => fun xy => fst xy + snd xy
     | Sub _ _ _ => fun xy => fst xy - snd xy
     | Mul _ _ _ => fun xy => fst xy * snd xy
     | Shl _ _ _ => fun xy => Z.shiftl (fst xy) (snd xy)
     | Shr _ _ _ => fun xy => Z.shiftr (fst xy) (snd xy)
     | Land _ _ _ => fun xy => Z.land (fst xy) (snd xy)
     | Lor _ _ _ => fun xy => Z.lor (fst xy) (snd xy)
     | Opp _ _ => fun x => Z.opp x
     | IdWithAlt _ _ _ => fun xy => id_with_alt (fst xy) (snd xy)
     | Zselect _ _ _ _ => fun ctf => let '(c, t, f) := eta3 ctf in Z.zselect c t f
     | MulSplit bitwidth _ _ _ _ => fun xy => Z.mul_split_at_bitwidth bitwidth (fst xy) (snd xy)
     | AddWithCarry _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.add_with_carry c x y
     | AddWithGetCarry bitwidth _ _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.add_with_get_carry bitwidth c x y
     | SubWithBorrow _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.sub_with_borrow c x y
     | SubWithGetBorrow bitwidth _ _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.sub_with_get_borrow bitwidth c x y
     end%Z.

Definition interp_op src dst (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := lift_op (Zinterp_op src dst f).
