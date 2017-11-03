(** * PHOAS Syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Curry.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.NatUtil. (* for nat_beq for equality schemes *)
Export Syntax.Notations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive base_type := TZ | TBool.

Local Notation tZ := (Tbase TZ).
Local Notation tBool := (Tbase TBool).

Definition interp_base_type (v : base_type) : Set :=
  match v with
  | TZ => Z
  | TBool => bool
  end.

Inductive op : flat_type base_type -> flat_type base_type -> Set :=
| AddWithGetCarry : op (tuple tZ 4) (tuple tZ 2)
| SubWithGetBorrow : op (tuple tZ 4) (tuple tZ 2)
| MulSplitAtBitwidth : op (tuple tZ 3) (tuple tZ 2)
| AddWithGetCarryZ (bitwidth : Z) : op (tuple tZ 3) (tuple tZ 2)
| SubWithGetBorrowZ (bitwidth : Z) : op (tuple tZ 3) (tuple tZ 2)
| MulSplitAtBitwidthZ (bitwidth : Z) : op (tuple tZ 2) (tuple tZ 2)
| Zselect : op (tuple tZ 3) (tuple tZ 1)
| Zmul    : op (tuple tZ 2) (tuple tZ 1)
| Zadd    : op (tuple tZ 2) (tuple tZ 1)
| Zopp    : op (tuple tZ 1) (tuple tZ 1)
| Zshiftr : op (tuple tZ 2) (tuple tZ 1)
| Zshiftl : op (tuple tZ 2) (tuple tZ 1)
| Zland   : op (tuple tZ 2) (tuple tZ 1)
| Zlor    : op (tuple tZ 2) (tuple tZ 1)
| Zmodulo : op (tuple tZ 2) (tuple tZ 1)
| Zdiv    : op (tuple tZ 2) (tuple tZ 1)
| Zlog2   : op (tuple tZ 1) (tuple tZ 1)
| Zpow    : op (tuple tZ 2) (tuple tZ 1)
| Zones   : op (tuple tZ 1) (tuple tZ 1)
| Zeqb    : op (tuple tZ 2) (tuple tBool 1)
| ConstZ (v : BinNums.Z) : op (tuple tZ 0) (tuple tZ 1)
| ConstBool (v : bool) : op (tuple tZ 0) (tuple tBool 1)
| BoolCase {T} : op (Prod (Prod tBool T) T) T.

Definition Const {t} : interp_base_type t -> op Unit (Tbase t)
  := match t with
     | TZ => ConstZ
     | Tbool => ConstBool
     end.

Definition interp_op {s d} (opv : op s d) : interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d
  := match opv with
     | AddWithGetCarry => curry4 Z.add_with_get_carry
     | SubWithGetBorrow => curry4 Z.sub_with_get_borrow
     | MulSplitAtBitwidth => curry3 Z.mul_split_at_bitwidth
     | AddWithGetCarryZ bitwidth => curry3 (Z.add_with_get_carry bitwidth)
     | SubWithGetBorrowZ bitwidth => curry3 (Z.sub_with_get_borrow bitwidth)
     | MulSplitAtBitwidthZ bitwidth => curry2 (Z.mul_split_at_bitwidth bitwidth)
     | Zselect => curry3 Z.zselect
     | Zmul => curry2 Z.mul
     | Zadd => curry2 Z.add
     | Zopp => Z.opp
     | Zshiftr => curry2 Z.shiftr
     | Zshiftl => curry2 Z.shiftl
     | Zland => curry2 Z.land
     | Zlor => curry2 Z.lor
     | Zmodulo => curry2 Z.modulo
     | Zdiv => curry2 Z.div
     | Zlog2 => Z.log2
     | Zpow => curry2 Z.pow
     | Zones => Z.ones
     | Zeqb => curry2 Z.eqb
     | ConstZ v => fun _ => v
     | ConstBool v => fun _ => v
     | BoolCase T => fun '(b, t, f) => if b then t else f
     end.

Notation Expr := (Expr base_type op).
Notation Interp := (Interp (@interp_op)).
