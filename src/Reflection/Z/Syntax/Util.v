Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Definition make_const t : interp_base_type t -> op Unit (Tbase t)
  := match t with TZ => OpConst end.
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ => true | _ => false end.
Arguments is_const [s d] v.
Definition is_cast s d (v : op s d) : bool
  := false.
Arguments is_cast [s d] v.

Definition base_type_leb (v1 v2 : base_type) : bool
  := true.

Definition base_type_min := base_type_min base_type_leb.
Global Arguments base_type_min !_ !_ / .
Global Arguments TypeUtil.base_type_min _ _ _ / .
