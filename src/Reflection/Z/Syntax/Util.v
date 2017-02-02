Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Syntax.

Definition make_const t : interp_base_type t -> op Unit (Tbase t)
  := match t with TZ => OpConst end.
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ => true | _ => false end.
