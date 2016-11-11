(** * Definitions of some basic operations on ℤ used in ModularBaseSystemList *)
(** We separate these out so that we can depend on them in other files
    without waiting for ModularBaseSystemList to build. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.

Definition cmovl (x y r1 r2 : Z) := if Z.leb x y then r1 else r2.
Definition cmovne (x y r1 r2 : Z) := if Z.eqb x y then r1 else r2.

(* analagous to NEG assembly instruction on an integer that is 0 or 1:
   neg 1 = 2^64 - 1 (on 64-bit; 2^32-1 on 32-bit, etc.)
   neg 0 = 0 *)
Definition neg (int_width : Z) (b : Z) := if Z.eqb b 1 then Z.ones int_width else 0%Z.
