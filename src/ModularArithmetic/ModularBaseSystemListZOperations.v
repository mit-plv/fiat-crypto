(** * Definitions of some basic operations on ℤ used in ModularBaseSystemList *)
(** We separate these out so that we can depend on them in other files
    without waiting for ModularBaseSystemList to build. *)
Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Word.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tuple.

Definition cmovl (x y r1 r2 : Z) := if Z.leb x y then r1 else r2.
Definition cmovne (x y r1 r2 : Z) := if Z.eqb x y then r1 else r2.

(* analagous to NEG assembly instruction on an integer that is 0 or 1:
   neg 1 = 2^64 - 1 (on 64-bit; 2^32-1 on 32-bit, etc.)
   neg 0 = 0 *)
Definition neg (int_width : Z) (b : Z) := if Z.eqb b 1 then Z.ones int_width else 0%Z.

Definition wcmovl_gen {logsz} x y r1 r2
  := @ZToWord logsz (cmovl (@wordToZ logsz x) (@wordToZ logsz y) (@wordToZ logsz r1) (@wordToZ logsz r2)).
Definition wcmovne_gen {logsz} x y r1 r2
  := @ZToWord logsz (cmovne (@wordToZ logsz x) (@wordToZ logsz y) (@wordToZ logsz r1) (@wordToZ logsz r2)).
Definition wneg_gen {logsz} (int_width : Z) b
  := @ZToWord logsz (neg int_width (@wordToZ logsz b)).

Definition wcmovl32 x y r1 r2 := ZToWord32 (cmovl (word32ToZ x) (word32ToZ y) (word32ToZ r1) (word32ToZ r2)).
Definition wcmovne32 x y r1 r2 := ZToWord32 (cmovne (word32ToZ x) (word32ToZ y) (word32ToZ r1) (word32ToZ r2)).
Definition wneg32 (int_width : Z) b := ZToWord32 (neg int_width (word32ToZ b)).

Definition wcmovl64 x y r1 r2 := ZToWord64 (cmovl (word64ToZ x) (word64ToZ y) (word64ToZ r1) (word64ToZ r2)).
Definition wcmovne64 x y r1 r2 := ZToWord64 (cmovne (word64ToZ x) (word64ToZ y) (word64ToZ r1) (word64ToZ r2)).
Definition wneg64 (int_width : Z) b := ZToWord64 (neg int_width (word64ToZ b)).

Definition wcmovl128 x y r1 r2 := ZToWord128 (cmovl (word128ToZ x) (word128ToZ y) (word128ToZ r1) (word128ToZ r2)).
Definition wcmovne128 x y r1 r2 := ZToWord128 (cmovne (word128ToZ x) (word128ToZ y) (word128ToZ r1) (word128ToZ r2)).
Definition wneg128 (int_width : Z) b := ZToWord128 (neg int_width (word128ToZ b)).

Definition wcmovl {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz -> word sz -> word sz)
               logsz wcmovl32 wcmovl64 wcmovl128 (@wcmovl_gen).
Definition wcmovne {logsz}
  := word_case (T:=fun sz => word sz -> word sz -> word sz -> word sz -> word sz)
               logsz wcmovne32 wcmovne64 wcmovne128 (@wcmovne_gen).
Definition wneg {logsz}
  := word_case (T:=fun sz => Z -> word sz -> word sz)
               logsz wneg32 wneg64 wneg128 (@wneg_gen).
