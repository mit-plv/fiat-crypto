(** Some constants that return their first argument, and hold an equal second argument. *)
Require Import Crypto.Util.Tuple.
Definition id_with_alt {A} (value : A) (value_for_alt : A) : A
:= value.
Definition id_with_alt_proof {A} (value : A) (value_for_alt : A)
           {pf : value = value_for_alt}
  : A
  := id_with_alt value value_for_alt.
Fixpoint id_tuple'_with_alt {A n}
         {struct n}
  : forall (value value_for_alt : tuple' A n),
    tuple' A n
  := match n return forall value value_for_alt : tuple' A n, tuple' A n with
     | O => id_with_alt
     | S n' => fun (value value_for_alt : tuple' A n' * A)
               => (@id_tuple'_with_alt A n' (fst value) (fst value_for_alt),
                   @id_with_alt A (snd value) (snd value_for_alt))
     end.
Fixpoint id_tuple'_with_alt_proof {A n}
         {struct n}
  : forall (value value_for_alt : tuple' A n) {pf : value = value_for_alt},
    tuple' A n
  := match n return forall value value_for_alt : tuple' A n, _ -> tuple' A n with
     | O => id_with_alt_proof
     | S n' => fun (value value_for_alt : tuple' A n' * A) (pf : value = value_for_alt)
               => (@id_tuple'_with_alt_proof A n' (fst value) (fst value_for_alt)
                                             (f_equal (@fst _ _) pf),
                   @id_with_alt_proof A (snd value) (snd value_for_alt)
                                      (f_equal (@snd _ _) pf))
     end.
Definition id_tuple_with_alt {A n}
  : forall (value value_for_alt : tuple A n), tuple A n
  := match n with
     | O => id_with_alt
     | S n' => id_tuple'_with_alt
     end.
Fixpoint id_tuple_with_alt_proof {A n}
         {struct n}
  : forall (value value_for_alt : tuple A n) {pf : value = value_for_alt},
    tuple A n
  := match n with
     | O => id_with_alt_proof
     | S n' => id_tuple'_with_alt_proof
     end.
