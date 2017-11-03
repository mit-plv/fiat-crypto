Require Import Coq.Bool.Bool.

Definition adjust_is_true {P} (v : is_true P) : is_true P
  := match P as P return is_true P -> is_true P with
     | true => fun _ => eq_refl
     | false => fun v => v
     end v.
