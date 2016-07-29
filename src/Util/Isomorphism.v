Class IsIso {A B} (f : A -> B) :=
  { iso_inv : B -> A;
    is_right_inv : forall x, f (iso_inv x) = x;
    is_left_inv : forall x, iso_inv (f x) = x }.

Arguments iso_inv {_ _} _ {_} _.
Arguments is_right_inv {_ _} _ {_} _.
Arguments is_left_inv {_ _} _ {_} _.
