Definition curry2 {A B C} (f : A -> B -> C) (x : A * B) : C
:= let '(a, b) := x in f a b.
