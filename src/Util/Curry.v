Definition curry2 {A B C} (f : A -> B -> C) (x : A * B) : C
:= f (fst x) (snd x).
