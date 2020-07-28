Fixpoint fueled_lub {A}
         (Aeq : A -> A -> bool)
         (join : A -> A -> A)
         (fuel : nat)
         (f : A -> A) (x : A)
: bool (* fixpoint reached *) * A
:= match fuel with
   | 0 => (false, x)
   | S n
     => let fx := join x (f x) in
        if Aeq x fx
        then (true, fx)
        else @fueled_lub A Aeq join n f fx
   end.
