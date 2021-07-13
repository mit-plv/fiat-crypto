Require Export Crypto.Util.FixCoqMistakes.

Ltac append_underscores term count :=
  lazymatch count with
  | O => term
  | S ?n => append_underscores uconstr:(term _) n
  | ?n
    => lazymatch type of n with
       | nat => fail 0 "invalid non-literal count of underscores" n
       | ?T => fail 0 "invalid non-literal-nat count of underscores" n ":" T
       end
  end.
