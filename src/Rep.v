Class RepConversions (T:Type) (RT:Type) : Type :=
  {
    toRep : T -> RT;
    unRep : RT -> T
  }.

Definition RepConversionsOK {T RT} (RC:RepConversions T RT) := forall x, unRep (toRep x) = x.

Definition RepFunOK {T RT} `(RC:RepConversions T RT) (f:T->T) (rf : RT -> RT) :=
  forall x, f (unRep x) = unRep (rf x).

Definition RepBinOpOK {T RT} `(RC:RepConversions T RT) (op:T->T->T) (rop : RT -> RT -> RT) :=
  forall x y, op (unRep x) (unRep y) = unRep (rop x y).
