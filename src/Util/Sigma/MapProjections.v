Require Export Crypto.Util.GlobalSettings.

Definition projT2_map {A P Q} (f : forall a, P a -> Q a) (x : @sigT A P) : @sigT A Q
  := let 'existT a p := x in existT Q a (f a p).
Definition proj2_sig_map {A} {P Q : A -> Prop} (f : forall a, P a -> Q a) (x : @sig A P) : @sig A Q
  := let 'exist a p := x in exist Q a (f a p).
