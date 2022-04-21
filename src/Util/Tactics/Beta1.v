Require Export Crypto.Util.Notations.

Ltac beta1 x :=
  lazymatch x with
  | (fun a => ?f) ?b => constr:(subst_let a := b in f)
  end.
