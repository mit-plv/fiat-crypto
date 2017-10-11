Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Ltac pose_square_sig sz m wt mul_sig square_sig :=
  cache_term_with_type_by
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       Positional.Fdecode (m := m) wt (square a) = (eval a * eval a)%F}
    ltac:(idtac;
          let a := fresh "a" in
          eexists; cbv beta zeta; intros a;
          rewrite <-(proj2_sig mul_sig);
          apply f_equal;
          cbv [proj1_sig mul_sig];
          reflexivity)
           square_sig.
