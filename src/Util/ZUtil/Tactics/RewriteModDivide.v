Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Divide.
Local Open Scope Z_scope.

Module Z.
  (** [rewrite_mod_divide] is a better version of [rewrite <- Z.mod_div_mod_full
      by rewrite_mod_divide_solver]; it backtracks across occurences
      that the solver fails to solve the side-conditions on. *)
  Ltac rewrite_mod_divide_solver := assumption.
  Ltac rewrite_mod_divide :=
    repeat match goal with
           | [ |- context[(?a mod ?m) mod ?n] ]
             => rewrite <- (@Z.mod_div_mod_full a m n) by rewrite_mod_divide_solver
           end.
  Ltac rewrite_mod_divide_in_hyps :=
    repeat match goal with
           | [ H : context[(?a mod ?m) mod ?n] |- _ ]
             => rewrite <- (@Z.mod_div_mod_full a m n) in H by rewrite_mod_divide_solver
           end.
  Ltac rewrite_mod_divide_in_all := repeat (rewrite_mod_divide || rewrite_mod_divide_in_hyps).
End Z.
