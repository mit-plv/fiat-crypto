Require Import Coq.Lists.List Coq.Lists.SetoidList. Import ListNotations.
Require Import Coq.Numbers.BinNums Coq.NArith.BinNat.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Algebra.Monoid Crypto.Algebra.ScalarMult.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.

Section AddChainExp.
  (* TODO: rewrite this.
     - use CPS and Loop
     - use an inner loop for repeated squaring
     - connect to something that abstracts over F.pow, Z.pow, N.pow NOT scalarmult
  *)

  Function fold_chain {T} (id:T) (op:T->T->T) (is:list (nat*nat)) (acc:list T) {struct is} : T :=
    match is with
    | nil =>
      match acc with
      | nil => id
      | ret::_ => ret
      end
    | (i,j)::is' =>
      let ijx := op (nth_default id acc i) (nth_default id acc j) in
      fold_chain id op is' (ijx::acc)
    end.

  Example wikipedia_addition_chain : fold_chain 0 plus [
  (0, 0); (* 2 = 1 + 1 *) (* the indices say how far back the chain to look *)
  (0, 1); (* 3 = 2 + 1 *)
  (0, 0); (* 6 = 3 + 3 *)
  (0, 0); (* 12 = 6 + 6 *)
  (0, 0); (* 24 = 12 + 12 *)
  (0, 2); (* 30 = 24 + 6 *)
  (0, 6)] (* 31 = 30 + 1 *)
  [1] = 31. reflexivity. Qed.
End AddChainExp.
