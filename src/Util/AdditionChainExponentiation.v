Require Import Coq.Lists.List Coq.Lists.SetoidList. Import ListNotations.
Require Import Coq.Numbers.BinNums Coq.NArith.BinNat.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Algebra Crypto.Algebra.Monoid Crypto.Algebra.ScalarMult.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Option.

Section AddChainExp.
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

  Context {G eq op id} {monoid:@Algebra.monoid G eq op id}.
  Context {scalarmult} {is_scalarmult:@ScalarMult.is_scalarmult G eq op id scalarmult}.
  Local Infix "=" := eq : type_scope.
  Local Open Scope N_scope.
  Local Notation "n * P" := (scalarmult (N.to_nat n) P) (only parsing).

  Lemma fold_chain_exp' : forall (x:G) is acc ref
      (H:forall i, nth_default id acc i = (nth_default 0 ref i) * x)
      (Hl:Logic.eq (length acc) (length ref)),
      fold_chain id op is acc = (fold_chain 0 N.add is ref) * x.
  Proof.
    induction is; intros; simpl @fold_chain.
    { repeat break_match; specialize (H 0%nat); rewrite ?nth_default_cons, ?nth_default_cons_S in H;
      solve [ simpl length in *; discriminate | apply H | rewrite scalarmult_0_l; reflexivity ]. }
    { repeat break_match. eapply IHis; intros; [|auto with distr_length]; [].
      match goal with
          [H:context [nth_default _ ?l _] |- context[nth_default _ (?h::?l) ?i] ]
          => destruct i; rewrite ?nth_default_cons, ?nth_default_cons_S;
             solve [ apply H | rewrite !H, <-scalarmult_add_l, Nnat.N2Nat.inj_add; reflexivity ]
        end. }
  Qed.

  Lemma fold_chain_exp x is: fold_chain id op is [x] = (fold_chain 0 N.add is [1]) * x.
  Proof.
    eapply fold_chain_exp'; intros; trivial.
    destruct i; try destruct i; rewrite ?nth_default_cons_S, ?nth_default_cons, ?nth_default_nil;
      rewrite ?scalarmult_1_l, ?scalarmult_0_l; reflexivity.
  Qed.
End AddChainExp.
