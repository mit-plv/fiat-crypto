Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Lists.List.
Local Open Scope Z.

Module Z.
  Definition modexp_nat a p m :=
    fold_right
      (fun a b => (a * b) mod m) 1 (repeat a p).

  Lemma modexp_nat_correct a p m
        (Hm : 1 < m) :
    modexp_nat a p m = (Zpower_nat a p) mod m.
  Proof.
    induction p.
    - rewrite Z.mod_1_l by assumption; reflexivity.
    - simpl; rewrite  <- Zmult_mod_idemp_r, <- IHp; reflexivity. Qed.

  Definition modexp a p m := modexp_nat a (Z.to_nat p) m.

  Lemma modexp_correct a p m
        (Hp : 0 <= p)
        (Hm : 1 < m) :
    modexp a p m = a ^ p mod m.
  Proof.
    unfold modexp; destruct p; simpl; rewrite modexp_nat_correct, ?Zpower_pos_nat by assumption; first [reflexivity|lia]. Qed.
End Z.
