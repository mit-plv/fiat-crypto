Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Lists.List.
Local Open Scope Z.

Local Open Scope Z_scope.
Module Z.
  Definition modexp_pos a p m := Pos.iter (fun z => (a * z) mod m) (1 mod m) p.
  Definition modexp a p m
    := match p with
       | 0 => 1 mod m
       | Z.neg _ => 0
       | Z.pos p => modexp_pos a p m
       end.
  Lemma modexp_pos_correct a p m
    : modexp_pos a p m = Z.pow_pos a p mod m.
  Proof.
    cbv [Z.pow_pos modexp_pos].
    erewrite Pos.iter_swap_gen with (f := fun a => a mod m).
    { reflexivity. }
    { cbv beta; intros; now rewrite Zmult_mod_idemp_r. }
  Qed.
  Lemma modexp_correct a p m
    : modexp a p m = a ^ p mod m.
  Proof.
    cbv [modexp Z.pow]; destruct p;
      now rewrite ?modexp_pos_correct, ?Zmod_0_l.
  Qed.
End Z.
