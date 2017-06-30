Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Tuple Crypto.Util.LetIn.
Local Notation "A ^ n" := (tuple A n) : type_scope.

Module B.
  Module Positional.
    Section Positional.
      Context {s:Z}. (* s is bitwidth *)
      Let small {n} := @small s n.
      Section GenericOp.
        Context {op : Z -> Z -> Z}
                {op_get_carry : Z -> Z -> Z * Z} (* no carry in, carry out *)
                {op_with_carry : Z -> Z -> Z -> Z * Z}. (* carry in, carry out  *)

        Fixpoint chain_op'_cps {n}:
          option Z->Z^n->Z^n->forall T, (Z*Z^n->T)->T :=
          match n with
          | O => fun c p _ _ f =>
                   let carry := match c with | None => 0 | Some x => x end in
                   f (carry,p)
          | S n' =>
            fun c p q _ f =>
              (* for the first call, use op_get_carry, then op_with_carry *)
              let op' := match c with
                         | None => op_get_carry
                         | Some x => op_with_carry x end in
              dlet carry_result := op' (hd p) (hd q) in
                chain_op'_cps (Some (snd carry_result)) (tl p) (tl q) _
                              (fun carry_pq =>
                                 f (fst carry_pq,
                                    append (fst carry_result) (snd carry_pq)))
          end.
        Definition chain_op' {n} c p q := @chain_op'_cps n c p q _ id.
        Definition chain_op_cps {n} p q {T} f := @chain_op'_cps n None p q T f.
        Definition chain_op {n} p q : Z * Z^n := chain_op_cps p q id.

        Lemma chain_op'_id {n} : forall c p q T f,
          @chain_op'_cps n c p q T f = f (chain_op' c p q).
        Proof.
          cbv [chain_op']; induction n; intros; destruct c;
            simpl chain_op'_cps; cbv [Let_In]; try reflexivity.
          { etransitivity; rewrite IHn; reflexivity. }
          { etransitivity; rewrite IHn; reflexivity. }
        Qed.

        Lemma chain_op_id {n} p q T f :
          @chain_op_cps n p q T f = f (chain_op p q).
        Proof. apply chain_op'_id. Qed.
      End GenericOp.

      Section AddSub.
        Let eval {n} := B.Positional.eval (n:=n) (uweight s).

        Definition sat_add_cps {n} p q T (f:Z*Z^n->T) :=
          chain_op_cps (op_get_carry := Z.add_get_carry_full s)
                       (op_with_carry := Z.add_with_get_carry_full s)
                       p q f.
        Definition sat_add {n} p q := @sat_add_cps n p q _ id.

        Lemma sat_add_id n p q T f :
          @sat_add_cps n p q T f = f (sat_add p q).
        Proof. cbv [sat_add sat_add_cps]. rewrite !chain_op_id. reflexivity. Qed.

        Lemma sat_add_mod n p q :
          eval (snd (@sat_add n p q)) = (eval p + eval q) mod (uweight s n).
        Admitted.

        Lemma sat_add_div n p q :
          fst (@sat_add n p q) = (eval p + eval q) / (uweight s n).
        Admitted.

        Lemma small_sat_add n p q : small (snd (@sat_add n p q)).
        Admitted.

        Definition sat_sub_cps {n} p q T (f:Z*Z^n->T) :=
          chain_op_cps (op_get_carry := Z.sub_get_borrow_full s)
                       (op_with_carry := Z.sub_with_get_borrow_full s)
                       p q f.
        Definition sat_sub {n} p q := @sat_sub_cps n p q _ id.

        Lemma sat_sub_id n p q T f :
          @sat_sub_cps n p q T f = f (sat_sub p q).
        Proof. cbv [sat_sub sat_sub_cps]. rewrite !chain_op_id. reflexivity. Qed.

        Lemma sat_sub_mod n p q :
          eval (snd (@sat_sub n p q)) = (eval p - eval q) mod (uweight s n).
        Admitted.

        Lemma sat_sub_div n p q :
          fst (@sat_sub n p q) = - ((eval p - eval q) / uweight s n).
        Admitted.

        Lemma small_sat_sub n p q : small (snd (@sat_sub n p q)).
        Admitted.

      End AddSub.
    End Positional.
  End Positional.
End B.
Hint Opaque B.Positional.sat_sub B.Positional.sat_add B.Positional.chain_op B.Positional.chain_op' : uncps.
Hint Rewrite @B.Positional.sat_sub_id @B.Positional.sat_add_id @B.Positional.chain_op_id @B.Positional.chain_op' : uncps.
Hint Rewrite @B.Positional.sat_sub_mod @B.Positional.sat_sub_div @B.Positional.sat_add_mod @B.Positional.sat_add_div using (omega || assumption) : push_basesystem_eval.