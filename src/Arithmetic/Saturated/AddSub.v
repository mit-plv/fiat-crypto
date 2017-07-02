Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.Tuple Crypto.Util.LetIn.
Local Notation "A ^ n" := (tuple A n) : type_scope.

Module B.
  Module Positional.
    Section Positional.
      Context {s:Z} {s_pos : 0 < s}. (* s is bitwidth *)
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
      Hint Opaque chain_op chain_op' : uncps.
      Hint Rewrite @chain_op_id @chain_op'_id : uncps.

      Section AddSub.
        Create HintDb divmod discriminated.
        Hint Rewrite
             Z.add_get_carry_full_mod
             Z.add_get_carry_full_div
             Z.add_with_get_carry_full_mod
             Z.add_with_get_carry_full_div
             Z.sub_get_borrow_full_mod
             Z.sub_get_borrow_full_div
             Z.sub_with_get_borrow_full_mod
             Z.sub_with_get_borrow_full_div
          : divmod.
        Let eval {n} := B.Positional.eval (n:=n) (uweight s).

        Definition sat_add_cps {n} p q T (f:Z*Z^n->T) :=
          chain_op_cps (op_get_carry := Z.add_get_carry_full s)
                       (op_with_carry := Z.add_with_get_carry_full s)
                       p q f.
        Definition sat_add {n} p q := @sat_add_cps n p q _ id.

        Lemma sat_add_id n p q T f :
          @sat_add_cps n p q T f = f (sat_add p q).
        Proof. cbv [sat_add sat_add_cps]. rewrite !chain_op_id. reflexivity. Qed.

        Lemma sat_add_mod_step n c d :
          c mod s + s * ((d + c / s) mod (uweight s n))
          = (s * d + c) mod (s * uweight s n).
        Proof.
          assert (0 < uweight s n) as wt_pos
              by auto using Z.lt_gt, Z.gt_lt, uweight_positive.
          rewrite <-(Columns.compact_mod_step s (uweight s n) c d s_pos wt_pos).
          repeat (ring_simplify; f_equal; ring_simplify; try omega).
        Qed.

        Lemma sat_add_div_step n c d :
          (d + c / s) / uweight s n =  (s * d + c) / (s * uweight s n).
        Proof.
          assert (0 < uweight s n) as wt_pos
              by auto using Z.lt_gt, Z.gt_lt, uweight_positive.
          rewrite <-(Columns.compact_div_step s (uweight s n) c d s_pos wt_pos).
          repeat (ring_simplify; f_equal; ring_simplify; try omega).
        Qed.

        Lemma sat_add_divmod n p q :
          eval (snd (@sat_add n p q)) = (eval p + eval q) mod (uweight s n)
          /\ fst (@sat_add n p q) = (eval p + eval q) / (uweight s n).
        Proof.
          cbv [sat_add sat_add_cps chain_op_cps].
          remember None as c.
          replace (eval p + eval q) with
          (eval p + eval q + match c with | None => 0 | Some x => x end)
            by (subst; ring).
          destruct Heqc. revert c.
          induction n; [|destruct c]; intros; simpl chain_op'_cps;
          repeat match goal with
                 | _ => progress cbv [eval Let_In] in *
                 | _ => progress autorewrite with uncps divmod push_id cancel_pair push_basesystem_eval
                 | _ => rewrite uweight_0, ?Z.mod_1_r, ?Z.div_1_r
                 | _ => rewrite uweight_succ
                 | _ => rewrite Z.sub_opp_r 
                 | _ => rewrite sat_add_mod_step 
                 | _ => rewrite sat_add_div_step 
                 | p : Z ^ 0 |- _ => destruct p
                 | _ => rewrite uweight_eval_step, ?hd_append, ?tl_append
                 | |- context[B.Positional.eval _ (snd (chain_op' ?c ?p ?q))]
                   => specialize (IHn p q c); autorewrite with push_id uncps in IHn;
                   rewrite (proj1 IHn); rewrite (proj2 IHn)
                 | _ => split; ring
                 | _ => solve [split; repeat (f_equal; ring_simplify; try omega)]
                 end.
        Qed.

        Lemma sat_add_mod n p q :
          eval (snd (@sat_add n p q)) = (eval p + eval q) mod (uweight s n).
        Proof. exact (proj1 (sat_add_divmod n p q)). Qed.

        Lemma sat_add_div n p q :
          fst (@sat_add n p q) = (eval p + eval q) / (uweight s n).
        Proof. exact (proj2 (sat_add_divmod n p q)). Qed.

        Lemma small_sat_add n p q : small (snd (@sat_add n p q)).
        Proof.
          cbv [small UniformWeight.small sat_add sat_add_cps chain_op_cps].
          remember None as c. destruct Heqc. revert c.
          induction n; intros;
            repeat match goal with
                   | p: Z^0 |- _ => destruct p
                   | _ => progress (cbv [Let_In] in * )
                   | _ => progress (simpl chain_op'_cps in * )
                   | _ => progress autorewrite with uncps push_id cancel_pair in H
                   | H : _ |- _ => rewrite to_list_append in H;
                                     simpl In in H 
                   | H : _ \/ _ |- _ => destruct H 
                   | _ => contradiction
                   end.
            { subst x.
              destruct c; rewrite ?Z.add_with_get_carry_full_mod,
                          ?Z.add_get_carry_full_mod;
              apply Z.mod_pos_bound; omega. }
            {  apply IHn in H. assumption. }
       Qed.

        Definition sat_sub_cps {n} p q T (f:Z*Z^n->T) :=
          chain_op_cps (op_get_carry := Z.sub_get_borrow_full s)
                       (op_with_carry := Z.sub_with_get_borrow_full s)
                       p q f.
        Definition sat_sub {n} p q := @sat_sub_cps n p q _ id.

        Lemma sat_sub_id n p q T f :
          @sat_sub_cps n p q T f = f (sat_sub p q).
        Proof. cbv [sat_sub sat_sub_cps]. rewrite !chain_op_id. reflexivity. Qed.
        Lemma sat_sub_divmod n p q :
          eval (snd (@sat_sub n p q)) = (eval p - eval q) mod (uweight s n)
          /\ fst (@sat_sub n p q) = - ((eval p - eval q) / (uweight s n)).
        Proof.
          cbv [sat_sub sat_sub_cps chain_op_cps].
          remember None as c.
          replace (eval p - eval q) with
          (eval p - eval q - match c with | None => 0 | Some x => x end)
            by (subst; ring).
          destruct Heqc. revert c.
          induction n; [|destruct c]; intros; simpl chain_op'_cps;
          repeat match goal with
                 | _ => progress cbv [eval Let_In] in *
                 | _ => progress autorewrite with uncps divmod push_id cancel_pair push_basesystem_eval
                 | _ => rewrite uweight_0, ?Z.mod_1_r, ?Z.div_1_r
                 | _ => rewrite uweight_succ
                 | _ => rewrite Z.sub_opp_r 
                 | _ => rewrite sat_add_mod_step 
                 | _ => rewrite sat_add_div_step 
                 | p : Z ^ 0 |- _ => destruct p
                 | _ => rewrite uweight_eval_step, ?hd_append, ?tl_append
                 | |- context[B.Positional.eval _ (snd (chain_op' ?c ?p ?q))]
                   => specialize (IHn p q c); autorewrite with push_id uncps in IHn;
                   rewrite (proj1 IHn); rewrite (proj2 IHn)
                 | _ => split; ring
                 | _ => solve [split; repeat (f_equal; ring_simplify; try omega)]
                 end.
        Qed.
        
        Lemma sat_sub_mod n p q :
          eval (snd (@sat_sub n p q)) = (eval p - eval q) mod (uweight s n).
        Proof. exact (proj1 (sat_sub_divmod n p q)). Qed.

        Lemma sat_sub_div n p q :
          fst (@sat_sub n p q) = - ((eval p - eval q) / uweight s n).
        Proof. exact (proj2 (sat_sub_divmod n p q)). Qed.

        Lemma small_sat_sub n p q : small (snd (@sat_sub n p q)).
        Proof.
          cbv [small UniformWeight.small sat_sub sat_sub_cps chain_op_cps].
          remember None as c. destruct Heqc. revert c.
          induction n; intros;
            repeat match goal with
                   | p: Z^0 |- _ => destruct p
                   | _ => progress (cbv [Let_In] in * )
                   | _ => progress (simpl chain_op'_cps in * )
                   | _ => progress autorewrite with uncps push_id cancel_pair in H
                   | H : _ |- _ => rewrite to_list_append in H;
                                     simpl In in H 
                   | H : _ \/ _ |- _ => destruct H 
                   | _ => contradiction
                   end.
          { subst x.
            destruct c; rewrite ?Z.sub_with_get_borrow_full_mod,
                        ?Z.sub_get_borrow_full_mod;
            apply Z.mod_pos_bound; omega. }
          {  apply IHn in H. assumption. }
        Qed.
      End AddSub.
    End Positional.
  End Positional.
End B.
Hint Opaque B.Positional.sat_sub B.Positional.sat_add B.Positional.chain_op B.Positional.chain_op' : uncps.
Hint Rewrite @B.Positional.sat_sub_id @B.Positional.sat_add_id @B.Positional.chain_op_id @B.Positional.chain_op' : uncps.
Hint Rewrite @B.Positional.sat_sub_mod @B.Positional.sat_sub_div @B.Positional.sat_add_mod @B.Positional.sat_add_div using (omega || assumption) : push_basesystem_eval.