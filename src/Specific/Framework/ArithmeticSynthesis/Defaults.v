Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Module Export Exports.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Local Ltac solve_constant_local_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => (exists (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v)));
       lazymatch goal with
       | [ sz_nonzero : sz <> 0%nat, base_pos : (1 <= _)%Q |- _ ]
         => clear -base_pos sz_nonzero
       end
  end;
  abstract (
      setoid_rewrite Positional.Fdecode_Fencode_id;
      [ reflexivity
      | auto using wt_gen0_1, wt_gen_nonzero, wt_gen_divides', div_mod.. ]
    ).

Section gen.
  Context (m : positive)
          (base : Q)
          (sz : nat)
          (s : Z)
          (c : list limb)
          (carry_chains : list (list nat))
          (coef : Z^sz)
          (mul_code : option (Z^sz -> Z^sz -> Z^sz))
          (square_code : option (Z^sz -> Z^sz))
          (sz_nonzero : sz <> 0%nat)
          (s_nonzero : s <> 0)
          (base_pos : (1 <= base)%Q)
          (sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m)).

  Local Notation wt := (wt_gen base).
  Local Notation sz2 := (sz2' sz).
  Local Notation wt_divides' := (wt_gen_divides' base base_pos).
  Local Notation wt_nonzero := (wt_gen_nonzero base base_pos).

  (* side condition needs cbv [Positional.mul_cps Positional.reduce_cps]. *)
  Context (mul_code_correct
           : match mul_code with
             | None => True
             | Some v
               => forall a b,
                 v a b
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end)
          (square_code_correct
           : match square_code with
             | None => True
             | Some v
               => forall a,
                 v a
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end).

  Context (coef_mod : mod_eq m (Positional.eval wt coef) 0)
          (m_correct : Z.pos m = s - Associational.eval c).


  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig'
    : { carry : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (carry a) = eval a }.
  Proof.
    let a := fresh "a" in
    eexists; cbv beta zeta; intros a.
    pose proof (wt_gen0_1 base).
    pose proof wt_nonzero; pose proof div_mod.
    pose proof (wt_gen_divides_chains base base_pos carry_chains).
    pose proof wt_divides'.
    let x := constr:(chained_carries' sz wt s c a carry_chains) in
    presolve_op_F constr:(wt) x;
      [ cbv [chained_carries_cps' chained_carries_cps'_step];
        autorewrite with pattern_runtime;
        reflexivity
      | ].
    { cbv [chained_carries'].
      change a with (id a) at 2.
      revert a; induction carry_chains as [|carry_chain carry_chains' IHcarry_chains];
        [ reflexivity | destruct_head_hnf' and ]; intros.
      rewrite step_chained_carries_cps'.
      destruct (length carry_chains') eqn:Hlenc.
      { destruct carry_chains'; [ | simpl in Hlenc; congruence ].
        destruct_head'_and;
          autorewrite with uncps push_id push_basesystem_eval;
          reflexivity. }
      { repeat autounfold;
          autorewrite with uncps push_id push_basesystem_eval.
        unfold chained_carries'.
        rewrite IHcarry_chains by auto.
        repeat autounfold; autorewrite with uncps push_id push_basesystem_eval.
        rewrite Positional.eval_carry by auto.
        rewrite Positional.eval_chained_carries by auto; reflexivity. } }
  Defined.

  Definition constant_sig' v
    : { c : Z^sz | Positional.Fdecode (m:=m) wt c = v}.
  Proof. solve_constant_local_sig. Defined.

  Definition zero_sig'
    : { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    := Eval hnf in constant_sig' _.

  Definition one_sig'
    : { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    := Eval hnf in constant_sig' _.

  Definition add_sig'
    : { add : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m:=m) wt in
          eval (add a b) = (eval a + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.add_cps (n := sz) wt a b id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition sub_sig'
    : { sub : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m:=m) wt in
          eval (sub a b) = (eval a - eval b)%F }.
  Proof.
    let a := fresh "a" in
    let b := fresh "b" in
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition opp_sig'
    : { opp : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (opp a) = F.opp (eval a) }.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (mul a b) = (eval a * eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    pose proof (sz2'_nonzero sz sz_nonzero).
    let x := constr:(
               Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                  (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    presolve_op_F constr:(wt) x; [ | reflexivity ].
    let rhs := match goal with |- _ = ?rhs => rhs end in
    transitivity (match mul_code with
                  | None => rhs
                  | Some v => v a b
                  end);
      [ reflexivity | ].
    destruct mul_code; try reflexivity.
    transitivity (Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                     (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)); [ | reflexivity ].
    auto.
  Defined.

  Definition square_sig'
    : { square : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (square a) = (eval a * eval a)%F }.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    pose proof (sz2'_nonzero sz sz_nonzero).
    let x := constr:(
               Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                  (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    presolve_op_F constr:(wt) x; [ | reflexivity ].
    let rhs := match goal with |- _ = ?rhs => rhs end in
    transitivity (match square_code with
                  | None => rhs
                  | Some v => v a
                  end);
      [ reflexivity | ].
    destruct square_code; try reflexivity.
    transitivity (Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                     (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)); [ | reflexivity ].
    auto.
  Defined.

  Let ring_pkg : { T : _ & T }.
  Proof.
    eexists.
    refine (fun zero_sig one_sig add_sig sub_sig mul_sig opp_sig
            => Ring.ring_by_isomorphism
                 (F := F m)
                 (H := Z^sz)
                 (phi := Positional.Fencode wt)
                 (phi' := Positional.Fdecode wt)
                 (zero := proj1_sig zero_sig)
                 (one := proj1_sig one_sig)
                 (opp := proj1_sig opp_sig)
                 (add := proj1_sig add_sig)
                 (sub := proj1_sig sub_sig)
                 (mul := proj1_sig mul_sig)
                 (phi'_zero := _)
                 (phi'_one := _)
                 (phi'_opp := _)
                 (Positional.Fdecode_Fencode_id
                    (sz_nonzero := sz_nonzero)
                    (div_mod := div_mod)
                    wt (wt_gen0_1 base) wt_nonzero wt_divides')
                 (Positional.eq_Feq_iff wt)
                 _ _ _);
      lazymatch goal with
      | [ |- context[@proj1_sig ?A ?P ?x] ]
        => pattern (@proj1_sig A P x);
             exact (@proj2_sig A P x)
      end.
  Defined.

  Definition ring' zero_sig one_sig add_sig sub_sig mul_sig opp_sig
    := Eval cbv [ring_pkg projT2] in
        projT2 ring_pkg zero_sig one_sig add_sig sub_sig mul_sig opp_sig.
End gen.

Ltac internal_solve_code_correct P_tac :=
  hnf;
  lazymatch goal with
  | [ |- True ] => constructor
  | _
    => cbv [Positional.mul_cps Positional.reduce_cps];
       intros;
       autorewrite with pattern_runtime;
       repeat autounfold;
       autorewrite with pattern_runtime;
       basesystem_partial_evaluation_RHS;
       P_tac ();
       break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring
  end.

Ltac pose_mul_code_correct P_extra_prove_mul_eq sz sz2 wt s c mul_code mul_code_correct :=
  cache_proof_with_type_by
    (match mul_code with
     | None => True
     | Some v
       => forall a b,
         v a b
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_mul_eq)
           mul_code_correct.

Ltac pose_square_code_correct P_extra_prove_square_eq sz sz2 wt s c square_code square_code_correct :=
  cache_proof_with_type_by
    (match square_code with
     | None => True
     | Some v
       => forall a,
         v a
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_square_eq)
           square_code_correct.

Ltac cache_sig_with_type_by_existing_sig ty existing_sig id :=
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [carry_sig' constant_sig' zero_sig' one_sig' add_sig' sub_sig' mul_sig' square_sig' opp_sig'])
           ty existing_sig id.

Ltac pose_carry_sig wt m base sz s c carry_chains carry_sig :=
  cache_sig_with_type_by_existing_sig
    {carry : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (carry a) = eval a}
    (carry_sig' m base sz s c carry_chains)
    carry_sig.

Ltac pose_zero_sig wt m base sz sz_nonzero base_pos zero_sig :=
  cache_vm_sig_with_type
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    (zero_sig' m base sz sz_nonzero base_pos)
    zero_sig.

Ltac pose_one_sig wt m base sz sz_nonzero base_pos one_sig :=
  cache_vm_sig_with_type
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    (one_sig' m base sz sz_nonzero base_pos)
    one_sig.

Ltac pose_add_sig wt m base sz add_sig :=
  cache_sig_with_type_by_existing_sig
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
      forall a b : Z^sz,
        let eval := Positional.Fdecode (m:=m) wt in
        eval (add a b) = (eval a + eval b)%F }
    (add_sig' m base sz)
    add_sig.

Ltac pose_sub_sig wt m base sz coef sub_sig :=
  cache_sig_with_type_by_existing_sig
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m:=m) wt in
       eval (sub a b) = (eval a - eval b)%F}
    (sub_sig' m base sz coef)
    sub_sig.

Ltac pose_opp_sig wt m base sz coef opp_sig :=
  cache_sig_with_type_by_existing_sig
    {opp : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (opp a) = F.opp (eval a)}
    (opp_sig' m base sz coef)
    opp_sig.

Ltac pose_mul_sig wt m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct mul_sig :=
  cache_sig_with_type_by_existing_sig
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (mul a b) = (eval a * eval b)%F}
    (mul_sig' m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct)
    mul_sig.

Ltac pose_square_sig wt m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct square_sig :=
  cache_sig_with_type_by_existing_sig
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (square a) = (eval a * eval a)%F}
    (square_sig' m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct)
    square_sig.

Ltac pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring :=
  cache_term
    (Ring.ring_by_isomorphism
       (F := F m)
       (H := Z^sz)
       (phi := Positional.Fencode wt)
       (phi' := Positional.Fdecode wt)
       (zero := proj1_sig zero_sig)
       (one := proj1_sig one_sig)
       (opp := proj1_sig opp_sig)
       (add := proj1_sig add_sig)
       (sub := proj1_sig sub_sig)
       (mul := proj1_sig mul_sig)
       (phi'_zero := proj2_sig zero_sig)
       (phi'_one := proj2_sig one_sig)
       (phi'_opp := proj2_sig opp_sig)
       (Positional.Fdecode_Fencode_id
          (sz_nonzero := sz_nonzero)
          (div_mod := div_mod)
          wt eq_refl wt_nonzero wt_divides')
       (Positional.eq_Feq_iff wt)
       (proj2_sig add_sig)
       (proj2_sig sub_sig)
       (proj2_sig mul_sig)
    )
    ring.

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
 *)
