Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.Tactics.VM.
Require Import Crypto.Util.QUtil.

Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Hint Opaque freeze : uncps.
Hint Rewrite freeze_id : uncps.

Module Export Exports.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Module MakeArithmeticSynthesisTestTactics (Curve : CurveParameters.CurveParameters).
  Module P := CurveParameters.FillCurveParameters Curve.

  Local Infix "^" := tuple : type_scope.

  (* emacs for adjusting definitions *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_ \.]*\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      (\2)^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.): *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\3^J  let v := P.do_compute \2 in cache_term v \1.):  *)

  (* These definitions will need to be passed as Ltac arguments (or
  cleverly inferred) when things are eventually automated *)
  Ltac pose_sz sz :=
    cache_term_with_type_by
      nat
      ltac:(let v := P.do_compute P.sz in exact v)
             sz.
  Ltac pose_bitwidth bitwidth :=
    cache_term_with_type_by
      Z
      ltac:(let v := P.do_compute P.bitwidth in exact v)
             bitwidth.
  Ltac pose_s s := (* don't want to compute, e.g., [2^255] *)
    cache_term_with_type_by
      Z
      ltac:(let v := P.do_unfold P.s in exact v)
             s.
  Ltac pose_c c :=
    cache_term_with_type_by
      (list B.limb)
      ltac:(let v := P.do_compute P.c in exact v)
             c.
  Ltac pose_carry_chains carry_chains :=
    let v := P.do_compute P.carry_chains in
    cache_term v carry_chains.

  Ltac pose_a24 a24 :=
    let v := P.do_compute P.a24 in
    cache_term v a24.
  Ltac pose_coef_div_modulus coef_div_modulus :=
    cache_term_with_type_by
      nat
      ltac:(let v := P.do_compute P.coef_div_modulus in exact v)
             coef_div_modulus.
  Ltac pose_goldilocks goldilocks :=
    cache_term_with_type_by
      bool
      ltac:(let v := P.do_compute P.goldilocks in exact v)
             goldilocks.
  (* These definitions are inferred from those above *)
  Ltac pose_m s c m := (* modulus *)
    let v := (eval vm_compute in (Z.to_pos (s - Associational.eval c))) in
    cache_term v m.
  Section wt.
    Import QArith Qround.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Definition wt_gen (m : positive) (sz : nat) (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
  End wt.
  Ltac pose_wt m sz wt :=
    let v := (eval cbv [wt_gen] in (wt_gen m sz)) in
    cache_term v wt.
  Ltac pose_sz2 sz sz2 :=
    let v := (eval vm_compute in ((sz * 2) - 1)%nat) in
    cache_term v sz2.
  Ltac pose_m_enc sz s c wt m_enc :=
    let v := (eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c))) in
    cache_term v m_enc.
  Ltac pose_coef sz wt m_enc coef_div_modulus coef := (* subtraction coefficient *)
    let v := (eval vm_compute in
                 ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
                     match ctr with
                     | O => acc
                     | S n => addm (Positional.add_cps wt acc m_enc id) n
                     end) (Positional.zeros sz) coef_div_modulus)) in
    cache_term v coef.

  Ltac pose_coef_mod sz wt m coef coef_mod :=
    cache_term_with_type_by
      (mod_eq m (Positional.eval (n:=sz) wt coef) 0)
      ltac:(exact eq_refl)
             coef_mod.
  Ltac pose_sz_nonzero sz sz_nonzero :=
    cache_proof_with_type_by
      (sz <> 0%nat)
      ltac:(vm_decide_no_check)
             sz_nonzero.
  Ltac pose_wt_nonzero wt wt_nonzero :=
    cache_proof_with_type_by
      (forall i, wt i <> 0)
      ltac:(eapply pow_ceil_mul_nat_nonzero; vm_decide_no_check)
             wt_nonzero.
  Ltac pose_wt_nonneg wt wt_nonneg :=
    cache_proof_with_type_by
      (forall i, 0 <= wt i)
      ltac:(apply pow_ceil_mul_nat_nonneg; vm_decide_no_check)
             wt_nonneg.
  Ltac pose_wt_divides wt wt_divides :=
    cache_proof_with_type_by
      (forall i, wt (S i) / wt i > 0)
      ltac:(apply pow_ceil_mul_nat_divide; vm_decide_no_check)
             wt_divides.
  Ltac pose_wt_divides' wt wt_divides wt_divides' :=
    cache_proof_with_type_by
      (forall i, wt (S i) / wt i <> 0)
      ltac:(symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides)
             wt_divides'.
  Ltac helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chain :=
    cache_term_with_type_by
      (forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
      ltac:(let i := fresh "i" in intros i ?; exact (wt_divides' i))
             wt_divides_chain.
  Ltac pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains :=
    lazymatch carry_chains with
    | ?carry_chain :: nil
      => helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chains
    | ?carry_chain :: ?carry_chains
      => let wt_divides_chains := fresh wt_divides_chains in
         let wt_divides_chain := fresh wt_divides_chains in
         let wt_divides_chain := helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chain in
         let wt_divides_chains := pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains in
         constr:((wt_divides_chain, wt_divides_chains))
    end.
  Ltac pose_wt_divides_chains wt carry_chains wt_divides' wt_divides_chains :=
    let carry_chains := (eval cbv delta [carry_chains] in carry_chains) in
    pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains.

  Local Ltac solve_constant_sig :=
    idtac;
    lazymatch goal with
    | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
      => let t := (eval vm_compute in
                      (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
         (exists t; vm_decide)
    end.

  Ltac pose_zero_sig sz m wt zero_sig :=
    cache_term_with_type_by
      { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
      solve_constant_sig
      zero_sig.

  Ltac pose_one_sig sz m wt one_sig :=
    cache_term_with_type_by
      { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
      solve_constant_sig
      one_sig.

  Ltac pose_a24_sig sz m wt a24 a24_sig :=
    cache_term_with_type_by
      { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m P.a24 }
      solve_constant_sig
      a24_sig.

  Ltac pose_add_sig sz m wt wt_nonzero add_sig :=
    cache_term_with_type_by
      { add : (Z^sz -> Z^sz -> Z^sz)%type |
        forall a b : Z^sz,
          let eval := Positional.Fdecode (m:=m) wt in
          eval (add a b) = (eval a + eval b)%F }
      ltac:(idtac;
            let a := fresh "a" in
            let b := fresh "b" in
            eexists; cbv beta zeta; intros a b;
            pose proof wt_nonzero;
            let x := constr:(
                       Positional.add_cps (n := sz) wt a b id) in
            solve_op_F wt x; reflexivity)
             add_sig.

  Ltac pose_sub_sig sz m wt wt_nonzero coef sub_sig :=
    cache_term_with_type_by
      {sub : (Z^sz -> Z^sz -> Z^sz)%type |
       forall a b : Z^sz,
         let eval := Positional.Fdecode (m:=m) wt in
         eval (sub a b) = (eval a - eval b)%F}
      ltac:(idtac;
            let a := fresh "a" in
            let b := fresh "b" in
            eexists; cbv beta zeta; intros a b;
            pose proof wt_nonzero;
            let x := constr:(
                       Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
            solve_op_F wt x; reflexivity)
             sub_sig.

  Ltac pose_opp_sig sz m wt wt_nonzero coef opp_sig :=
    cache_term_with_type_by
      {opp : (Z^sz -> Z^sz)%type |
       forall a : Z^sz,
         let eval := Positional.Fdecode (m := m) wt in
         eval (opp a) = F.opp (eval a)}
      ltac:(idtac;
            let a := fresh in
            eexists; cbv beta zeta; intros a;
            pose proof wt_nonzero;
            let x := constr:(
                       Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
            solve_op_F wt x; reflexivity)
             opp_sig.

  Ltac pose_half_sz sz half_sz :=
    let v := (eval compute in (sz / 2)%nat) in
    cache_term v half_sz.
  Ltac pose_half_sz_nonzero half_sz half_sz_nonzero :=
    cache_proof_with_type_by
      (half_sz <> 0%nat)
      ltac:(cbv; congruence)
             half_sz_nonzero.

  Ltac basesystem_partial_evaluation_RHS :=
    let t0 := (match goal with
               | |- _ _ ?t => t
               end) in
    let t :=
     eval
      cbv
       delta [Positional.to_associational_cps Positional.to_associational
             Positional.eval Positional.zeros Positional.add_to_nth_cps
             Positional.add_to_nth Positional.place_cps Positional.place
             Positional.from_associational_cps Positional.from_associational
             Positional.carry_cps Positional.carry
             Positional.chained_carries_cps Positional.chained_carries
             Positional.sub_cps Positional.sub Positional.split_cps
             Positional.scmul_cps Positional.unbalanced_sub_cps
             Positional.negate_snd_cps Positional.add_cps Positional.opp_cps
             Associational.eval Associational.multerm Associational.mul_cps
             Associational.mul Associational.split_cps Associational.split
             Associational.reduce_cps Associational.reduce
             Associational.carryterm_cps Associational.carryterm
             Associational.carry_cps Associational.carry
             Associational.negate_snd_cps Associational.negate_snd div modulo
             id_tuple_with_alt id_tuple'_with_alt
             ]
     in t0
    in
    let t := eval pattern @runtime_mul in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @runtime_add in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @runtime_opp in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @runtime_shr in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @runtime_and in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @Let_In in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t := eval pattern @id_with_alt in t in
    let t := (match t with
              | ?t _ => t
              end) in
    let t1 := fresh "t1" in
    pose (t1 := t);
     transitivity
      (t1 (@id_with_alt) (@Let_In) (@runtime_and) (@runtime_shr) (@runtime_opp) (@runtime_add)
         (@runtime_mul));
     [ replace_with_vm_compute t1; clear t1 | reflexivity ].

  (** XXX TODO(jadep) FIXME: Is sqrt(s) the right thing to pass to goldilocks_mul_cps (the original code hard-coded 2^224 *)
  Ltac pose_sqrt_s s sqrt_s :=
    let v := (eval vm_compute in (Z.log2 s / 2)) in
    cache_term (2^v) sqrt_s.

  Ltac pose_goldilocks_mul_sig goldilocks sz wt s c half_sz sqrt_s goldilocks_mul_sig :=
    lazymatch eval compute in goldilocks with
    | true
      => cache_term_with_type_by
           {mul : (Z^sz -> Z^sz -> Z^sz)%type |
            forall a b : Z^sz,
              mul a b = goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id)}
           ltac:(eexists; cbv beta zeta; intros;
                 cbv [goldilocks_mul_cps];
                 repeat autounfold;
                 basesystem_partial_evaluation_RHS;
                 do_replace_match_with_destructuring_match_in_goal;
                 reflexivity)
                  goldilocks_mul_sig
    | false
      => goldilocks_mul_sig
    end.

  Ltac pose_mul_sig sz m wt s c sz2 wt_nonzero mul_sig :=
    cache_term_with_type_by
      {mul : (Z^sz -> Z^sz -> Z^sz)%type |
       forall a b : Z^sz,
         let eval := Positional.Fdecode (m := m) wt in
         eval (mul a b) = (eval a * eval b)%F}
      ltac:(idtac;
            let a := fresh "a" in
            let b := fresh "b" in
            eexists; cbv beta zeta; intros a b;
            pose proof wt_nonzero;
            let x := constr:(
                       Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                          (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
            solve_op_F wt x;
            P.default_mul;
            P.extra_prove_mul_eq;
            break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring)
             mul_sig.

  Ltac pose_mul_sig_from_goldilocks_mul_sig sz m wt s c half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig :=
    cache_term_with_type_by
      {mul : (Z^sz -> Z^sz -> Z^sz)%type |
       forall a b : Z^sz,
         let eval := Positional.Fdecode (m := m) wt in
         Positional.Fdecode (m := m) wt (mul a b) = (eval a * eval b)%F}
      ltac:(idtac;
            let a := fresh "a" in
            let b := fresh "b" in
            eexists; cbv beta zeta; intros a b;
            pose proof wt_nonzero;
            let x := constr:(
                       goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id)) in
            F_mod_eq;
            transitivity (Positional.eval wt x); repeat autounfold;

            [
            | autorewrite with uncps push_id push_basesystem_eval;
              apply goldilocks_mul_correct; try assumption; cbv; congruence ];
            cbv [mod_eq]; apply f_equal2;
            [ | reflexivity ];
            apply f_equal;
            etransitivity; [|apply (proj2_sig goldilocks_mul_sig)];
            cbv [proj1_sig goldilocks_mul_sig];
            reflexivity)
             mul_sig.

  Ltac pose_mul_sig_full goldilocks sz m wt s c sz2 half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig :=
    lazymatch eval compute in goldilocks with
    | true
      => pose_mul_sig_from_goldilocks_mul_sig sz m wt s c half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig
    | false
      => pose_mul_sig sz m wt s c sz2 wt_nonzero mul_sig
    end.

  Ltac pose_square_sig sz m wt s c sz2 wt_nonzero square_sig :=
    cache_term_with_type_by
      {square : (Z^sz -> Z^sz)%type |
       forall a : Z^sz,
         let eval := Positional.Fdecode (m := m) wt in
         eval (square a) = (eval a * eval a)%F}
      ltac:(idtac;
            let a := fresh "a" in
            eexists; cbv beta zeta; intros a;
            pose proof wt_nonzero;
            let x := constr:(
                       Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                          (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
            solve_op_F wt x;
            P.default_square;
            P.extra_prove_square_eq;
            break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring)
             square_sig.

  Ltac pose_square_sig_from_mul_sig sz m wt mul_sig square_sig :=
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

  Ltac pose_square_sig_full goldilocks sz m wt s c sz2 wt_nonzero mul_sig square_sig :=
    lazymatch eval compute in goldilocks with
    | true
      => pose_square_sig_from_mul_sig sz m wt mul_sig square_sig
    | false
      => pose_square_sig sz m wt s c sz2 wt_nonzero square_sig
    end.

  Ltac pose_proof_tuple ls :=
    lazymatch ls with
    | pair ?x ?y => pose_proof_tuple x; pose_proof_tuple y
    | ?ls => pose proof ls
    end.

  Ltac make_chained_carries_cps' sz wt s c a carry_chains :=
    lazymatch carry_chains with
    | ?carry_chain :: nil
      => constr:(Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain id)
    | ?carry_chain :: ?carry_chains
      => let r := fresh "r" in
         let r' := fresh r in
         constr:(Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain
                (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                (fun r' => ltac:(let v := make_chained_carries_cps' sz wt s c r' carry_chains in exact v))))
    end.
  Ltac make_chained_carries_cps sz wt s c a carry_chains :=
    let carry_chains := (eval cbv delta [carry_chains] in carry_chains) in
    make_chained_carries_cps' sz wt s c a carry_chains.
  (* Performs a full carry loop (as specified by carry_chain) *)
  Ltac pose_carry_sig sz m wt s c carry_chains wt_nonzero wt_divides_chains carry_sig :=
    cache_term_with_type_by
      {carry : (Z^sz -> Z^sz)%type |
       forall a : Z^sz,
         let eval := Positional.Fdecode (m := m) wt in
         eval (carry a) = eval a}
      ltac:(idtac;
            let a := fresh "a" in
            eexists; cbv beta zeta; intros a;
            pose proof wt_nonzero; pose proof div_mod;
            pose_proof_tuple wt_divides_chains;
            let x := make_chained_carries_cps sz wt s c a carry_chains in
            solve_op_F wt x; reflexivity)
             carry_sig.

  Ltac pose_wt_pos wt wt_pos :=
    cache_proof_with_type_by
      (forall i, wt i > 0)
      ltac:(eapply pow_ceil_mul_nat_pos; vm_decide_no_check)
             wt_pos.

  Ltac pose_wt_multiples wt wt_multiples :=
    cache_proof_with_type_by
      (forall i, wt (S i) mod (wt i) = 0)
      ltac:(apply pow_ceil_mul_nat_multiples; vm_decide_no_check)
             wt_multiples.


  (* kludge to get around name clashes in the following, and the fact
     that the python script cares about argument names *)
  Local Ltac rewrite_eval_freeze_with_c c' :=
    rewrite eval_freeze with (c:=c').

  Ltac pose_freeze_sig sz m wt c m_enc bitwidth wt_nonzero wt_pos wt_divides wt_multiples freeze_sig :=
    cache_term_with_type_by
      {freeze : (Z^sz -> Z^sz)%type |
       forall a : Z^sz,
         (0 <= Positional.eval wt a < 2 * Z.pos m)->
         let eval := Positional.Fdecode (m := m) wt in
         eval (freeze a) = eval a}
      ltac:(let a := fresh "a" in
            eexists; cbv beta zeta; (intros a ?);
            pose proof wt_nonzero; pose proof wt_pos;
            pose proof div_mod; pose proof wt_divides;
            pose proof wt_multiples;
            pose proof div_correct; pose proof modulo_correct;
            let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
            F_mod_eq;
            transitivity (Positional.eval wt x); repeat autounfold;
            [ | autorewrite with uncps push_id push_basesystem_eval;
                rewrite_eval_freeze_with_c c;
                try eassumption; try omega; try reflexivity;
                try solve [auto using B.Positional.select_id,
                           B.Positional.eval_select(*, zselect_correct*)];
                vm_decide];
            cbv[mod_eq]; apply f_equal2;
            [  | reflexivity ]; apply f_equal;
            cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect];
            reflexivity)
             freeze_sig.

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

  (**
<<
#!/usr/bin/env python
from __future__ import with_statement
import re

with open('ArithmeticSynthesisFramework.v', 'r') as f:
    lines = f.readlines()

header = 'Ltac pose_'

fns = [(name, args.strip())
       for line in lines
       if line.strip()[:len(header)] == header
       for name, args in re.findall('Ltac pose_([^ ]*' + ') ([A-Za-z0-9_\' ]*' + ')', line.strip())]

print(r'''  Ltac get_ArithmeticSynthesis_package _ :=
    %s'''
    % '\n    '.join('let %s := fresh "%s" in' % (name, name) for name, args in fns))
print('    ' + '\n    '.join('let %s := pose_%s %s in' % (name, name, args) for name, args in fns))
print('    constr:((%s)).' % ', '.join(name for name, args in fns))
print(r'''
  Ltac make_ArithmeticSynthesis_package _ :=
    lazymatch goal with
    | [ |- { T : _ & T } ] => eexists
    | [ |- _ ] => idtac
    end;
    let pkg := get_ArithmeticSynthesis_package () in
    exact pkg.
End MakeArithmeticSynthesisTestTactics.

Module Type ArithmeticSynthesisPrePackage.
  Parameter ArithmeticSynthesis_package' : { T : _ & T }.
  Parameter ArithmeticSynthesis_package : projT1 ArithmeticSynthesis_package'.
End ArithmeticSynthesisPrePackage.

Module MakeArithmeticSynthesisTest (AP : ArithmeticSynthesisPrePackage).
  Ltac get_MakeArithmeticSynthesisTest_package _ := eval hnf in AP.ArithmeticSynthesis_package.
  Ltac AS_reduce_proj x :=
    eval cbv beta iota zeta in x.
''')
terms = ', '.join(name for name, args in fns)
for name, args in fns:
    print("  Ltac get_%s _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(%s) := pkg in %s)." % (name, terms, name))
    print("  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (name, name))
print('End MakeArithmeticSynthesisTest.')
>> **)
  Ltac get_ArithmeticSynthesis_package _ :=
    let sz := fresh "sz" in
    let bitwidth := fresh "bitwidth" in
    let s := fresh "s" in
    let c := fresh "c" in
    let carry_chains := fresh "carry_chains" in
    let a24 := fresh "a24" in
    let coef_div_modulus := fresh "coef_div_modulus" in
    let goldilocks := fresh "goldilocks" in
    let m := fresh "m" in
    let wt := fresh "wt" in
    let sz2 := fresh "sz2" in
    let m_enc := fresh "m_enc" in
    let coef := fresh "coef" in
    let coef_mod := fresh "coef_mod" in
    let sz_nonzero := fresh "sz_nonzero" in
    let wt_nonzero := fresh "wt_nonzero" in
    let wt_nonneg := fresh "wt_nonneg" in
    let wt_divides := fresh "wt_divides" in
    let wt_divides' := fresh "wt_divides'" in
    let wt_divides_chains := fresh "wt_divides_chains" in
    let zero_sig := fresh "zero_sig" in
    let one_sig := fresh "one_sig" in
    let a24_sig := fresh "a24_sig" in
    let add_sig := fresh "add_sig" in
    let sub_sig := fresh "sub_sig" in
    let opp_sig := fresh "opp_sig" in
    let half_sz := fresh "half_sz" in
    let half_sz_nonzero := fresh "half_sz_nonzero" in
    let sqrt_s := fresh "sqrt_s" in
    let goldilocks_mul_sig := fresh "goldilocks_mul_sig" in
    let mul_sig := fresh "mul_sig" in
    let square_sig := fresh "square_sig" in
    let carry_sig := fresh "carry_sig" in
    let wt_pos := fresh "wt_pos" in
    let wt_multiples := fresh "wt_multiples" in
    let freeze_sig := fresh "freeze_sig" in
    let ring := fresh "ring" in
    let sz := pose_sz sz in
    let bitwidth := pose_bitwidth bitwidth in
    let s := pose_s s in
    let c := pose_c c in
    let carry_chains := pose_carry_chains carry_chains in
    let a24 := pose_a24 a24 in
    let coef_div_modulus := pose_coef_div_modulus coef_div_modulus in
    let goldilocks := pose_goldilocks goldilocks in
    let m := pose_m s c m in
    let wt := pose_wt m sz wt in
    let sz2 := pose_sz2 sz sz2 in
    let m_enc := pose_m_enc sz s c wt m_enc in
    let coef := pose_coef sz wt m_enc coef_div_modulus coef in
    let coef_mod := pose_coef_mod sz wt m coef coef_mod in
    let sz_nonzero := pose_sz_nonzero sz sz_nonzero in
    let wt_nonzero := pose_wt_nonzero wt wt_nonzero in
    let wt_nonneg := pose_wt_nonneg wt wt_nonneg in
    let wt_divides := pose_wt_divides wt wt_divides in
    let wt_divides' := pose_wt_divides' wt wt_divides wt_divides' in
    let wt_divides_chains := pose_wt_divides_chains wt carry_chains wt_divides' wt_divides_chains in
    let zero_sig := pose_zero_sig sz m wt zero_sig in
    let one_sig := pose_one_sig sz m wt one_sig in
    let a24_sig := pose_a24_sig sz m wt a24 a24_sig in
    let add_sig := pose_add_sig sz m wt wt_nonzero add_sig in
    let sub_sig := pose_sub_sig sz m wt wt_nonzero coef sub_sig in
    let opp_sig := pose_opp_sig sz m wt wt_nonzero coef opp_sig in
    let half_sz := pose_half_sz sz half_sz in
    let half_sz_nonzero := pose_half_sz_nonzero half_sz half_sz_nonzero in
    let sqrt_s := pose_sqrt_s s sqrt_s in
    let goldilocks_mul_sig := pose_goldilocks_mul_sig goldilocks sz wt s c half_sz sqrt_s goldilocks_mul_sig in
    let mul_sig := pose_mul_sig_full goldilocks sz m wt s c sz2 half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig in
    let square_sig := pose_square_sig_full goldilocks sz m wt s c sz2 wt_nonzero mul_sig square_sig in
    let carry_sig := pose_carry_sig sz m wt s c carry_chains wt_nonzero wt_divides_chains carry_sig in
    let wt_pos := pose_wt_pos wt wt_pos in
    let wt_multiples := pose_wt_multiples wt wt_multiples in
    let freeze_sig := pose_freeze_sig sz m wt c m_enc bitwidth wt_nonzero wt_pos wt_divides wt_multiples freeze_sig in
    let ring := pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring in
    constr:((sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring)).

  Ltac make_ArithmeticSynthesis_package _ :=
    lazymatch goal with
    | [ |- { T : _ & T } ] => eexists
    | [ |- _ ] => idtac
    end;
    let pkg := get_ArithmeticSynthesis_package () in
    exact pkg.
End MakeArithmeticSynthesisTestTactics.

Module Type ArithmeticSynthesisPrePackage.
  Parameter ArithmeticSynthesis_package' : { T : _ & T }.
  Parameter ArithmeticSynthesis_package : projT1 ArithmeticSynthesis_package'.
End ArithmeticSynthesisPrePackage.

Module MakeArithmeticSynthesisTest (AP : ArithmeticSynthesisPrePackage).
  Ltac get_MakeArithmeticSynthesisTest_package _ := eval hnf in AP.ArithmeticSynthesis_package.
  Ltac AS_reduce_proj x :=
    eval cbv beta iota zeta in x.

  Ltac get_sz _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in sz).
  Notation sz := (ltac:(let v := get_sz () in exact v)) (only parsing).
  Ltac get_bitwidth _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in bitwidth).
  Notation bitwidth := (ltac:(let v := get_bitwidth () in exact v)) (only parsing).
  Ltac get_s _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in s).
  Notation s := (ltac:(let v := get_s () in exact v)) (only parsing).
  Ltac get_c _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in c).
  Notation c := (ltac:(let v := get_c () in exact v)) (only parsing).
  Ltac get_carry_chains _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in carry_chains).
  Notation carry_chains := (ltac:(let v := get_carry_chains () in exact v)) (only parsing).
  Ltac get_a24 _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in a24).
  Notation a24 := (ltac:(let v := get_a24 () in exact v)) (only parsing).
  Ltac get_coef_div_modulus _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in coef_div_modulus).
  Notation coef_div_modulus := (ltac:(let v := get_coef_div_modulus () in exact v)) (only parsing).
  Ltac get_goldilocks _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in goldilocks).
  Notation goldilocks := (ltac:(let v := get_goldilocks () in exact v)) (only parsing).
  Ltac get_m _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in m).
  Notation m := (ltac:(let v := get_m () in exact v)) (only parsing).
  Ltac get_wt _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt).
  Notation wt := (ltac:(let v := get_wt () in exact v)) (only parsing).
  Ltac get_sz2 _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in sz2).
  Notation sz2 := (ltac:(let v := get_sz2 () in exact v)) (only parsing).
  Ltac get_m_enc _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in m_enc).
  Notation m_enc := (ltac:(let v := get_m_enc () in exact v)) (only parsing).
  Ltac get_coef _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in coef).
  Notation coef := (ltac:(let v := get_coef () in exact v)) (only parsing).
  Ltac get_coef_mod _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in coef_mod).
  Notation coef_mod := (ltac:(let v := get_coef_mod () in exact v)) (only parsing).
  Ltac get_sz_nonzero _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in sz_nonzero).
  Notation sz_nonzero := (ltac:(let v := get_sz_nonzero () in exact v)) (only parsing).
  Ltac get_wt_nonzero _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_nonzero).
  Notation wt_nonzero := (ltac:(let v := get_wt_nonzero () in exact v)) (only parsing).
  Ltac get_wt_nonneg _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_nonneg).
  Notation wt_nonneg := (ltac:(let v := get_wt_nonneg () in exact v)) (only parsing).
  Ltac get_wt_divides _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_divides).
  Notation wt_divides := (ltac:(let v := get_wt_divides () in exact v)) (only parsing).
  Ltac get_wt_divides' _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_divides').
  Notation wt_divides' := (ltac:(let v := get_wt_divides' () in exact v)) (only parsing).
  Ltac get_wt_divides_chains _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_divides_chains).
  Notation wt_divides_chains := (ltac:(let v := get_wt_divides_chains () in exact v)) (only parsing).
  Ltac get_zero_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in zero_sig).
  Notation zero_sig := (ltac:(let v := get_zero_sig () in exact v)) (only parsing).
  Ltac get_one_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in one_sig).
  Notation one_sig := (ltac:(let v := get_one_sig () in exact v)) (only parsing).
  Ltac get_a24_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in a24_sig).
  Notation a24_sig := (ltac:(let v := get_a24_sig () in exact v)) (only parsing).
  Ltac get_add_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in add_sig).
  Notation add_sig := (ltac:(let v := get_add_sig () in exact v)) (only parsing).
  Ltac get_sub_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in sub_sig).
  Notation sub_sig := (ltac:(let v := get_sub_sig () in exact v)) (only parsing).
  Ltac get_opp_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in opp_sig).
  Notation opp_sig := (ltac:(let v := get_opp_sig () in exact v)) (only parsing).
  Ltac get_half_sz _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in half_sz).
  Notation half_sz := (ltac:(let v := get_half_sz () in exact v)) (only parsing).
  Ltac get_half_sz_nonzero _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in half_sz_nonzero).
  Notation half_sz_nonzero := (ltac:(let v := get_half_sz_nonzero () in exact v)) (only parsing).
  Ltac get_sqrt_s _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in sqrt_s).
  Notation sqrt_s := (ltac:(let v := get_sqrt_s () in exact v)) (only parsing).
  Ltac get_mul_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in mul_sig).
  Notation mul_sig := (ltac:(let v := get_mul_sig () in exact v)) (only parsing).
  Ltac get_square_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in square_sig).
  Notation square_sig := (ltac:(let v := get_square_sig () in exact v)) (only parsing).
  Ltac get_carry_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in carry_sig).
  Notation carry_sig := (ltac:(let v := get_carry_sig () in exact v)) (only parsing).
  Ltac get_wt_pos _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_pos).
  Notation wt_pos := (ltac:(let v := get_wt_pos () in exact v)) (only parsing).
  Ltac get_wt_multiples _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in wt_multiples).
  Notation wt_multiples := (ltac:(let v := get_wt_multiples () in exact v)) (only parsing).
  Ltac get_freeze_sig _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in freeze_sig).
  Notation freeze_sig := (ltac:(let v := get_freeze_sig () in exact v)) (only parsing).
  Ltac get_ring _ := let pkg := get_MakeArithmeticSynthesisTest_package () in AS_reduce_proj (let '(sz, bitwidth, s, c, carry_chains, a24, coef_div_modulus, goldilocks, m, wt, sz2, m_enc, coef, coef_mod, sz_nonzero, wt_nonzero, wt_nonneg, wt_divides, wt_divides', wt_divides_chains, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, half_sz, half_sz_nonzero, sqrt_s, mul_sig, square_sig, carry_sig, wt_pos, wt_multiples, freeze_sig, ring) := pkg in ring).
  Notation ring := (ltac:(let v := get_ring () in exact v)) (only parsing).
End MakeArithmeticSynthesisTest.
