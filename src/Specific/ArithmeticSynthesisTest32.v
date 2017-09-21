Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.QUtil.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(***
Modulus : 2^255-19
Base: 25/26
***)
Section Ops25p5.
  Local Infix "^" := tuple : type_scope.

  (* These definitions will need to be passed as Ltac arguments (or
  cleverly inferred) when things are eventually automated *)
  Definition sz := 10%nat.
  Definition bitwidth := 32.
  Definition s : Z := 2^255.
  Definition c : list B.limb := [(1, 19)].
  Definition carry_chain1 := Eval vm_compute in (seq 0 (pred sz)).
  Definition carry_chain2 := [0;1]%nat.

  Definition a24 := 121665%Z.
  Definition coef_div_modulus : nat := 2. (* add 2*modulus before subtracting *)
  (* These definitions are inferred from those above *)
  Definition m := Eval vm_compute in Z.to_pos (s - Associational.eval c). (* modulus *)
  Section wt.
    Import QArith Qround.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Definition wt (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
  End wt.
  Definition sz2 := Eval vm_compute in ((sz * 2) - 1)%nat.
  Definition m_enc :=
    Eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c)).
  Definition coef := (* subtraction coefficient *)
    Eval vm_compute in
      ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
         match ctr with
         | O => acc
         | S n => addm (Positional.add_cps wt acc m_enc id) n
         end) (Positional.zeros sz) coef_div_modulus).
  Definition coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0 := eq_refl.
  Lemma sz_nonzero : sz <> 0%nat. Proof. vm_decide. Qed.
  Lemma wt_nonzero i : wt i <> 0.
  Proof. eapply pow_ceil_mul_nat_nonzero; vm_decide. Qed.
  Lemma wt_divides i : wt (S i) / wt i > 0.
  Proof. apply pow_ceil_mul_nat_divide; vm_decide. Qed.
  Lemma wt_divides' i : wt (S i) / wt i <> 0.
  Proof. symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides. Qed.
  Definition wt_divides_chain1 i (H:In i carry_chain1) : wt (S i) / wt i <> 0 := wt_divides' i.
  Definition wt_divides_chain2 i (H:In i carry_chain2) : wt (S i) / wt i <> 0 := wt_divides' i.

  Local Ltac solve_constant_sig :=
    lazymatch goal with
    | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
      => let t := (eval vm_compute in
                      (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
         (exists t; vm_decide)
    end.

  Definition zero_sig :
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}.
  Proof.
    solve_constant_sig.
  Defined.

  Definition one_sig :
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}.
  Proof.
    solve_constant_sig.
  Defined.

  Definition a24_sig :
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24 }.
  Proof.
    solve_constant_sig.
  Defined.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (add a b) = (eval a  + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
        Positional.add_cps (n := sz) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition sub_sig :
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (sub a b) = (eval a - eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition opp_sig :
    {opp : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (opp a) = F.opp (eval a)}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (mul a b) = (eval a  * eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                            (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    solve_op_F wt x.
    instantiate (1 := fun a b =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in_9, in_8, in_7, in_6, in_5, in_4, in_3, in_2, in_1, in_0) := a in
      let '(in2_9, in2_8, in2_7, in2_6, in2_5, in2_4, in2_3, in2_2, in2_1, in2_0) := b in
      dlet output_0 := in2_0 * in_0 in
dlet output_1 :=       in2_0 * in_1 +
                    in2_1 * in_0 in
dlet output_2 :=  2 *  in2_1 * in_1 +
                    in2_0 * in_2 +
                    in2_2 * in_0 in
dlet output_3 :=       in2_1 * in_2 +
                    in2_2 * in_1 +
                    in2_0 * in_3 +
                    in2_3 * in_0 in
dlet output_4 :=       in2_2 * in_2 +
               2 * (in2_1 * in_3 +
                    in2_3 * in_1) +
                    in2_0 * in_4 +
                    in2_4 * in_0 in
dlet output_5 :=       in2_2 * in_3 +
                    in2_3 * in_2 +
                    in2_1 * in_4 +
                    in2_4 * in_1 +
                    in2_0 * in_5 +
                    in2_5 * in_0 in
dlet output_6 :=  2 * (in2_3 * in_3 +
                    in2_1 * in_5 +
                    in2_5 * in_1) +
                    in2_2 * in_4 +
                    in2_4 * in_2 +
                    in2_0 * in_6 +
                    in2_6 * in_0 in
dlet output_7 :=       in2_3 * in_4 +
                    in2_4 * in_3 +
                    in2_2 * in_5 +
                    in2_5 * in_2 +
                    in2_1 * in_6 +
                    in2_6 * in_1 +
                    in2_0 * in_7 +
                    in2_7 * in_0 in
dlet output_8 :=       in2_4 * in_4 +
               2 * (in2_3 * in_5 +
                    in2_5 * in_3 +
                    in2_1 * in_7 +
                    in2_7 * in_1) +
                    in2_2 * in_6 +
                    in2_6 * in_2 +
                    in2_0 * in_8 +
                    in2_8 * in_0 in
dlet output_9 :=       in2_4 * in_5 +
                    in2_5 * in_4 +
                    in2_3 * in_6 +
                    in2_6 * in_3 +
                    in2_2 * in_7 +
                    in2_7 * in_2 +
                    in2_1 * in_8 +
                    in2_8 * in_1 +
                    in2_0 * in_9 +
                    in2_9 * in_0 in
dlet output_10 := 2 * (in2_5 * in_5 +
                    in2_3 * in_7 +
                    in2_7 * in_3 +
                    in2_1 * in_9 +
                    in2_9 * in_1) +
                    in2_4 * in_6 +
                    in2_6 * in_4 +
                    in2_2 * in_8 +
                    in2_8 * in_2 in
dlet output_11 :=      in2_5 * in_6 +
                    in2_6 * in_5 +
                    in2_4 * in_7 +
                    in2_7 * in_4 +
                    in2_3 * in_8 +
                    in2_8 * in_3 +
                    in2_2 * in_9 +
                    in2_9 * in_2 in
dlet output_12 :=      in2_6 * in_6 +
               2 * (in2_5 * in_7 +
                    in2_7 * in_5 +
                    in2_3 * in_9 +
                    in2_9 * in_3) +
                    in2_4 * in_8 +
                    in2_8 * in_4 in
dlet output_13 :=      in2_6 * in_7 +
                    in2_7 * in_6 +
                    in2_5 * in_8 +
                    in2_8 * in_5 +
                    in2_4 * in_9 +
                    in2_9 * in_4 in
dlet output_14 := 2 * (in2_7 * in_7 +
                    in2_5 * in_9 +
                    in2_9 * in_5) +
                    in2_6 * in_8 +
                    in2_8 * in_6 in
dlet output_15 :=      in2_7 * in_8 +
                    in2_8 * in_7 +
                    in2_6 * in_9 +
                    in2_9 * in_6 in
dlet output_16 :=      in2_8 * in_8 +
               2 * (in2_7 * in_9 +
                    in2_9 * in_7) in
dlet output_17 :=      in2_8 * in_9 +
                    in2_9 * in_8 in
dlet output_18 := 2 *  in2_9 * in_9 in
dlet output_8 := output_8 + output_18 << 4 in
dlet output_8 := output_8 + output_18 << 1 in
dlet output_8 := output_8 + output_18 in
dlet output_7 := output_7 + output_17 << 4 in
dlet output_7 := output_7 + output_17 << 1 in
dlet output_7 := output_7 + output_17 in
dlet output_6 := output_6 + output_16 << 4 in
dlet output_6 := output_6 + output_16 << 1 in
dlet output_6 := output_6 + output_16 in
dlet output_5 := output_5 + output_15 << 4 in
dlet output_5 := output_5 + output_15 << 1 in
dlet output_5 := output_5 + output_15 in
dlet output_4 := output_4 + output_14 << 4 in
dlet output_4 := output_4 + output_14 << 1 in
dlet output_4 := output_4 + output_14 in
dlet output_3 := output_3 + output_13 << 4 in
dlet output_3 := output_3 + output_13 << 1 in
dlet output_3 := output_3 + output_13 in
dlet output_2 := output_2 + output_12 << 4 in
dlet output_2 := output_2 + output_12 << 1 in
dlet output_2 := output_2 + output_12 in
dlet output_1 := output_1 + output_11 << 4 in
dlet output_1 := output_1 + output_11 << 1 in
dlet output_1 := output_1 + output_11 in
dlet output_0 := output_0 + output_10 << 4 in
dlet output_0 := output_0 + output_10 << 1 in
dlet output_0 := output_0 + output_10 in
(output_9, output_8, output_7, output_6, output_5, output_4, output_3, output_2, output_1, output_0)
    ).
    break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring.
  Defined.

  Definition square_sig :
    {square : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (square a) = (eval a  * eval a)%F}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                            (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    solve_op_F wt x.
    instantiate (1 := fun a =>
      (* Micro-optimized form from curve25519-donna by Adam Langley (Google) and Daniel Bernstein. See <https://github.com/agl/curve25519-donna/blob/master/LICENSE.md>. *)
      let '(in_9, in_8, in_7, in_6, in_5, in_4, in_3, in_2, in_1, in_0) := a in
dlet output_0 :=       in_0 * in_0 in
dlet output_1 :=  2 *  in_0 * in_1 in
dlet output_2 :=  2 * (in_1 * in_1 +
                    in_0 * in_2) in
dlet output_3 :=  2 * (in_1 * in_2 +
                    in_0 * in_3) in
dlet output_4 :=       in_2 * in_2 +
               4 *  in_1 * in_3 +
               2 *  in_0 * in_4 in
dlet output_5 :=  2 * (in_2 * in_3 +
                    in_1 * in_4 +
                    in_0 * in_5) in
dlet output_6 :=  2 * (in_3 * in_3 +
                    in_2 * in_4 +
                    in_0 * in_6 +
               2 *  in_1 * in_5) in
dlet output_7 :=  2 * (in_3 * in_4 +
                    in_2 * in_5 +
                    in_1 * in_6 +
                    in_0 * in_7) in
dlet output_8 :=       in_4 * in_4 +
               2 * (in_2 * in_6 +
                    in_0 * in_8 +
               2 * (in_1 * in_7 +
                    in_3 * in_5)) in
dlet output_9 :=  2 * (in_4 * in_5 +
                    in_3 * in_6 +
                    in_2 * in_7 +
                    in_1 * in_8 +
                    in_0 * in_9) in
dlet output_10 := 2 * (in_5 * in_5 +
                    in_4 * in_6 +
                    in_2 * in_8 +
               2 * (in_3 * in_7 +
                    in_1 * in_9)) in
dlet output_11 := 2 * (in_5 * in_6 +
                    in_4 * in_7 +
                    in_3 * in_8 +
                    in_2 * in_9) in
dlet output_12 :=      in_6 * in_6 +
               2 * (in_4 * in_8 +
               2 * (in_5 * in_7 +
                    in_3 * in_9)) in
dlet output_13 := 2 * (in_6 * in_7 +
                    in_5 * in_8 +
                    in_4 * in_9) in
dlet output_14 := 2 * (in_7 * in_7 +
                    in_6 * in_8 +
               2 *  in_5 * in_9) in
dlet output_15 := 2 * (in_7 * in_8 +
                    in_6 * in_9) in
dlet output_16 :=      in_8 * in_8 +
               4 *  in_7 * in_9 in
dlet output_17 := 2 *  in_8 * in_9 in
dlet output_18 := 2 *  in_9 * in_9 in
dlet output_8 := output_8 + output_18 << 4 in
dlet output_8 := output_8 + output_18 << 1 in
dlet output_8 := output_8 + output_18 in
dlet output_7 := output_7 + output_17 << 4 in
dlet output_7 := output_7 + output_17 << 1 in
dlet output_7 := output_7 + output_17 in
dlet output_6 := output_6 + output_16 << 4 in
dlet output_6 := output_6 + output_16 << 1 in
dlet output_6 := output_6 + output_16 in
dlet output_5 := output_5 + output_15 << 4 in
dlet output_5 := output_5 + output_15 << 1 in
dlet output_5 := output_5 + output_15 in
dlet output_4 := output_4 + output_14 << 4 in
dlet output_4 := output_4 + output_14 << 1 in
dlet output_4 := output_4 + output_14 in
dlet output_3 := output_3 + output_13 << 4 in
dlet output_3 := output_3 + output_13 << 1 in
dlet output_3 := output_3 + output_13 in
dlet output_2 := output_2 + output_12 << 4 in
dlet output_2 := output_2 + output_12 << 1 in
dlet output_2 := output_2 + output_12 in
dlet output_1 := output_1 + output_11 << 4 in
dlet output_1 := output_1 + output_11 << 1 in
dlet output_1 := output_1 + output_11 in
dlet output_0 := output_0 + output_10 << 4 in
dlet output_0 := output_0 + output_10 << 1 in
dlet output_0 := output_0 + output_10 in
(output_9, output_8, output_7, output_6, output_5, output_4, output_3, output_2, output_1, output_0)
    ).
    break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring.
  Defined.

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig :
    {carry : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (carry a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero. pose proof wt_divides_chain1.
    pose proof div_mod. pose proof wt_divides_chain2.
    let x := constr:(
               Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain1
                  (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                  (fun rrr => Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt rrr carry_chain2 id
             ))) in
    solve_op_F wt x. reflexivity.
  Defined.

  Section PreFreeze.
    Lemma wt_pos i : wt i > 0.
    Proof. eapply pow_ceil_mul_nat_pos; vm_decide. Qed.

    Lemma wt_multiples i : wt (S i) mod (wt i) = 0.
    Proof. apply pow_ceil_mul_nat_multiples; vm_decide. Qed.
  End PreFreeze.

  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.

  Definition freeze_sig :
    {freeze : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
         (0 <= Positional.eval wt a < 2 * Z.pos m)->
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (freeze a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros a ?.
    pose proof wt_nonzero. pose proof wt_pos.
    pose proof div_mod. pose proof wt_divides.
    pose proof wt_multiples.
    pose proof div_correct. pose proof modulo_correct.
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    F_mod_eq;
      transitivity (Positional.eval wt x); repeat autounfold;
        [ | autorewrite with uncps push_id push_basesystem_eval;
            rewrite eval_freeze with (c:=c);
            try eassumption; try omega; try reflexivity;
            try solve [auto using B.Positional.select_id,
                       B.Positional.eval_select, zselect_correct];
            vm_decide].
   cbv[mod_eq]; apply f_equal2;
     [  | reflexivity ]; apply f_equal.
   cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect].
   reflexivity.
  Defined.

  Definition ring_25p5 :=
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
      ).

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)

End Ops25p5.
