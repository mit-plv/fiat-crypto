Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.Tactics.VM.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Crypto.Specific.Framework.ArithmeticSynthesis.SquareFromMul.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.
Local Infix "^" := Tuple.tuple : type_scope.

(** XXX TODO(jadep) FIXME: Is sqrt(s) the right thing to pass to goldilocks_mul_cps (the original code hard-coded 2^224 *)
Ltac internal_pose_sqrt_s s sqrt_s :=
  let v := (eval vm_compute in (Z.log2 s / 2)) in
  cache_term (2^v) sqrt_s.

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

Ltac internal_pose_goldilocks_mul_sig sz wt s c half_sz sqrt_s goldilocks_mul_sig :=
  cache_term_with_type_by
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       mul a b = goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id)}
    ltac:(eexists; cbv beta zeta; intros;
          cbv [goldilocks_mul_cps];
          repeat autounfold;
          basesystem_partial_evaluation_RHS;
          do_replace_match_with_destructuring_match_in_goal;
          reflexivity)
           goldilocks_mul_sig.

Ltac internal_pose_mul_sig_from_goldilocks_mul_sig sz m wt s c half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig :=
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

Ltac pose_mul_sig sz m wt s c half_sz wt_nonzero mul_sig :=
  let sqrt_s := fresh "sqrt_s" in
  let goldilocks_mul_sig := fresh "goldilocks_mul_sig" in
  let sqrt_s := internal_pose_sqrt_s s sqrt_s in
  let goldilocks_mul_sig := internal_pose_goldilocks_mul_sig sz wt s c half_sz sqrt_s goldilocks_mul_sig in
  internal_pose_mul_sig_from_goldilocks_mul_sig sz m wt s c half_sz sqrt_s goldilocks_mul_sig wt_nonzero mul_sig.

Ltac pose_square_sig sz m wt mul_sig square_sig :=
  SquareFromMul.pose_square_sig sz m wt mul_sig square_sig.
