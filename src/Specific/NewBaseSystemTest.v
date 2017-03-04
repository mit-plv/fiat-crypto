Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.NewBaseSystem. Import B.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tactics Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Crypto.Util.Tuple.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(*** 
Modulus : 2^255-19
Base: 25.5
Comparison : F
***)
Section Ops.
  Local Infix "^" := tuple : type_scope.

  (* These `Let`s will need to be passed as Ltac arguments (or cleverly inferred *)
  Let wt := fun i : nat => 2^(25 * (i / 2) + 26 * ((i + 1) / 2)).
  Let sz := 10%nat.
  Let s : Z := 2^255.
  Let c : list B.limb := [(1, 19)].
  Let coef_div_modulus := 2. (* add 2*modulus before subtracting *)
  Let carry_chain := (seq 0 sz) ++ ([0;1])%nat.

  (* These `Lets` are inferred from those above *)
  Let m := Eval compute in Z.to_pos (s - Associational.eval c). (* modulus *)
  Let sz2 := Eval compute in ((sz * 2) - 1)%nat.
  Let coef := Eval vm_compute in (@Positional.encode wt modulo div sz (coef_div_modulus * (s-Associational.eval c))). (* subtraction coefficient *)
  Let coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0 := eq_refl.

  Definition zero_sig :
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}.
  Proof.
    let t := eval vm_compute in
    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt 0) in
        exists t; vm_decide.
  Defined.

  Definition one_sig :
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}.
  Proof.
    let t := eval vm_compute in
    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt 1) in
        exists t; vm_decide.
  Defined.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (add a b) = (eval a  + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros; assert_preconditions.
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
    eexists; cbv beta zeta; intros; assert_preconditions.
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
    eexists; cbv beta zeta; intros; assert_preconditions.
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
    eexists; cbv beta zeta; intros; assert_preconditions.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a b
           (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    solve_op_F wt x. reflexivity.

    (* rough breakdown of synthesis time *)
    (* 1.2s for side conditions -- should improve significantly when [chained_carries] gets a correctness lemma *)
    (* basesystem_partial_evaluation_RHS (primarily vm_compute): 1.8s, which gets re-computed during defined *)

    (* doing [cbv -[Let_In runtime_add runtime_mul]] took 37s *)

  Defined. (* 3s *)

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig :
    {carry : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (carry a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros; assert_preconditions.
    let x := constr:(
               Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain id) in
    solve_op_F wt x. reflexivity.
  Defined.

End Ops.

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)