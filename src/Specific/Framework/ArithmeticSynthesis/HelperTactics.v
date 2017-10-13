Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Ltac if_cond_else cond tac default id :=
  lazymatch (eval compute in cond) with
  | true => tac id
  | false => default
  end.
Ltac if_cond cond tac id := if_cond_else cond tac (0%Z) id.

Ltac pose_modinv modinv_fuel a modulus modinv :=
  let v := constr:(Option.invert_Some (Z.modinv_fueled modinv_fuel a modulus)) in
  let v := (eval vm_compute in v) in
  let v := (eval vm_compute in (v : Z)) in
  cache_term v modinv.
Ltac pose_correct_if_Z v mkeqn id :=
  let T := type of v in
  let eqn :=
      lazymatch (eval vm_compute in T) with
      | Z => mkeqn ()
      | ?T
        => let v := (eval vm_compute in v) in
           lazymatch T with
           | option _
             => lazymatch v with
                | None => constr:(v = v)
                end
           | unit
             => lazymatch v with
                | tt => constr:(tt = tt)
                end
           end
      end in
  cache_proof_with_type_by
    eqn
    ltac:(vm_compute; reflexivity)
           id.

Ltac pose_proof_tuple ls :=
  let t := type of ls in
  lazymatch ls with
  | prod ?x ?y => pose_proof_tuple x; pose_proof_tuple y
  | conj ?x ?y => pose_proof_tuple x; pose_proof_tuple y
  | _
    => lazymatch eval hnf in t with
       | prod ?x ?y => pose_proof_tuple (fst ls); pose_proof_tuple (snd ls)
       | and ?x ?y => pose_proof_tuple (proj1 ls); pose_proof_tuple (proj2 ls)
       | _ => pose proof ls
       end
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
