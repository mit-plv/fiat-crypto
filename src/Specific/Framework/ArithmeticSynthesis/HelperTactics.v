Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Arithmetic.Saturated.Wrappers.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Decidable.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Ltac if_cond_else cond tac default id :=
  lazymatch (eval compute in cond) with
  | true => tac id
  | false => default
  end.
Ltac if_cond cond tac id := if_cond_else cond tac (0%Z) id.

Ltac pose_modinv modinv_fuel a modulus modinv :=
  let v0 := constr:(Option.invert_Some (Z.modinv_fueled modinv_fuel a modulus)) in
  let v := (eval vm_compute in v0) in
  let v := lazymatch type of v with (* if the computation failed, display a reasonable error message about the attempted computation *)
           | Z => v
           | _ => (eval cbv -[Option.invert_Some Z.modinv_fueled] in v0)
           end in
  let v := (eval vm_compute in (v <: Z)) in
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

Ltac make_chained_carries_cps sz wt s c a carry_chains :=
  (eval cbv [Positional.chained_carries_reduce_cps Positional.chained_carries_reduce_cps_step carry_chains] in
      (Positional.chained_carries_reduce_cps sz wt s c a carry_chains id)).

Ltac specialize_existing_sig existing_sig :=
  lazymatch type of existing_sig with
  | ?T -> _
    => let H := fresh "existing_sig_subproof" in
       let H := cache_proof_with_type_by
                  T
                  ltac:(vm_decide_no_check)
                         H in
       specialize_existing_sig (existing_sig H)
  | _ => existing_sig
  end.

Ltac cache_sig_with_type_by_existing_sig_helper cbv_tac ty existing_sig id :=
  let existing_sig := specialize_existing_sig existing_sig in
  cache_sig_with_type_by
    ty
    ltac:(eexists; intros; etransitivity;
          [ apply f_equal
          | solve [ eapply (proj2_sig existing_sig); eassumption ] ];
          do 2 (cbv [proj1_sig
                       Positional.chained_carries_reduce_cps Positional.chained_carries_reduce_cps_step
                       Positional.mul_cps Positional.reduce_cps];
                cbv_tac ());
          repeat autounfold;
          let next_step _ := basesystem_partial_evaluation_RHS_gen Wrappers.basesystem_partial_evaluation_unfolder in
          lazymatch goal with
          | [ |- _ = match ?code with
                     | None => _
                     | _ => _
                     end ]
            => let c := (eval hnf in code) in
               change code with c;
               cbv beta iota;
               lazymatch c with
               | None => next_step ()
               | _ => idtac
               end
          | _ => next_step ()
          end;
          do_replace_match_with_destructuring_match_in_goal;
          reflexivity)
           id.

Ltac solve_constant_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => let t := (eval vm_compute in
                    (Positional.encode (n:=sz) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt (F.to_Z (m:=M) v))) in
       (exists t; vm_decide)
  end.
