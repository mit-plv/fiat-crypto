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


Section chained_carries_cps'.
  Context (sz : nat) (wt : nat -> Z) (s : Z) (c : list limb).

  Definition chained_carries_cps'_step
             (chained_carries_cps' : forall (a : Tuple.tuple Z sz) (carry_chains : list (list nat)) (f : Tuple.tuple Z sz -> Tuple.tuple Z sz), Tuple.tuple Z sz)
             (a : Tuple.tuple Z sz) (carry_chains : list (list nat))
             (f : Tuple.tuple Z sz -> Tuple.tuple Z sz)
    : Tuple.tuple Z sz
    := match carry_chains with
       | nil => f a
       | carry_chain :: nil
         => Positional.chained_carries_cps
              (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain f
       | carry_chain :: carry_chains
         => Positional.chained_carries_cps
              (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain
              (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
              (fun r' => chained_carries_cps' r' carry_chains f))
       end.
  Fixpoint chained_carries_cps' (a : Tuple.tuple Z sz) (carry_chains : list (list nat))
           (f : Tuple.tuple Z sz -> Tuple.tuple Z sz)
    : Tuple.tuple Z sz
    := chained_carries_cps'_step (chained_carries_cps') a carry_chains f.

  Lemma step_chained_carries_cps' a carry_chain carry_chains (f : tuple Z sz -> tuple Z sz)
    : chained_carries_cps' a (carry_chain :: carry_chains) f
      = match length carry_chains with
        | O => Positional.chained_carries_cps
                 (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain f
        | S _
          => Positional.chained_carries_cps
               (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain
               (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
               (fun r' => chained_carries_cps' r' carry_chains f))
        end.
  Proof.
    destruct carry_chains; reflexivity.
  Qed.

  Definition chained_carries' (a : Tuple.tuple Z sz) (carry_chains : list (list nat))
    : Tuple.tuple Z sz
    := chained_carries_cps' a carry_chains id.

  Lemma chained_carries'_id a carry_chains f
    : @chained_carries_cps' a carry_chains f = f (@chained_carries' a carry_chains).
  Proof.
    destruct carry_chains as [|carry_chain carry_chains]; [ reflexivity | ].
    cbv [chained_carries'].
    revert a carry_chain; induction carry_chains as [|? carry_chains IHcarry_chains]; intros.
    { simpl; repeat autounfold; autorewrite with uncps; reflexivity. }
    { rewrite !step_chained_carries_cps'.
      simpl @length; cbv iota beta.
      repeat autounfold; autorewrite with uncps.
      rewrite !IHcarry_chains.
      reflexivity. }
  Qed.
End chained_carries_cps'.

Hint Opaque chained_carries' : uncps.
Hint Unfold chained_carries'.
Hint Rewrite chained_carries'_id : uncps.

Ltac make_chained_carries_cps sz wt s c a carry_chains :=
  (eval cbv [chained_carries_cps' chained_carries_cps'_step carry_chains] in
      (chained_carries_cps' sz wt s c a carry_chains id)).

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
                       chained_carries_cps' chained_carries_cps'_step
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
                    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
       (exists t; vm_decide)
  end.
