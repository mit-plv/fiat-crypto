Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.ArithmeticCPS.Core.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.
Import CPSBindNotations.
Local Open Scope cps_scope.

Section mod_ops.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).
  Definition weight (i : nat)
    := 2^(-(-(limbwidth_num * i) / limbwidth_den)).
End mod_ops.
(*
Require Import Crypto.Arithmetic.ModOps.
Print encodemod.
*)

Module ModOps (Import RT : Runtime).
  Module Import Deps.
    Module Export Positional := Positional RT.
  End Deps.

  Section mod_ops.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).

  Local Notation weight := (weight limbwidth_num limbwidth_den).

  Definition carry_mulmod_cps (f g : list Z) : ~> list Z
    := (fg <- mulmod_cps weight s c n f g; v <- chained_carries_cps weight n s c fg idxs; return v).
  Definition carry_mulmod (f g : list Z) : list Z := carry_mulmod_cps f g _ id.

  Definition carry_squaremod_cps (f : list Z) : ~> list Z
    := (ff <- squaremod_cps weight s c n f; v <- chained_carries_cps weight n s c ff idxs; return v).
  Definition carry_squaremod (f : list Z) : list Z := carry_squaremod_cps f _ id.

  Definition carry_scmulmod_cps (x : Z) (f : list Z) : ~> list Z
    := (x <- encode_cps weight n s c x;
          xf <- mulmod_cps weight s c n x f;
          xf <- chained_carries_cps weight n s c xf idxs;
          return xf).
  Definition carry_scmulmod (x : Z) (f : list Z) : list Z := carry_scmulmod_cps x f _ id.

  Definition carrymod_cps (f : list Z) : ~> list Z
    := chained_carries_cps weight n s c f idxs.
  Definition carrymod (f : list Z) : list Z := carrymod_cps f _ id.

  Definition addmod_cps (f g : list Z) : ~> list Z
    := add_cps weight n f g.
  Definition addmod (f g : list Z) : list Z := addmod_cps f g _ id.

  Definition submod_cps (coef : Z) (f g : list Z) : ~> list Z
    := sub_cps weight n s c coef f g.
  Definition submod (coef : Z) (f g : list Z) : list Z := submod_cps coef f g _ id.

  Definition oppmod_cps (coef : Z) (f : list Z) : ~> list Z
    := opp_cps weight n s c coef f.
  Definition oppmod (coef : Z) (f : list Z) : list Z := oppmod_cps coef f _ id.

  Definition encodemod_cps (f : Z) : ~> list Z
    := encode_cps weight n s c f.
  Definition encodemod (f : Z) : list Z := encodemod_cps f _ id.
  End mod_ops.
End ModOps.

(*
Module Import RT_ExtraAx := RT_Extra RuntimeAxioms.
Module ModOpsAx := ModOps RuntimeAxioms.

Import List.ListNotations.
Import RuntimeAxioms.

Axiom hide : forall {T} {v : T}, True.
Time Compute @hide _ (fun f g => ModOpsAx.addmod 51 2 5 (expand_list 0 f 5) (expand_list 0 g 5)).
Time Compute @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).
Time Eval cbv in @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).
Time Eval lazy in @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).




Module Import RT_ExtraDef := RT_Extra RuntimeDefinitions.
Module ModOpsDef := ModOps RuntimeDefinitions.
Import RuntimeDefinitions.


Time Eval cbv_no_rt in @hide _ (fun f g => ModOpsDef.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).
Time Eval lazy_no_rt in @hide _ (fun f g => ModOpsDef.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).

(* Goal forall f g : list Z, True.
  intros.
  pose (ModOpsAx.addmod 51 2 5 (expand_list 0 f 5) (expand_list 0 g 5)) as e.
  cbv [ModOpsAx.addmod expand_list expand_list_helper nat_rect List.seq List.app] in e.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd] in e.
  vm_compute in e.
  cbv [ModOpsAx.addmod_cps]
  cbv [
  ModOpsAx.carry_mulmod ModOpsAx.carry_mulmod_cps cpsbind cpsreturn] in e.
  cbv [ModOpsAx.Deps.Positional.mulmod_cps ModOpsAx.Deps.Positional.from_associational_cps ModOpsAx.Deps.Positional.zeros List.repeat] in e.
  cbv [cpscall] in e.
  set (k :=  ModOpsAx.Deps.Positional.Deps.Associational.repeat_reduce _ _ _) in (value of e).
  set (k' := k _) in (value of e).
  subst k.
  vm_compute in k'.
  subst k'.
  cbv [fold_right_cps2] in e.
  cbv [fold_right_cps2_specialized] in e.
  cbv [fold_right_cps2_specialized_step] in e.
  cbv [weight Init.Nat.pred ModOpsAx.Deps.Positional.place nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd] in e.
  cbv [ModOpsAx.Deps.Positional.add_to_nth update_nth cpscall] in e.
  set (w := fun i : nat => _) in (value of e).
  cbv [ModOpsAx.Deps.Positional.chained_carries_cps] in e.
  cbv [List.rev List.app id] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [ModOpsAx.Deps.Positional.carry_reduce_cps] in e.
  cbv [ModOpsAx.Deps.Positional.to_associational] in e.
  unfold ModOpsAx.Deps.Positional.carry_cps at 1 in (value of e).
  cbv [ModOpsAx.Deps.Positional.Deps.Associational.carry_cps] in e.
  cbv [ModOpsAx.Deps.Positional.to_associational List.map List.seq] in e.
  Arguments List.combine _ _ !_ !_.
  cbn [List.combine] in e.
  cbv [flat_map_cps flat_map_cps_specialized] in e.
  cbv [ModOpsAx.Deps.Positional.Deps.Associational.carryterm_cps ] in e.
  cbv [fst snd] in e.
  cbv [w] in e.
  clear w.
  set (w := fun i : nat => _) in (value of e).
  cbv [weight Init.Nat.pred ModOpsAx.Deps.Positional.place nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd] in e.
  cbv [List.app] in e.
  cbv [cpsbind cpsreturn cpscall] in e.
  unfold ModOpsAx.Deps.Positional.from_associational_cps at 1 in (value of e).
  cbv [ModOpsAx.Deps.Positional.zeros List.repeat ModOpsAx.Deps.Positional.add_to_nth fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step Init.Nat.pred ModOpsAx.Deps.Positional.place fst snd nat_rect] in e.
  vm_compute in e.
  cbv [] in e.
  subst w; cbv beta iota zeta in e.
  cbv beta iota zeta in
  cbv [cpsbind cpsreturn cpscall ModOpsAx.Deps.Positional.carry_cps] in e.
  cbv [ModOpsAx.Deps.Positional.Deps.Associational.carry_cps ModOpsAx.Deps.Positional.to_associational] in e.
  cbv [List.map List.combine List.seq] in e.
  cbv [flat_map_cps] in e.
  cbv [ModOpsAx.Deps.Positional.from_associational_cps] in e.
  cbv [flat_map_cps_specialized] in e.
  cbv [ModOpsAx.Deps.Positional.Deps.Associational.carryterm_cps] in e.
  cbv [ModOpsAx.Deps.Positional.zeros] in e.









  cbv [ModOpsAx.Deps.Positional.Deps.Associational.split] in e.

 *)
*)
