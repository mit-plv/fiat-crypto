Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.ArithmeticCPS.Core.
Require Import Crypto.ArithmeticCPS.Freeze.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.ArithmeticCPS.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import CPSBindNotations.
Local Open Scope cps_scope.

Module WordByWordMontgomery (Import RT : Runtime).
  Module Import Deps.
    Module Positional := Positional RT.
    Module Rows := Rows RT.
    Module Export FreezeModOps := FreezeModOps RT.
    Module Export RT_Extra := RT_Extra RT.
  End Deps.
  Section with_args.
    Context (lgr : Z)
            (m : Z).
    Local Notation weight := (uweight lgr).
    Let T (n : nat) := list Z.
    Let r := (2^lgr).
    Definition eval {n} : T n -> Z := Positional.eval weight n.
    Let zero {n} : T n := Positional.zeros n.
    Let divmod {n} : T (S n) -> T n * Z := Rows.divmod.
    Let scmul_cps {n} (c : Z) (p : T n) : ~> T (S n) (* uses double-output multiply *)
      := (vc <- Rows.mul_cps weight r n (S n) (Positional.extend_to_length 1 n [c]) p;
            let '(v, c) := vc in
            return v).
    Let addT_cps {n} (p q : T n) : ~> T (S n) (* joins carry *)
      := (vc <- Rows.add_cps weight n p q;
            let '(v, c) := vc in
            return (v ++ [c])).
    Let drop_high_addT'_cps {n} (p : T (S n)) (q : T n) : ~> T (S n) (* drops carry *)
      := (pq <- Rows.add_cps weight (S n) p (Positional.extend_to_length n (S n) q); return (fst pq)).
    Let conditional_sub_cps {n} (arg : T (S n)) (N : T n) : ~> T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
      := (v <- Rows.conditional_sub_cps weight (S n) arg (Positional.extend_to_length n (S n) N); return (Positional.drop_high_to_length n v)).
    Context (R_numlimbs : nat)
            (N : T R_numlimbs). (* encoding of m *)
    Let sub_then_maybe_add_cps (a b : T R_numlimbs) : ~> T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
      := (v <- Rows.sub_then_maybe_add_cps weight R_numlimbs (r-1) a b N; return (fst v)).
    Local Opaque T.
    Section Iteration.
      Context (pred_A_numlimbs : nat)
              (B : T R_numlimbs) (k : Z)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs)).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

      Local Definition A'_S3_cps : ~> _
        := fun _ cont
           => let '(A', a) := @divmod _ A in
              dlet_list A' := A' in
              dlet a := a in
           @scmul_cps _ a B _ (fun aB =>
           @addT_cps _ S aB _ (fun S1 =>
           dlet_list S1 := S1 in
           dlet s := snd (@divmod (Datatypes.S (Datatypes.S R_numlimbs)) S1) in
           dlet q := fst (RT_Z.mul_split r s k) in
           @scmul_cps _ q N _ (fun qN =>
           @drop_high_addT'_cps _ S1 qN _ (fun S2 =>
           dlet_list S2 := S2 in
           dlet_list S3 := fst (@divmod (Datatypes.S R_numlimbs) S2) in
           cont (A', S3))))).
     End Iteration.

    Section loop.
      Context (A_numlimbs : nat)
              (A : T A_numlimbs)
              (B : T R_numlimbs)
              (k : Z)
              (S' : T (S R_numlimbs)).

      Definition redc_body_cps {pred_A_numlimbs} : T (S pred_A_numlimbs) * T (S R_numlimbs)
                                               ~> T pred_A_numlimbs * T (S R_numlimbs)
        := fun '(A, S') => A'_S3_cps _ B k A S'.

      Definition redc_loop_cps (count : nat) : T count * T (S R_numlimbs) ~> T O * T (S R_numlimbs)
        := nat_rect
             (fun count => T count * _ ~> _)
             (fun A_S => return A_S)
             (fun count' redc_loop_count' A_S
              => A'_S' <- redc_body_cps A_S; redc_loop_count' A'_S')
             count.

      Definition pre_redc_cps : ~> T (S R_numlimbs)
        := (v <- redc_loop_cps A_numlimbs (A, @zero (1 + R_numlimbs)%nat); return (snd v)).

      Definition redc_cps : ~> T R_numlimbs
        := (pre_redc <- pre_redc_cps; conditional_sub_cps pre_redc N).
    End loop.

    Definition add_cps (A B : T R_numlimbs) : ~> T R_numlimbs
      := (AB <- @addT_cps _ A B; conditional_sub_cps AB N).
    Definition sub_cps (A B : T R_numlimbs) : ~> T R_numlimbs
      := sub_then_maybe_add_cps A B.
    Definition opp_cps (A : T R_numlimbs) : ~> T R_numlimbs
      := sub_cps (@zero _) A.
    Definition nonzero (A : list Z) : Z
      := fold_right Z.lor 0 A.
  End with_args.

  Section modops.
    Context (bitwidth : Z)
            (n : nat)
            (m : Z).
    Let r := 2^bitwidth.
    Local Notation weight := (uweight bitwidth).
    Local Notation eval := (@eval bitwidth n).
    Let m_enc := Partition.partition weight n m.
    Local Coercion Z.of_nat : nat >-> Z.
    Context (r' : Z)
            (m' : Z)
            (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bitwidth_big : 0 < bitwidth)
            (m_big : 1 < m)
            (n_nz : n <> 0%nat)
            (m_small : m < r^n).

    Definition mulmod_cps (a b : list Z) : ~> list Z := @redc_cps bitwidth n m_enc n a b m'.
    Definition squaremod_cps (a : list Z) : ~> list Z := mulmod_cps a a.
    Definition addmod_cps (a b : list Z) : ~> list Z := @add_cps bitwidth n m_enc a b.
    Definition submod_cps (a b : list Z) : ~> list Z := @sub_cps bitwidth n m_enc a b.
    Definition oppmod_cps (a : list Z) : ~> list Z := @opp_cps bitwidth n m_enc a.

    Definition mulmod (a b : list Z) : list Z := mulmod_cps a b _ id.
    Definition squaremod (a : list Z) : list Z := squaremod_cps a _ id.
    Definition addmod (a b : list Z) : list Z := addmod_cps a b _ id.
    Definition submod (a b : list Z) : list Z := submod_cps a b _ id.
    Definition oppmod (a : list Z) : list Z := oppmod_cps a _ id.

    Definition nonzeromod (a : list Z) : Z := @nonzero a.
    Definition to_bytesmod_cps (a : list Z) : ~> list Z := @to_bytesmod_cps bitwidth 1 n a.
    Definition to_bytesmod (a : list Z) : list Z := to_bytesmod_cps a _ id.
    Definition onemod : list Z := Partition.partition weight n 1.
    Definition R2mod : list Z := Partition.partition weight n ((r^n * r^n) mod m).
    Definition from_montgomerymod_cps (v : list Z) : ~> list Z
      := mulmod_cps v onemod.
    Definition from_montgomerymod (v : list Z) : list Z := from_montgomerymod_cps v _ id.
    Definition encodemod_cps (v : Z) : ~> list Z
      := mulmod_cps (Partition.partition weight n v) R2mod.
    Definition encodemod (v : Z) : list Z := encodemod_cps v _ id.
  End modops.
End WordByWordMontgomery.

(*
Module Import RT_ExtraAx := RT_Extra RuntimeAxioms.
Module Import WordByWordMontgomeryAx := WordByWordMontgomery RuntimeAxioms.

Import List.ListNotations.
Import RuntimeAxioms.

Axiom hide : forall {T} {v : T}, True.
Require Import Crypto.Util.ZUtil.ModInv.

Time Compute @hide _ (fun a b => (let m := (2^256 - 2^224 + 2^192 + 2^96 - 1) in mulmod 64 4 m (Z.modinv (-m) (2^64)) (expand_list 0 a 4) (expand_list 0 b 4))).
Time Eval lazy in @hide _ (fun a b => (let m := (2^256 - 2^224 + 2^192 + 2^96 - 1) in mulmod 64 4 m (Z.modinv (-m) (2^64)) (expand_list 0 a 4) (expand_list 0 b 4))).

Goal forall (a b : list Z), True.
  intros.
  pose (let m := (2^256 - 2^224 + 2^192 + 2^96 - 1) in mulmod 64 4 m (Z.modinv (-m) (2^64)) (expand_list 0 a 4) (expand_list 0 b 4)) as e.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  set (k := Z.modinv _ _) in (value of e).
  vm_compute in k; subst k.
  cbv [expand_list expand_list_helper nat_rect] in e.
  cbv [mulmod mulmod_cps] in e.
  cbv [Partition.partition seq map] in e.
  cbv [uweight ModOps.weight] in e.
  cbv -[redc_cps] in e.
  cbv [redc_cps] in e.
  cbv [pre_redc_cps] in e.
  cbv [redc_loop_cps] in e.
  cbv [nat_rect] in e.
  cbv [Deps.Positional.zeros Nat.add] in e.
  cbv [cpscall cpsbind cpsreturn] in e.
  cbv [repeat] in e.
  cbv [redc_body_cps] in e.
  unfold WordByWordMontgomeryAx.A'_S3_cps in (value of e) at 1.
  cbv [Deps.Rows.divmod hd tl] in e.
  cbn [Deps.RT_Extra.dlet_nd_list] in e.
  cbv [Deps.Positional.extend_to_length] in e.
  cbv [Nat.sub Deps.Positional.zeros repeat] in e.
  cbn [List.app] in e.
  unfold Deps.Rows.mul_cps at 1 in (value of e).
  cbv [Deps.Rows.Deps.Positional.to_associational map seq] in e.
  cbn [combine] in e.
  set (uw := uweight 64) in (value of e).
  cbv [Deps.Rows.Deps.Associational.sat_mul_cps ] in e.
  cbv [flat_map_cps flat_map_cps_specialized] in e.
  cbv [Deps.Rows.Deps.Associational.sat_multerm_cps] in e; cbn [fst snd] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  Arguments app _ !_ !_.
  cbn [app] in e.
  unfold Deps.Rows.from_associational_cps in (value of e) at 1; cbv [Deps.Rows.Deps.Columns.from_associational_cps] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  Set Printing Depth 1000000.
  cbv [Deps.Rows.Deps.Columns.nils repeat Init.Nat.pred] in e.
  cbv [Deps.Rows.Deps.Columns.cons_to_nth] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [Deps.Rows.Deps.Columns.Deps.Positional.place] in e.
  cbv [nat_rect] in e.
  cbn [fst snd] in e.
  set (k := uw 0%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 1%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 2%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 3%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 4%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 5%nat) in (value of e); vm_compute in k; subst k.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  cbv [update_nth] in e.
  cbv [Deps.Rows.from_columns Deps.Rows.max_column_size Deps.Rows.from_columns' map List.repeat length Nat.max Deps.Rows.extract_row map hd tl List.app] in e.
  cbv delta [fold_right] in e.
  cbn [fst snd combine] in e.
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbn [fst snd] in e.
  unfold Deps.Rows.sum_rows_cps at 1 in (value of e).
  cbv [Deps.Rows.sum_rows'_cps rev] in e; cbn [app combine fst snd] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbn [fst snd combine app] in e.
  unfold Deps.Rows.sum_rows_cps at 1 in (value of e).
  cbv [Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e.
  cbn [fst snd combine app] in e.
  cbv [Deps.Rows.sum_rows_cps Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e; cbn [fst snd combine app] in e.
  unfold Deps.Rows.add_cps at 1 in (value of e).
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e.
  cbn [fst snd] in e.
  cbv [Deps.Rows.sum_rows_cps Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e; cbn [fst snd combine app] in e.
  cbn [Deps.RT_Extra.dlet_nd_list] in e.
  cbv [Deps.Rows.mul_cps] in e.
  cbv [Deps.Rows.Deps.Positional.to_associational map seq] in e.
  cbn [combine] in e.
  cbv [Deps.Rows.Deps.Associational.sat_mul_cps flat_map_cps flat_map_cps_specialized Deps.Rows.Deps.Associational.sat_multerm_cps cpscall cpsbind cpsreturn id] in e; cbn [fst snd app combine] in e.
  unfold Deps.Rows.from_associational_cps in (value of e) at 1.
  cbv [Deps.Rows.Deps.Columns.from_associational_cps cpscall cpsbind cpsreturn id Deps.Rows.Deps.Columns.nils repeat Init.Nat.pred Deps.Rows.Deps.Columns.cons_to_nth fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step Deps.Rows.Deps.Columns.Deps.Positional.place nat_rect] in e;
    cbn [fst snd app combine] in e.
  set (k := uw 0%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 1%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 2%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 3%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 4%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 5%nat) in (value of e); vm_compute in k; subst k.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  cbv [update_nth Deps.Rows.from_columns Deps.Rows.max_column_size Deps.Rows.from_columns' map List.repeat length Nat.max Deps.Rows.extract_row map hd tl List.app] in e.
  cbv delta [fold_right] in e.
  cbn [fst snd combine app] in e.
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e.
  cbn [fst snd combine app] in e.
  cbv [Deps.Rows.sum_rows_cps Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e; cbn [fst snd combine app] in e.
  unfold Deps.Rows.add_cps at 1 in (value of e).
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e.
  cbv [Deps.Rows.sum_rows_cps Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e; cbn [fst snd combine app] in e.
  cbn [Deps.RT_Extra.dlet_nd_list] in e.
  cbv [update_nth] in e.
  unfold WordByWordMontgomeryAx.A'_S3_cps at 1 in (value of e).
  cbv -[Deps.Positional.drop_high_to_length Deps.Rows.conditional_sub_cps WordByWordMontgomeryAx.A'_S3_cps] in e.
  clear uw.
  set (uw := fun i : nat => _) in (value of e).
  cbv -[Deps.Positional.drop_high_to_length Deps.Rows.conditional_sub_cps] in e.
  clear uw.
  set (uw := fun i : nat => _) in (value of e).
  cbv [Deps.Rows.conditional_sub_cps] in e.
  change uw with (uweight 64) in (value of e).
  clear uw.
  set (uw := uweight 64) in (value of e).
  cbv [Deps.Rows.sub_cps] in e.
  cbv [map_cps2] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbv [Deps.Rows.flatten_cps] in e.
  cbv [hd tl] in e.
  cbv [Deps.Rows.flatten'_cps] in e.
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e.
  cbv [Deps.Rows.sum_rows_cps Deps.Rows.sum_rows'_cps rev fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step cpscall cpsbind cpsreturn id] in e; cbn [fst snd combine app] in e.
  cbv [Deps.Rows.Deps.Positional.select] in e.
  cbn [combine map] in e.
  Print Z.zselect.
  cbv -[Deps.Positional.drop_high_to_length] in e.
  clear uw.
  set (uw := fun i : nat => _) in (value of e).
  vm_compute in e.


  cbv [] in e.

  cbv [Deps.Rows.from_columns]



  set (k := Deps.Rows.mul_cps _ _ _ _) in (value of e) at 1
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbv [List.app List.repeat] in e.
  subst k.
  cbv [Deps.Rows.mul_cps] in e.
  cbv [Deps.Rows.Deps.Positional.to_associational ] in e.
  set (k := map _ _) in (value of e).
  vm_compute in k; subst k.
  Arguments combine _ _ !_ !_.
  cbn [combine] in e.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  unfold Deps.Rows.Deps.Associational.sat_mul_cps in (value of e) at 1.
  cbv [flat_map_cps flat_map_cps_specialized] in e.
  cbv [Deps.Rows.Deps.Associational.sat_multerm_cps] in e.
  cbn [fst snd] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbv [List.app] in e.
  cbv [Z.mul Z.add Pos.mul Pos.add] in e.
  unfold Deps.Rows.from_associational_cps in (value of e) at 1.
  cbv [Deps.Rows.Deps.Columns.from_associational_cps] in e.
  cbv [Deps.Rows.Deps.Columns.nils] in e.
  cbv [repeat fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step Init.Nat.pred] in e.
  cbv [Deps.Rows.Deps.Columns.Deps.Positional.place] in e.
  cbn [fst snd] in e.
  cbv [nat_rect] in e.
  cbv [cpscall cpsbind cpsreturn] in e.
  set (k := uw 0%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 1%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 2%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 3%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 4%nat) in (value of e); vm_compute in k; subst k.
  cbv [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  cbv [Deps.Rows.Deps.Columns.cons_to_nth] in e.
  cbv [update_nth] in e.
  cbv [Deps.Rows.from_columns Deps.Rows.max_column_size Deps.Rows.from_columns' map List.repeat length Nat.max] in e.
  unfold fold_right in (value of e) at 2.
  cbn [snd] in e.
  cbv [Deps.Rows.extract_row] in e.
  cbv [map hd tl List.app] in e.
  cbv delta [fold_right] in e.
  cbn [fst snd] in e.
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [cpsbind cpscall cpsreturn id] in e.
  cbn [fst snd] in e.
  unfold Deps.Rows.sum_rows_cps at 1 in (value of e).
  cbv [cpscall cpsbind cpsreturn id Deps.Rows.sum_rows'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step rev app] in e.
  cbn [combine fst snd] in e.
  cbv [Deps.Rows.sum_rows_cps cpscall cpsbind cpsreturn id Deps.Rows.sum_rows'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step rev app] in e.
  cbn [fst snd combine] in e.
  cbv [Deps.Rows.add_cps] in e.
  cbv [Deps.Rows.flatten_cps hd tl Deps.Rows.flatten'_cps] in e.
  cbv [fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step] in e.
  cbv [cpsbind cpscall cpsreturn id] in e.
  cbn [fst snd] in e.
  unfold Deps.Rows.sum_rows_cps at 1 in (value of e).
  cbv [cpscall cpsbind cpsreturn id Deps.Rows.sum_rows'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step rev app] in e.
  cbn [combine fst snd] in e.
  cbv [Deps.Rows.sum_rows_cps cpscall cpsbind cpsreturn id Deps.Rows.sum_rows'_cps fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step rev app] in e.
  cbn [fst snd combine] in e.
  cbv [add_cps] in e.
  cbv [Deps.Rows.Deps.Associational.sat_mul_cps] in e.
  cbv [flat_map_cps flat_map_cps_specialized] in e.
  cbv [Deps.Rows.Deps.Associational.sat_multerm_cps] in e.
  cbn [fst snd] in e.
  cbv [cpscall cpsbind cpsreturn id] in e.
  cbv [List.app] in e.
  cbv [Z.mul Z.add Pos.mul Pos.add] in e.
  cbv [Deps.Rows.from_associational_cps] in e.
 cbv [Deps.Rows.Deps.Columns.from_associational_cps] in e.
 cbv [Deps.Rows.Deps.Columns.nils] in e.
 cbv [Deps.Rows.Deps.Positional.zeros] in e.
 cbv [repeat cpsbind cpscall cpsreturn] in e.
  cbv [repeat fold_right_cps2 fold_right_cps2_specialized fold_right_cps2_specialized_step Init.Nat.pred] in e.
  cbv [Deps.Rows.Deps.Columns.Deps.Positional.place] in e.
  cbn [fst snd] in e.
  cbv [nat_rect] in e.
  cbv [cpscall cpsbind cpsreturn] in e.
  set (k := uw 0%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 1%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 2%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 3%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 4%nat) in (value of e); vm_compute in k; subst k.
  set (k := uw 5%nat) in (value of e); vm_compute in k; subst k.
  Arguments Z.pow !_ !_.
  Arguments Z.mul !_ !_.
  Arguments Z.sub !_ !_.
  Arguments Z.add !_ !_.

  cbn [Z.pow Pos.pow Init.Nat.pred nat_rect fst Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Pos.iter Z.opp Z.div Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare Pos.compare_cont Z.add Z.ltb Z.sub Z.pos_sub Z.succ_double Z.double Z.pow Z.pow_pos Z.modulo Z.eqb Pos.eqb Pos.compare snd Pos.pred_double Z.opp] in e.
  cbv [Deps.Rows.Deps.Columns.cons_to_nth] in e.
  cbv [update_nth] in e.
  cbv [Deps.Rows.from_columns Deps.Rows.max_column_size Deps.Rows.from_columns' map List.repeat length Nat.max] in e.
  cbn [snd] in e.
  cbv [Deps.Rows.extract_row map hd tl List.app] in e.
  cbv delta [fold_right] in e.
  cbn [fst snd] in e.
  cbn [fst snd combine] in e.
  cbv [List.app Lis
   vm_compute in e.
  unfold fold_right in (value of e) at 2.] i
  unfold fold_right in (value of e) at 1.

  cbn [fold_right] in e.
  Deps.Rows.Deps.Columns.cons_to_nth Deps.Rows.Deps.Columns.Deps.Positional.place] in e.
  vm_compute in e.

Time Compute @hide _ (fun a b => let m := (2^256 - 2^224 + 2^192 + 2^96 - 1) in mulmod 64 4 m match Z.modinv (-m) (2^64) with
            | Some m' => m'
            | None => 0
            end (expand_list 0 a 4) (expand_list 0 b 4)).
Time Compute @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).
Time Eval cbv in @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).
Time Eval lazy in @hide _ (fun f g => ModOpsAx.carry_mulmod 51 2 (2^255) [(1,19)] 5 (List.seq 0 5 ++ [0; 1])%nat%list (expand_list 0 f 5) (expand_list 0 g 5)).


*)
