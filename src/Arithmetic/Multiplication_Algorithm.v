Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Require Import Coq.Numbers.NatInt.NZDiv.
(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Module myStuff.

Definition split_one (s:Z) (w fw : Z) (p:list (Z*Z)) :=
  let quot := fw / s in
  let hi_lo := partition (fun t => (fst t =? w)) p in
    (snd hi_lo, map (fun t => (fst t / fw, snd t * quot)) (fst hi_lo)).

Lemma mod_thing : forall a b, b <> 0 -> a mod b = 0 -> (forall c, b * (c * a / b) = c * a).
Proof.
  intros. symmetry. apply Z_div_exact_full_2.
  - apply H.
  - rewrite Z.mul_mod_full. rewrite H0. rewrite Z.mul_comm. simpl. apply Z.mod_0_l. apply H.
Qed.

Check Z_div_exact_full_2.

Lemma eval_split_one s w fw p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0):
  Associational.eval (fst (split_one s w fw p)) + s * Associational.eval (snd (split_one s w fw p)) = Associational.eval p.
Proof.
  remember (Z_div_exact_full_2 _ _ fw_nz w_fw) as H2.
  clear HeqH2 fw_nz w_fw.
  induction p as [|t p'].
  - simpl. cbv [Associational.eval]. simpl. lia.
  - cbv [split_one]. simpl. destruct (fst t =? w) eqn:E.
    + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing.
      destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
      ring_simplify. simpl.
      rewrite (Z.mul_comm s). rewrite Z.mul_assoc. rewrite <- (Z.mul_assoc _ s). rewrite <- (Z.mul_assoc).
      rewrite (Z.mul_comm s). rewrite <- (Z.mul_assoc _ s). rewrite <- (Z_div_exact_full_2 _ _ s_nz fw_s).
      rewrite Z.mul_assoc.
      rewrite Z.mul_comm. rewrite Z.mul_assoc. apply Z.eqb_eq in E. rewrite E.
      rewrite <- H2. rewrite <- IHp'. ring.
    + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing.
      destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
      rewrite <- IHp'. ring.
Qed.

Lemma reduction_rule' b s c (modulus_nz:s-c<>0) :
  (s * b) mod (s - c) = (c * b) mod (s - c).
Proof using Type. replace (s * b) with ((c*b) + b*(s-c)) by nsatz.
  rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
  (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
Proof using Type. apply Z.add_mod_Proper; [ reflexivity | apply reduction_rule', modulus_nz ]. Qed.

(*assumes that (H1 : w mod fw = 0) (H2 : fw mod s = 0) *)
Definition reduce_one (s:Z) (w fw : Z) (c:list _) (p:list _) : list (Z*Z) :=
  let lo_hi := split_one s w fw p in
  fst lo_hi ++ map (fun thing => (fst thing, snd thing * Associational.eval c)) (snd lo_hi).

Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

Lemma eval_map_mul_snd (x:Z) (p:list (Z*Z))
  : Associational.eval (List.map (fun t => (fst t, snd t * x)) p) = x * Associational.eval p.
Proof. induction p; push; nsatz. Qed.

Lemma eval_reduce_one s w fw c p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0)
                             (modulus_nz: s - Associational.eval c<>0) :
            Associational.eval (reduce_one s w fw c p) mod (s - Associational.eval c) =
            Associational.eval p mod (s - Associational.eval c).
Proof using Type.
  cbv [reduce_one]; push.
  rewrite eval_map_mul_snd.
  rewrite <-reduction_rule, eval_split_one; trivial.
Qed.

(* 'carrying down', aka borrowing *)
Definition carryterm_down (w fw:Z) (t:Z * Z) :=
    let quot := w / fw in
    if (Z.eqb (fst t) w)
      then [(quot, snd t * fw)]
      else [t].

Lemma eval_carryterm_down w fw (t:Z * Z) (fw_nz:fw<>0) (w_fw:w mod fw = 0) :
      Associational.eval (carryterm_down w fw t) = Associational.eval [t].
Proof using Type*.
  cbv [carryterm_down Let_In]; break_match; push; [|trivial].
  pose proof (Z.div_mod (snd t) fw fw_nz).
  rewrite Z.eqb_eq in *.
  remember (mod_thing _ _ fw_nz w_fw) as H'.
  ring_simplify. rewrite Z.mul_comm. rewrite Z.mul_assoc. rewrite <- (Z.mul_1_l w). rewrite H'. rewrite Heqb.
  destruct w; ring.
Qed.

Definition carry_down (w fw:Z) (p:list (Z*Z)) :=
  flat_map (carryterm_down w fw) p.

Lemma eval_carry_down w fw p (fw_nz:fw<>0) (w_fw:w mod fw = 0):
      Associational.eval (carry_down w fw p) = Associational.eval p.
Proof using Type*.
  cbv [carry_down carryterm_down]. induction p.
  - trivial.
  - push. destruct (fst a =? w) eqn:E.
    + rewrite IHp. remember (mod_thing _ _ fw_nz w_fw) as H. rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
      rewrite <- (Z.mul_1_l w). rewrite H. ring_simplify. apply Z.eqb_eq in E. rewrite E. ring.
    + rewrite IHp. ring.
Qed.




Notation "a ** b" := (Zpower_nat a b)
  (at level 41, right associativity).

Definition s := 2 ** 256.

Definition c := [(2 ** 32 + 977, 1)].

Definition prime : Z := s - Associational.eval c.

Definition limbs : nat := 5.

Definition weight n := (2 ** 52) ** n.

Lemma weight_0 : weight 0 = 1.
Proof. trivial. Qed.

Lemma weight_nz : forall i, weight i <> 0.
Proof.
  intros i. cbv [weight]. rewrite Zpower_nat_Z. apply Z.pow_nonzero.
  - rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia.
  - lia.
Qed.

Lemma s_nz : s <> 0.
Proof. discriminate. Qed.

Lemma p_nz : s - Associational.eval c <> 0.
Proof. discriminate. Qed.

Lemma mod_is_zero : forall base (n m : nat), base <> 0 -> le n m -> (base ** m) mod (base ** n) = 0.
  intros base n m H1 H2. induction H2.
  - rewrite Z_mod_same_full. constructor.
  - rewrite Zpower_nat_succ_r. rewrite Z.mul_mod_full. rewrite IHle. rewrite Z.mul_0_r.
    apply Z.mod_0_l. rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia.
Qed.

Print Associational.carry.

Compute (Associational.carry 8 2 [(8, 11); (8, 22)]).

(* When to collect terms?  Do carries first or reductions first?  *)

Definition mulmod (a b : list Z) : list Z :=
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r0a := Positional.from_associational weight (2 * limbs - 1) r0 in
  let r0b := Positional.to_associational weight (2 * limbs - 1) r0a in
  let r1 := Associational.carry (weight 8) (weight 1) r0b in
  let r2 := reduce_one s (weight 8) (weight limbs) c r1 in
  let r3 := Associational.carry (weight 3) (weight 1) r2 in
  let r4 := reduce_one s (weight 9) (weight limbs) c r3 in
  let r5 := Associational.carry (weight 4) (weight 1) r4 in
  let r6 := Associational.carry (weight 5) (weight 1) r5 in
  let r7 := carry_down (weight 5) (weight 5 / s) r6 in
  let r8 := Associational.carry (weight 4) (s / weight 4) r7 in
  let r9 := reduce_one s s s c r8 in
  let r10 := Associational.carry (weight 0) (weight 1) r9 in
  let r11 := Associational.carry (weight 6) (weight 1) r10 in
  let r12 := reduce_one s (weight 6) (weight limbs) c r11 in
  let r13 := Associational.carry (weight 1) (weight 1) r12 in
  let r14 := Associational.carry (weight 7) (weight 1) r13 in
  let r15 := reduce_one s (weight 7) (weight limbs) c r14 in
  let r16 := Associational.carry (weight 2) (weight 1) r15 in
  let r17 := reduce_one s (weight 8) (weight limbs) c r16 in
  let r18 := Associational.carry (weight 3) (weight 1) r17 in
  Positional.from_associational weight limbs r18.

Theorem mulmod_works (a b : list Z) :
        (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - Associational.eval c) =
        (Positional.eval weight limbs (mulmod a b)) mod (s - Associational.eval c).
Proof.
  cbv [mulmod].
  repeat (try erewrite Positional.eval_from_associational; try erewrite Positional.eval_to_associational;
          try erewrite Associational.eval_carry; try erewrite eval_reduce_one; try erewrite eval_carry_down).
  rewrite Associational.eval_mul. repeat rewrite Positional.eval_to_associational. reflexivity.
  all: try (left; discriminate); try discriminate; try reflexivity; try apply weight_nz.
Qed.

Definition a := [1; 2; 3; 4; 2 ** 51].
Definition b := [3; 3; 3; 3; 3].

Compute (mulmod a b).

Compute (Positional.eval weight limbs (mulmod a b) mod prime).
Compute ((Positional.eval weight limbs a * Positional.eval weight limbs b) mod prime).

Local Open Scope nat_scope.

(* want to start with i = 1, so want to start with l_minus_2_minus_i = l - 2 - 1 *)
Fixpoint loop l_minus_2_minus_i l weight s c r0 :=
  match l_minus_2_minus_i with
  | O => r0
  | S l_minus_2_minus_i' =>
    let i := (l - 2) - l_minus_2_minus_i in
    let r1 := Associational.carry (weight (i + l)) (weight 1) r0 in
    let r2 := reduce_one s (weight (i + l)) (weight l) c r1 in
    let r3 := Associational.carry (weight i) (weight 1) r2 in
    loop l_minus_2_minus_i' l weight s c r3
  end.

Definition mulmod_general limbs weight s c a b :=
  let l := limbs in
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r1 := Associational.carry (weight (2 * l - 2)) (weight 1) r0 in
  let r2 := reduce_one s (weight (2 * l - 2)) (weight l) c r1 in
  let r3 := Associational.carry (weight (l - 2)) (weight 1) r2 in
  let r4 := reduce_one s (weight (2 * l - 1)) (weight l) c r3 in
  let r5 := Associational.carry (weight (l - 1)) (weight 1) r4 in
  let r6 := Associational.carry (weight l) (weight 1) r5 in
  let r7 := carry_down (weight l) (weight l / s) r6 in
  let r8 := Associational.carry (weight (l - 1)) (s / weight (l - 1)) r7 in
  let r9 := reduce_one s s s c r8 in
  let r10 := Associational.carry (weight 0) (weight 1) r9 in
  let r11 := loop (l - 2 - 1) l weight s c r10 in
  let r12 := reduce_one s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := Associational.carry (weight (l - 2)) (weight 1) r12 in
  Positional.from_associational weight l r13.

Compute (mulmod_general limbs weight s c a b).
Compute (mulmod a b).

End myStuff.

Check Pipeline.BoundsPipelineToString.

Import Stringification.C.
Import Stringification.C.Compilers.

Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.

Local Existing Instance ToString.C.OutputCAPI.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Existing Instance default_output_options.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : emit_primitives_opt := true.

Compute (2 ^ 52).
Compute (2 ^ 52 - 1).

Definition bounds := (repeat (Some r[0 ~> 2^52 - 1]%zrange) 4) ++ [Some r[0 ~> 2^48 - 1]%zrange].

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_my_mul_u64"
        true true None [64; 128] 64
        ltac:(let r := Reify (myStuff.mulmod) in
              exact r)
               (fun _ _ => [])
               (Some bounds, (Some bounds, tt))
               (Some ((Some r[0 ~> 2^54 - 1]%zrange) :: (repeat (Some r[0 ~> 2^49 - 1]%zrange) 4)))
               (None, (None, tt))
               None
   : Pipeline.ErrorT _).
