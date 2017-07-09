Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Util.Sigma.Lift.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.BinPos.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.

Definition wt (i:nat) : Z := Z.shiftl 1 (128*Z.of_nat i).
Definition r := Eval compute in (2^128)%positive.
Definition sz := 2%nat.
Definition m : positive := 2^256-2^224+2^192+2^96-1.
Definition p256 :=
  Eval vm_compute in
    ((Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (Z.pos m))).
Definition r' := Eval vm_compute in Zpow_facts.Zpow_mod (Z.pos r) (Z.pos m - 2) (Z.pos m).
Definition r'_correct := eq_refl : ((Z.pos r * r') mod (Z.pos m) = 1)%Z.
Definition m' : Z := Eval vm_compute in Option.invert_Some (Z.modinv_fueled 10 (-Z.pos m) (Z.pos r)).
Definition m'_correct := eq_refl : ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r)%Z.
Definition m_p256 := eq_refl (Z.pos m) <: Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) p256.

Lemma r'_pow_correct : ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) p256 = 1)%Z.
Proof. vm_compute; reflexivity. Qed.

Definition mulmod_256' : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
                        | forall (A B : Tuple.tuple Z sz),
                               f A B =
                               (redc (r:=r)(R_numlimbs:=sz) p256 A B m')
                            }.
Proof.
  eapply (lift2_sig (fun A B c => c = _)); eexists.
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp Let_In].
  (*
  cbv [
      r wt sz p256
        CPSUtil.Tuple.tl_cps CPSUtil.Tuple.hd_cps
       CPSUtil.to_list_cps CPSUtil.to_list'_cps CPSUtil.to_list_cps' CPSUtil.flat_map_cps CPSUtil.fold_right_cps
       CPSUtil.map_cps CPSUtil.Tuple.left_append_cps CPSUtil.firstn_cps CPSUtil.combine_cps CPSUtil.on_tuple_cps CPSUtil.update_nth_cps CPSUtil.from_list_default_cps CPSUtil.from_list_default'_cps
       fst snd length List.seq List.hd List.app
       redc pre_redc_cps redc_cps redc_loop_cps redc_body_cps
       Positional.to_associational_cps
       MontgomeryAPI.divmod_cps
       MontgomeryAPI.conditional_sub_cps
       MontgomeryAPI.scmul_cps
       uweight
       MontgomeryAPI.Columns.mul_cps
       MontgomeryAPI.Associational.mul_cps
       (*Z.of_nat Pos.of_succ_nat  Nat.pred
       Z.pow Z.pow_pos Z.mul Pos.iter Pos.mul Pos.succ*)
       Tuple.hd Tuple.append Tuple.tl Tuple.hd' Tuple.tl' CPSUtil.Tuple.left_tl_cps CPSUtil.Tuple.left_hd_cps CPSUtil.Tuple.hd_cps CPSUtil.Tuple.tl_cps
       CPSUtil.Tuple.map2_cps
       MontgomeryAPI.Columns.from_associational_cps
       MontgomeryAPI.Associational.multerm_cps
       MontgomeryAPI.Positional.sat_add_cps
       MontgomeryAPI.Positional.sat_sub_cps
       MontgomeryAPI.Positional.chain_op_cps
       MontgomeryAPI.Positional.chain_op'_cps
       MontgomeryAPI.Columns.compact_cps
       MontgomeryAPI.Columns.compact_step_cps
       MontgomeryAPI.Columns.compact_digit_cps
       MontgomeryAPI.drop_high_cps
       MontgomeryAPI.add_cps
       MontgomeryAPI.add_S1_cps
       MontgomeryAPI.Columns.add_cps
       MontgomeryAPI.Columns.cons_to_nth_cps
       Nat.pred
       MontgomeryAPI.join0
       MontgomeryAPI.join0_cps CPSUtil.Tuple.left_append_cps
       CPSUtil.Tuple.mapi_with_cps
       id
       Positional.zeros MontgomeryAPI.zero MontgomeryAPI.Columns.nils Tuple.repeat Tuple.append
       Positional.place_cps
       CPSUtil.Tuple.mapi_with'_cps Tuple.hd Tuple.hd' Tuple.tl Tuple.tl' CPSUtil.Tuple.hd_cps CPSUtil.Tuple.tl_cps fst snd
       Z.of_nat fst snd Z.pow Z.pow_pos Pos.of_succ_nat Z.div Z.mul Pos.mul Z.modulo Z.div_eucl Z.pos_div_eucl Z.leb Z.compare Pos.compare_cont Pos.compare Z.pow_pos Pos.iter Z.mul Pos.succ Z.ltb Z.gtb Z.geb Z.div Z.sub Z.pos_sub Z.add Z.opp Z.double
       Decidable.dec Decidable.dec_eq_Z Z.eq_dec Z_rec Z_rec Z_rect
       Positional.zeros MontgomeryAPI.zero MontgomeryAPI.Columns.nils Tuple.repeat Tuple.append
       (*
       MontgomeryAPI.Associational.multerm_cps
       MontgomeryAPI.Columns.from_associational_cps Positional.place_cps MontgomeryAPI.Columns.cons_to_nth_cps MontgomeryAPI.Columns.nils
Tuple.append
Tuple.from_list Tuple.from_list'
Tuple.from_list_default Tuple.from_list_default'
Tuple.hd
Tuple.repeat
Tuple.tl
Tuple.tuple *)
       (* MontgomeryAPI.add_cps MontgomeryAPI.divmod_cps MontgomeryAPI.drop_high_cps MontgomeryAPI.scmul_cps MontgomeryAPI.zero MontgomeryAPI.Columns.mul_cps MontgomeryAPI.Columns.add_cps uweight MontgomeryAPI.T *)
            (*
            CPSUtil.to_list_cps CPSUtil.to_list'_cps CPSUtil.to_list_cps'
Positional.zeros
Tuple.to_list
Tuple.to_list'
List.hd
List.tl
Nat.max
Positional.to_associational_cps
Z.of_nat *)
    ].
  Unset Printing Notations.

  (* cbv -[runtime_add runtime_mul LetIn.Let_In Definitions.Z.add_get_carry_full Definitions.Z.mul_split]. *)

  (* basesystem_partial_evaluation_RHS. *)
   *)
  reflexivity.
Defined.

Definition mulmod_256'' : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
                        | forall (A B : Tuple.tuple Z sz),
                            small (Z.pos r) A -> small (Z.pos r) B ->
                            let eval := MontgomeryAPI.eval (Z.pos r) in
                            (small (Z.pos r) (f A B)
                             /\ (eval B < eval p256 -> 0 <= eval (f A B) < eval p256)
                             /\ (eval (f A B) mod Z.pos m
                                 = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
                            }.
Proof.
  exists (proj1_sig mulmod_256').
  abstract (
      intros; rewrite (proj2_sig mulmod_256');
      split; [ | split ];
      [ apply small_redc with (ri:=r') | apply redc_bound_N with (ri:=r') | apply redc_mod_N ];
      try match goal with
          | _ => assumption
          | [ |- _ = _ :> Z ] => vm_compute; reflexivity
          | _ => reflexivity
          | [ |- small (Z.pos r) p256 ]
            => hnf; cbv [Tuple.to_list sz p256 r Tuple.to_list' List.In]; intros; destruct_head'_or;
               subst; try lia
          | [ |- MontgomeryAPI.eval (Z.pos r) p256 <> 0%Z ]
            => vm_compute; lia
          end
    ).
Defined.

Definition add' : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
                 | forall (A B : Tuple.tuple Z sz),
                     f A B =
                     (add (r:=r)(R_numlimbs:=sz) p256 A B)
                 }.
Proof.
  eapply (lift2_sig (fun A B c => c = _)); eexists.
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp Let_In].
  reflexivity.
Defined.

Definition sub' : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
                 | forall (A B : Tuple.tuple Z sz),
                     f A B =
                     (sub (r:=r) (R_numlimbs:=sz) p256 A B)
                 }.
Proof.
  eapply (lift2_sig (fun A B c => c = _)); eexists.
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp Let_In].
  reflexivity.
Defined.

Definition opp' : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz
                 | forall (A : Tuple.tuple Z sz),
                     f A =
                     (opp (r:=r) (R_numlimbs:=sz) p256 A)
                 }.
Proof.
  eapply (lift1_sig (fun A c => c = _)); eexists.
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp Let_In].
  reflexivity.
Defined.

Definition nonzero' : { f:Tuple.tuple Z sz -> Z
                      | forall (A : Tuple.tuple Z sz),
                          f A =
                          (nonzero (R_numlimbs:=sz) A)
                      }.
Proof.
  eapply (lift1_sig (fun A c => c = _)); eexists.
  cbv -[runtime_lor Let_In].
  reflexivity.
Defined.

Import ModularArithmetic.

(*Definition mulmod_256 : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
                        | forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
                                 (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
                            small (Z.pos r) (f A B)
                            /\ (let eval := MontgomeryAPI.eval (Z.pos r) in
                                0 <= eval (f A B) < Z.pos r^Z.of_nat sz
                                /\ (eval (f A B) mod Z.pos m
                                    = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
                        }.
Proof.*)

(** TODO: MOVE ME *)
Definition montgomery_to_F (v : Z) : F m
  := (F.of_Z m v * F.of_Z m (r'^Z.of_nat sz)%Z)%F.

Definition mulmod_256_ext
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
              (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
          montgomery_to_F (eval (f A B))
          = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F)
      /\ (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
                 (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
             (eval B < eval p256 -> 0 <= eval (f A B) < eval p256)%Z) }.
Proof.
  exists (proj1_sig mulmod_256'').
  abstract (
      split; intros A Asm B Bsm;
      pose proof (proj2_sig mulmod_256'' A B Asm Bsm) as H;
      cbv zeta in *;
      try solve [ destruct_head'_and; assumption ];
      rewrite ModularArithmeticTheorems.F.eq_of_Z_iff in H;
      unfold montgomery_to_F;
      destruct H as [H1 [H2 H3]];
      rewrite H3;
      rewrite <- !ModularArithmeticTheorems.F.of_Z_mul;
      f_equal; nia
    ).
Defined.

Definition mulmod_256
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
             (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
        montgomery_to_F (eval (f A B))
        = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F }.
Proof.
  let v := (eval cbv [proj1_sig mulmod_256_ext mulmod_256'' mulmod_256' lift2_sig] in (proj1_sig mulmod_256_ext)) in
  (exists v).
  abstract apply (proj2_sig mulmod_256_ext).
Defined.

Lemma mulmod_256_bounded
  : let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
           (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
      (eval B < eval p256 -> 0 <= eval (proj1_sig mulmod_256 A B) < eval p256)%Z.
Proof. apply (proj2_sig mulmod_256_ext). Qed.

Local Ltac t_fin :=
  [ > reflexivity
  | repeat match goal with
           | _ => assumption
           | [ |- _ = _ :> Z ] => vm_compute; reflexivity
           | _ => reflexivity
           | [ |- small (Z.pos r) p256 ]
             => hnf; cbv [Tuple.to_list sz p256 r Tuple.to_list' List.In]; intros; destruct_head'_or;
                subst; try lia
           | [ |- MontgomeryAPI.eval (Z.pos r) p256 <> 0%Z ]
             => vm_compute; lia
           | [ |- and _ _ ] => split
           | [ |- (0 <= MontgomeryAPI.eval (Z.pos r) _)%Z ] => apply MontgomeryAPI.eval_small
           end.. ].

Definition add_ext
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
               (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
           (eval A < eval p256
            -> eval B < eval p256
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F))
       /\ (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
                  (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
              (eval A < eval p256
               -> eval B < eval p256
               -> 0 <= eval (f A B) < eval p256)))%Z }.
Proof.
  exists (proj1_sig add').
  abstract (
      split; intros; rewrite (proj2_sig add');
      unfold montgomery_to_F; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_add;
      rewrite <- ?Z.mul_add_distr_r;
      [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_p256; push_Zmod; rewrite eval_add_mod_N; pull_Zmod
      | apply add_bound ];
      t_fin
    ).
Defined.

Definition sub_ext
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
               (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
           (eval A < eval p256
            -> eval B < eval p256
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F))
       /\ (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
                  (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
              (eval A < eval p256
               -> eval B < eval p256
               -> 0 <= eval (f A B) < eval p256)))%Z }.
Proof.
  exists (proj1_sig sub').
  abstract (
      split; intros; rewrite (proj2_sig sub');
      unfold montgomery_to_F; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_sub;
      rewrite <- ?Z.mul_sub_distr_r;
      [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_p256; push_Zmod; rewrite eval_sub_mod_N; pull_Zmod
      | apply sub_bound ];
      t_fin
    ).
Defined.

Definition opp_ext
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
           (eval A < eval p256
            -> montgomery_to_F (eval (f A))
               = (F.opp (montgomery_to_F (eval A)))%F))
       /\ (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
              (eval A < eval p256
               -> 0 <= eval (f A) < eval p256)))%Z }.
Proof.
  exists (proj1_sig opp').
  abstract (
      split; intros; rewrite (proj2_sig opp');
      unfold montgomery_to_F; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?F_of_Z_opp;
      rewrite <- ?Z.mul_opp_l;
      [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_p256; push_Zmod; rewrite eval_opp_mod_N; pull_Zmod
      | apply opp_bound ];
      t_fin
    ).
Defined.

Definition nonzero_ext
  : { f:Tuple.tuple Z sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
        (eval A < eval p256
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }.
Proof.
  exists (proj1_sig nonzero').
  abstract (
      intros eval A H **; rewrite (proj2_sig nonzero'), (@eval_nonzero r) by (eassumption || reflexivity);
      subst eval;
      unfold montgomery_to_F, uweight in *; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul;
      rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_p256;
      let H := fresh in
      split; intro H;
      [ rewrite H; autorewrite with zsimplify_const; reflexivity
      | cut ((MontgomeryAPI.eval (Z.pos r) A * (r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz)) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) p256 = 0)%Z;
        [ rewrite Z.mul_mod, r'_pow_correct; autorewrite with zsimplify_const; pull_Zmod; [ | vm_compute; congruence ];
          rewrite Z.mod_small; [ trivial | split; try assumption; apply MontgomeryAPI.eval_small; try assumption; lia ]
        | rewrite Z.mul_assoc, Z.mul_mod, H by (vm_compute; congruence); autorewrite with zsimplify_const; reflexivity ] ]
    ).
Defined.

Definition add
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
             (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
        (eval A < eval p256
         -> eval B < eval p256
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F)%Z }.
Proof.
  let v := (eval cbv [proj1_sig add_ext add' lift2_sig] in (proj1_sig add_ext)) in
  (exists v).
  abstract apply (proj2_sig add_ext).
Defined.

Lemma add_bounded
  : let eval := MontgomeryAPI.eval (Z.pos r) in
    (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
            (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
        (eval A < eval p256
         -> eval B < eval p256
         -> 0 <= eval (proj1_sig add A B) < eval p256))%Z.
Proof. apply (proj2_sig add_ext). Qed.

Definition sub
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
             (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
        (eval A < eval p256
         -> eval B < eval p256
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F)%Z }.
Proof.
  let v := (eval cbv [proj1_sig sub_ext sub' lift2_sig] in (proj1_sig sub_ext)) in
  (exists v).
  abstract apply (proj2_sig sub_ext).
Defined.

Lemma sub_bounded
  : let eval := MontgomeryAPI.eval (Z.pos r) in
    (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A)
            (B : Tuple.tuple Z sz) (_ : small (Z.pos r) B),
        (eval A < eval p256
         -> eval B < eval p256
         -> 0 <= eval (proj1_sig sub A B) < eval p256))%Z.
Proof. apply (proj2_sig sub_ext). Qed.

Definition opp
  : { f:Tuple.tuple Z sz -> Tuple.tuple Z sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
        (eval A < eval p256
         -> montgomery_to_F (eval (f A))
            = (F.opp (montgomery_to_F (eval A)))%F)%Z }.
Proof.
  let v := (eval cbv [proj1_sig opp_ext opp' lift1_sig] in (proj1_sig opp_ext)) in
  (exists v).
  abstract apply (proj2_sig opp_ext).
Defined.

Lemma opp_bounded
  : let eval := MontgomeryAPI.eval (Z.pos r) in
    (forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
        (eval A < eval p256
         -> 0 <= eval (proj1_sig opp A) < eval p256))%Z.
Proof. apply (proj2_sig opp_ext). Qed.

Definition nonzero
  : { f:Tuple.tuple Z sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Tuple.tuple Z sz) (_ : small (Z.pos r) A),
        (eval A < eval p256
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }.
Proof.
  let v := (eval cbv [proj1_sig nonzero_ext nonzero' lift1_sig] in (proj1_sig nonzero_ext)) in
  (exists v).
  abstract apply (proj2_sig nonzero_ext).
Defined.


Local Definition for_assumptions := (mulmod_256, add, sub, opp, nonzero).
Print Assumptions for_assumptions.
