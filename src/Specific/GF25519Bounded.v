Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Specific.GF25519Reflective.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.ModularBaseSystemWord.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.


Local Ltac cbv_tuple_map :=
  cbv [Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list' HList.hlistP HList.hlistP'].

Local Ltac post_bounded_t :=
  (* much pain and hackery to work around [Defined] taking forever *)
  cbv_tuple_map;
  let blem' := fresh "blem'" in
  let is_bounded_lem := fresh "is_bounded_lem" in
  intros is_bounded_lem blem';
  apply blem'; repeat apply conj; apply is_bounded_lem.
Local Ltac bounded_t opW blem :=
  generalize blem; generalize is_bounded_proj1_fe25519; post_bounded_t.
Local Ltac bounded_wire_digits_t opW blem :=
  generalize blem; generalize is_bounded_proj1_wire_digits; post_bounded_t.

Local Ltac define_binop f g opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f, proj1_fe25519W g)) _);
  abstract bounded_t opW blem.
Local Ltac define_unop f opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f)) _);
  abstract bounded_t opW blem.
Local Ltac define_unop_FEToZ f opW :=
  refine (opW (proj1_fe25519W f)).
Local Ltac define_unop_FEToWire f opW blem :=
  refine (exist_wire_digitsW (opW (proj1_fe25519W f)) _);
  abstract bounded_t opW blem.
Local Ltac define_unop_WireToFE f opW blem :=
  refine (exist_fe25519W (opW (proj1_wire_digitsW f)) _);
  abstract bounded_wire_digits_t opW blem.

Local Opaque Let_In.
Local Opaque Z.add Z.sub Z.mul Z.shiftl Z.shiftr Z.land Z.lor Z.eqb NToWord64.
Local Arguments interp_radd / _.
Local Arguments interp_rsub / _.
Local Arguments interp_rmul / _.
Local Arguments interp_ropp / _.
Local Arguments interp_rprefreeze / _.
Local Arguments interp_rge_modulus / _.
Local Arguments interp_rpack / _.
Local Arguments interp_runpack / _.
Definition addW (f : fe25519W * fe25519W) : fe25519W := Eval simpl in interp_radd f.
Definition subW (f : fe25519W * fe25519W) : fe25519W := Eval simpl in interp_rsub f.
Definition mulW (f : fe25519W * fe25519W) : fe25519W := Eval simpl in interp_rmul f.
Definition oppW (f : fe25519W) : fe25519W := Eval simpl in interp_ropp f.
Definition prefreezeW (f : fe25519W) : fe25519W := Eval simpl in interp_rprefreeze f.
Definition ge_modulusW (f : fe25519W) : word64 := Eval simpl in interp_rge_modulus f.
Definition packW (f : fe25519W) : wire_digitsW := Eval simpl in interp_rpack f.
Definition unpackW (f : wire_digitsW) : fe25519W := Eval simpl in interp_runpack f.

Definition modulusW :=
  Eval cbv - [ZToWord64] in (Tuple.map ZToWord64 (Tuple.from_list_default 0%Z length_fe25519 GF25519.modulus_digits_)).

Definition postfreeze : GF25519.fe25519 -> GF25519.fe25519 :=
  GF25519.postfreeze.

Lemma freeze_prepost_freeze : forall x, postfreeze (prefreeze x) = GF25519.freeze x.
Proof. reflexivity. Qed.

Definition postfreezeW : fe25519W -> fe25519W :=
      (conditional_subtract_modulusW
         (num_limbs := length_fe25519)
         modulusW
         ge_modulusW
         (Interpretations64.WordW.neg GF25519.int_width)
      ).

Definition freezeW (f : fe25519W) : fe25519W := Eval cbv beta delta [prefreezeW postfreezeW] in postfreezeW (prefreezeW f).

Local Transparent Let_In.
(* Wrapper to allow extracted code to not unfold [mulW] *)
Definition mulW_noinline := mulW.
Definition powW (f : fe25519W) chain := fold_chain_opt (proj1_fe25519W one) (fun f g => mulW_noinline (f, g)) chain [f].
Definition invW (f : fe25519W) : fe25519W
  := Eval cbv -[Let_In fe25519W mulW_noinline] in powW f (chain inv_ec).

Local Ltac port_correct_and_bounded pre_rewrite opW interp_rop rop_cb :=
  change opW with (interp_rop);
  rewrite pre_rewrite;
  intros; apply rop_cb; assumption.

Lemma addW_correct_and_bounded : ibinop_correct_and_bounded addW (Curry.curry2 carry_add).
Proof. port_correct_and_bounded interp_radd_correct addW interp_radd radd_correct_and_bounded. Qed.
Lemma subW_correct_and_bounded : ibinop_correct_and_bounded subW (Curry.curry2 carry_sub).
Proof. port_correct_and_bounded interp_rsub_correct subW interp_rsub rsub_correct_and_bounded. Qed.
Lemma mulW_correct_and_bounded : ibinop_correct_and_bounded mulW (Curry.curry2 mul).
Proof. port_correct_and_bounded interp_rmul_correct mulW interp_rmul rmul_correct_and_bounded. Qed.
Lemma oppW_correct_and_bounded : iunop_correct_and_bounded oppW carry_opp.
Proof. port_correct_and_bounded interp_ropp_correct oppW interp_ropp ropp_correct_and_bounded. Qed.
Lemma prefreezeW_correct_and_bounded : iunop_correct_and_bounded prefreezeW prefreeze.
Proof. port_correct_and_bounded interp_rprefreeze_correct prefreezeW interp_rprefreeze rprefreeze_correct_and_bounded. Qed.
Lemma ge_modulusW_correct : iunop_FEToZ_correct ge_modulusW ge_modulus.
Proof. port_correct_and_bounded interp_rge_modulus_correct ge_modulusW interp_rge_modulus rge_modulus_correct_and_bounded. Qed.
Lemma packW_correct_and_bounded : iunop_FEToWire_correct_and_bounded packW pack.
Proof. port_correct_and_bounded interp_rpack_correct packW interp_rpack rpack_correct_and_bounded. Qed.
Lemma unpackW_correct_and_bounded : iunop_WireToFE_correct_and_bounded unpackW unpack.
Proof. port_correct_and_bounded interp_runpack_correct unpackW interp_runpack runpack_correct_and_bounded. Qed.

Ltac lower_bound_minus_ge_modulus :=
  apply Z.le_0_sub;
  cbv [ge_modulus Let_In ModularBaseSystemListZOperations.cmovl ModularBaseSystemListZOperations.cmovne ModularBaseSystemListZOperations.neg];
  repeat break_if; Z.ltb_to_lt; subst; try omega;
    rewrite ?Z.land_0_l; auto;
    change Interpretations64.WordW.wordWToZ with word64ToZ;
    etransitivity; try apply Z.land_upper_bound_r; instantiate; try omega;
    apply Z.ones_nonneg; instantiate; vm_compute; discriminate.

Ltac upper_bound_minus_ge_modulus :=
   (apply Z.log2_lt_pow2_alt; [ vm_compute; reflexivity | ]);
   eapply Z.le_lt_trans; [ apply Z.le_sub_nonneg; apply Z.land_nonneg; right; omega | ];
   eapply Z.le_lt_trans; [ eassumption | ];
   instantiate; vm_compute; reflexivity.

Lemma postfreezeW_correct_and_bounded : iunop_correct_and_bounded postfreezeW postfreeze.
Proof.
  intros x H.
  pose proof (ge_modulusW_correct x H) as Hgm.
  destruct_head_hnf' prod.
  unfold_is_bounded_in H.
  destruct_head' and.
  Z.ltb_to_lt.
  cbv [postfreezeW].
  cbv [conditional_subtract_modulusW Interpretations64.WordW.neg].
  change word64ToZ with Interpretations64.WordW.wordWToZ in *.
  rewrite Hgm.

  cbv [modulusW Tuple.map].
  cbv [on_tuple List.map to_list to_list' from_list from_list'
                HList.hlistP HList.hlistP'
                Tuple.map2 on_tuple2 ListUtil.map2 fe25519WToZ length_fe25519].
  cbv [postfreeze GF25519.postfreeze].
  cbv [Let_In].

  split.
  { match goal with
    |- (_,word64ToZ (_ ^- (Interpretations64.WordW.ZToWordW ?x) ^& _)) = (_,_ - (?y &' _)) => assert (x = y) as Hxy by reflexivity; repeat rewrite <-Hxy; clear Hxy end.

    change ZToWord64 with Interpretations64.WordW.ZToWordW in *.
    preunfold_is_bounded.
  rewrite !Interpretations64.WordW.wordWToZ_sub;
  rewrite !Interpretations64.WordW.wordWToZ_land;
  rewrite !Interpretations64.WordW.wordWToZ_ZToWordW;
  try match goal with
         | |- 0 <=  ModularBaseSystemListZOperations.neg _ _ < 2 ^ _ => apply ModularBaseSystemListZOperationsProofs.neg_range; omega
         | |- 0 <= _ < 2 ^ Z.of_nat _ => vm_compute; split; [refine (fun x => match x with eq_refl => I end) | reflexivity]
         | |- 0 <= _ &' _ => apply Z.land_nonneg; right; omega
         | |- (_,_) = (_,_) => reflexivity
      end;
  try solve [
  (apply Z.log2_lt_pow2_alt; [ vm_compute; reflexivity | ]);
  eapply Z.le_lt_trans; try apply Z.land_upper_bound_r; try apply ModularBaseSystemListZOperationsProofs.neg_range; instantiate; try match goal with |- ?G => not has_evar G; vm_compute; discriminate end; reflexivity];
  match goal with
  | |- 0 <= _ - _ => lower_bound_minus_ge_modulus
  | |- Z.log2 (_ - _) < _ => upper_bound_minus_ge_modulus
  end. }


  change ZToWord64 with Interpretations64.WordW.ZToWordW in *;
  preunfold_is_bounded.
  rewrite !Interpretations64.WordW.wordWToZ_sub;
  rewrite !Interpretations64.WordW.wordWToZ_land;
  rewrite !Interpretations64.WordW.wordWToZ_ZToWordW;
  repeat match goal with |- _ /\ _ => split; Z.ltb_to_lt end;
  Z.ltb_to_lt; unfold_is_bounded; Z.ltb_to_lt;
  try match goal with
         | |- 0 <=  ModularBaseSystemListZOperations.neg _ _ < 2 ^ _ => apply ModularBaseSystemListZOperationsProofs.neg_range; omega
         | |- 0 <= _ < 2 ^ Z.of_nat _ => vm_compute; split; [refine (fun x => match x with eq_refl => I end) | reflexivity]
         | |- 0 <= _ &' _ => apply Z.land_nonneg; right; omega
      end;
  try solve [
  (apply Z.log2_lt_pow2_alt; [ vm_compute; reflexivity | ]);
  eapply Z.le_lt_trans; try apply Z.land_upper_bound_r; try apply ModularBaseSystemListZOperationsProofs.neg_range; instantiate; try match goal with |- ?G => not has_evar G; vm_compute; discriminate end; reflexivity];
  try match goal with
  | |- 0 <= _ - _ => lower_bound_minus_ge_modulus
  | |- Z.log2 (_ - _) < _ => upper_bound_minus_ge_modulus
  | |- _ - _ <= _ => etransitivity; [ apply Z.le_sub_nonneg; apply Z.land_nonneg; right; omega | instantiate; assumption ]
  | |- 0 <= ModularBaseSystemListZOperations.neg _ _ =>
    apply ModularBaseSystemListZOperationsProofs.neg_range; vm_compute; discriminate
  | |- ModularBaseSystemListZOperations.neg _ _ < _ =>
    apply ModularBaseSystemListZOperationsProofs.neg_range; vm_compute; discriminate
  | |- _ => vm_compute; (discriminate || reflexivity)
      end.
Qed.

Lemma freezeW_correct_and_bounded : iunop_correct_and_bounded freezeW freeze.
Proof.
  intros f H; rewrite <- freeze_prepost_freeze.
  change (freezeW f) with (postfreezeW (prefreezeW f)).
  destruct (prefreezeW_correct_and_bounded f H) as [H0 H1].
  destruct (postfreezeW_correct_and_bounded _ H1) as [H0' H1'].
  split; [ | assumption ].
  rewrite H0', H0; reflexivity.
Qed.

Lemma powW_correct_and_bounded chain : iunop_correct_and_bounded (fun x => powW x chain) (fun x => pow x chain).
Proof.
  cbv [powW pow].
  intro x; intros; apply (fold_chain_opt_gen fe25519WToZ is_bounded [x]).
  { reflexivity. }
  { reflexivity. }
  { intros; pose proof (fun k0 k1 X Y => proj1 (mulW_correct_and_bounded (k0, k1) (conj X Y))) as H'.
    cbv [Curry.curry2 Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list'] in H'.
    rewrite <- H' by assumption.
    apply mulW_correct_and_bounded; split; assumption. }
  { intros; rewrite (fun X Y => proj1 (mulW_correct_and_bounded (_, _) (conj X Y))) by assumption; reflexivity. }
  { intros [|?]; autorewrite with simpl_nth_default;
      (assumption || reflexivity). }
Qed.

Lemma invW_correct_and_bounded : iunop_correct_and_bounded invW inv.
Proof.
  intro f.
  assert (H : forall f, invW f = powW f (chain inv_ec))
    by abstract (cbv -[Let_In fe25519W mulW_noinline]; reflexivity).
  rewrite H.
  rewrite inv_correct.
  cbv [inv_opt].
  rewrite <- pow_correct.
  apply powW_correct_and_bounded.
Qed.

Definition fieldwisebW_sig (f g : fe25519W)
  : { b | b = GF25519.fieldwiseb (fe25519WToZ f) (fe25519WToZ g) }.
Proof.
  hnf in f, g; destruct_head' prod.
  eexists.
  cbv [GF25519.fieldwiseb fe25519WToZ].
  rewrite ?word64eqb_Zeqb.
  reflexivity.
Defined.

Definition fieldwisebW (f g : fe25519W) : bool :=
  Eval cbv [proj1_sig fieldwisebW_sig appify2 app_fe25519W] in
    appify2 (fun f g => proj1_sig (fieldwisebW_sig f g)) f g.

Lemma fieldwisebW_correct f g
  : fieldwisebW f g = GF25519.fieldwiseb (fe25519WToZ f) (fe25519WToZ g).
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (fieldwisebW_sig f' g')).
Qed.

Local Arguments freezeW : simpl never.
Local Arguments fe25519WToZ !_ / .
Local Opaque freezeW.

Definition eqbW_sig (f g : fe25519W)
  : { b | is_bounded (fe25519WToZ f) = true
          -> is_bounded (fe25519WToZ g) = true
          -> b = GF25519.eqb (fe25519WToZ f) (fe25519WToZ g) }.
Proof.
  pose proof (fun pf => proj1 (freezeW_correct_and_bounded f pf)) as frf.
  pose proof (fun pf => proj1 (freezeW_correct_and_bounded g pf)) as frg.
  hnf in f, g; destruct_head' prod.
  eexists.
  unfold GF25519.eqb.
  simpl @fe25519WToZ in *; cbv beta iota.
  intros A B; specialize_by assumption; clear A B.
  cbv [Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list' fe25519WToZ] in *.
  etransitivity. Focus 2. {
    apply f_equal2.
    apply frf.
    apply frg. } Unfocus.
  etransitivity; [ eapply fieldwisebW_correct | ].
  cbv [fe25519WToZ].
  reflexivity.
Defined.

Definition eqbW (f g : fe25519W) : bool :=
  Eval cbv [proj1_sig eqbW_sig appify2 app_fe25519W] in
    appify2 (fun f g => proj1_sig (eqbW_sig f g)) f g.

Lemma eqbW_correct f g
  : is_bounded (fe25519WToZ f) = true
    -> is_bounded (fe25519WToZ g) = true
    -> eqbW f g = GF25519.eqb (fe25519WToZ f) (fe25519WToZ g).
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (eqbW_sig f' g')).
Qed.

Definition sqrt_m1W' : fe25519W :=
  Eval vm_compute in fe25519ZToW sqrt_m1.
Definition sqrt_m1W := Eval cbv [sqrt_m1W' fe25519W_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in fe25519W_word64ize sqrt_m1W'.

Definition GF25519sqrt (x : GF25519.fe25519) : GF25519.fe25519.
Proof.
  lazymatch (eval cbv delta [GF25519.sqrt] in GF25519.sqrt) with
  | (fun powf powf_squared f => dlet a := powf in _)
    => exact (dlet powx := powW (fe25519ZToW x) (chain GF25519.sqrt_ec) in
              GF25519.sqrt (fe25519WToZ powx) (fe25519WToZ (mulW_noinline (powx, powx))) x)
  | (fun f => pow f _)
    => exact (GF25519.sqrt x)
  end.
Defined.

Definition sqrtW_sig
  : { sqrtW | iunop_correct_and_bounded sqrtW GF25519sqrt }.
Proof.
  eexists.
  unfold GF25519sqrt, GF25519.sqrt.
  intros.
  rewrite ?fe25519ZToW_WToZ.
  split.
  { etransitivity.
    Focus 2. {
      lazymatch goal with
      | [ |- _ = pow _ _ ]
        => apply powW_correct_and_bounded; assumption
      | [ |- _ = (dlet powx := _ in _) ]
        => apply Proper_Let_In_nd_changebody_eq; intros;
             set_evars;
             match goal with (* unfold the first dlet ... in, but only if it's binding a var *)
             | [ |- ?x = dlet y := fe25519WToZ ?z in ?f ]
               => is_var z; change (x = match fe25519WToZ z with y => f end)
             end;
             change sqrt_m1 with (fe25519WToZ sqrt_m1W);
             pose proof (fun X Y => proj1 (mulW_correct_and_bounded (sqrt_m1W, a) (conj X Y))) as correctness;
             let cbv_in_all _ := (cbv [fe25519WToZ Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list' fe25519WToZ Curry.curry2 HList.hlistP HList.hlistP'] in *; idtac) in
             cbv_in_all ();
               let solver _ := (repeat match goal with
                                       | _ => progress subst
                                       | _ => progress unfold fst, snd
                                       | _ => progress cbv_in_all ()
                                       | [ |- ?x /\ ?x ] => cut x; [ intro; split; assumption | ]
                                       | [ |- is_bounded ?op = true ]
                                         => let H := fresh in
                                            lazymatch op with
                                            | context[mulW (_, _)] => pose proof mulW_correct_and_bounded as H
                                            | context[mulW_noinline (_, _)] => pose proof mulW_correct_and_bounded as H
                                            | context[powW _ _] => pose proof powW_correct_and_bounded as H
                                            | context[sqrt_m1W] => vm_compute; reflexivity
                                            | _ => assumption
                                            end;
                                            cbv_in_all ();
                                            apply H
                                       end) in
               rewrite <- correctness by solver (); clear correctness;
                 let lem := fresh in
                 pose proof eqbW_correct as lem; cbv_in_all (); rewrite <- lem by solver (); clear lem;
                   pose proof (pull_bool_if fe25519WToZ) as lem; cbv_in_all (); rewrite lem by solver (); clear lem;
                     subst_evars; reflexivity
      end.
    } Unfocus.
    assert (Hfold : forall x, fe25519WToZ x = fe25519WToZ x) by reflexivity.
    unfold fe25519WToZ at 2 in Hfold.
    etransitivity.
    Focus 2. {
      apply Proper_Let_In_nd_changebody; [ reflexivity | intro ].
      apply Hfold.
    } Unfocus.
    clear Hfold.
    lazymatch goal with
    | [ |- context G[dlet x := ?v in fe25519WToZ (@?f x)] ]
      => let G' := context G[fe25519WToZ (dlet x := v in f x)] in
         cut G'; cbv beta;
           [ cbv [Let_In]; exact (fun x => x) | apply f_equal ]
    | _ => idtac
    end;
      reflexivity.
  }

  { cbv [Let_In HList.hlistP HList.hlistP'];
      try break_if;
      repeat lazymatch goal with
             | [ |- is_bounded (?WToZ (powW _ _)) = true ]
               => apply powW_correct_and_bounded; assumption
             | [ |- is_bounded (snd (?WToZ (_, powW _ _))) = true ]
               => generalize powW_correct_and_bounded;
                    cbv [snd Tuple.map Tuple.on_tuple Tuple.to_list Tuple.to_list' List.map Tuple.from_list Tuple.from_list' HList.hlistP HList.hlistP'];
                    let H := fresh in intro H; apply H; assumption
             | [ |- is_bounded (?WToZ (mulW (_, _))) = true ]
               => apply mulW_correct_and_bounded; split; [ vm_compute; reflexivity | ]
             end.
  }
Defined.

Definition sqrtW (f : fe25519W) : fe25519W :=
  Eval cbv [proj1_sig sqrtW_sig app_fe25519W] in
    app_fe25519W f (proj1_sig sqrtW_sig).

Lemma sqrtW_correct_and_bounded : iunop_correct_and_bounded sqrtW GF25519sqrt.
Proof.
  intro f.
  set (f' := f).
  hnf in f; destruct_head' prod.
  assert (H : sqrtW f' = proj1_sig sqrtW_sig f')
    by (subst f'; cbv beta iota delta [proj1_sig sqrtW_sig sqrtW]; reflexivity).
  rewrite H.
  exact (proj2_sig sqrtW_sig f').
Qed.



Definition add (f g : fe25519) : fe25519.
Proof. define_binop f g addW addW_correct_and_bounded. Defined.
Definition sub (f g : fe25519) : fe25519.
Proof. define_binop f g subW subW_correct_and_bounded. Defined.
Definition mul (f g : fe25519) : fe25519.
Proof. define_binop f g mulW mulW_correct_and_bounded. Defined.
Definition opp (f : fe25519) : fe25519.
Proof. define_unop f oppW oppW_correct_and_bounded. Defined.
Definition freeze (f : fe25519) : fe25519.
Proof. define_unop f freezeW freezeW_correct_and_bounded. Defined.
Definition ge_modulus (f : fe25519) : word64.
Proof. define_unop_FEToZ f ge_modulusW. Defined.
Definition pack (f : fe25519) : wire_digits.
Proof. define_unop_FEToWire f packW packW_correct_and_bounded. Defined.
Definition unpack (f : wire_digits) : fe25519.
Proof. define_unop_WireToFE f unpackW unpackW_correct_and_bounded. Defined.

Definition pow (f : fe25519) (chain : list (nat * nat)) : fe25519.
Proof. define_unop f (fun x => powW x chain) powW_correct_and_bounded. Defined.
Definition inv (f : fe25519) : fe25519.
Proof. define_unop f invW (fun x p => proj2 (invW_correct_and_bounded x p)). Defined.
Definition sqrt (f : fe25519) : fe25519.
Proof. define_unop f sqrtW sqrtW_correct_and_bounded. Defined.

Local Ltac op_correct_t op opW_correct_and_bounded :=
  cbv [op];
  lazymatch goal with
  | [ |- context[proj1_fe25519 (exist_fe25519W _ _)] ]
    => rewrite proj1_fe25519_exist_fe25519W
  | [ |- context[proj1_wire_digits (exist_wire_digitsW _ _)] ]
    => rewrite proj1_wire_digits_exist_wire_digitsW
  | _ => idtac
  end;
  generalize opW_correct_and_bounded;
  cbv_tuple_map;
  cbv [fst snd];
  let H := fresh in
  intro H; apply H;
  repeat match goal with |- and _ _ => apply conj end;
  lazymatch goal with
  | [ |- is_bounded _ = true ]
    => apply is_bounded_proj1_fe25519
  | [ |- wire_digits_is_bounded _ = true ]
    => apply is_bounded_proj1_wire_digits
  end.

Lemma add_correct (f g : fe25519) : proj1_fe25519 (add f g) = carry_add (proj1_fe25519 f) (proj1_fe25519 g).
Proof. op_correct_t add addW_correct_and_bounded. Qed.
Lemma sub_correct (f g : fe25519) : proj1_fe25519 (sub f g) = carry_sub (proj1_fe25519 f) (proj1_fe25519 g).
Proof. op_correct_t sub subW_correct_and_bounded. Qed.
Lemma mul_correct (f g : fe25519) : proj1_fe25519 (mul f g) = GF25519.mul (proj1_fe25519 f) (proj1_fe25519 g).
Proof. op_correct_t mul mulW_correct_and_bounded. Qed.
Lemma opp_correct (f : fe25519) : proj1_fe25519 (opp f) = carry_opp (proj1_fe25519 f).
Proof. op_correct_t opp oppW_correct_and_bounded. Qed.
Lemma freeze_correct (f : fe25519) : proj1_fe25519 (freeze f) = GF25519.freeze (proj1_fe25519 f).
Proof. op_correct_t freeze freezeW_correct_and_bounded. Qed.
Lemma ge_modulus_correct (f : fe25519) : word64ToZ (ge_modulus f) = GF25519.ge_modulus (proj1_fe25519 f).
Proof. op_correct_t ge_modulus ge_modulusW_correct. Qed.
Lemma pack_correct (f : fe25519) : proj1_wire_digits (pack f) = GF25519.pack (proj1_fe25519 f).
Proof. op_correct_t pack packW_correct_and_bounded. Qed.
Lemma unpack_correct (f : wire_digits) : proj1_fe25519 (unpack f) = GF25519.unpack (proj1_wire_digits f).
Proof. op_correct_t unpack unpackW_correct_and_bounded. Qed.
Lemma pow_correct (f : fe25519) chain : proj1_fe25519 (pow f chain) = GF25519.pow (proj1_fe25519 f) chain.
Proof. op_correct_t pow (powW_correct_and_bounded chain). Qed.
Lemma inv_correct (f : fe25519) : proj1_fe25519 (inv f) = GF25519.inv (proj1_fe25519 f).
Proof. op_correct_t inv (fun x p => proj1 (invW_correct_and_bounded x p)). Qed.
Lemma sqrt_correct (f : fe25519) : proj1_fe25519 (sqrt f) = GF25519sqrt (proj1_fe25519 f).
Proof. op_correct_t sqrt sqrtW_correct_and_bounded. Qed.

Import Morphisms.

Local Existing Instance prime_modulus.

Lemma field25519_and_homomorphisms
  : @field fe25519 eq zero one opp add sub mul inv div
    /\ @Ring.is_homomorphism (F _) (@Logic.eq _) 1%F F.add F.mul fe25519 eq one add mul encode
    /\ @Ring.is_homomorphism fe25519 eq one add mul (F _) (@Logic.eq _) 1%F F.add F.mul decode.
Proof.
  eapply @Field.field_and_homomorphism_from_redundant_representation.
  { exact (F.field_modulo _). }
  { cbv [decode encode]; intros; rewrite !proj1_fe25519_exist_fe25519; apply encode_rep. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { cbv [decode encode]; intros; rewrite opp_correct, carry_opp_correct, carry_opp_opt_correct, carry_opp_rep; apply opp_rep; reflexivity. }
  { cbv [decode encode]; intros; rewrite add_correct, carry_add_correct, carry_add_opt_correct, carry_add_rep; apply add_rep; reflexivity. }
  { cbv [decode encode]; intros; rewrite sub_correct, carry_sub_correct, carry_sub_opt_correct, carry_sub_rep; apply sub_rep; reflexivity. }
  { cbv [decode encode]; intros; rewrite mul_correct, GF25519.mul_correct, carry_mul_opt_correct by reflexivity; apply carry_mul_rep; reflexivity. }
  { cbv [decode encode]; intros; rewrite inv_correct, GF25519.inv_correct, inv_opt_correct by reflexivity; apply inv_rep; reflexivity. }
  { cbv [decode encode div]; intros; rewrite !proj1_fe25519_exist_fe25519; apply encode_rep. }
Qed.

Global Instance field25519 : @field fe25519 eq zero one opp add sub mul inv div := proj1 field25519_and_homomorphisms.

Local Opaque proj1_fe25519 exist_fe25519 proj1_fe25519W exist_fe25519W.
Global Instance homomorphism_F25519_encode
  : @Ring.is_homomorphism (F modulus) Logic.eq F.one F.add F.mul fe25519 eq one add mul encode.
Proof. apply field25519_and_homomorphisms. Qed.

Global Instance homomorphism_F25519_decode
  : @Ring.is_homomorphism fe25519 eq one add mul (F modulus) Logic.eq F.one F.add F.mul decode.
Proof. apply field25519_and_homomorphisms. Qed.
