Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN aliases for word extraction *)
Definition word64 := Word.word 64.
Coercion word64ToZ (x : word64) : Z
  := Z.of_N (wordToN x).
Coercion ZToWord64 (x : Z) : word64 := NToWord _ (Z.to_N x).

(* END aliases for word extraction *)

Local Arguments Z.pow_pos !_ !_ / .
Lemma ZToWord64ToZ x : 0 <= x < 2^64 -> word64ToZ (ZToWord64 x) = x.
Proof.
  intros; unfold word64ToZ, ZToWord64.
  rewrite ?wordToN_NToWord_idempotent, ?N2Z.id, ?Z2N.id
    by (omega || apply N2Z.inj_lt; rewrite ?N2Z.id, ?Z2N.id by omega; simpl in *; omega).
  reflexivity.
Qed.

(* BEGIN precomputation. *)
Local Notation b_of exp := (0, 2^exp + 2^(exp-3))%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
Local Notation Z_of exp := { v : Z | fst (b_of exp) <= v <= snd (b_of exp) }.
Local Notation word_of exp := { v : word64 | fst (b_of exp) <= v <= snd (b_of exp) }.
Definition bounds : list (Z * Z)
  := Eval compute in
      [b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26; b_of 25; b_of 26].

Definition fe25519W := Eval cbv -[word64] in (tuple word64 (length limb_widths)).
Definition fe25519WToZ (x : fe25519W) : Specific.GF25519.fe25519
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (x0 : Z, x1 : Z, x2 : Z, x3 : Z, x4 : Z, x5 : Z, x6 : Z, x7 : Z, x8 : Z, x9 : Z).
Definition fe25519ZToW (x : Specific.GF25519.fe25519) : fe25519W
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (x0 : word64, x1 : word64, x2 : word64, x3 : word64, x4 : word64, x5 : word64, x6 : word64, x7 : word64, x8 : word64, x9 : word64).
Definition fe25519 :=
  Eval cbv [fst snd] in
    let sanity := eq_refl : length bounds = length limb_widths in
    (word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26 * word_of 25 * word_of 26)%type.
Definition proj1_fe25519W (x : fe25519) : fe25519W
  := let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
     (proj1_sig x0, proj1_sig x1, proj1_sig x2, proj1_sig x3, proj1_sig x4,
      proj1_sig x5, proj1_sig x6, proj1_sig x7, proj1_sig x8, proj1_sig x9).
Coercion proj1_fe25519 (x : fe25519) : Specific.GF25519.fe25519
  := fe25519WToZ (proj1_fe25519W x).
Definition is_bounded (x : Specific.GF25519.fe25519) : bool
  := let res := Tuple.map2
                  (fun bounds v =>
                     let '(lower, upper) := bounds in
                     (lower <=? v) && (v <=? upper))%bool%Z
                  (Tuple.from_list _ (List.rev bounds) eq_refl) x in
     List.fold_right andb true (Tuple.to_list _ res).

Lemma is_bounded_proj1_fe25519 (x : fe25519) : is_bounded (proj1_fe25519 x) = true.
Proof.
  refine (let '(exist x0 p0, exist x1 p1, exist x2 p2, exist x3 p3, exist x4 p4,
                exist x5 p5, exist x6 p6, exist x7 p7, exist x8 p8, exist x9 p9)
            as x := x return is_bounded (proj1_fe25519 x) = true in
          _).
  cbv [is_bounded proj1_fe25519 proj1_fe25519W fe25519WToZ to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj1_sig].
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [fold_right List.map].
  cbv beta in *.
  repeat split; rewrite !Bool.andb_true_iff, !Z.leb_le;
    assumption.
Qed.

(* Make small [vm_computable] versions of proofs *)
Definition correct_le_le {l v u} : l <= v <= u -> l <= v <= u.
Proof.
  intro pf; pose proof (proj1 pf) as pf1; pose proof (proj2 pf) as pf2; clear pf;
    split; hnf in *;
      lazymatch goal with
      | [ H : ?x = Gt -> False |- ?x = Gt -> False ]
        => revert H;
             refine match x as y return (y = Gt -> False) -> y = Gt -> False with
                    | Gt => fun f => f
                    | _ => fun _ pf => match pf with
                                       | eq_refl => I
                                       end
                    end
      end.
Defined.

(** TODO: Turn this into a lemma to speed up proofs *)
Local Ltac unfold_is_bounded_in H :=
  unfold is_bounded, fe25519WToZ in H;
  cbv [to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app] in H;
  rewrite !Bool.andb_true_iff, !Z.leb_le in H.

Definition Pow2_64 := Eval compute in 2^64.
Definition unfold_Pow2_64 : 2^64 = Pow2_64 := eq_refl.

Definition exist_fe25519W (x : fe25519W) : is_bounded (fe25519WToZ x) = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded (fe25519WToZ x) = true -> fe25519 in
          fun H => (fun H' => (exist _ x0 _, exist _ x1 _, exist _ x2 _, exist _ x3 _, exist _ x4 _,
                               exist _ x5 _, exist _ x6 _, exist _ x7 _, exist _ x8 _, exist _ x9 _))
                     (let H' := proj1 (@fold_right_andb_true_iff_fold_right_and_True _) H in
                      _));
    [
    | | | | | | | | |
    | clearbody H'; clear H x;
      unfold_is_bounded_in H';
      exact H' ];
    destruct_head and; auto.
Defined.

Definition exist_fe25519' (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  intro H; apply (exist_fe25519W (fe25519ZToW x)).
  abstract (
      hnf in x; destruct_head prod;
      pose proof H as H';
      unfold_is_bounded_in H;
      destruct_head and;
      rewrite !ZToWord64ToZ by (simpl; omega);
      assumption
    ).
Defined.

Definition exist_fe25519 (x : Specific.GF25519.fe25519) : is_bounded x = true -> fe25519.
Proof.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return is_bounded x = true -> fe25519 in
          fun H => _).
  let v := constr:(exist_fe25519' (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) H) in
  let rec do_refine v :=
      first [ let v' := (eval cbv [exist_fe25519W fe25519ZToW exist_fe25519' proj1_sig snd fst] in (proj1_sig v)) in
              refine (exist _ v' (correct_le_le _)); abstract exact (proj2_sig v)
            | let v' := (eval cbv [exist_fe25519W fe25519ZToW exist_fe25519' proj1_sig snd fst] in (proj1_sig (snd v))) in
              refine (_, exist _ v' (correct_le_le _));
              [ do_refine (fst v) | abstract exact (proj2_sig (snd v)) ] ] in
  do_refine v.
Defined.

Lemma proj1_fe25519_exist_fe25519W x pf : proj1_fe25519 (exist_fe25519W x pf) = fe25519WToZ x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded (fe25519WToZ x) = true, proj1_fe25519 (exist_fe25519W x pf) = fe25519WToZ x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_fe25519W_exist_fe25519 x pf : proj1_fe25519W (exist_fe25519 x pf) = fe25519ZToW x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded x = true, proj1_fe25519W (exist_fe25519 x pf) = fe25519ZToW x in
          fun pf => _).
  reflexivity.
Qed.
Lemma proj1_fe25519_exist_fe25519 x pf : proj1_fe25519 (exist_fe25519 x pf) = x.
Proof.
  revert pf.
  refine (let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) as x := x return forall pf : is_bounded x = true, proj1_fe25519 (exist_fe25519 x pf) = x in
          fun pf => _).
  cbv [proj1_fe25519 exist_fe25519 proj1_fe25519W fe25519WToZ proj1_sig].
  unfold_is_bounded_in pf.
  destruct_head and.
  rewrite !ZToWord64ToZ by (rewrite unfold_Pow2_64; cbv [Pow2_64]; omega).
  reflexivity.
Qed.

(* END precomputation *)

(* Precompute constants *)

Definition one := Eval cbv -[Z.le] in exist_fe25519 Specific.GF25519.one_ eq_refl.

Definition zero := Eval cbv -[Z.le] in exist_fe25519 Specific.GF25519.zero_ eq_refl.

Axiom ExprBinOp : Type.
Axiom ExprUnOp : Type.
Axiom interp_bexpr : ExprBinOp -> fe25519W -> fe25519W -> fe25519W.
Axiom interp_uexpr : ExprUnOp -> fe25519W -> fe25519W.
Axiom radd : ExprBinOp.
Axiom rsub : ExprBinOp.
Axiom rmul : ExprBinOp.
Axiom ropp : ExprUnOp.
Axiom rfreeze : ExprUnOp.
Local Notation ibinop_correct_and_bounded irop op
  := (forall x y,
         is_bounded (fe25519WToZ x) = true
         -> is_bounded (fe25519WToZ y) = true
         -> fe25519WToZ (irop x y) = op (fe25519WToZ x) (fe25519WToZ y)
            /\ is_bounded (fe25519WToZ (irop x y)) = true) (only parsing).
Local Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Local Notation iunop_correct_and_bounded irop op
  := (forall x,
         is_bounded (fe25519WToZ x) = true
         -> fe25519WToZ (irop x) = op (fe25519WToZ x)
            /\ is_bounded (fe25519WToZ (irop x)) = true) (only parsing).
Local Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Axiom radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Axiom rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Axiom rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Axiom ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Axiom rfreeze_correct_and_bounded : unop_correct_and_bounded rfreeze freeze.

Local Ltac bounded_t opW blem :=
  apply blem; apply is_bounded_proj1_fe25519.

Local Ltac define_binop f g opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f) (proj1_fe25519W g)) _);
  abstract bounded_t opW blem.
Local Ltac define_unop f opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f)) _);
  abstract bounded_t opW blem.

Definition addW (f g : fe25519W) : fe25519W := interp_bexpr radd f g.
Definition subW (f g : fe25519W) : fe25519W := interp_bexpr rsub f g.
Definition mulW (f g : fe25519W) : fe25519W := interp_bexpr rmul f g.
Definition oppW (f : fe25519W) : fe25519W := interp_uexpr ropp f.
Definition freezeW (f : fe25519W) : fe25519W := interp_uexpr rfreeze f.
Definition powW (f : fe25519W) chain := fold_chain_opt (proj1_fe25519W one) mulW chain [f].
Definition invW (f : fe25519W) : fe25519W
  := Eval cbv -[Let_In fe25519W mulW] in powW f (chain inv_ec).

Definition add (f g : fe25519) : fe25519.
Proof. define_binop f g addW radd_correct_and_bounded. Defined.
Definition sub (f g : fe25519) : fe25519.
Proof. define_binop f g subW rsub_correct_and_bounded. Defined.
Definition mul (f g : fe25519) : fe25519.
Proof. define_binop f g mulW rmul_correct_and_bounded. Defined.
Definition opp (f : fe25519) : fe25519.
Proof. define_unop f oppW ropp_correct_and_bounded. Defined.
Definition freeze (f : fe25519) : fe25519.
Proof. define_unop f freezeW rfreeze_correct_and_bounded. Defined.

Lemma fold_chain_opt_gen {A B} (F : A -> B) is_bounded ls id' op' id op chain
      (Hid_bounded : is_bounded (F id') = true)
      (Hid : id = F id')
      (Hop_bounded : forall x y, is_bounded (F x) = true
                                 -> is_bounded (F y) = true
                                 -> is_bounded (op (F x) (F y)) = true)
      (Hop : forall x y, is_bounded (F x) = true
                         -> is_bounded (F y) = true
                         -> op (F x) (F y) = F (op' x y))
      (Hls_bounded : forall n, is_bounded (F (nth_default id' ls n)) = true)
  : F (fold_chain_opt id' op' chain ls)
    = fold_chain_opt id op chain (List.map F ls)
    /\ is_bounded (F (fold_chain_opt id' op' chain ls)) = true.
Proof.
  rewrite !fold_chain_opt_correct.
  revert dependent ls; induction chain as [|x xs IHxs]; intros.
  { pose proof (Hls_bounded 0%nat).
    destruct ls; simpl; split; trivial; congruence. }
  { destruct x; simpl; unfold Let_In; simpl.
    rewrite (fun ls pf => proj1 (IHxs ls pf)) at 1; simpl.
    { do 2 f_equal.
      rewrite <- Hop, Hid by auto.
      rewrite !map_nth_default_always.
      split; try reflexivity.
      apply (IHxs (_::_)).
      intros [|?]; autorewrite with simpl_nth_default; auto.
      rewrite <- Hop; auto. }
    { intros [|?]; simpl;
        autorewrite with simpl_nth_default; auto.
      rewrite <- Hop; auto. } }
Qed.

Lemma powW_correct_and_bounded chain : iunop_correct_and_bounded (fun x => powW x chain) (fun x => pow x chain).
Proof.
  cbv [powW pow].
  intro x; intros; apply (fold_chain_opt_gen fe25519WToZ is_bounded [x]).
  { reflexivity. }
  { reflexivity. }
  { intros; progress rewrite <- ?mul_correct,
            <- ?(fun X Y => proj1 (rmul_correct_and_bounded _ _ X Y)) by assumption.
    apply rmul_correct_and_bounded; assumption. }
  { intros; symmetry; apply rmul_correct_and_bounded; assumption. }
  { intros [|?]; autorewrite with simpl_nth_default;
      (assumption || reflexivity). }
Qed.

Lemma invW_correct_and_bounded : iunop_correct_and_bounded invW inv.
Proof.
  intro f.
  assert (H : forall f, invW f = powW f (chain inv_ec))
    by abstract (cbv -[Let_In fe25519W mulW]; reflexivity).
  rewrite !H.
  rewrite inv_correct.
  cbv [inv_opt].
  rewrite <- pow_correct.
  apply powW_correct_and_bounded.
Qed.

Definition pow (f : fe25519) (chain : list (nat * nat)) : fe25519.
Proof. define_unop f (fun x => powW x chain) powW_correct_and_bounded. Defined.
Definition inv (f : fe25519) : fe25519.
Proof. define_unop f invW invW_correct_and_bounded. Defined.

Local Ltac unop_correct_t op opW rop_correct_and_bounded :=
  cbv [op opW]; rewrite proj1_fe25519_exist_fe25519W;
  rewrite (fun X => proj1 (rop_correct_and_bounded _ X)) by apply is_bounded_proj1_fe25519;
  try reflexivity.
Local Ltac binop_correct_t op opW rop_correct_and_bounded :=
  cbv [op opW]; rewrite proj1_fe25519_exist_fe25519W;
  rewrite (fun X Y => proj1 (rop_correct_and_bounded _ _ X Y)) by apply is_bounded_proj1_fe25519;
  try reflexivity.

Lemma add_correct (f g : fe25519) : proj1_fe25519 (add f g) = carry_add (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t add addW radd_correct_and_bounded. Qed.
Lemma sub_correct (f g : fe25519) : proj1_fe25519 (sub f g) = carry_sub (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t sub subW rsub_correct_and_bounded. Qed.
Lemma mul_correct (f g : fe25519) : proj1_fe25519 (mul f g) = GF25519.mul (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t mul mulW rmul_correct_and_bounded. Qed.
Lemma opp_correct (f : fe25519) : proj1_fe25519 (opp f) = carry_opp (proj1_fe25519 f).
Proof. unop_correct_t opp oppW ropp_correct_and_bounded. Qed.
Lemma freeze_correct (f : fe25519) : proj1_fe25519 (freeze f) = GF25519.freeze (proj1_fe25519 f).
Proof. unop_correct_t freeze freezeW rfreeze_correct_and_bounded. Qed.
Lemma pow_correct (f : fe25519) chain : proj1_fe25519 (pow f chain) = GF25519.pow (proj1_fe25519 f) chain.
Proof. unop_correct_t pow pow (powW_correct_and_bounded chain). Qed.
Lemma inv_correct (f : fe25519) : proj1_fe25519 (inv f) = GF25519.inv (proj1_fe25519 f).
Proof. unop_correct_t inv inv invW_correct_and_bounded. Qed.

Lemma encode_bounded x : is_bounded (encode x) = true.
Proof.
  pose proof (bounded_encode x).
  generalize dependent (encode x).
  intro t; compute in t; intros.
  destruct_head prod.
  unfold Pow2Base.bounded in H.
  pose proof (H 0%nat); pose proof (H 1%nat); pose proof (H 2%nat);
    pose proof (H 3%nat); pose proof (H 4%nat); pose proof (H 5%nat);
      pose proof (H 6%nat); pose proof (H 7%nat); pose proof (H 8%nat);
        pose proof (H 9%nat); clear H.
  simpl in *.
  cbv [Z.pow_pos Z.mul Pos.mul Pos.iter nth_default nth_error value] in *.
  unfold is_bounded.
  apply fold_right_andb_true_iff_fold_right_and_True.
  cbv [is_bounded proj1_fe25519 to_list length bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map List.rev List.app proj1_sig fold_right].
  repeat split; rewrite !Bool.andb_true_iff, !Z.leb_le; omega.
Qed.

Definition encode (x : F modulus) : fe25519
  := exist_fe25519 (encode x) (encode_bounded x).

Definition div (f g : fe25519) : fe25519
  := exist_fe25519 (div (proj1_fe25519 f) (proj1_fe25519 g)) (encode_bounded _).

Definition eq (f g : fe25519) : Prop := eq (proj1_fe25519 f) (proj1_fe25519 g).

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  assert (Reflexive eq) by (repeat intro; reflexivity).
  eapply (Field.field_from_redundant_representation
            (fieldF:=Specific.GF25519.carry_field25519)
            (phi':=proj1_fe25519)).
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { intros; rewrite opp_correct; reflexivity. }
  { intros; rewrite add_correct; reflexivity. }
  { intros; rewrite sub_correct; reflexivity. }
  { intros; rewrite mul_correct; reflexivity. }
  { intros; rewrite inv_correct; reflexivity. }
  { cbv [div]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
Qed.

Local Opaque proj1_fe25519 exist_fe25519 proj1_fe25519W exist_fe25519W.
Lemma homomorphism_F25519 :
  @Ring.is_homomorphism
    (F modulus) Logic.eq F.one F.add F.mul
    fe25519 eq one add mul encode.
Proof.
  pose proof homomorphism_carry_F25519 as H.
  destruct H as [ [H0 H1] H2 H3].
  econstructor; [ econstructor | | ];
    cbv [eq encode]; repeat intro;
      rewrite ?add_correct, ?mul_correct, ?proj1_fe25519_exist_fe25519, ?proj1_fe25519_exist_fe25519W, ?proj1_fe25519W_exist_fe25519 in *.
  { rewrite H0; reflexivity. }
  { apply H1; assumption. }
  { rewrite H2; reflexivity. }
  { reflexivity. }
Qed.

(** TODO: pack, unpack, sqrt *)
