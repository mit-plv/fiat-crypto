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
Require Import Crypto.Util.Decidable.
Require Import Crypto.Arithmetic.Saturated.UniformWeightInstances.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Local Definition sig_by_eq {A P} (x : { a : A | P a }) (a : A) (H : a = proj1_sig x)
  : { a : A | P a }.
Proof.
  exists a; subst; exact (proj2_sig x).
Defined.

Section with_args.
  Context (wt : nat -> Z)
          (r : positive)
          (sz : nat)
          (m : positive)
          (m_enc : Z^sz)
          (r' : Z)
          (r'_correct : ((Z.pos r * r') mod (Z.pos m) = 1)%Z)
          (m' : Z)
          (m'_correct : ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r)%Z)
          (m_enc_correct_montgomery : Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
          (r'_pow_correct : ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)%Z)
          (* computable *)
          (r_big : Z.pos r > 1)
          (m_big : 1 < Z.pos m)
          (m_enc_small : small (Z.pos r) m_enc)
          (map_m_enc : Tuple.map (Z.land (Z.pos r - 1)) m_enc = m_enc).

  Local Ltac t_fin :=
    repeat match goal with
           | _ => assumption
           | [ |- ?x = ?x ] => reflexivity
           | [ |- and _ _ ] => split
           | [ |- (0 <= MontgomeryAPI.eval (Z.pos r) _)%Z ] => apply MontgomeryAPI.eval_small
           | _ => rewrite <- !m_enc_correct_montgomery
           | _ => rewrite !r'_correct
           | _ => rewrite !Z.mod_1_l by assumption; reflexivity
           | _ => rewrite !(Z.mul_comm m' (Z.pos m))
           | _ => lia
           end.


  Local Definition mul'_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | forall (A B : Z^sz),
          small (Z.pos r) A -> small (Z.pos r) B ->
          let eval := MontgomeryAPI.eval (Z.pos r) in
          (small (Z.pos r) (f A B)
           /\ (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)
           /\ (eval (f A B) mod Z.pos m
               = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
      }.
  Proof.
    exists (fun A B => redc (r:=r)(R_numlimbs:=sz) m_enc A B m').
    abstract (
        intros;
        split; [ | split ];
        [ apply small_redc with (ri:=r') | apply redc_bound_N with (ri:=r') | rewrite !m_enc_correct_montgomery; apply redc_mod_N ];
        t_fin
      ).
  Defined.

  Import ModularArithmetic.

  Definition montgomery_to_F_gen (v : Z) : F m
    := (F.of_Z m v * F.of_Z m (r'^Z.of_nat sz)%Z)%F.

  Local Definition mul_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        (forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            montgomery_to_F_gen (eval (f A B))
            = (montgomery_to_F_gen (eval A) * montgomery_to_F_gen (eval B))%F)
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z) }.
  Proof.
    exists (proj1_sig mul'_gen).
    abstract (
        split; intros A Asm B Bsm;
        pose proof (proj2_sig mul'_gen A B Asm Bsm) as H;
        cbv zeta in *;
        try solve [ destruct_head'_and; assumption ];
        rewrite ModularArithmeticTheorems.F.eq_of_Z_iff in H;
        unfold montgomery_to_F_gen;
        destruct H as [H1 [H2 H3]];
        rewrite H3;
        rewrite <- !ModularArithmeticTheorems.F.of_Z_mul;
        f_equal; nia
      ).
  Defined.

  Local Definition add_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) + montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    exists (fun A B => add (r:=r)(R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_add;
        rewrite <- ?Z.mul_add_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_add_mod_N; pull_Zmod
        | apply add_bound ];
        t_fin
      ).
  Defined.

  Local Definition sub_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) - montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    exists (fun A B => sub (r:=r) (R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_sub;
        rewrite <- ?Z.mul_sub_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_sub_mod_N; pull_Zmod
        | apply sub_bound ];
        t_fin
      ).
  Defined.

  Local Definition opp_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = (F.opp (montgomery_to_F_gen (eval A)))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc)))%Z }.
  Proof.
    exists (fun A => opp (r:=r) (R_numlimbs:=sz) m_enc A).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?F_of_Z_opp;
        rewrite <- ?Z.mul_opp_l;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_opp_mod_N; pull_Zmod
        | apply opp_bound ];
        t_fin
      ).
  Defined.

  Local Definition nonzero_ext_gen
    : { f:Z^sz -> Z
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        forall (A : Z^sz) (_ : small (Z.pos r) A),
          (eval A < eval m_enc
           -> f A = 0 <-> (montgomery_to_F_gen (eval A) = F.of_Z m 0))%Z }.
  Proof.
    exists (fun A => nonzero (R_numlimbs:=sz) A).
    abstract (
        intros eval A H **; rewrite (@eval_nonzero r) by (eassumption || reflexivity);
        subst eval;
        unfold montgomery_to_F_gen, uweight in *; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul;
        rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery;
        let H := fresh in
        split; intro H;
        [ rewrite H; autorewrite with zsimplify_const; reflexivity
        | cut ((MontgomeryAPI.eval (Z.pos r) A * (r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz)) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 0)%Z;
          [ rewrite Z.mul_mod, r'_pow_correct; autorewrite with zsimplify_const; pull_Zmod; [ | t_fin ];
            rewrite Z.mod_small; [ trivial | split; try assumption; apply MontgomeryAPI.eval_small; try assumption; lia ]
          | rewrite Z.mul_assoc, Z.mul_mod, H by t_fin; autorewrite with zsimplify_const; reflexivity ] ]
      ).
  Defined.
End with_args.

Local Definition for_assumptions
  := (mul_ext_gen, add_ext_gen, sub_ext_gen, opp_ext_gen, nonzero_ext_gen).

Print Assumptions for_assumptions.

Ltac pose_m' modinv_fuel m r m' := (* (-m)⁻¹ mod r *)
  pose_modinv modinv_fuel (-Z.pos m) (Z.pos r) m'.
Ltac pose_r' modinv_fuel m r r' := (* r⁻¹ mod m *)
  pose_modinv modinv_fuel (Z.pos r) (Z.pos m) r'.

Ltac pose_m'_correct m m' r m'_correct :=
  pose_correct_if_Z
    m'
    ltac:(fun _ => constr:((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r))
           m'_correct.
Ltac pose_r'_correct m r r' r'_correct :=
  pose_correct_if_Z
    r'
    ltac:(fun _ => constr:((Z.pos r * r') mod (Z.pos m) = 1))
           r'_correct.

Ltac pose_m_enc_correct_montgomery m sz r m_enc m_enc_correct_montgomery :=
  cache_proof_with_type_by
    (Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
    ltac:(vm_compute; vm_cast_no_check (eq_refl (Z.pos m)))
           m_enc_correct_montgomery.

Ltac pose_r'_pow_correct r' sz r m_enc r'_pow_correct :=
  cache_proof_with_type_by
    ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)
    ltac:(vm_compute; reflexivity)
           r'_pow_correct.

Ltac pose_montgomery_to_F sz m r' montgomery_to_F :=
  let v := (eval cbv [montgomery_to_F_gen] in (montgomery_to_F_gen sz m r')) in
  cache_term v montgomery_to_F.

Ltac pose_r_big r r_big :=
  cache_proof_with_type_by
    (Z.pos r > 1)
    ltac:(vm_compute; reflexivity)
           r_big.

Ltac pose_m_big m m_big :=
  cache_proof_with_type_by
    (1 < Z.pos m)
    ltac:(vm_compute; reflexivity)
           m_big.

Ltac pose_m_enc_small sz r m_enc m_enc_small :=
  cache_proof_with_type_by
    (small (n:=sz) (Z.pos r) m_enc)
    ltac:(pose (small_Decidable (n:=sz) (bound:=Z.pos r)); vm_decide_no_check)
           m_enc_small.

Ltac pose_map_m_enc sz r m_enc map_m_enc :=
  cache_proof_with_type_by
    (Tuple.map (n:=sz) (Z.land (Z.pos r - 1)) m_enc = m_enc)
    ltac:(pose (@dec_eq_prod); pose dec_eq_Z; vm_decide_no_check)
           map_m_enc.

Ltac internal_pose_sig_by_eq ty sigl tac_eq id :=
  cache_term_with_type_by
    ty
    ltac:(eapply (@sig_by_eq _ _ sigl _); tac_eq ())
           id.

Import ModularArithmetic.

Local Ltac reduce_eq _ :=
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp runtime_lor Let_In].

Ltac pose_mul_ext r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F mul_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      (forall (A : Z^sz) (_ : small (Z.pos r) A)
              (B : Z^sz) (_ : small (Z.pos r) B),
          montgomery_to_F (eval (f A B))
          = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F)
      /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z) }
    (@mul_ext_gen r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small)
    ltac:(fun _ => reduce_eq (); reflexivity)
           mul_ext.

Ltac pose_add_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F add_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A)
               (B : Z^sz) (_ : small (Z.pos r) B),
           (eval A < eval m_enc
            -> eval B < eval m_enc
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                  (B : Z^sz) (_ : small (Z.pos r) B),
              (eval A < eval m_enc
               -> eval B < eval m_enc
               -> 0 <= eval (f A B) < eval m_enc)))%Z }
    (@add_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small)
    ltac:(fun _ => reduce_eq (); reflexivity)
           add_ext.

Ltac pose_sub_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F sub_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A)
               (B : Z^sz) (_ : small (Z.pos r) B),
           (eval A < eval m_enc
            -> eval B < eval m_enc
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                  (B : Z^sz) (_ : small (Z.pos r) B),
              (eval A < eval m_enc
               -> eval B < eval m_enc
               -> 0 <= eval (f A B) < eval m_enc)))%Z }
    (@sub_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc)
    ltac:(fun _ => reduce_eq (); reflexivity)
           sub_ext.

Ltac pose_opp_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F opp_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A),
           (eval A < eval m_enc
            -> montgomery_to_F (eval (f A))
               = (F.opp (montgomery_to_F (eval A)))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
              (eval A < eval m_enc
               -> 0 <= eval (f A) < eval m_enc)))%Z }
    (@opp_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc)
    ltac:(fun _ => reduce_eq (); reflexivity)
           opp_ext.

Ltac pose_nonzero_ext r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big montgomery_to_F nonzero_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    (@nonzero_ext_gen r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big)
    ltac:(fun _ => reduce_eq (); reflexivity)
           nonzero_ext.

Ltac pose_mul_sig r sz montgomery_to_F mul_ext mul_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        montgomery_to_F (eval (f A B))
        = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig mul_ext_gen mul_ext sig_by_eq] in (proj1_sig mul_ext)) in
          (exists v);
          abstract apply (proj2_sig mul_ext))
           mul_sig.

Ltac pose_mul_bounded r sz m_enc montgomery_to_F mul_ext mul_sig mul_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     forall (A : Z^sz) (_ : small (Z.pos r) A)
            (B : Z^sz) (_ : small (Z.pos r) B),
       (eval B < eval m_enc
        -> 0 <= eval (proj1_sig mul_sig A B) < eval m_enc)%Z)
    ltac:(apply (proj2_sig mul_ext))
           mul_bounded.


Ltac pose_add_sig r sz m_enc montgomery_to_F add_ext add_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        (eval A < eval m_enc
         -> eval B < eval m_enc
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig add_ext_gen add_ext sig_by_eq] in (proj1_sig add_ext)) in
          (exists v);
          abstract apply (proj2_sig add_ext))
           add_sig.

Ltac pose_add_bounded r sz m_enc montgomery_to_F add_ext add_sig add_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
         (eval A < eval m_enc
          -> eval B < eval m_enc
          -> 0 <= eval (proj1_sig add_sig A B) < eval m_enc))%Z)
    ltac:(apply (proj2_sig add_ext))
           add_bounded.


Ltac pose_sub_sig r sz m_enc montgomery_to_F sub_ext sub_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        (eval A < eval m_enc
         -> eval B < eval m_enc
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig sub_ext_gen sub_ext sig_by_eq] in (proj1_sig sub_ext)) in
          (exists v);
          abstract apply (proj2_sig sub_ext))
           sub_sig.

Ltac pose_sub_bounded r sz m_enc montgomery_to_F sub_ext sub_sig sub_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
         (eval A < eval m_enc
          -> eval B < eval m_enc
          -> 0 <= eval (proj1_sig sub_sig A B) < eval m_enc))%Z)
    ltac:(apply (proj2_sig sub_ext))
           sub_bounded.


Ltac pose_opp_sig r sz m_enc montgomery_to_F opp_ext opp_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> montgomery_to_F (eval (f A))
            = (F.opp (montgomery_to_F (eval A)))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig opp_ext_gen opp_ext sig_by_eq] in (proj1_sig opp_ext)) in
          (exists v);
          abstract apply (proj2_sig opp_ext))
           opp_sig.

Ltac pose_opp_bounded r sz m_enc montgomery_to_F opp_ext opp_sig opp_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A),
         (eval A < eval m_enc
          -> 0 <= eval (proj1_sig opp_sig A) < eval m_enc))%Z)
    ltac:(apply (proj2_sig opp_ext))
           opp_bounded.


Ltac pose_nonzero_sig r sz m m_enc montgomery_to_F nonzero_ext nonzero_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig nonzero_ext_gen nonzero_ext sig_by_eq] in (proj1_sig nonzero_ext)) in
          (exists v);
          abstract apply (proj2_sig nonzero_ext))
           nonzero_sig.

Ltac pose_ring ring :=
  (* FIXME: TODO *)
  cache_term
    I
    ring.

(* disable default unused things *)
Ltac pose_carry_sig carry_sig :=
  cache_term tt carry_sig.
Ltac pose_freeze_sig freeze_sig :=
  cache_term tt freeze_sig.
Ltac pose_Mxzladderstep_sig Mxzladderstep_sig :=
  cache_term tt Mxzladderstep_sig.
