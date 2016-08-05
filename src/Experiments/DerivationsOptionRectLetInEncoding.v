Require Import Coq.omega.Omega.
Require Import Bedrock.Word.
Require Import Crypto.Spec.EdDSA.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.NArith.BinNat Coq.ZArith.BinInt Coq.NArith.NArith Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.Encoding Crypto.Spec.ModularWordEncoding.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.Util.IterAssocOp Crypto.Util.WordUtil.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Require Import Coq.ZArith.Zdiv.
Require Import Crypto.Util.Tuple.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope equiv_scope.

Generalizable All Variables.


Definition path_sig {A P} {RA:relation A} {Rsig:relation (@sig A P)}
           {HP:Proper (RA==>Basics.impl) P}
           (H:forall (x y:A) (px:P x) (py:P y), RA x y -> Rsig (exist _ x px) (exist _ y py))
           (x : @sig A P) (y0:A) (pf : RA (proj1_sig x) y0)
: Rsig x (exist _ y0 (HP _ _ pf (proj2_sig x))).
Proof. destruct x. eapply H. assumption. Defined.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Global Instance Let_In_Proper_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof.
  lazy; intros; try congruence.
  subst; auto.
Qed.

Lemma Let_In_Proper_changevalue {A B} RA {RB} (f:A->B) {Proper_f:Proper (RA==>RB) f}
  : Proper (RA ==> RB) (fun x => Let_In x f).
Proof. intuition. Qed.

Ltac fold_identity_lambdas :=
  repeat match goal with
           | [ H: appcontext [fun x => ?f x] |- _ ] => change (fun x => f x) with f in *
           | |- appcontext [fun x => ?f x] => change (fun x => f x) with f in *
         end.

Local Ltac replace_let_in_with_Let_In :=
  match goal with
  | [ |- context G[let x := ?y in @?z x] ]
    => let G' := context G[Let_In y z] in change G'
  end.

Local Ltac Let_In_app fn :=
  match goal with
  | [ |- appcontext G[Let_In (fn ?x) ?f] ]
    => change (Let_In (fn x) f) with (Let_In x (fun y => f (fn y))); cbv beta
  end.

Lemma if_map : forall {T U} (f:T->U) (b:bool) (x y:T), (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; trivial.
Qed.

Lemma pull_Let_In {B C} (f : B -> C) A (v : A) (b : A -> B)
  : Let_In v (fun v' => f (b v')) = f (Let_In v b).
Proof.
  reflexivity.
Qed.

Lemma Let_app_In {A B T} (g:A->B) (f:B->T) (x:A) :
    @Let_In _ (fun _ => T) (g x) f =
    @Let_In _ (fun _ => T) x (fun p => f (g x)).
Proof. reflexivity. Qed.

Lemma Let_app_In' : forall {A B T} {R} {R_equiv:@Equivalence T R}
                      (g : A -> B) (f : B -> T) (x : A)
    f' (f'_ok: forall z, f' z === f (g z)),
    Let_In (g x) f === Let_In x f'.
Proof. intros; cbv [Let_In]; rewrite f'_ok; reflexivity. Qed.
Definition unfold_Let_In {A B} x (f:A->B) : Let_In x f = let y := x in f y := eq_refl.

Lemma Let_app2_In {A B C D T} (g1:A->C) (g2:B->D) (f:C*D->T) (x:A) (y:B) :
    @Let_In _ (fun _ => T) (g1 x, g2 y) f =
    @Let_In _ (fun _ => T) (x, y) (fun p => f ((g1 (fst p), g2 (snd p)))).
Proof. reflexivity. Qed.

Lemma funexp_proj {T T'} `{@Equivalence T' RT'}
      (proj : T -> T')
      (f : T -> T)
      (f' : T' -> T') {Proper_f':Proper (RT'==>RT') f'}
      (f_proj : forall a, proj (f a) === f' (proj a))
      x n
  : proj (funexp f x n) === funexp f' (proj x) n.
Proof.
  revert x; induction n as [|n IHn]; simpl; intros.
  - reflexivity.
  - rewrite f_proj. rewrite IHn. reflexivity.
Qed.

Global Instance pair_Equivalence {A B} `{@Equivalence A RA} `{@Equivalence B RB} : @Equivalence (A*B) (fun x y => fst x = fst y /\ snd x === snd y).
Proof.
  constructor; repeat intro; intuition auto with relations; try congruence.
  match goal with [H : _ |- _ ] => solve [rewrite H; auto] end.
Qed.

Global Instance Proper_test_and_op {T scalar} `{Requiv:@Equivalence T RT}
      {op:T->T->T} {Proper_op:Proper (RT==>RT==>RT) op}
      {testbit:scalar->nat->bool} {s:scalar} {zero:T} :
  let R := fun x y => fst x = fst y /\ snd x === snd y in
  Proper (R==>R) (@test_and_op _ op _ testbit s zero).
Proof.
  unfold test_and_op; simpl; repeat intro; intuition;
  repeat match goal with
         | [ |- context[match ?n with _ => _ end] ] => destruct n eqn:?; simpl in *; subst; try discriminate; auto
         | [ H: _ |- _ ] => setoid_rewrite H; reflexivity
         end.
Qed.

Lemma iter_op_proj {T T' S} `{T'Equiv:@Equivalence T' RT'}
      (proj : T -> T') (op : T -> T -> T) (op' : T' -> T' -> T') {Proper_op':Proper (RT' ==> RT' ==> RT') op'} x y z
      (testbit : S -> nat -> bool) (bound : nat)
      (op_proj : forall a b, proj (op a b) === op' (proj a) (proj b))
  : proj (@iter_op _ op x _ testbit y z bound) === @iter_op _ op' (proj x) _ testbit y (proj z) bound.
Proof.
  unfold iter_op.
  lazymatch goal with
  | [ |- ?proj (snd (funexp ?f ?x ?n)) === snd (funexp ?f' _ ?n) ]
    => pose proof (fun pf x0 x1 => @funexp_proj _ _ _ _ (fun x' => (fst x', proj (snd x'))) f f' (Proper_test_and_op (Requiv:=T'Equiv)) pf (x0, x1)) as H';
      lazymatch type of H' with
      | ?H'' -> _ => assert (H'') as pf; [clear H'|edestruct (H' pf); simpl in *; solve [eauto]]
      end
  end.

  intros [??]; simpl.
  repeat match goal with
         | [ |- context[match ?n with _ => _ end] ] => destruct n eqn:?
         | _ => progress (unfold equiv; simpl)
         | _ => progress (subst; intuition)
         | _ => reflexivity
         | _ => rewrite op_proj
         end.
Qed.

Definition COMPILETIME {T} (x:T) : T := x.

Lemma N_to_nat_le_mono : forall a b, (a <= b)%N -> (N.to_nat a <= N.to_nat b)%nat.
Proof.
  intros.
  pose proof (Nomega.Nlt_out a (N.succ b)).
  rewrite N2Nat.inj_succ, N.lt_succ_r, <-NPeano.Nat.lt_succ_r in *; auto.
Qed.
Lemma N_size_nat_le_mono : forall a b, (a <= b)%N -> (N.size_nat a <= N.size_nat b)%nat.
Proof.
  intros.
  destruct (N.eq_dec a 0), (N.eq_dec b 0); try abstract (subst;rewrite ?N.le_0_r in *;subst;simpl;omega).
  rewrite !Nsize_nat_equiv, !N.size_log2 by assumption.
  edestruct N.succ_le_mono; eauto using N_to_nat_le_mono, N.log2_le_mono.
Qed.

Lemma Z_to_N_Z_of_nat : forall n, Z.to_N (Z.of_nat n) = N.of_nat n.
Proof. induction n; auto. Qed.

Lemma Z_of_nat_nonzero : forall m, m <> 0 -> (0 < Z.of_nat m)%Z.
Proof. intros. destruct m; [congruence|reflexivity]. Qed.

Section with_unqualified_modulo.
Import NPeano Nat.
Local Infix "mod" := modulo : nat_scope.
Lemma N_of_nat_modulo : forall n m, m <> 0 -> N.of_nat (n mod m)%nat = (N.of_nat n mod N.of_nat m)%N.
Proof.
  intros.
  apply Znat.N2Z.inj_iff.
  rewrite !Znat.nat_N_Z.
  rewrite Zdiv.mod_Zmod by auto.
  apply Znat.Z2N.inj_iff.
  { apply Z.mod_pos_bound. apply Z_of_nat_nonzero. assumption. }
  { apply Znat.N2Z.is_nonneg. }
  rewrite Znat.Z2N.inj_mod by (auto using Znat.Nat2Z.is_nonneg, Z_of_nat_nonzero).
  rewrite !Z_to_N_Z_of_nat, !Znat.N2Z.id; reflexivity.
Qed.
End with_unqualified_modulo.

Lemma encoding_canonical' {T} {B} {encoding:canonical encoding of T as B} :
  forall a b, enc a = enc b -> a = b.
Proof.
  intros.
  pose proof (f_equal dec H).
  pose proof encoding_valid.
  pose proof encoding_canonical.
  congruence.
Qed.

Lemma compare_encodings {T} {B} {encoding:canonical encoding of T as B}
           (B_eqb:B->B->bool) (B_eqb_iff : forall a b:B, (B_eqb a b = true) <-> a = b)
           : forall a b : T, (a = b) <-> (B_eqb (enc a) (enc b) = true).
Proof.
  intros.
  split; intro H.
  { rewrite B_eqb_iff; congruence. }
  { apply B_eqb_iff in H; eauto using encoding_canonical'. }
Qed.

Lemma eqb_eq_dec' {T} (eqb:T->T->bool) (eqb_iff:forall a b, eqb a b = true <-> a = b) :
    forall a b, if eqb a b then a = b else a <> b.
Proof.
  intros.
  case_eq (eqb a b); intros.
  { eapply eqb_iff; trivial. }
  { specialize (eqb_iff a b). rewrite H in eqb_iff. intuition auto with bool. }
Qed.

Definition eqb_eq_dec {T} (eqb:T->T->bool) (eqb_iff:forall a b, eqb a b = true <-> a = b) :
  forall a b : T, {a=b}+{a<>b}.
Proof.
  intros.
  pose proof (eqb_eq_dec' eqb eqb_iff a b).
  destruct (eqb a b); eauto.
Qed.

Definition eqb_eq_dec_and_output {T} (eqb:T->T->bool) (eqb_iff:forall a b, eqb a b = true <-> a = b) :
  forall a b : T, {a = b /\ eqb a b = true}+{a<>b /\ eqb a b = false}.
Proof.
  intros.
  pose proof (eqb_eq_dec' eqb eqb_iff a b).
  destruct (eqb a b); eauto.
Qed.

Lemma eqb_compare_encodings {T} {B} {encoding:canonical encoding of T as B}
           (T_eqb:T->T->bool) (T_eqb_iff : forall a b:T, (T_eqb a b = true) <-> a = b)
           (B_eqb:B->B->bool) (B_eqb_iff : forall a b:B, (B_eqb a b = true) <-> a = b)
           : forall a b : T, T_eqb a b = B_eqb (enc a) (enc b).
Proof.
  intros;
    destruct (eqb_eq_dec_and_output T_eqb T_eqb_iff a b);
    destruct (eqb_eq_dec_and_output B_eqb B_eqb_iff (enc a) (enc b));
    intuition;
    try find_copy_apply_lem_hyp B_eqb_iff;
    try find_copy_apply_lem_hyp T_eqb_iff;
    try congruence.
    apply (compare_encodings B_eqb B_eqb_iff) in H2; congruence.
Qed.

Lemma decode_failed_neq_encoding {T B} (encoding_T_B:canonical encoding of T as B) (X:B)
  (dec_failed:dec X = None) (a:T) : X <> enc a.
Proof. pose proof encoding_valid. congruence. Qed.
Lemma compare_without_decoding {T B} (encoding_T_B:canonical encoding of T as B)
      (T_eqb:T->T->bool) (T_eqb_iff:forall a b, T_eqb a b = true <-> a = b)
      (B_eqb:B->B->bool) (B_eqb_iff:forall a b, B_eqb a b = true <-> a = b)
      (P_:B) (Q:T) :
  option_rect (fun _ : option T => bool)
                 (fun P : T => T_eqb P Q)
                 false
              (dec P_)
    = B_eqb P_ (enc Q).
Proof.
  destruct (dec P_) eqn:Hdec; simpl option_rect.
  { apply encoding_canonical in Hdec; subst; auto using eqb_compare_encodings. }
  { pose proof encoding_canonical.
    pose proof encoding_valid.
    pose proof eqb_compare_encodings.
    eapply decode_failed_neq_encoding in Hdec.
    destruct (B_eqb P_ (enc Q)) eqn:Heq; [rewrite B_eqb_iff in Heq; eauto | trivial]. }
Qed.