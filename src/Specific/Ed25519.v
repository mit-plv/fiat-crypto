Require Import Bedrock.Word.
Require Import Crypto.Spec.EdDSA.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import ModularArithmetic.ModularArithmeticTheorems.
Require Import ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Encoding.PointEncodingPre.
Require Import Crypto.Spec.Encoding Crypto.Spec.ModularWordEncoding Crypto.Spec.PointEncoding.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.Util.IterAssocOp Crypto.Util.WordUtil Crypto.Rep.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Require Import Zdiv.
Local Open Scope equiv_scope.

Generalizable All Variables.
  
(*TODO: move enerything before the section out of this file *)

Fixpoint tuple' n T : Type :=
  match n with
  | O => T
  | S n' => (tuple' n' T * T)%type
  end.

Definition tuple n T : Type :=
  match n with
    | O => unit
    | S n' => tuple' n' T
  end.

Fixpoint fieldwise' {A B} (n:nat) (R:A->B->Prop) (a:tuple' n A) (b:tuple' n B) {struct n} : Prop.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) /\ fieldwise' _ _ n R (fst a) (fst b)). }
Defined.

Definition fieldwise {A B} (n:nat) (R:A->B->Prop) (a:tuple n A) (b:tuple n B) : Prop.
  destruct n; simpl @tuple in *.
  { exact True. }
  { exact (fieldwise' _ R a b). }
Defined.

Global Instance Equivalence_fieldwise' {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise' n R).
Proof.
  induction n; [solve [auto]|].
  simpl; constructor; repeat intro; intuition eauto.
Qed.

Global Instance Equivalence_fieldwise {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise n R).
Proof.
  destruct n; (repeat constructor || apply Equivalence_fieldwise').
Qed.

Arguments fieldwise' {A B n} _ _ _.
Arguments fieldwise {A B n} _ _ _.


Local Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.

Local Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.

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
  constructor; repeat intro; intuition; try congruence.
  match goal with [H : _ |- _ ] => solve [rewrite H; auto] end.
Qed.

Global Instance Proper_test_and_op {T scalar} `{Requiv:@Equivalence T RT}
      {op:T->T->T} {Proper_op:Proper (RT==>RT==>RT) op}
      {testbit:scalar->nat->bool} {s:scalar} {zero:T} :
  let R := fun x y => fst x = fst y /\ snd x === snd y in
  Proper (R==>R) (test_and_op op testbit s zero).
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
  : proj (iter_op op x testbit y z bound) === iter_op op' (proj x) testbit y (proj z) bound.
Proof.
  unfold iter_op.
  lazymatch goal with
  | [ |- ?proj (snd (funexp ?f ?x ?n)) === snd (funexp ?f' _ ?n) ]
    => pose proof (fun pf x0 x1 => @funexp_proj _ _ _ _ (fun x => (fst x, proj (snd x))) f f' (Proper_test_and_op (Requiv:=T'Equiv)) pf (x0, x1)) as H';
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

Global Instance option_rect_Proper_nd {A T}
  : Proper ((pointwise_relation _ eq) ==> eq  ==> eq ==> eq) (@option_rect A (fun _ => T)).
Proof.
  intros ?? H ??? [|]??; subst; simpl; congruence.
Qed.

Global Instance option_rect_Proper_nd' {A T}
  : Proper ((pointwise_relation _ eq) ==> eq  ==> forall_relation (fun _ => eq)) (@option_rect A (fun _ => T)).
Proof.
  intros ?? H ??? [|]; subst; simpl; congruence.
Qed.

Hint Extern 1 (Proper _ (@option_rect ?A (fun _ => ?T))) => exact (@option_rect_Proper_nd' A T) : typeclass_instances.

Lemma option_rect_option_map : forall {A B C} (f:A->B) some none v,
    option_rect (fun _ => C) (fun x => some (f x)) none v = option_rect (fun _ => C) some none (option_map f v).
Proof.
  destruct v; reflexivity.
Qed.

Lemma option_rect_function {A B C S' N' v} f
  : f (option_rect (fun _ : option A => option B) S' N' v)
    = option_rect (fun _ : option A => C) (fun x => f (S' x)) (f N') v.
Proof. destruct v; reflexivity. Qed.
Local Ltac commute_option_rect_Let_In := (* pull let binders out side of option_rect pattern matching *)
  idtac;
  lazymatch goal with
  | [ |- ?LHS = option_rect ?P ?S ?N (Let_In ?x ?f) ]
    => (* we want to just do a [change] here, but unification is stupid, so we have to tell it what to unfold in what order *)
    cut (LHS = Let_In x (fun y => option_rect P S N (f y))); cbv beta;
    [ set_evars;
      let H := fresh in
      intro H;
      rewrite H;
      clear;
      abstract (cbv [Let_In]; reflexivity)
    | ]
  end.

(** TODO: possibly move me, remove local *)
Local Ltac replace_option_match_with_option_rect :=
  idtac;
  lazymatch goal with
  | [ |- _ = ?RHS :> ?T ]
    => lazymatch RHS with
       | match ?a with None => ?N | Some x => @?S x end
         => replace RHS with (option_rect (fun _ => T) S N a) by (destruct a; reflexivity)
       end
  end.
Local Ltac simpl_option_rect := (* deal with [option_rect _ _ _ None] and [option_rect _ _ _ (Some _)] *)
  repeat match goal with
         | [ |- context[option_rect ?P ?S ?N None] ]
           => change (option_rect P S N None) with N
         | [ |- context[option_rect ?P ?S ?N (Some ?x) ] ]
           => change (option_rect P S N (Some x)) with (S x); cbv beta
         end.

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
  { specialize (eqb_iff a b). rewrite H in eqb_iff. intuition. }
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

Lemma unfoldDiv : forall {m} (x y:F m), (x/y = x * inv y)%F. Proof. unfold div. congruence. Qed.

Definition FieldToN {m} (x:F m) := Z.to_N (FieldToZ x).
Lemma FieldToN_correct {m} (x:F m) : FieldToN (m:=m) x = Z.to_N (FieldToZ x). reflexivity. Qed.

Definition natToField {m} x : F m := ZToField (Z.of_nat x).
Definition FieldToNat {m} (x:F m) : nat := Z.to_nat (FieldToZ x).
Lemma FieldToNat_natToField {m} : m <> 0 -> forall x, x mod m = FieldToNat (natToField (m:=Z.of_nat m) x).
  unfold natToField, FieldToNat; intros.
  rewrite (FieldToZ_ZToField), <-mod_Zmod, Nat2Z.id; trivial.
Qed.

Lemma F_eqb_iff {q} : forall x y : F q, F_eqb x y = true <-> x = y.
Proof.
  split; eauto using F_eqb_eq, F_eqb_complete.
Qed.
Lemma E_eqb_iff : forall {prm:TwistedEdwardsParams} (x y : E.point), E.point_eqb x y = true <-> x = y.
Proof.
  split; eauto using E.point_eqb_sound, E.point_eqb_complete.
Qed.

Lemma unfold_E_sub : forall {prm:TwistedEdwardsParams} a b, (a - b = a + E.opp b)%E. Proof. reflexivity. Qed.

Section FSRepOperations.
  Context {q:Z} {prime_q:Znumtheory.prime q} {two_lt_q:(2 < q)%Z}.
  Context {l:Z} {two_lt_l:(2 < l)%Z}.
  Context `{rcS:RepConversions (F l) SRep} {rcSOK:RepConversionsOK rcS}.
  Context `(rcF:RepConversions (F q) FRep) (rcFOK:RepConversionsOK rcF).
  Context (FRepAdd FRepSub FRepMul:FRep->FRep->FRep) (FRepAdd_correct:RepBinOpOK rcF add FRepMul).
  Context (FRepSub_correct:RepBinOpOK rcF sub FRepSub) (FRepMul_correct:RepBinOpOK rcF mul FRepMul).
  Axiom SRep_testbit : SRep -> nat -> bool.
  Axiom SRep_testbit_correct : forall (x0 : SRep) (i : nat), SRep_testbit x0 i = N.testbit_nat (FieldToN (unRep x0)) i.

  Definition FSRepPow width x n := iter_op FRepMul (toRep 1%F) SRep_testbit n x width.
  Lemma FSRepPow_correct : forall width x n, (N.size_nat (FieldToN (unRep n)) <= width)%nat -> (unRep x ^ FieldToN (unRep n))%F = unRep (FSRepPow width x n).
  Proof. (* this proof derives the required formula, which I copy-pasted above to be able to reference it without the length precondition *)
    unfold FSRepPow; intros.
    erewrite <-pow_nat_iter_op_correct by auto.
    erewrite <-(fun x => iter_op_spec (scalar := SRep) mul F_mul_assoc _ F_mul_1_l _ _ SRep_testbit_correct n x width) by auto.
    rewrite <-(rcFOK 1%F) at 1.
    erewrite <-iter_op_proj;
      [apply eq_refl
      |eauto with typeclass_instances
      |symmetry; eapply FRepMul_correct].
  Qed.

  Context (q_minus_2_lt_l:(q - 2 < l)%Z).
  Definition FRepInv x : FRep := FSRepPow (COMPILETIME (N.size_nat (Z.to_N (q - 2)))) x (COMPILETIME (toRep (ZToField (q - 2)))).
  Lemma FRepInv_correct : forall x, inv (unRep x)%F = unRep (FRepInv x).
    unfold FRepInv, COMPILETIME; intros.
    rewrite <-FSRepPow_correct; rewrite FieldToN_correct, rcSOK, FieldToZ_ZToField, Zmod_small by omega; trivial.
    pose proof @Fq_inv_fermat_correct as Hf; unfold inv_fermat in Hf; rewrite Hf by
        auto using prime_q, two_lt_q.
    reflexivity.
  Qed.
End FSRepOperations.

Section ESRepOperations.
  Context {tep:TwistedEdwardsParams} {a_eq_minus1:a = opp 1}.
  Context {l:Z} {two_lt_l:(2 < l)%Z} `{rep2S : SRep -> F l}.
  Context {SRep_testbit : SRep -> nat -> bool}.
  Context {SRep_testbit_correct : forall (x0 : SRep) (i : nat), SRep_testbit x0 i = N.testbit_nat (FieldToN (rep2S x0)) i}.

  Definition scalarMultExtendedSRep (a:SRep) (P:extendedPoint) :=
    iter_op (@unifiedAddM1 _ a_eq_minus1) (mkExtendedPoint E.zero) SRep_testbit a P (COMPILETIME (N.size_nat (Z.to_N (Z.pred l)))).

  Lemma bound_satisfied : forall a, (N.size_nat (FieldToN (rep2S a)) <= N.size_nat (Z.to_N (Z.pred l)))%nat.
  Proof.
    intros.
    apply N_size_nat_le_mono.
    rewrite FieldToN_correct.
    destruct (FieldToZ_range (rep2S a)); [omega|].
    rewrite <-Z2N.inj_le; omega.
  Qed.
    
  Definition scalarMultExtendedSRep_correct : forall (a:SRep) (P:extendedPoint),
      unExtendedPoint (scalarMultExtendedSRep a P) = (N.to_nat (FieldToN (rep2S a)) * unExtendedPoint P)%E.
  Proof. (* derivation result copy-pasted to above to remove preconditions from it *)
    intros.
    rewrite <-(scalarMultM1_rep a_eq_minus1), <-(@iter_op_spec _ extendedPoint_eq _ _ (@unifiedAddM1 _ a_eq_minus1) _ (@unifiedAddM1_assoc _ a_eq_minus1) _ (@unifiedAddM1_0_l _ a_eq_minus1) _ _ SRep_testbit_correct _ _ _ (bound_satisfied _)).
    reflexivity.
  Defined.
End ESRepOperations.

Section EFRepDefn.
  Context {tep:TwistedEdwardsParams} {a_eq_minus1:a = opp 1}.
  Context `{FRepEquiv_ok:Equivalence FRep FRepEquiv} {F2Rep : F q -> FRep} {rep2F:FRep -> F q} {rep2F_proper: Proper (FRepEquiv==>eq) rep2F} {rep2F_F2Rep: forall x, rep2F (F2Rep x) = x}.
  Definition extended2Rep (P:extended) :=
    let 'mkExtended X Y Z T := P in
    (F2Rep X, F2Rep Y, F2Rep Z, F2Rep T).
  Definition extendedRep2Extended P : extended :=
    let '(X, Y, Z, T) := P in
    mkExtended (rep2F X) (rep2F Y) (rep2F Z) (rep2F T).
  Definition extendedPointInvariant P := rep P (extendedToTwisted P) /\ E.onCurve (extendedToTwisted P).
  Definition extendedRepInvariant XYZT := extendedPointInvariant (extendedRep2Extended XYZT).
  Definition extendedRep := { XYZT | extendedRepInvariant XYZT }.

  Lemma extendedRep2Extended_extended2Rep P : extendedRep2Extended (extended2Rep P) = P.
  Proof. destruct P as [? ? ? ?]; simpl; rewrite !rep2F_F2Rep; reflexivity. Qed.

  Definition extendedPoint2ExtendedRep (P:extendedPoint) : extendedRep. exists (extended2Rep (proj1_sig P)).
  Proof. abstract (unfold extendedRepInvariant; rewrite extendedRep2Extended_extended2Rep; destruct P; eauto). Defined.

  Definition extendedRep2ExtendedPoint (P:extendedRep) : extendedPoint. exists (extendedRep2Extended (proj1_sig P)).
  Proof. abstract (destruct P; eauto). Defined.

  Definition point2ExtendedRep (P:E.point) : extendedRep := (extendedPoint2ExtendedRep (mkExtendedPoint P)).
  Definition extendedRep2Point (P:extendedRep) : E.point := unExtendedPoint (extendedRep2ExtendedPoint P).

  Lemma extendedRep2ExtendedPoint_extendedPoint2ExtendedRep_proj1_sig : forall P,
      proj1_sig (extendedRep2ExtendedPoint (extendedPoint2ExtendedRep P)) = proj1_sig P.
  Proof. destruct P; simpl; rewrite extendedRep2Extended_extended2Rep; reflexivity. Qed.
 
  Definition extendedRepEquiv (P Q:extendedRep) := extendedRep2Point P = extendedRep2Point Q.

  Lemma extendedRepEquiv_iff_extendedPoint P Q : extendedRepEquiv P Q <-> extendedRep2ExtendedPoint P === extendedRep2ExtendedPoint Q.
  Proof. unfold extendedRepEquiv, extendedRep2Point; split; intros; congruence. Qed.

  Global Instance Equivalence_extendedRepEquiv : Equivalence extendedRepEquiv.
  Proof. constructor; intros; congruence. Qed.

  Global Instance Proper_extendedPoint2ExtendedRep : Proper (extendedPoint_eq==>extendedRepEquiv) extendedPoint2ExtendedRep.
  Proof.
    repeat intro. apply E.point_eq.
    rewrite !extendedRep2ExtendedPoint_extendedPoint2ExtendedRep_proj1_sig.
    injection H; trivial.
  Qed.

  Global Instance Proper_extendedRep2Point : Proper (extendedRepEquiv==>eq) extendedRep2Point.
  Proof. repeat intro. congruence. Qed.

  Lemma unExtendedPoint_extendedRep2ExtendedPoint : forall P,
      unExtendedPoint (extendedRep2ExtendedPoint P) = extendedRep2Point P.
  Proof. reflexivity. Qed.

  (* TODO: move *)
  Lemma extendedToTwisted_twistedToExtended : forall P, extendedToTwisted (twistedToExtended P) = P.
  Proof.
    destruct P; unfold extendedToTwisted, twistedToExtended; simpl; rewrite !@F_div_1_r; auto using prime_q.
  Qed.
  Lemma mkExtendedPoint_unExtendedPoint : forall P, mkExtendedPoint (unExtendedPoint P) === P.
  Proof.
    intros.  destruct P; cbv [mkExtendedPoint unExtendedPoint proj1_sig extendedPoint_eq equiv].
    apply E.point_eq. rewrite extendedToTwisted_twistedToExtended; reflexivity.
  Qed.
    
  Lemma extendedRep2Point_point2ExtendedRep : forall P, 
      extendedRep2Point (point2ExtendedRep P) = P.
  Proof.
    intros.
    unfold extendedRep2Point, point2ExtendedRep.
    destruct P; apply E.point_eq.
    rewrite !extendedRep2ExtendedPoint_extendedPoint2ExtendedRep_proj1_sig.
    apply extendedToTwisted_twistedToExtended.
  Qed.

  Lemma point2ExtendedRep_unExtendedPoint : forall P,
      (point2ExtendedRep (unExtendedPoint P)) === extendedPoint2ExtendedRep P.
  Proof.
    intros. unfold point2ExtendedRep. f_equiv. apply mkExtendedPoint_unExtendedPoint.
  Qed.

  Lemma point2ExtendedRep_extendedRep2Point : forall P, point2ExtendedRep (extendedRep2Point P) === P.
  Proof.
    intros; unfold equiv, extendedRepEquiv; pose proof extendedRep2Point_point2ExtendedRep; congruence.
  Qed.

  Global Instance Proper_extendedRepInvariant : Proper ((fieldwise (n:=4) FRepEquiv) ==> Basics.impl) (extendedRepInvariant).
  Proof.
    repeat intro; cbv [tuple tuple' fieldwise fieldwise' extendedRepInvariant extendedRep2Extended] in *.
    repeat match goal with
           | [x : prod _ _ |- _ ] => destruct x
           end.
    simpl in *; intuition.
    repeat match goal with
           | [H: FRepEquiv _ _ |- _ ] => rewrite <- H; []
           end; trivial.
  Qed.

  Lemma extendedRep_proof_equiv: forall x y px py, fieldwise (n:=4) FRepEquiv x y -> 
    exist extendedRepInvariant x px === exist extendedRepInvariant y py.
  Proof.
    destruct x as [[[]]]; destruct y as [[[]]]; simpl in *; intuition.
    apply E.point_eq. unfold extendedRep2ExtendedPoint; simpl.
    repeat match goal with
           | [H: FRepEquiv _ _ |- _ ] => rewrite <- H; []
           end; trivial.
  Qed.

  Definition extended2Rep_mkExtended x y z t :
    extended2Rep (mkExtended x y z t) = (F2Rep x, F2Rep y, F2Rep z, F2Rep t) := eq_refl.

  Context `{F2Rep_rep2F: forall x, F2Rep (rep2F x) === x}.
  Existing Instances tep FRepEquiv_ok.

  Context `{FRepAdd_correct:forall a b, F2Rep (add a b) === FRepAdd (F2Rep a) (F2Rep b)} {FRepAdd_proper: Proper (FRepEquiv==>FRepEquiv==>FRepEquiv) FRepAdd}.
  Context `{FRepMul_correct:forall a b, F2Rep (mul a b) === FRepMul (F2Rep a) (F2Rep b)} {FRepMul_proper: Proper (FRepEquiv==>FRepEquiv==>FRepEquiv) FRepMul}.
  Context `{FRepSub_correct:forall a b, F2Rep (sub a b) === FRepSub (F2Rep a) (F2Rep b)} {FRepSub_proper: Proper (FRepEquiv==>FRepEquiv==>FRepEquiv) FRepSub}.
  Context {FRepInv:FRep->FRep} {FRepInv_correct:forall x, F2Rep (inv x) === FRepInv (F2Rep x)} {FRepInv_proper: Proper (FRepEquiv==>FRepEquiv) FRepInv}.
  Context {FRepOpp : FRep -> FRep} {FRepOpp_correct : forall x, F2Rep (opp x) = FRepOpp (F2Rep x)} {FRepOpp_proper: Proper (FRepEquiv==>FRepEquiv) FRepOpp}.

  Create HintDb toFRep discriminated.
  Hint Rewrite
       @unfoldDiv
       FRepAdd_correct FRepMul_correct FRepSub_correct FRepInv_correct FRepOpp_correct
       F2Rep_rep2F
    : toFRep.

  Definition extendedRepAdd_sig : forall P Q,
      { x | forall Pref Qref,
            P === point2ExtendedRep Pref
          -> Q === point2ExtendedRep Qref
          -> x === point2ExtendedRep (E.add Pref Qref)}.
  Proof.
    destruct P as [[[[]]] ?]; destruct Q as [[[[]]] ?].
    eexists; intros ? ? HP HQ; fold_identity_lambdas.

    match goal with
      [ Hx : ?x === point2ExtendedRep ?p, Hy : ?y === point2ExtendedRep ?q |- _ ]
      => pose proof unifiedAddM1_rep a_eq_minus1 (extendedRep2ExtendedPoint x) (extendedRep2ExtendedPoint y) as H;
          setoid_rewrite unExtendedPoint_extendedRep2ExtendedPoint in H;
          rewrite HP, HQ, !extendedRep2Point_point2ExtendedRep in H;
          rewrite H; clear H Hx Hy; try clear p q
    end.
    
    rewrite point2ExtendedRep_unExtendedPoint.
    
    symmetry;
      eapply (path_sig (RA:=fieldwise (n:=4) FRepEquiv));
      eapply extendedRep_proof_equiv; assumption.

    Grab Existential Variables.
    cbv iota beta delta [proj1_sig extendedRep2Extended extendedRep2ExtendedPoint extendedPoint2ExtendedRep unifiedAddM1 unifiedAddM1'].

    assert (Proper (eq==>fieldwise (n:=4) FRepEquiv) extended2Rep) as HProper by admit.
    etransitivity; [
                     eapply HProper;
                     repeat (replace_let_in_with_Let_In;
                             eapply Let_In_Proper_changebody;
                             [reflexivity|
                              cbv beta delta [pointwise_relation]; intro
                            ]);
                     reflexivity|].

    Local Opaque Let_In.
    repeat setoid_rewrite <-(pull_Let_In extended2Rep). setoid_rewrite extended2Rep_mkExtended.

    Ltac pattern_reflexivity :=
      intros;
      try reflexivity;
      lazymatch goal with
        |- _ ?LHS (?f ?a) =>
        let t := eval pattern a in LHS in
            lazymatch t with
              ?LHS' ?x => unify LHS' f; reflexivity
            end
      end.
    
    Ltac descend :=
      idtac; (
        lazymatch goal with
          |- ?R (Let_In ?x ?f) ?RHS  =>
          let A := type of x in
          eapply (@Let_In_Proper_changebody A _ R);
          [eauto with typeclass_instances
          |reflexivity
          |cbv beta delta [pointwise_relation]; intro]
        end || fail "goal must be of the form [LetIn _ _ == _]").

    Ltac inLetInBody' t :=
      etransitivity; [descend; t; pattern_reflexivity|].
    Tactic Notation "inLetInBody" tactic3(t) := inLetInBody' t.

    Ltac inLetInValue' properTac rewriteTac :=
      etransitivity;
      [eapply (Let_In_Proper_changevalue equiv); [properTac|rewriteTac; pattern_reflexivity]|].
    Tactic Notation "inLetInValue" tactic3(rewriteTac) := inLetInValue' idtac rewriteTac.
    Tactic Notation "inLetInValue" tactic3(rewriteTac) "by" tactic3(properTac) := inLetInValue' properTac rewriteTac.
    Ltac prtc := abstract (repeat intro; repeat rewrite unfold_Let_In; simpl; intuition; repeat f_equiv; assumption).

    etransitivity.

    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.
    etransitivity.
    descend.

    pattern_reflexivity.
    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 

    erewrite <- Let_app_In' with (g:=F2Rep); [|pattern_reflexivity];
      try (inLetInValue (rewrite_strat topdown hints toFRep) by prtc).
    pattern_reflexivity. 
     
    rewrite_strat bottomup unfold_Let_In.

    reflexivity.
  Defined.

  Definition extendedRepAdd (P Q:extendedRep) : extendedRep :=
    Eval cbv beta delta [proj1_sig extendedRepAdd_sig] in (proj1_sig (extendedRepAdd_sig P Q)).

  Lemma extendedRepAdd_correct : forall P Q,
    point2ExtendedRep (E.add P Q) === extendedRepAdd (point2ExtendedRep P) (point2ExtendedRep Q).
  Proof.
    intros.
    rewrite (proj2_sig (extendedRepAdd_sig (point2ExtendedRep P) (point2ExtendedRep Q)) P Q); reflexivity.
  Qed.

  Lemma extendedRepAdd_proper : Proper (extendedRepEquiv==>extendedRepEquiv==>extendedRepEquiv) extendedRepAdd.
  Proof.
    repeat intro.
    pose proof (proj2_sig (extendedRepAdd_sig x x0) (extendedRep2Point x) (extendedRep2Point x0)) as H1.
    pose proof (proj2_sig (extendedRepAdd_sig y y0) (extendedRep2Point y) (extendedRep2Point y0)) as H2.
    rewrite !point2ExtendedRep_extendedRep2Point in *.
    setoid_rewrite H1; try setoid_rewrite H2; congruence.
  Qed.

  Context {l:Z} {two_lt_l:(2 < l)%Z} `{S2Rep : F l -> SRep} {rep2S : SRep -> F l}.
  Context`{SRepEquiv_ok:Equivalence SRep SRepEquiv} {rep2S_Proper: Proper (SRepEquiv==>eq) rep2S}.
  Context {rep2S_S2Rep: forall x, rep2S (S2Rep x) = x}.

  Context {SRep_testbit : SRep -> nat -> bool}.
  Context {SRep_testbit_correct : forall (x0 : SRep) (i : nat), SRep_testbit x0 i = N.testbit_nat (FieldToN (rep2S x0)) i}.

  Lemma FieldToNat_natToField' {m:Z} (x:nat) : (0<m)%Z -> FieldToNat (@natToField m x) = x mod (Z.to_nat m).
    intros. symmetry.
    pose proof (fun pf => @FieldToNat_natToField (Z.to_nat m) pf x) as Hn.
    rewrite Z2Nat.id in Hn by omega.
    apply Hn; pose (Z2Nat.inj_le m 0); omega.
  Qed.

  Definition N_to_nat_FieldToN {m} (x : F m) : N.to_nat (FieldToN x) = FieldToNat x.
  Proof. intros. apply Z_N_nat. Qed.

  Definition extendedRepMul_sig : forall (n:SRep) (P:extendedRep),
      { x | forall (nref:nat) (Pref:E.point),
          nref = nref mod Z.to_nat l
          -> n === S2Rep (natToField nref)
          -> P === point2ExtendedRep Pref
          -> x === point2ExtendedRep (E.mul nref Pref)}.
  Proof.
    eexists; intros ? ? nred nRep PRep.

    pose proof (@scalarMultExtendedSRep_correct tep a_eq_minus1 l two_lt_l SRep rep2S SRep_testbit SRep_testbit_correct n (extendedRep2ExtendedPoint P)) as H.
    rewrite unExtendedPoint_extendedRep2ExtendedPoint in H.
    rewrite PRep, extendedRep2Point_point2ExtendedRep in H.
    replace (rep2S n) with (@natToField l nref) in H by (rewrite nRep, rep2S_S2Rep; reflexivity).
    replace (N.to_nat (FieldToN (natToField nref))) with nref in H
      by (rewrite N_to_nat_FieldToN, FieldToNat_natToField', <-nred; intuition omega).
    rewrite <-H; clear H nref nred nRep PRep.

    setoid_rewrite point2ExtendedRep_unExtendedPoint.
    setoid_rewrite (iter_op_proj _ _ extendedRepAdd). (* FIXME: Finished transaction in 5. secs (5.169999u,0.s) *)
    Lemma extendedPoint2ExtendedRep_extendedRep2ExtendedPoint :
      forall P, extendedPoint2ExtendedRep (extendedRep2ExtendedPoint P) === P.
    Admitted.
    Lemma Proper_iter_op : forall {T S} {TR:relation T} {SR:relation S} op zero testbit,
        Proper (SR==>TR==>eq==>TR) (@iter_op T S op zero testbit).
    Proof.
      unfold iter_op; intros.
      repeat intro; subst.
    Admitted.
    etransitivity.
    2:eapply Proper_iter_op.
    2:apply eq_refl.
    2:setoid_rewrite extendedPoint2ExtendedRep_extendedRep2ExtendedPoint; reflexivity.
    2:reflexivity.

    Definition extendedPoint2ExtendedRep_mkExtendedPoint P :
        (extendedPoint2ExtendedRep (mkExtendedPoint P)) = point2ExtendedRep P := eq_refl.

    rewrite extendedPoint2ExtendedRep_mkExtendedPoint.

    match goal with |- context [?f E.zero] => change (f E.zero) with (COMPILETIME (f E.zero)) end.
      
    reflexivity.
  Defined.


End EFRepDefn.

Section EdDSADerivation.
  Context `{eddsaprm:EdDSAParams}.
  Context `{ERepEquiv_ok:Equivalence ERep ERepEquiv} {E2Rep : E.point -> ERep}.
  Context `{SRepEquiv_ok:Equivalence SRep SRepEquiv} {S2Rep : F (Z.of_nat l) -> SRep}.

  Context `{ERepEnc_correct : forall (P:E.point), enc P = ERepEnc (E2Rep P)} {ERepEnc_proper:Proper (ERepEquiv==>eq) ERepEnc}.

  Context `{ERepAdd_correct : forall (P Q:E.point), E2Rep (E.add P Q) === ERepAdd (E2Rep P) (E2Rep Q)} {ERepAdd_proper:Proper (ERepEquiv==>ERepEquiv==>ERepEquiv) ERepAdd}.
  Context `{ESRepMul_correct : forall (n:F (Z.of_nat l)) (Q:E.point), E2Rep (E.mul (FieldToNat n) Q) === ESRepMul (S2Rep (ZToField n)) (E2Rep Q)} {ESRepMul_proper : Proper (SRepEquiv==>ERepEquiv==>ERepEquiv) ESRepMul}.
  Context `{ERepOpp_correct : forall P:E.point, E2Rep (E.opp P) === ERepOpp (E2Rep P)} {ERepOpp_proper:Proper (ERepEquiv==>ERepEquiv) ERepOpp}.

  Context `{SRepDec_correct : forall x, option_map (fun x : F (Z.of_nat l) => S2Rep x) (dec x) === SRepDec x}.
  Context `{ERepDec_correct:forall P_, option_map E2Rep (dec P_) === ERepDec P_}.

  Axiom nonequivalent_optimization_Hmodl : forall n (x:word n) A, (wordToNat (H x) * A = (wordToNat (H x) mod l * A))%E.
  Axiom (SRepH:forall {n}, word n -> SRep).
  Axiom SRepH_correct : forall {n} (x:word n), S2Rep (natToField (H x)) === SRepH x.

  (* TODO: move to EdDSAProofs *)
  Lemma two_lt_l : (2 < Z.of_nat l)%Z.
  Proof.
    pose proof l_odd. omega.
  Qed.
  Lemma l_nonzero : l <> 0.
  Proof.
    pose proof l_odd. omega.
  Qed.

  Local Infix "++" := Word.combine.
  Local Infix "==?" := E.point_eqb (at level 70) : E_scope.
  Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
  Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).
  Local Arguments H {_ _} _.

  Lemma solve_for_R_eq : forall A B C, (A = B + C <-> B = A - C)%E.
  Proof.
    intros; split; intros; subst; unfold E.sub;
      rewrite <-E.add_assoc, ?E.add_opp_r, ?E.add_opp_l, E.add_0_r; reflexivity.
  Qed.
  
  Lemma solve_for_R : forall A B C, (A ==? B + C)%E = (B ==? A - C)%E.
  Proof.
    intros;
      rewrite !E.point_eqb_correct;
      repeat match goal with |- context[E.point_eq_dec ?x ?y] => destruct (E.point_eq_dec x y) end;
      rewrite solve_for_R_eq in *;
      congruence.
  Qed.

  Create HintDb toESRep discriminated.
  Hint Rewrite <-E.point_eqb_correct : toESRep.
  Hint Rewrite
    nonequivalent_optimization_Hmodl
    (FieldToNat_natToField l_nonzero)

    (fun n => solve_for_R (n * B)%E)
    (compare_without_decoding PointEncoding _ E_eqb_iff _ (@weqb_true_iff _))

    unfold_E_sub
    E.opp_mul

    ESRepMul_correct
    ERepAdd_correct
    ERepEnc_correct
    ERepOpp_correct

    @ZToField_FieldToZ
    @SRepH_correct : toESRep.

  Ltac recursive_replace_option_match_with_option_rect :=
    etransitivity;
    [|
     repeat match goal with 
            | [ |- ?x = ?x ] => reflexivity
            | _ => replace_option_match_with_option_rect
            | [ |- _ = option_rect _ _ _ _ ]
              => eapply option_rect_Proper_nd; [ intro | reflexivity.. ]
            end;
     reflexivity].
  
  Lemma sharper_verify : forall pk l msg sig, { sherper_verify | sherper_verify = verify (n:=l) pk msg sig}.
  Proof.
    eexists; cbv [EdDSA.verify]; intros.

    recursive_replace_option_match_with_option_rect.
    
    rewrite_strat topdown hints toESRep.
    setoid_rewrite ESRepMul_correct. (* TODO: change the spec to use FieldToNat instead of (Z.to_nat (ZToField _))*)
    rewrite_strat topdown hints toESRep.
    
    (* decoding of  S : option_rect (F l) -> option_map SRep *)
    (* TODO: we want this section to look more like the following:
        setoid_rewrite (@option_rect_option_map (F (Z.of_nat EdDSA.l)) _ bool toRep). *)
    etransitivity.
    Focus 2.
    { lazymatch goal with |- _ = option_rect _ _ ?false ?dec =>
                          symmetry; etransitivity; [|eapply (option_rect_option_map (fun (x:F _) => S2Rep x) _ false dec)]
      end.
      eapply option_rect_Proper_nd; [intro | reflexivity.. ].
      match goal with
      | [ |- ?RHS = ?e ?v ]
        => let RHS' := (match eval pattern v in RHS with ?RHS' _ => RHS' end) in
           unify e RHS'
      end.
      reflexivity.
    } Unfocus.
    rewrite SRepDec_correct.

    (* decoding of A : option_rect E.point -> option_map E2Rep *)
    (* TODO: automate *)
    etransitivity.
    Focus 2.
    { do 1 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
      set_evars.
      lazymatch goal with |- _ = option_rect _ _ ?false ?dec =>
                          symmetry; etransitivity; [|eapply (option_rect_option_map E2Rep _ false dec)]
      end.
      eapply option_rect_Proper_nd; [intro|reflexivity..].
      match goal with
      | [ |- ?RHS = ?e ?v ]
        => let RHS' := (match eval pattern v in RHS with ?RHS' _ => RHS' end) in
           unify e RHS'
      end.
      reflexivity.
    } Unfocus.
    rewrite ERepDec_correct.

    reflexivity.
  Defined.
  
  (*

    (** start dropping sigma-types from Extended points **)

    setoid_rewrite point_enc_coordinates_correct.
    cbv beta delta [unExtendedPoint unifiedAddM1 negateExtended scalarMultExtendedSRep E.opp].
    unfold_proj1_sig_exist.

    etransitivity.
    Focus 2.
    { do 2 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
      set_evars.
      repeat match goal with
             | [ |- appcontext[@proj1_sig ?A ?P (@iter_op ?T ?f ?neutral ?T' ?testbit ?exp ?base ?bound)] ]
               => erewrite (@iter_op_proj T _ _ (@proj1_sig _ _)) by reflexivity
             end.
      subst_evars.
      reflexivity. }
    Unfocus.

    cbv [mkExtendedPoint E.zero].
    unfold_proj1_sig_exist.
    rewrite B_proj.

    (* decoding of A : option_rect E.point -> option_map (F q * F q) *)
    (* TODO: change to (FRep * FRep) instead *)
    etransitivity.
    Focus 2.
    { do 1 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
      set_evars.
      lazymatch goal with |- _ = option_rect _ _ ?false ?dec =>
                          symmetry; etransitivity; [|eapply (option_rect_option_map (@proj1_sig _ _) _ false dec)]
      end.
      eapply option_rect_Proper_nd; [intro|reflexivity..].
      match goal with
      | [ |- ?RHS = ?e ?v ]
        => let RHS' := (match eval pattern v in RHS with ?RHS' _ => RHS' end) in
           unify e RHS'
      end.
      reflexivity.
    } Unfocus.

    (* TODO: this is specific to the encoding pattern (but not specific parameters:
    etransitivity.
    Focus 2.
    { do 1 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
      etransitivity.
      Focus 2.
      { apply f_equal.
        symmetry.
        apply point_dec_coordinates_correct. }
      Unfocus.
      reflexivity. }
    Unfocus.

    cbv iota beta delta [point_dec_coordinates sign_bit dec FqEncoding modular_word_encoding E.solve_for_x2 sqrt_mod_q].

    etransitivity.
    Focus 2. {
      do 1 (eapply option_rect_Proper_nd; [|reflexivity..]). cbv beta delta [pointwise_relation]. intro.
      etransitivity.
      Focus 2.
      { apply f_equal.
        lazymatch goal with
        | [ |- _ = ?term :> ?T ]
          => lazymatch term with (match ?a with None => ?N | Some x => @?S x end)
                                 => let term' := constr:((option_rect (fun _ => T) S N) a) in
                                    replace term with term' by reflexivity
             end
        end.
        reflexivity. } Unfocus. reflexivity. } Unfocus.

    etransitivity.
    Focus 2. {
      do 1 (eapply option_rect_Proper_nd; [cbv beta delta [pointwise_relation]; intro|reflexivity..]).
      do 1 (eapply option_rect_Proper_nd; [ intro; reflexivity | reflexivity | ]).
      eapply option_rect_Proper_nd; [ cbv beta delta [pointwise_relation]; intro | reflexivity.. ].
      replace_let_in_with_Let_In.
      reflexivity.
    } Unfocus.

    etransitivity.
    Focus 2. {
      do 1 (eapply option_rect_Proper_nd; [cbv beta delta [pointwise_relation]; intro|reflexivity..]).
      set_evars.
      rewrite option_rect_function. (* turn the two option_rects into one *)
      subst_evars.
      simpl_option_rect.
      do 1 (eapply option_rect_Proper_nd; [cbv beta delta [pointwise_relation]; intro|reflexivity..]).
      (* push the [option_rect] inside until it hits a [Some] or a [None] *)
      repeat match goal with
             | _ => commute_option_rect_Let_In
             | [ |- _ = Let_In _ _ ]
               => apply Let_In_Proper_nd; [ reflexivity | cbv beta delta [pointwise_relation]; intro ]
             | [ |- ?LHS = option_rect ?P ?S ?N (if ?b then ?t else ?f) ]
               => transitivity (if b then option_rect P S N t else option_rect P S N f);
                    [
                    | destruct b; reflexivity ]
             | [ |- _ = if ?b then ?t else ?f ]
               => apply (f_equal2 (fun x y => if b then x else y))
             | [ |- _ = false ] => reflexivity
             | _ => progress simpl_option_rect
             end.
      reflexivity.
    } Unfocus.

    setoid_rewrite wire2FRep_correct.
    *)

    etransitivity.
    Focus 2. {
      eapply option_rect_Proper_nd; [|reflexivity..]. cbv beta delta [pointwise_relation]. intro.
      rewrite <-!(option_rect_option_map rep2F).
      eapply option_rect_Proper_nd; [|reflexivity..]. cbv beta delta [pointwise_relation]. intro.
      autorewrite with EdDSA_opts.
      rewrite <-(rcFOK 1%F).
      pattern Ed25519.d at 1. rewrite <-(rcFOK Ed25519.d) at 1.
      pattern Ed25519.a at 1. rewrite <-(rcFOK Ed25519.a) at 1.
      rewrite <- (rcSOK (Z.to_N (Ed25519.q / 8 + 1))).
      autorewrite with EdDSA_opts.
      (Let_In_unRep).
      eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro].
      etransitivity. Focus 2. eapply Let_In_Proper_nd; [|cbv beta delta [pointwise_relation]; intro;reflexivity]. {
        rewrite FSRepPow_correct by (rewrite rcSOK; cbv; omega).
        (Let_In_unRep).
        etransitivity. Focus 2. eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro]. {
          set_evars.
          rewrite <-(rcFOK sqrt_minus1).
          autorewrite with EdDSA_opts.
          subst_evars.
          reflexivity. } Unfocus.
        rewrite pull_Let_In.
        reflexivity. } Unfocus.
      set_evars.
      (Let_In_unRep).

      subst_evars. eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro]. set_evars.

      autorewrite with EdDSA_opts.

      subst_evars.
      lazymatch goal with  |- _ = if ?b then ?t else ?f => apply (f_equal2 (fun x y => if b then x else y)) end; [|reflexivity].
      eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro].
      set_evars.

      unfold twistedToExtended.
      autorewrite with EdDSA_opts.
      progress cbv beta delta [erep2trep].

      subst_evars.
      reflexivity. } Unfocus.
    reflexivity.
  Defined.
End EdDSADerivation.
*)