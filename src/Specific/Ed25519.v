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
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
  
(*TODO: move enerything before the section out of this file *)

Local Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.
Local Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Global Instance Let_In_Proper_nd {A P}
  : Proper (eq ==> pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => P)).
Proof.
  lazy; intros; congruence.
Qed.

Local Ltac replace_let_in_with_Let_In :=
  repeat match goal with
         | [ |- context G[let x := ?y in @?z x] ]
           => let G' := context G[Let_In y z] in change G'
         | [ |- _ = Let_In _ _ ]
           => apply Let_In_Proper_nd; [ reflexivity | cbv beta delta [pointwise_relation]; intro ]
         end.

Lemma funexp_proj {T T'} (proj : T -> T') (f : T -> T) (f' : T' -> T') x n
      (f_proj : forall a, proj (f a) = f' (proj a))
  : proj (funexp f x n) = funexp f' (proj x) n.
Proof.
  revert x; induction n as [|n IHn]; simpl; congruence.
Qed.

Lemma iter_op_proj {T T' S} (proj : T -> T') (op : T -> T -> T) (op' : T' -> T' -> T') x y z
      (testbit : S -> nat -> bool) (bound : nat)
      (op_proj : forall a b, proj (op a b) = op' (proj a) (proj b))
  : proj (iter_op op x testbit y z bound) = iter_op op' (proj x) testbit y (proj z) bound.
Proof.
  unfold iter_op.
  simpl.
  lazymatch goal with
  | [ |- ?proj (snd (funexp ?f ?x ?n)) = snd (funexp ?f' _ ?n) ]
    => pose proof (fun x0 x1 => funexp_proj (fun x => (fst x, proj (snd x))) f f' (x0, x1)) as H'
  end.
  simpl in H'.
  rewrite <- H'.
  { reflexivity. }
  { intros [??]; simpl.
    repeat match goal with
           | [ |- context[match ?n with _ => _ end] ]
             => destruct n eqn:?
           | _ => progress simpl
           | _ => progress subst
           | _ => reflexivity
           | _ => rewrite op_proj
           end. }
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

Generalizable All Variables.
Section FSRepOperations.
  Context {q:Z} {prime_q:Znumtheory.prime q} {two_lt_q:(2 < q)%Z}.
  Context `(rcS:RepConversions N SRep) (rcSOK:RepConversionsOK rcS).
  Context `(rcF:RepConversions (F q) FRep) (rcFOK:RepConversionsOK rcF).
  Context (FRepAdd FRepSub FRepMul:FRep->FRep->FRep) (FRepAdd_correct:RepBinOpOK rcF add FRepMul).
  Context (FRepSub_correct:RepBinOpOK rcF sub FRepSub) (FRepMul_correct:RepBinOpOK rcF mul FRepMul).
  Axiom SRep_testbit : SRep -> nat -> bool.
  Axiom SRep_testbit_correct : forall (x0 : SRep) (i : nat), SRep_testbit x0 i = N.testbit_nat (unRep x0) i.

  Definition FSRepPow width x n := iter_op FRepMul (toRep 1%F) SRep_testbit n x width.
  Lemma FSRepPow_correct : forall width x n, (N.size_nat (unRep n) <= width)%nat -> (unRep x ^ unRep n)%F = unRep (FSRepPow width x n).
  Proof. (* this proof derives the required formula, which I copy-pasted above to be able to reference it without the length precondition *)
    unfold FSRepPow; intros.
    erewrite <-pow_nat_iter_op_correct by auto.
    erewrite <-(fun x => iter_op_spec (scalar := SRep) mul F_mul_assoc _ F_mul_1_l _ unRep SRep_testbit_correct n x width) by auto.
    rewrite <-(rcFOK 1%F) at 1.
    erewrite <-iter_op_proj by auto.
    reflexivity.
  Qed.

  Definition FRepInv x : FRep := FSRepPow (COMPILETIME (N.size_nat (Z.to_N (q - 2)))) x (COMPILETIME (toRep (Z.to_N (q - 2)))).
  Lemma FRepInv_correct : forall x, inv (unRep x)%F = unRep (FRepInv x).
    unfold FRepInv, COMPILETIME; intros.
    rewrite <-FSRepPow_correct; rewrite rcSOK; try reflexivity.
    pose proof @Fq_inv_fermat_correct as H; unfold inv_fermat in H; rewrite H by
        auto using prime_q, two_lt_q.
    reflexivity.
  Qed.
End FSRepOperations.

Section ESRepOperations.
  Context {tep:TwistedEdwardsParams} {a_is_minus1:a = opp 1}.
  Context `{rcS:RepConversions N SRep} {rcSOK:RepConversionsOK rcS}.
  Context {SRep_testbit : SRep -> nat -> bool}.
  Context {SRep_testbit_correct : forall (x0 : SRep) (i : nat), SRep_testbit x0 i = N.testbit_nat (unRep x0) i}.
  Definition scalarMultExtendedSRep (bound:nat) (a:SRep) (P:extendedPoint) :=
    unExtendedPoint (iter_op (@unifiedAddM1 _ a_is_minus1) (mkExtendedPoint E.zero) SRep_testbit a P bound).
  Definition scalarMultExtendedSRep_correct : forall (bound:nat) (a:SRep) (P:extendedPoint) (bound_satisfied:(N.size_nat (unRep a) <= bound)%nat),
      scalarMultExtendedSRep bound a P = (N.to_nat (unRep a) * unExtendedPoint P)%E.
  Proof. (* derivation result copy-pasted to above to remove preconditions from it *)
    intros.
    rewrite <-(scalarMultM1_rep a_is_minus1), <-(@iter_op_spec _ extendedPoint_eq _ _ (@unifiedAddM1 _ a_is_minus1) _ (@unifiedAddM1_assoc _ a_is_minus1) _ (@unifiedAddM1_0_l _ a_is_minus1) _ _ SRep_testbit_correct _ _ bound) by assumption.
    reflexivity.
  Defined.
End ESRepOperations.

Section EdDSADerivation.
  Context `(eddsaprm:EdDSAParams).
  Context `(rcS:RepConversions N SRep) (rcSOK:RepConversionsOK rcS).
  Context `(rcF:RepConversions (F q) FRep) (rcFOK:RepConversionsOK rcF).
  Context (FRepAdd FRepSub FRepMul:FRep->FRep->FRep) (FRepAdd_correct:RepBinOpOK rcF add FRepMul).
  Context (FRepSub_correct:RepBinOpOK rcF sub FRepSub) (FRepMul_correct:RepBinOpOK rcF mul FRepMul).
  Context (FSRepPow:FRep->SRep->FRep) (FSRepPow_correct: forall x n, (N.size_nat (unRep n) <= (N.size_nat (N.of_nat l)))%nat -> (unRep x ^ unRep n)%F = unRep (FSRepPow x n)).
  Context (FRepInv:FRep->FRep) (FRepInv_correct:forall x, inv (unRep x)%F = unRep (FRepInv x)).
  Context (a_is_minus1:CompleteEdwardsCurve.a = opp 1).

  Local Infix "++" := Word.combine.
  Local Infix "==?" := E.point_eqb (at level 70) : E_scope.
  Local Infix "==?" := ModularArithmeticTheorems.F_eq_dec (at level 70) : F_scope.
  Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
  Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).
  Local Arguments H {_ _} _.
  Local Arguments unifiedAddM1 {_} {_} _ _.

  (*TODO:move*)
  Lemma F_eqb_iff : forall x y : F q, F_eqb x y = true <-> x = y.
  Proof.
    split; eauto using F_eqb_eq, F_eqb_complete.
  Qed.
  Lemma E_eqb_iff : forall x y : E.point, E.point_eqb x y = true <-> x = y.
  Proof.
    split; eauto using E.point_eqb_sound, E.point_eqb_complete.
  Qed.
  
  Lemma B_proj : proj1_sig B = (fst(proj1_sig B), snd(proj1_sig B)). destruct B as [[]]; reflexivity. Qed.

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

  Axiom decode_scalar : word b -> option N.
  Axiom decode_scalar_correct : forall x, decode_scalar x = option_map (fun x : F (Z.of_nat l) => Z.to_N x) (dec x).
  
  Axiom enc':(F q * F q) -> word b.
  Axiom enc'_correct : @enc E.point _ _ = (fun x => enc' (proj1_sig x)).

  Axiom FRepOpp : FRep -> FRep.
  Axiom FRepOpp_correct : forall x, opp (unRep x) = unRep (FRepOpp x).

  Axiom wltu : forall {b}, word b -> word b -> bool.
  Axiom wltu_correct : forall {b} (x y:word b), wltu x y = (wordToN x <? wordToN y)%N.

  Axiom wire2FRep : word (b-1) -> option FRep.
  Axiom wire2FRep_correct : forall x, Fm_dec x = option_map unRep (wire2FRep x).

  Axiom FRep2wire : FRep -> word (b-1).
  Axiom FRep2wire_correct : forall x, FRep2wire x = @enc _ _ FqEncoding (unRep x).
  
  Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended X Y Z T).
  Local Notation "2" := (ZToField 2) : F_scope.

  Lemma unfoldDiv : forall {m} (x y:F m), (x/y = x * inv y)%F. Proof. unfold div. congruence. Qed.

  Definition rep2E (r:FRep * FRep * FRep * FRep) : extended :=
    match r with (((x, y), z), t) => mkExtended (unRep x) (unRep y) (unRep z) (unRep t) end.

  Lemma if_map : forall {T U} (f:T->U) (b:bool) (x y:T), (if b then f x else f y) = f (if b then x else y).
  Proof.
    destruct b; trivial.
  Qed.

  (** TODO: Move me *)
  Local Ltac Let_In_app fn :=
    match goal with
    | [ |- appcontext G[Let_In (fn ?x) ?f] ]
      => change (Let_In (fn x) f) with (Let_In x (fun y => f (fn y))); cbv beta
    end.

  Lemma pull_Let_In {B C} (f : B -> C) A (v : A) (b : A -> B)
    : Let_In v (fun v' => f (b v')) = f (Let_In v b).
  Proof.
    reflexivity.
  Qed.

  Lemma Let_app_In {A B T} (g:A->B) (f:B->T) (x:A) :
      @Let_In _ (fun _ => T) (g x) f =
      @Let_In _ (fun _ => T) x (fun p => f (g x)).
  Proof. reflexivity. Qed.

  Lemma Let_app2_In {A B C D T} (g1:A->C) (g2:B->D) (f:C*D->T) (x:A) (y:B) :
      @Let_In _ (fun _ => T) (g1 x, g2 y) f =
      @Let_In _ (fun _ => T) (x, y) (fun p => f ((g1 (fst p), g2 (snd p)))).
  Proof. reflexivity. Qed.


  Create HintDb FRepOperations discriminated.
  Hint Rewrite FRepMul_correct FRepAdd_correct FRepSub_correct @FRepInv_correct @FSRepPow_correct FRepOpp_correct : FRepOperations.

  Create HintDb EdDSA_opts discriminated.
  Hint Rewrite FRepMul_correct FRepAdd_correct FRepSub_correct @FRepInv_correct @FSRepPow_correct FRepOpp_correct : EdDSA_opts.

  Lemma unifiedAddM1Rep_sig : forall a b : FRep * FRep * FRep * FRep, { unifiedAddM1Rep | rep2E unifiedAddM1Rep = unifiedAddM1' (rep2E a) (rep2E b) }.
  Proof.
    destruct a as [[[]]]; destruct b as [[[]]].
    eexists.
    lazymatch goal with |- ?LHS = ?RHS :> ?T =>
                    evar (e:T); replace LHS with e; [subst e|]
    end.
    unfold rep2E. cbv beta delta [unifiedAddM1'].
    pose proof (rcFOK twice_d) as H; rewrite <-H; clear H. (* XXX: this is a hack -- rewrite misresolves typeclasses? *)

    { etransitivity; [|replace_let_in_with_Let_In; reflexivity].
      repeat (
        autorewrite with FRepOperations;
        Let_In_app unRep;
        eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [Proper respectful pointwise_relation]; intro]).
        lazymatch goal with |- ?LHS = (unRep ?x, unRep ?y, unRep ?z, unRep ?t) =>
                            change (LHS = (rep2E (((x, y), z), t)))
        end.
        reflexivity. }

    subst e.
    Local Opaque Let_In.
    repeat setoid_rewrite (pull_Let_In rep2E).
    Local Transparent Let_In.
    reflexivity.
  Defined.

  Definition unifiedAddM1Rep (a b:FRep * FRep * FRep * FRep) : FRep * FRep * FRep * FRep := Eval hnf in proj1_sig (unifiedAddM1Rep_sig a b).
  Definition unifiedAddM1Rep_correct a b : rep2E (unifiedAddM1Rep a b) = unifiedAddM1' (rep2E a) (rep2E b)  := Eval hnf in proj2_sig (unifiedAddM1Rep_sig a b).

  Definition rep2T (P:FRep * FRep) := (unRep (fst P), unRep (snd P)).
  Definition erep2trep (P:FRep * FRep * FRep * FRep) := Let_In P (fun P => Let_In (FRepInv (snd (fst P))) (fun iZ => (FRepMul (fst (fst (fst P))) iZ, FRepMul (snd (fst (fst P))) iZ))).
  Lemma erep2trep_correct : forall P, rep2T (erep2trep P) = extendedToTwisted (rep2E P).
  Proof.
    unfold rep2T, rep2E, erep2trep, extendedToTwisted; destruct P as [[[]]]; simpl.
    rewrite !unfoldDiv, <-!FRepMul_correct, <-FRepInv_correct. reflexivity.
  Qed.

  Lemma Fl_SRep_bound : forall (a:F (Z.of_nat EdDSA.l)), (N.size_nat (unRep (toRep (Z.to_N (FieldToZ a)))) <= N.size_nat (Z.to_N (Z.pred (Z.of_nat EdDSA.l))))%nat.
  Proof.
    intros.
    rewrite rcSOK.
    apply N_size_nat_le_mono.
    pose proof l_odd.
    edestruct (FieldToZ_range a); [omega|].
    apply Znat.Z2N.inj_le; trivial; omega.
  Qed.

  (** TODO: Move me, remove Local *)
  Definition proj1_sig_unmatched {A P} := @proj1_sig A P.
  Definition proj1_sig_nounfold {A P} := @proj1_sig A P.
  Definition proj1_sig_unfold {A P} := Eval cbv [proj1_sig] in @proj1_sig A P.
  Local Ltac unfold_proj1_sig_exist :=
  (** Change the first [proj1_sig] into [proj1_sig_unmatched]; if it's applied to [exist], mark it as unfoldable, otherwise mark it as not unfoldable.  Then repeat.  Finally, unfold. *)
    repeat (change @proj1_sig with @proj1_sig_unmatched at 1;
            match goal with
            | [ |- context[proj1_sig_unmatched (exist _ _ _)] ]
              => change @proj1_sig_unmatched with @proj1_sig_unfold
            | _ => change @proj1_sig_unmatched with @proj1_sig_nounfold
            end);
    (* [proj1_sig_nounfold] is a thin wrapper around [proj1_sig]; unfolding it restores [proj1_sig].  Unfolding [proj1_sig_nounfold] exposes the pattern match, which is reduced by ι. *)
    cbv [proj1_sig_nounfold proj1_sig_unfold].

  Lemma unfold_E_sub : forall a b, (a - b = a + E.opp b)%E. Proof. reflexivity. Qed.


  Local Existing Instance eq_Reflexive. (* To get some of the [setoid_rewrite]s below to work, we need to infer [Reflexive eq] before [Reflexive Equivalence.equiv] *)

  (* TODO: move me *)
  Lemma fold_rep2E x y z t
    : (unRep x, unRep y, unRep z, unRep t) = rep2E (((x, y), z), t).
  Proof. reflexivity. Qed.
  Lemma commute_negateExtended'_rep2E x y z t
    : negateExtended' (rep2E (((x, y), z), t))
      = rep2E (((FRepOpp x, y), z), FRepOpp t).
  Proof. simpl; autorewrite with FRepOperations; reflexivity. Qed.
  Lemma fold_rep2E_ffff x y z t
    : (x, y, z, t) = rep2E (((toRep x, toRep y), toRep z), toRep t).
  Proof. simpl; rewrite !rcFOK; reflexivity. Qed.
  Lemma fold_rep2E_rrfr x y z t
    : (unRep x, unRep y, z, unRep t) = rep2E (((x, y), toRep z), t).
  Proof. simpl; rewrite !rcFOK; reflexivity. Qed.
  Lemma fold_rep2E_0fff y z t
    : (0%F, y, z, t) = rep2E (((toRep 0%F, toRep y), toRep z), toRep t).
  Proof. apply fold_rep2E_ffff. Qed.
  Lemma fold_rep2E_ff1f x y t
    : (x, y, 1%F, t) = rep2E (((toRep x, toRep y), toRep 1%F), toRep t).
  Proof. apply fold_rep2E_ffff. Qed.
  Lemma commute_negateExtended'_rep2E_rrfr x y z t
    : negateExtended' (unRep x, unRep y, z, unRep t)
      = rep2E (((FRepOpp x, y), toRep z), FRepOpp t).
  Proof. rewrite <- commute_negateExtended'_rep2E; simpl; rewrite !rcFOK; reflexivity. Qed.

  Local Existing Instance FqEncoding.

  Hint Rewrite @F_mul_0_l commute_negateExtended'_rep2E_rrfr fold_rep2E_0fff solve_for_R
       (@fold_rep2E_ff1f (fst (proj1_sig B)))
       (eqb_compare_encodings F_eqb F_eqb_iff (@weqb (b-1)) (@weqb_true_iff (b-1)))
       (eqb_compare_encodings E.point_eqb E_eqb_iff (@weqb b) (@weqb_true_iff b))
       (if_map unRep) unfold_E_sub E.opp_mul
       (fun T => Let_app2_In (T := T) unRep unRep) @F_pow_2_r @unfoldDiv : EdDSA_opts.
  Hint Rewrite <- unifiedAddM1Rep_correct erep2trep_correct
       (fun x y z bound => iter_op_proj rep2E unifiedAddM1Rep unifiedAddM1' x y z N.testbit_nat bound unifiedAddM1Rep_correct)
       FRep2wire_correct E.point_eqb_correct
    : EdDSA_opts.

  Lemma sharper_verify : forall pk l msg sig, { sherper_verify | sherper_verify = verify (n:=l) pk msg sig}.
  Proof.
    eexists; cbv [EdDSA.verify]; intros.

    etransitivity. Focus 2. {
      repeat match goal with 
             | [ |- ?x = ?x ] => reflexivity
             | _ => replace_option_match_with_option_rect
             | [ |- _ = option_rect _ _ _ _ ]
               => eapply option_rect_Proper_nd; [ intro | reflexivity.. ]
             end.
      reflexivity. } Unfocus.
    
    setoid_rewrite <-E.point_eqb_correct.
    setoid_rewrite solve_for_R.
    setoid_rewrite (compare_without_decoding PointEncoding _ E_eqb_iff _ (@weqb_true_iff _)).

    rewrite_strat bottomup hints EdDSA_opts.

    setoid_rewrite <-(unExtendedPoint_mkExtendedPoint B).
    setoid_rewrite <-(fun a => unExtendedPoint_mkExtendedPoint (E.opp a)).

    setoid_rewrite <-Znat.Z_N_nat.
    Axiom nonequivalent_optimization_Hmodl : forall n (x:word n) A, (wordToNat (H x) * A = (wordToNat (H x) mod l * A))%E.
    setoid_rewrite nonequivalent_optimization_Hmodl.
    setoid_rewrite <-(Nat2N.id (_ mod EdDSA.l)).
    setoid_rewrite <-rcSOK.
    setoid_rewrite <-(scalarMultExtendedSRep_correct _ _ _ (Fl_SRep_bound _)).

    rewrite N_of_nat_modulo by (pose proof l_odd; omega).
    
    setoid_rewrite (unifiedAddM1_rep a_is_minus1).

    etransitivity.
    Focus 2.
    { lazymatch goal with |- _ = option_rect _ _ ?false ?dec =>
                          symmetry; etransitivity; [|eapply (option_rect_option_map (fun (x:F _) => Z.to_N x) _ false dec)]
      end.
      eapply option_rect_Proper_nd; [intro|reflexivity..].
      match goal with
      | [ |- ?RHS = ?e ?v ]
        => let RHS' := (match eval pattern v in RHS with ?RHS' _ => RHS' end) in
           unify e RHS'
      end.
      reflexivity.
    } Unfocus.
    rewrite <-decode_scalar_correct.

    rewrite enc'_correct.
    cbv [unExtendedPoint unifiedAddM1 negateExtended scalarMultM1].
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

    cbv [dec PointEncoding point_encoding].
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

    cbv iota beta delta [q d a].

    rewrite wire2FRep_correct.

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