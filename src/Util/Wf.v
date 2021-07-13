(** * Miscellaneous Well-Foundedness Facts *)
Require Import Coq.Setoids.Setoid Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Classes.Morphisms Coq.Init.Wf.
Require Import Coq.Lists.SetoidList.
Require Export Crypto.Util.FixCoqMistakes.

Local Set Implicit Arguments.
Local Unset Uniform Inductive Parameters.

Scheme Induction for Acc Sort Prop.
Scheme Induction for Acc Sort Set.
Scheme Induction for Acc Sort Type.

Section wf.
  Section wrap_wf.
    Context {A R} (Rwf : @well_founded A R).

    Definition lt_wf_idx_step
               (lt_wf_idx : nat -> well_founded R)
               (n : nat)
      : well_founded R.
    Proof.
      destruct n.
      { clear -Rwf; apply Rwf. }
      { constructor; intros; apply lt_wf_idx; assumption. }
    Defined.

    Fixpoint lt_wf_idx (n : nat) : well_founded R
      := lt_wf_idx_step (@lt_wf_idx) n.
  End wrap_wf.

  Section rel_hetero.
    Local Notation "R ==> S"
      := (@respectful_hetero _ _ _ _ R (fun _ _ => S))
         : signature_scope.
    Local Notation Proper S R
      := (S%signature R R) (only parsing).

    Context {A A'}
            (RA : A -> A' -> Prop)
            (P : A -> Type) (P' : A' -> Type)
            (RP : forall a a', RA a a' -> P a -> P' a' -> Prop)
            {R : relation A} {R' : relation A'}
            (HR : (RA ==> RA ==> Basics.impl)%signature R R')
            (Rwf : well_founded R) (Rwf' : well_founded R')
            (F : forall x, (forall y, R y x -> P y) -> P x)
            (F' : forall x, (forall y, R' y x -> P' y) -> P' x)
            (HF : forall a a' (r : RA a a')
                         (f := (fun (y : A) (_ : R y a) => Fix Rwf P F y))
                         (f' := (fun (y' : A') (_ : R' y' a') => Fix Rwf' P' F' y'))
                         (Hf : forall y y' (ry : RA y y') (r : R y a) (r' : R' y' a'),
                             RP _ _ ry (f y r) (f' y' r')),
                RP a a' r (F a f) (F' a' f'))
            (F_ext : forall x f g,
                (forall y p, f y p = g y p) -> F x f = F x g)
            (F'_ext : forall x f g,
                (forall y p, f y p = g y p) -> F' x f = F' x g).

    Lemma Fix_Proper_hetero
          {a a'}
          (Ha : RA a a')
      : @RP a a' Ha (Fix Rwf P F a) (Fix Rwf' P'  F' a').
    Proof.
      revert a' Ha.
      induction (Rwf a) as [a Hlt IHwf].
      intros a' Ha.
      rewrite (Fix_eq Rwf), (Fix_eq Rwf') by assumption.
      apply HF; intros.
      apply IHwf; assumption.
    Qed.
  End rel_hetero.

  Global Instance well_founded_subrelation {A}
    : Proper (flip subrelation ==> impl) (@well_founded A).
  Proof.
    intros R R' HR Rwf a.
    induction (Rwf a) as [a Ra R'a].
    constructor; intros y Hy.
    apply R'a, HR, Hy.
  Defined.

  Fixpoint no_wf_cycle_helper {A} {R : relation A} x y
           (H0 : R x y) (H1 : R y x) (wf : Acc R x)
    : False
    := match wf with
       | Acc_intro f => @no_wf_cycle_helper A R y x H1 H0 (f _ H1)
       end.

  Global Instance no_wf_cycle {A R} (Rwf : @well_founded A R) : Asymmetric R.
  Proof.
    intros x y H0 H1.
    specialize (Rwf x).
    eapply no_wf_cycle_helper; [ .. | eassumption ]; eassumption.
  Qed.

  Inductive RT_closure {A} (R : relation A) : relation A :=
  | cinject {x y} : R x y -> RT_closure R x y
  | crefl {x} : RT_closure R x x
  | ctrans {x y z} : RT_closure R x y -> RT_closure R y z -> RT_closure R x z.

  Fixpoint Acc_subrelation {A} (R1 R2 : relation A) (v : A) (Hacc : Acc R1 v)
        (HR : forall x y, RT_closure R2 y v -> R2 x y -> R1 x y) {struct Hacc}
    : Acc R2 v.
  Proof.
    destruct Hacc as [Hacc].
    constructor.
    intros y Hy.
    specialize (fun pf => @Acc_subrelation A R1 R2 y (Hacc y pf)).
    specialize (@Acc_subrelation (HR _ _ (@crefl _ _ _) Hy)).
    apply Acc_subrelation; clear -HR Hy.
    intros x y' Hxy Hr2.
    apply HR; clear HR; [ | assumption ].
    clear -Hy Hxy.
    eapply ctrans; [ eassumption | eapply cinject; eassumption ].
  Defined.

  Section wf_acc_of.
    Context A (RA : relation A).

    Definition well_founded_acc_relation_of
              B (f : B -> A) (fA : forall b, Acc RA (f b))
      : relation B
      := fun b0 b1 => match fA b1 with
                      | Acc_intro fAb1 => exists pf,
                                          fAb1 (f b0) pf = fA b0
                      end.


    Lemma well_founded_well_founded_acc_relation_of B f fA
      : well_founded (@well_founded_acc_relation_of B f fA).
    Proof.
      intro b.
      constructor.
      unfold well_founded_acc_relation_of.
      generalize (fA b).
      generalize (f b).
      lazymatch goal with
      | [ |- forall a' wf', @?P a' wf' ]
        => apply (@Acc_ind_dep A RA P)
      end.
      intros a Ha IH y [pf Hy].
      constructor.
      intros z Hz.
      specialize (IH (f y) pf z).
      apply IH; clear IH.
      destruct Hy.
      apply Hz.
    Defined.

    Fixpoint Acc_RA_of B (f : B -> A) b (ac : Acc RA (f b))
      : Acc (fun x y => RA (f x) (f y)) b.
    Proof.
      refine match ac with
             | Acc_intro fg => Acc_intro _ (fun y Ry => @Acc_RA_of _ _ _ (fg _ _))
             end.
      assumption.
    Defined.

    Lemma well_founded_RA_of B (f : B -> A) (wf_A : well_founded RA)
      : well_founded (fun x y => RA (f x) (f y)).
    Proof.
      intro a.
      apply Acc_RA_of, wf_A.
    Defined.
  End wf_acc_of.

  Section wf_acc_of_option.
    Context A (RA : relation A).

    Definition well_founded_acc_relation_of_opt
              B (f : B -> option A) (fA : forall b, match f b with
                                                    | Some fb => Acc RA fb
                                                    | None => True
                                                    end)
      : relation B
      := fun b0 b1
         => match f b1 as fb1 return match fb1 with
                                     | Some fb => Acc RA fb
                                     | None => True
                                     end -> _
            with
            | Some fb1
              => fun fAb
                 => match fAb with
                    | Acc_intro fAb1
                      => match f b0 as fb0 return match fb0 with
                                                  | Some fb => Acc RA fb
                                                  | None => True
                                                  end -> _
                         with
                         | Some fb0
                           => fun fAb0 => exists pf,
                                  fAb1 fb0 pf = fAb0
                         | None => fun _ => False
                         end (fA b0)
                    end
            | None => fun _ => False
            end (fA b1).

    Lemma well_founded_well_founded_acc_relation_of_opt B f fA
      : well_founded (@well_founded_acc_relation_of_opt B f fA).
    Proof.
      intro b.
      constructor.
      unfold well_founded_acc_relation_of_opt.
      generalize (fA b).
      generalize (f b).
      intros [fb|].
      { revert fb.
        lazymatch goal with
        | [ |- forall a' wf', @?P a' wf' ]
          => apply (@Acc_ind_dep A RA P)
        end.
        intros a Ha IH y.
        constructor.
        generalize dependent (fA y).
        destruct (f y) as [fy|] eqn:Hfy.
        { intros y0 [pf Hy].
          intros z Hz.
          specialize (IH fy pf z).
          apply IH; clear IH.
          destruct Hy.
          apply Hz. }
        { intros ? []. } }
      { intros ?? []. }
    Defined.

    Fixpoint Acc_RA_of_opt B (f : B -> option A) b v (Heq : f b = Some v)
             (ac : Acc RA v) {struct ac}
      : Acc (fun x y => match f x, f y with
                        | Some fx, Some fy => RA fx fy
                        | _, _ => False
                        end) b.
    Proof.
      destruct ac as [fg].
      constructor.
      intros y Ry.
      specialize (fun v H Rv => Acc_RA_of_opt B f y v H (fg _ Rv)); clear fg.
      destruct (f y) as [fy|] eqn:Hfy.
      { specialize (Acc_RA_of_opt _ eq_refl).
        destruct (f b) as [fb|] eqn:Hfb.
        { inversion Heq; clear Heq; subst.
          specialize (Acc_RA_of_opt Ry).
          assumption. }
        { destruct Ry. } }
      { destruct Ry. }
    Defined.

    Lemma well_founded_RA_of_opt B (f : B -> option A) (wf_A : well_founded RA)
      : well_founded (fun x y => match f x, f y with
                                 | Some fx, Some fy => RA fx fy
                                 | _, _ => False
                                 end).
    Proof.
      intro a.
      destruct (f a) eqn:H.
      { eapply Acc_RA_of_opt, wf_A; eassumption. }
      { constructor.
        intro y.
        destruct (f y); [ rewrite H | ]; intros []. }
    Defined.
  End wf_acc_of_option.

  Section wf_prodA.
    Context A B (eqA RA : relation A) (RB : relation B).

    Definition prod_relationA : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (eqA (fst a'b') (fst ab) /\ RB (snd ab) (snd a'b')).

    Context (prod_relationA_Proper
             : forall b'', Proper (eqA ==> impl) (fun a => Acc prod_relationA (a, b''))).

    Global Instance prod_relationA_Proper_from_Equivalence
          (RA_Proper : Proper (eq ==> eqA ==> flip impl) RA)
          (eqA_Proper : Proper (eqA ==> eq ==> flip impl) eqA)
      : forall b'', Proper (eqA ==> impl) (fun a => Acc prod_relationA (a, b'')).
    Proof.
      intros b'' a b H wf.
      revert dependent b.
      destruct wf as [f].
      constructor.
      intros y Hlt; apply f.
      unfold prod_relationA in Hlt |- *; simpl in *.
      destruct Hlt as [Hlt|[Hlt0 Hlt1]]; [ left | right; split; try assumption ].
      { eapply RA_Proper; [ reflexivity | exact H | exact Hlt ]. }
      { eapply eqA_Proper; [ exact H | reflexivity | exact Hlt0 ]. }
    Defined.

    Section step.
      Context (well_founded_prod_relationA_helper
               : forall a b (wf_A : Acc RA a) (wf_B : well_founded RB),
                  Acc prod_relationA (a, b)).

      Definition well_founded_prod_relationA_helper_step
                 a b
                 (wf_A : Acc RA a) (wf_B : well_founded RB)
                 (wf_B_rec : forall (fa : forall y : A, RA y a -> Acc RA y) b' (wf_B' : Acc RB b'), Acc prod_relationA (a, b'))
        : Acc prod_relationA (a, b)
        := match wf_A with
           | Acc_intro fa => @wf_B_rec fa b (wf_B b)
           end.
      Definition wf_B_rec_step
                 (wf_B : well_founded RB)
                 a (fa : forall y : A, RA y a -> Acc RA y)
                 (wf_B_rec : forall b' (wf_B' : Acc RB b'), Acc prod_relationA (a, b'))
                 b' (wf_B' : Acc RB b')
        :  Acc prod_relationA (a, b').
      Proof.
        refine (Acc_intro _ _).
        intros [a'' b''] [pf'|[pfa pfb]].
        { refine (@well_founded_prod_relationA_helper
                    _ _
                    (fa _ pf')
                    wf_B). }
        { refine match wf_B' with
                 | Acc_intro fb => @prod_relationA_Proper
                                     _ _ _ pfa
                                     (@wf_B_rec _ (fb _ pfb))
                 end. }
      Defined.
    End step.

    Fixpoint well_founded_prod_relationA_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
      : Acc prod_relationA (a, b)
      := @well_founded_prod_relationA_helper_step
           a b wf_A wf_B
           (fun fa
            => fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relationA (a, b')
            := @wf_B_rec_step
                 (@well_founded_prod_relationA_helper)
                 wf_B
                 a fa (@wf_B_rec)
                 b' wf_B').

    Definition well_founded_prod_relationA : well_founded RA -> well_founded RB -> well_founded prod_relationA.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relationA_helper; auto.
    Defined.
  End wf_prodA.

  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).

    Definition prod_relation : relation (A * B)
      := Eval cbv [prod_relationA] in prod_relationA eq RA RB.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      apply well_founded_prod_relationA.
      intros b'' a b H H'.
      induction H.
      exact H'.
    Defined.
  End wf_prod.

  Section wf_sig.
    Context A B (RA : relation A) (RB : forall a : A, relation (B a)).

    Definition sigT_relation : relation (sigT B)
      := fun ab a'b' =>
           RA (projT1 ab) (projT1 a'b') \/ (exists pf : projT1 a'b' = projT1 ab, RB (projT2 ab)
                                                                                    (eq_rect _ B (projT2 a'b') _ pf)).

    Fixpoint well_founded_sigT_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : forall a, well_founded (@RB a)) {struct wf_A}
    : Acc sigT_relation (existT _ a b).
    Proof.
      refine match wf_A with
               | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc (@RB a) b') : Acc sigT_relation (existT _ a b')
                                  := Acc_intro
                                       _
                                       (fun ab =>
                                          match ab as ab return sigT_relation ab (existT _ a b') -> Acc sigT_relation ab with
                                            | existT a'' b'' =>
                                              fun pf =>
                                                match pf with
                                                  | or_introl pf'
                                                    => @well_founded_sigT_relation_helper
                                                         _ _
                                                         (fa _ pf')
                                                         wf_B
                                                  | or_intror (ex_intro pfa pfb)
                                                    => match wf_B' with
                                                         | Acc_intro fb
                                                           => _(*eq_rect
                                                            _
                                                            (fun a'' => Acc sigT_relation (existT B a'' _(*b''*)))
                                                            (wf_B_rec _ (fb _ _(*pfb*)))
                                                            _
                                                            pfa*)
                                                       end
                                                end
                                          end)
                                 ) b (wf_B a b)
             end;
      simpl in *.
      destruct pfa; simpl in *.
      exact (wf_B_rec _ (fb _ pfb)).
    Defined.

    Definition well_founded_sigT_relation : well_founded RA
                                            -> (forall a, well_founded (@RB a))
                                            -> well_founded sigT_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_sigT_relation_helper; auto.
    Defined.
  End wf_sig.

  Section wf_projT1.
    Context A (B : A -> Type) (R : relation A).

    Definition projT1_relation : relation (sigT B)
      := fun ab a'b' =>
           R (projT1 ab) (projT1 a'b').

    Definition well_founded_projT1_relation : well_founded R -> well_founded projT1_relation.
    Proof.
      intros wf [a b]; hnf in *.
      induction (wf a) as [a H IH].
      constructor.
      intros y r.
      specialize (IH _ r (projT2 y)).
      destruct y.
      exact IH.
    Defined.
  End wf_projT1.

  Section wf_iterated_prod_ofA.
    Context A (eqA R : relation A) (Rwf : well_founded R)
            (RA_Proper : Proper (eq ==> eqA ==> flip impl) R)
            (eqA_Proper : Proper (eqA ==> eq ==> flip impl) eqA).

    Fixpoint iterated_prod (n : nat) : Type
      := match n with
         | 0 => unit
         | S n' => A * iterated_prod n'
         end%type.

    Fixpoint iterated_prod_relationA {n} : relation (iterated_prod n)
      := match n return relation (iterated_prod n) with
         | 0 => fun _ _ => False
         | S n' => prod_relationA eqA R (@iterated_prod_relationA n')
         end.

    Fixpoint nat_eq_transfer (P : nat -> Type) (n m : nat) : P n -> (P m) + (EqNat.beq_nat n m = false)
      := match n, m return P n -> (P m) + (EqNat.beq_nat n m = false) with
         | 0, 0 => fun x => inl x
         | S n', S m' => @nat_eq_transfer (fun v => P (S v)) n' m'
         | _, _ => fun _ => inr eq_refl
         end.

    Fixpoint nat_eq_transfer_refl (P : nat -> Type) (n : nat) : forall v : P n, nat_eq_transfer P n n v = inl v
      := match n return forall v : P n, nat_eq_transfer P n n v = inl v with
         | 0 => fun v => eq_refl
         | S n' => @nat_eq_transfer_refl (fun k => P (S k)) n'
         end.

    Fixpoint nat_eq_transfer_neq (P : nat -> Type) (n m : nat)
      : forall v : P n, (if EqNat.beq_nat n m as b return ((P m) + (b = false)) -> Prop
                         then fun _ => True
                         else fun v => v = inr eq_refl)
                          (nat_eq_transfer P n m v)
      := match n, m return forall v : P n, (if EqNat.beq_nat n m as b return ((P m) + (b = false)) -> Prop
                                            then fun _ => True
                                            else fun v => v = inr eq_refl)
                                             (nat_eq_transfer P n m v)
         with
         | 0, 0 => fun _ => I
         | S n', S m' => @nat_eq_transfer_neq (fun v => P (S v)) n' m'
         | _, _ => fun _ => eq_refl
         end.

    Definition iterated_prod_relationA_of
               B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
      : relation B
      := fun x y => match nat_eq_transfer _ (sz x) (sz y) (f x) with
                    | inl fx => iterated_prod_relationA fx (f y)
                    | inr _ => False
                    end.

    Definition iterated_prod_relationA_of_opt
               B (sz : nat) (f : B -> option (iterated_prod sz))
      : relation B
      := fun x y => match f x, f y with
                    | Some fx, Some fy => iterated_prod_relationA fx fy
                    | _, _ => False
                    end.

    Lemma well_founded_iterated_prod_relationA {n} : well_founded (@iterated_prod_relationA n).
    Proof.
      induction n as [|n IHn]; simpl.
      { constructor; intros ? []. }
      { apply well_founded_prod_relationA; try exact _; assumption. }
    Defined.

    Lemma well_founded_iterated_prod_relationA_of_opt {B n f} : well_founded (@iterated_prod_relationA_of_opt B n f).
    Proof.
      unfold iterated_prod_relationA_of_opt.
      apply well_founded_RA_of_opt, well_founded_iterated_prod_relationA.
    Defined.

    Local Ltac handle_nat_eq_transfer
      := repeat lazymatch goal with
                | [ |- forall n0 n1, @?P n0 n1 ]
                  => let n0' := fresh "n" in
                     let n1' := fresh "n" in
                     let H := fresh in
                     let H' := fresh in
                     intros n0' n1';
                     destruct (@nat_eq_transfer (P n0') n0' n1') as [H|H];
                     [ clear n1'; revert n0'
                     | apply H
                     | lazymatch goal with
                       | [ |- context[@nat_eq_transfer iterated_prod n1' n0' _] ]
                         => pose proof (@nat_eq_transfer_neq iterated_prod n1' n0') as H';
                            cbv beta in *;
                            generalize dependent (nat_eq_transfer iterated_prod n1' n0');
                            let Heq := fresh in
                            destruct (EqNat.beq_nat n1' n0') eqn:Heq;
                            [ apply EqNat.beq_nat_true_iff in Heq; subst; rewrite <- EqNat.beq_nat_refl in H;
                              exfalso; clear -H; congruence
                            | ]
                       | [ |- context[@nat_eq_transfer iterated_prod n0' n1' _] ]
                         => pose proof (@nat_eq_transfer_neq iterated_prod n0' n1') as H';
                            cbv beta in *;
                            generalize dependent (nat_eq_transfer iterated_prod n0' n1');
                            rewrite H
                       end
                     ]
                end;
         repeat match goal with
                | _ => reflexivity
                | [ H : False |- _ ] => exfalso; exact H
                | [ H : forall v, _ = inr _ |- _ ] => rewrite H
                | _ => intro
                end.

    Lemma RT_closure_same_size B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
          a b
          (H : RT_closure (iterated_prod_relationA_of sz f) a b)
      : sz a = sz b.
    Proof.
      induction H as [x y H | | ].
      { unfold iterated_prod_relationA_of in *.
        generalize dependent (f x).
        generalize dependent (f y).
        generalize dependent (sz x).
        generalize dependent (sz y).
        handle_nat_eq_transfer. }
      { reflexivity. }
      { etransitivity; eassumption. }
    Defined.

    Lemma well_founded_iterated_prod_relationA_of
          B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
      : well_founded (@iterated_prod_relationA_of B sz f).
    Proof.
      intro b.
      pose proof (@well_founded_RA_of_opt (iterated_prod (sz b)) iterated_prod_relationA B) as wf.
      specialize (wf (fun b' => match nat_eq_transfer _ (sz b') (sz b) (f b') with
                                | inl v => Some v
                                | inr _ => None
                                end)).
      specialize (wf well_founded_iterated_prod_relationA).
      eapply Acc_subrelation; [ eapply wf | clear wf ].
      intros x y H.
      apply RT_closure_same_size in H.
      unfold iterated_prod_relationA_of.
      generalize dependent (f b).
      generalize dependent (f x).
      generalize dependent (f y).
      generalize dependent (sz y).
      intros ??; subst.
      clear y.
      generalize dependent (sz b).
      generalize dependent (sz x).
      clear.
      handle_nat_eq_transfer.
      rewrite !nat_eq_transfer_refl in *.
      assumption.
    Defined.
  End wf_iterated_prod_ofA.

  Section wf_iterated_prod_of.
    Context A (R : relation A) (Rwf : well_founded R).

    Definition iterated_prod_relation {n} : relation (iterated_prod A n)
      := iterated_prod_relationA eq R.

    Definition iterated_prod_relation_of
      : forall B (sz : B -> nat) (f : forall b, iterated_prod A (sz b)),
        relation B
      := iterated_prod_relationA_of eq R.

    Definition iterated_prod_relation_of_opt
      : forall B (sz : nat) (f : B -> option (iterated_prod A sz)),
        relation B
      := iterated_prod_relationA_of_opt eq R.

    Lemma well_founded_iterated_prod_relation {n} : well_founded (@iterated_prod_relation n).
    Proof.
      apply well_founded_iterated_prod_relationA; try exact _; assumption.
    Defined.

    Lemma well_founded_iterated_prod_relation_of_opt {B n f} : well_founded (@iterated_prod_relation_of_opt B n f).
    Proof.
      apply well_founded_iterated_prod_relationA_of_opt; try exact _; assumption.
    Defined.

    Lemma well_founded_iterated_prod_relation_of
          B (sz : B -> nat) (f : forall b, iterated_prod A (sz b))
      : well_founded (@iterated_prod_relation_of B sz f).
    Proof.
      apply well_founded_iterated_prod_relationA_of; try exact _; assumption.
    Defined.
  End wf_iterated_prod_of.

  Section wf_functionsA.
    Context A (eqA R : relation A)
            (R_Proper : Proper (eq ==> eqA ==> flip impl) R)
            (R_Proper2 : Proper (eq ==> eqA ==> impl) R)
            (eqA_Proper : Proper (eqA ==> eq ==> flip impl) eqA)
            (eqA_Proper2 : Proper (eq ==> eqA ==> flip impl) eqA)
            (eqA_Symmetric : Symmetric eqA).

    Local Infix "<" := R.
    Local Notation "x <= y" := (eqA x y \/ x < y).

    Context (bot : A) (bot_bot : forall a, bot <= a)
            (Rwf : well_founded R)
            (B C : Type)
            (eqv : relation B)
            {Heqv : Reflexive eqv}
            (F : C -> (B -> A))
            (F_Proper : forall a b k k', eqv k' k -> eqA (F a k) (F b k) -> eqA (F a k') (F b k')).

    Definition is_finite_forA' (ls : list B) (f : B -> A)
      := forall x, ~SetoidList.InA eqv x ls -> eqA (f x) bot.

    Definition is_finite_forA (ls : list B) (c : C) := is_finite_forA' ls (F c).

    Definition function_relationA : relation (B -> A)
      := fun f g => (forall x, f x <= g x)
                    /\ exists x, ~(eqA (f x) (g x)).

    Definition iterated_prod_of_function_for (ls : list B) (f : B -> A)
      : iterated_prod A (List.length ls)
      := list_rect (fun ls => iterated_prod A (List.length ls))
                   tt
                   (fun x _ v => (f x, v))
                   ls.

    Global Instance is_finite_forA'_Proper_fr
      : Proper (eq ==> function_relationA ==> flip impl) is_finite_forA'.
    Proof.
      unfold is_finite_forA', function_relationA.
      intros ls g ?; subst g.
      intros f g [Hle Hne] Hfin x Hnin.
      specialize (Hle x); specialize (Hfin x Hnin).
      destruct Hle as [Heq|Hlt]; [ rewrite Heq; assumption | ].
      specialize (bot_bot (f x)).
      destruct bot_bot as [Heq|Hlt']; [ symmetry; assumption | ].
      rewrite Hfin in Hlt.
      clear -Hlt Hlt' Rwf.
      exfalso; eapply no_wf_cycle; eassumption.
    Qed.

    Global Instance is_finite_forA_Proper_fr
      : Proper (eq ==> (fun x y => function_relationA (F x) (F y)) ==> flip impl) is_finite_forA.
    Proof.
      unfold is_finite_forA.
      intros ??????.
      eapply is_finite_forA'_Proper_fr; eassumption.
    Qed.

    Global Instance is_finite_forA'_Proper_frc
      : Proper (eq ==> RT_closure function_relationA ==> flip impl) is_finite_forA'.
    Proof.
      intros ls ls' ? f g H Hfin.
      induction H as [ ?? H | | ].
      { eapply is_finite_forA'_Proper_fr; eassumption. }
      { subst; assumption. }
      { subst; eauto with nocore. }
    Qed.

    Global Instance is_finite_forA_Proper_frc
      : Proper (eq ==> (fun x y => RT_closure function_relationA (F x) (F y)) ==> flip impl) is_finite_forA.
    Proof.
      unfold is_finite_forA.
      intros ??????.
      eapply is_finite_forA'_Proper_frc; eassumption.
    Qed.

    Global Instance is_finite_forA_Proper_frc'
      : Proper (eq ==> RT_closure (fun x y => function_relationA (F x) (F y)) ==> flip impl) is_finite_forA.
    Proof.
      intros ls ls' ? f g H Hfin.
      induction H as [ ?? H | | ].
      { eapply is_finite_forA_Proper_fr; eassumption. }
      { subst; assumption. }
      { subst; eauto with nocore. }
    Qed.

    Lemma function_subrelationA ls c (H : is_finite_forA ls c)
      : forall x y : C,
        RT_closure (fun x0 y0 : C => function_relationA (F x0) (F y0)) y c ->
        function_relationA (F x) (F y) ->
        (fun x0 y0 : C =>
           iterated_prod_relationA_of eqA R (fun _ : B -> A => length ls)
                                      (iterated_prod_of_function_for ls) (F x0) (F y0)) x y.
    Proof.
      intros g h Hhf Hgh; cbv beta.
      assert (Hfinh : is_finite_forA ls h) by (rewrite Hhf; assumption).
      assert (Hfing : is_finite_forA ls g) by (unfold is_finite_forA; rewrite Hgh; assumption).
      unfold iterated_prod_relationA_of, function_relationA, iterated_prod_of_function_for in *.
      rewrite nat_eq_transfer_refl.
      destruct Hgh as [Hle Hne].
      destruct Hne as [b Hne].
      assert (Hin : ~~SetoidList.InA eqv b ls).
      { intro Hnin.
        rewrite Hfinh in Hne by assumption.
        eauto with nocore. }
      rewrite SetoidList.InA_alt in Hin.
      move ls at bottom.
      clear H Hfinh Hfing.
      induction ls as [|x xs IHxs];
        [
        | destruct (Hle x) as [Heqx|Hlex];
          [ right; split;
            [ | apply IHxs; clear IHxs ]
          | left ] ];
        simpl; unfold prod_relationA; simpl in *;
          repeat match goal with
                 | _ => congruence
                 | _ => tauto
                 | [ H : ex _ |- _ ] => destruct H
                 | [ H : and _ _ |- _ ] => destruct H
                 | [ H : or _ _ |- _ ] => destruct H
                 | _ => progress subst
                 | _ => progress eauto
                 | _ => solve [ exfalso; eauto ]
                 | [ H : ~~(exists x, _ /\ False) |- _ ]
                   => exfalso; apply H; clear
                 | _ => intro
                 | [ |- and _ _ ] => split
                 | [ H : ~~_ |- False ] => apply H; clear H
                 end.
    Qed.

    Definition function_relationA_of_Acc ls (c : C) (H : is_finite_forA ls c)
      : Acc (fun x y => function_relationA (F x) (F y)) c.
    Proof.
      pose proof (@well_founded_RA_of
                    _ _ _ F
                    (@well_founded_iterated_prod_relationA_of
                       _ eqA R Rwf _ _ _ (fun _ => List.length ls) (iterated_prod_of_function_for ls))
                    c)
        as wf.
      eapply Acc_subrelation; [ eexact wf | ].
      apply function_subrelationA; assumption.
    Defined.
  End wf_functionsA.

  Section wf_functions.
    Context A (R : relation A).

    Local Infix "<" := R.
    Local Notation "x <= y" := (x = y \/ x < y).

    Context (bot : A) (bot_bot : forall a, bot <= a)
            (Rwf : well_founded R)
            {B : Type}.

    Definition function_relation : relation (B -> A)
      := @function_relationA A eq R B.

    Definition is_finite_for (ls : list B) (f : B -> A)
      := forall x, ~List.In x ls -> f x = bot.

    Lemma is_finite_for_iff ls f
      : is_finite_for ls f <-> @is_finite_forA A eq bot B (B -> A) eq (fun f => f) ls f.
    Proof.
      unfold is_finite_for, is_finite_forA, is_finite_forA'.
      setoid_rewrite InA_alt.
      split; intros H x H'; apply H; intro H''; apply H'.
      { eexists; split; [ reflexivity | assumption ]. }
      { destruct H'' as [? [? ?]]; subst; assumption. }
    Qed.

    Definition function_relation_Acc ls (f : B -> A) (H : is_finite_for ls f)
      : Acc function_relation f.
    Proof.
      rewrite is_finite_for_iff in H.
      apply function_relationA_of_Acc with (bot := bot) (eqv := eq) (ls := ls);
        try exact _; try assumption.
      intros; subst; assumption.
    Defined.
  End wf_functions.
End wf.
