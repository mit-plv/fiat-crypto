(** Fixed precision machine words *)

Require Import Coq.Arith.Arith Coq.Arith.Div2 Coq.NArith.NArith Coq.Bool.Bool Coq.omega.Omega.
Require Import Bedrock.Nomega.

Set Implicit Arguments.


(** * Basic definitions and conversion to and from [nat] *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).

Fixpoint wordToNat sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false _ w' => (wordToNat w') * 2
    | WS true _ w' => S (wordToNat w' * 2)
  end.

Fixpoint wordToNat' sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false _ w' => 2 * wordToNat w'
    | WS true _ w' => S (2 * wordToNat w')
  end.

Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.
Proof.
  induction w. auto. simpl. rewrite mult_comm. reflexivity.
Qed.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Fixpoint wordToN sz (w : word sz) : N :=
  match w with
    | WO => 0
    | WS false _ w' => N.double (wordToN w')
    | WS true _ w' => N.succ_double (wordToN w')
  end%N.

Definition Nmod2 (n : N) : bool :=
  match n with
    | N0 => false
    | Npos (xO _) => false
    | _ => true
  end.

Definition wzero sz := natToWord sz 0.

Fixpoint wzero' (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS false (wzero' sz')
  end.

Fixpoint posToWord (sz : nat) (p : positive) {struct p} : word sz :=
  match sz with
    | O => WO
    | S sz' =>
      match p with
        | xI p' => WS true (posToWord sz' p')
        | xO p' => WS false (posToWord sz' p')
        | xH => WS true (wzero' sz')
      end
  end.

Definition NToWord (sz : nat) (n : N) : word sz :=
  match n with
    | N0 => wzero' sz
    | Npos p => posToWord sz p
  end.

Fixpoint Npow2 (n : nat) : N :=
  match n with
    | O => 1
    | S n' => 2 * Npow2 n'
  end%N.


Ltac rethink :=
  match goal with
    | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Local Hint Resolve mod2_S_double mod2_double.

Theorem div2_double : forall n, div2 (2 * n) = n.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.

Theorem div2_S_double : forall n, div2 (S (2 * n)) = n.
  induction n; simpl; intuition; f_equal; rethink.
Qed.

Hint Rewrite div2_double div2_S_double : div2.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
  induction w as [|b]; rewrite wordToNat_wordToNat'; intuition; f_equal; unfold natToWord, wordToNat'; fold natToWord; fold wordToNat';
    destruct b; f_equal; autorewrite with div2; intuition.
Qed.

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => 2 * pow2 n'
  end.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
  induction sz; simpl; intuition.
Qed.

Hint Rewrite roundTrip_0 : wordToNat.

Local Hint Extern 1 (@eq nat _ _) => omega.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
  auto.
Qed.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; omega.
  Qed.

  Theorem strong : forall n, P n.
    intros; eapply strong'; eauto.
  Qed.
End strong.

Theorem div2_odd : forall n,
  mod2 n = true
  -> n = S (2 * div2 n).
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
    discriminate.
  destruct n as [|n]; simpl in *; intuition.
  do 2 f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem div2_even : forall n,
  mod2 n = false
  -> n = 2 * div2 n.
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  destruct n as [|n]; simpl in *; intuition.
    discriminate.
  f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.
  induction sz as [|sz IHsz]; simpl; intro w; intuition; repeat rewrite untimes2.

  exists w; intuition.

  case_eq (mod2 w); intro Hmw.

  specialize (IHsz (div2 w)); firstorder.
  rewrite wordToNat_wordToNat' in *.
  let x' := match goal with H : _ + ?x * _ = _ |- _ => x end in
  rename x' into x. (* force non-auto-generated name *)
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite mult_comm. simpl mult at 1.
  rewrite (plus_Sn_m (2 * wordToNat' (natToWord sz (div2 w)))).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_odd; auto.

  specialize (IHsz (div2 w)); firstorder.
  let x' := match goal with H : _ + ?x * _ = _ |- _ => x end in
  rename x' into x. (* force non-auto-generated name *)
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite <- mult_assoc.
  rewrite mult_comm.
  rewrite <- mult_plus_distr_l.
  match goal with H : _ |- _ => rewrite H; clear H end.
  symmetry; apply div2_even; auto.
Qed.

Theorem wordToNat_natToWord : forall sz w, exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ k * pow2 sz <= w.
  intros sz w; destruct (wordToNat_natToWord' sz w) as [k]; exists k; intuition.
Qed.

Definition wone sz := natToWord sz 1.

Fixpoint wones (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS true (wones sz')
  end.


(** Comparisons *)

Fixpoint wmsb sz (w : word sz) (a : bool) : bool :=
  match w with
    | WO => a
    | WS b _ x => wmsb x b
  end.

Definition whd sz (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ _ => b
  end.

Definition wtl sz (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ _ w' => w'
  end.

Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.
  intros b1 b2 sz w1 w2 ? H0; intuition.
  apply (f_equal (@whd _)) in H0; tauto.
  apply (f_equal (@wtl _)) in H0; tauto.
Qed.


(** Shattering **)

Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
  destruct a; eauto.
Qed.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros n a; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros a; apply (shatter_word a).
Qed.

Hint Resolve shatter_word_0.

Require Import Coq.Logic.Eqdep_dec.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b _ x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  abstract (symmetry; apply shatter_word_0).

  abstract (subst; symmetry; apply (shatter_word (n:=S _) _)).

  let y' := y in (* kludge around warning of mechanically generated names not playing well with [abstract] *)
  abstract (rewrite (shatter_word y'); simpl; intro H; injection H; intros;
    eauto using inj_pair2_eq_dec, eq_nat_dec).

  let y' := y in (* kludge around warning of mechanically generated names not playing well with [abstract] *)
  abstract (rewrite (shatter_word y'); simpl; intro H; injection H; auto).
Defined.

Fixpoint weqb sz (x : word sz) : word sz -> bool :=
  match x in word sz return word sz -> bool with
    | WO => fun _ => true
    | WS b _ x' => fun y =>
      if eqb b (whd y)
      then if @weqb _ x' (wtl y) then true else false
      else false
  end.

Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.
Proof.
  induction x as [|b ? x IHx]; simpl; intros y.
  { split; auto. }
  { rewrite (shatter_word y) in *. simpl in *.
    case_eq (eqb b (whd y)); intros H.
    case_eq (weqb x (wtl y)); intros H0.
    split; auto; intros. rewrite eqb_true_iff in H. f_equal; eauto. eapply IHx; eauto.
    split; intros H1; try congruence. inversion H1; clear H1; subst.
    eapply inj_pair2_eq_dec in H4. eapply IHx in H4. congruence.
    eapply Peano_dec.eq_nat_dec.
    split; intros; try congruence.
    inversion H0. apply eqb_false_iff in H. congruence. }
Qed.

(** * Combining and splitting *)

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b _ w' => fun _ w'' => WS b (combine w' w'')
  end.

Fixpoint split1 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
    | O => fun _ => WO
    | S sz1' => fun w => WS (whd w) (split1 sz1' sz2 (wtl w))
  end.

Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end.

Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
  induction sz1; shatterer.
Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
  induction sz1; shatterer.
Qed.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
  induction sz1; shatterer.
Qed.

Require Import Coq.Logic.Eqdep_dec.


Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
  induction w1 as [|?? w1 IHw1]; simpl; intros n2 n3 w2 w3 Heq; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHw1 _ _ _ _ (plus_assoc _ _ _)); clear IHw1.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent (combine w1 (combine w2 w3)).
  rewrite plus_assoc; intros w Heq0 e.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
  induction n1 as [|n1 IHn1]; simpl; intros n2 n3 Heq w; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHn1 _ _ (plus_assoc _ _ _)).
  f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent w.
  simpl.
  fold plus.
  generalize (n1 + (n2 + n3)); clear.
  intros n w Heq e.
  generalize Heq e.
  subst.
  intros Heq0 e.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.
  induction n1 as [|n1 IHn1]; simpl; intros n2 n3 Heq w.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  apply combine_split.

  rewrite (shatter_word w) in *.
  simpl.
  eapply trans_eq; [ | apply IHn1 with (Heq := plus_assoc _ _ _) ]; clear IHn1.
  repeat f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  simpl.
  generalize dependent w.
  rewrite plus_assoc.
  intros w e Heq0.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.


(** * Extension operators *)

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then
    combine w (wones sz')
  else
    combine w (wzero sz').

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').


(** * Arithmetic *)

Definition wneg sz (x : word sz) : word sz :=
  NToWord sz (Npow2 sz - wordToN x).

Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).

Definition wplus := wordBin Nplus.
Definition wmult := wordBin Nmult.
Definition wmult' sz (x y : word sz) : word sz :=
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wminus sz (x y : word sz) : word sz := wplus x (wneg y).

Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).

Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).

Definition wplusN := wordBinN plus.

Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz :=
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).

Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).

(** * Notations *)

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Notation "w ~ 1" := (WS true w)
 (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" := (WS false w)
 (at level 7, left associativity, format "w '~' '0'") : word_scope.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
  induction w as [|b ? w IHw]; intuition.
  destruct b; unfold wordToN, wordToNat; fold wordToN; fold wordToNat.

  rewrite N_of_S.
  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  rewrite N.succ_double_spec.
  rewrite N.add_1_r.
  reflexivity.

  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.
Qed.

Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.
  induction n as [n] using strong; intros.
  destruct n; simpl in *.
  elimtype False; omega.
  destruct n; simpl in *; auto.
  destruct k as [|k]; simpl in *.
  discriminate.
  apply H with k; auto.
Qed.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.
  unfold wzero; induction sz; simpl; intuition.
  congruence.
Qed.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).
  induction p as [ p IHp | p IHp | ]; destruct sz; simpl; intuition; f_equal; try rewrite wzero'_def in *.

  rewrite ZL6.
  destruct (ZL4 p) as [x Heq]; rewrite Heq; simpl.
  replace (x + S x) with (S (2 * x)) by omega.
  symmetry; apply mod2_S_double.

  rewrite IHp.
  rewrite ZL6.
  destruct (nat_of_P p); simpl; intuition.
  replace (n + S n) with (S (2 * n)) by omega.
  rewrite div2_S_double; auto.

  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  symmetry; apply mod2_double.

  rewrite IHp.
  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  rewrite div2_double.
  auto.
  auto.
Qed.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
  destruct n; simpl; intuition; try rewrite wzero'_def in *.
  auto.
  apply posToWord_nat.
Qed.

Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.
  unfold wplusN, wplus, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.
  unfold wmultN, wmult, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nmult.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = pow2 n.
  induction n as [|n IHn]; simpl; intuition.
  rewrite <- IHn; clear IHn.
  case_eq (Npow2 n); intuition.
  rewrite untimes2.
  match goal with
  | [ |- context[Npos ?p~0] ]
    => replace (Npos p~0) with (Ndouble (Npos p)) by reflexivity
  end.
  apply nat_of_Ndouble.
Qed.

Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.
  unfold wnegN, wneg; intros.
  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nminus.
  do 2 f_equal.
  apply Npow2_nat.
  apply nat_of_N_of_nat.
Qed.

Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.
  intros; unfold wminusN, wminus; rewrite wneg_alt; apply wplus_alt.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
  intros; rewrite wplus_alt; unfold wplusN, wordBinN; intros.
  rewrite roundTrip_0; apply natToWord_wordToNat.
Qed.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; f_equal; auto.
Qed.

Theorem drop_mod2 : forall n k,
  2 * k <= n
  -> mod2 (n - 2 * k) = mod2 n.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; omega.
Qed.

Theorem div2_minus_2 : forall n k,
  2 * k <= n
  -> div2 (n - 2 * k) = div2 n - k.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
  destruct k; simpl in *; intuition.

  destruct k; simpl in *; intuition.
  rewrite <- plus_n_Sm.
  apply H; omega.
Qed.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= div2 n.
  intros ? n H; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  omega.

  rewrite (div2_even _ Heq) in H.
  omega.
Qed.

Theorem drop_sub : forall sz n k,
  k * pow2 sz <= n
  -> natToWord sz (n - k * pow2 sz) = natToWord sz n.
  induction sz as [|sz IHsz]; simpl; intros n k *; intuition; repeat rewrite untimes2 in *; f_equal.

  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  apply drop_mod2.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  rewrite <- (IHsz (div2 n) k).
  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  rewrite div2_minus_2.
  reflexivity.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  apply div2_bound.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
Qed.

Local Hint Extern 1 (_ <= _) => omega.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
  intros sz x y z *; repeat rewrite wplus_alt; unfold wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  match goal with
  | [ |- context[wordToNat ?x + wordToNat ?y - ?x1 * pow2 ?sz + wordToNat ?z] ]
    => replace (wordToNat x + wordToNat y - x1 * pow2 sz + wordToNat z)
      with (wordToNat x + wordToNat y + wordToNat z - x1 * pow2 sz) by auto
  end.
  match goal with
  | [ |- context[wordToNat ?x + (wordToNat ?y + wordToNat ?z - ?x0 * pow2 ?sz)] ]
    => replace (wordToNat x + (wordToNat y + wordToNat z - x0 * pow2 sz))
      with (wordToNat x + wordToNat y + wordToNat z - x0 * pow2 sz) by auto
  end.
  repeat rewrite drop_sub; auto.
Qed.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
  induction sz; simpl in *; intuition.
Qed.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.
  intros sz x b. rewrite wordToNat_wordToNat'.
  destruct b; simpl.

  rewrite untimes2.
  case_eq (2 * wordToNat x); intuition.
  eapply mod2_S; eauto.
  rewrite <- (mod2_double (wordToNat x)); f_equal; omega.
Qed.

Theorem div2_WS : forall sz (x : word sz) b, div2 (wordToNat (WS b x)) = wordToNat x.
  destruct b; rewrite wordToNat_wordToNat'; unfold wordToNat'; fold wordToNat'.
  apply div2_S_double.
  apply div2_double.
Qed.

Theorem wmult_unit : forall sz (x : word sz), natToWord sz 1 ^* x = x.
  intros sz x; rewrite wmult_alt; unfold wmultN, wordBinN; intros.
  destruct sz; simpl.
  rewrite (shatter_word x); reflexivity.
  rewrite roundTrip_0; simpl.
  rewrite plus_0_r.
  rewrite (shatter_word x).
  f_equal.

  apply mod2_WS.

  rewrite div2_WS.
  apply natToWord_wordToNat.
Qed.

Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
Qed.

Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.
  intros sz x y z; repeat rewrite wmult_alt; unfold wmultN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_l.
  rewrite mult_minus_distr_r.
  match goal with
  | [ |- natToWord _ (_ - _ * (?x0' * _)) = natToWord _ (_ - ?x1' * _ * _) ]
    => rename x0' into x0, x1' into x1 (* force the names to not be autogenerated *)
  end.
  rewrite (mult_assoc (wordToNat x) x0).
  rewrite <- (mult_assoc x1).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x1).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x1).
  rewrite <- (mult_assoc (wordToNat x)).
  rewrite (mult_comm (wordToNat y)).
  rewrite mult_assoc.
  rewrite (mult_comm (wordToNat x)).
  repeat rewrite <- mult_assoc.
  auto with arith.
  repeat rewrite <- mult_assoc.
  auto with arith.
Qed.

Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).
  intros sz x y z; repeat rewrite wmult_alt; repeat rewrite wplus_alt; unfold wmultN, wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_r.
  match goal with
  | [ |- natToWord _ (_ - ?x0' * _ * _) = natToWord _ (_ - ?x1' * _ + (_ - ?x2' * _)) ]
    => rename x0' into x0, x1' into x1, x2' into x2 (* force the names to not be autogenerated *)
  end.
  rewrite <- (mult_assoc x0).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x0).

  replace (wordToNat x * wordToNat z - x1 * pow2 sz +
    (wordToNat y * wordToNat z - x2 * pow2 sz))
    with (wordToNat x * wordToNat z + wordToNat y * wordToNat z - x1 * pow2 sz - x2 * pow2 sz).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x0).
  rewrite (mult_comm (wordToNat x + wordToNat y)).
  rewrite <- (mult_assoc (wordToNat z)).
  auto with arith.
  generalize dependent (wordToNat x * wordToNat z).
  generalize dependent (wordToNat y * wordToNat z).
  intros.
  omega.
Qed.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
  reflexivity.
Qed.

Theorem wordToNat_bound : forall sz (w : word sz), wordToNat w < pow2 sz.
  induction w as [|b]; simpl; intuition.
  destruct b; simpl; omega.
Qed.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
  induction sz as [|sz]; simpl; intuition.

  generalize (div2_double (pow2 sz)); simpl; intro Hr; rewrite Hr; clear Hr.
  f_equal.
  generalize (mod2_double (pow2 sz)); auto.
  auto.
Qed.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
  intros sz x; rewrite wneg_alt; rewrite wplus_alt; unfold wnegN, wplusN, wzero, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  match goal with
  | [ |- context[wordToNat ?x + (pow2 ?sz - wordToNat ?x - ?x0 * pow2 ?sz)] ]
    => replace (wordToNat x + (pow2 sz - wordToNat x - x0 * pow2 sz))
      with (pow2 sz - x0 * pow2 sz)
  end.
  rewrite drop_sub; auto with arith.
  apply natToWord_pow2.
  generalize (wordToNat_bound x).
  omega.
Qed.

Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).

Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.
Proof.
  eapply weqb_true_iff.
Qed.

Arguments weqb_sound : clear implicits.

Ltac isWcst w :=
  match eval hnf in w with
    | WO => constr:(true)
    | WS ?b ?w' =>
      match eval hnf in b with
        | true => isWcst w'
        | false => isWcst w'
        | _ => constr:(false)
      end
    | _ => constr:(false)
  end.

Ltac wcst w :=
  let b := isWcst w in
    match b with
      | true => w
      | _ => constr:(NotConstant)
    end.

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).
*)


(** * Bitwise operators *)

Fixpoint wnot sz (w : word sz) : word sz :=
  match w with
    | WO => WO
    | WS b _ w' => WS (negb b) (wnot w')
  end.

Fixpoint bitwp (f : bool -> bool -> bool) sz (w1 : word sz) : word sz -> word sz :=
  match w1 with
    | WO => fun _ => WO
    | WS b _ w1' => fun w2 => WS (f b (whd w2)) (bitwp f w1' (wtl w2))
  end.

Definition wor := bitwp orb.
Definition wand := bitwp andb.
Definition wxor := bitwp xorb.

Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).

Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.
  unfold wzero, wor; induction x; simpl; intuition congruence.
Qed.

Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.
  unfold wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.
  unfold wzero, wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).
  unfold wand, wor; induction x as [|b]; intro y; rewrite (shatter_word y); intro z; rewrite (shatter_word z); simpl; intuition; f_equal; auto with bool.
  destruct (whd y); destruct (whd z); destruct b; reflexivity.
Qed.

Definition wbring (sz : nat) : semi_ring_theory (wzero sz) (wones sz) (@wor sz) (@wand sz) (@eq _) :=
  mk_srt _ _ _ _ _
  (@wor_unit _) (@wor_comm _) (@wor_assoc _)
  (@wand_unit _) (@wand_kill _) (@wand_comm _) (@wand_assoc _)
  (@wand_or_distr _).


(** * Inequality proofs *)

Ltac word_simpl := unfold sext, zext, wzero in *; simpl in *.

Ltac word_eq := ring.

Ltac word_eq1 := match goal with
                   | _ => ring
                   | [ H : _ = _ |- _ ] => ring [H]
                 end.

Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> wzero sz
  -> w1 <> w2.
  intros; intro; subst.
  unfold wminus in H.
  rewrite wminus_inv in H.
  tauto.
Qed.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.

Ltac word_contra := match goal with
                      | [ H : _ <> _ |- False ] => apply H; ring
                    end.

Ltac word_contra1 := match goal with
                       | [ H : _ <> _ |- False ] => apply H;
                         match goal with
                           | _ => ring
                           | [ H' : _ = _ |- _ ] => ring [H']
                         end
                     end.

Open Scope word_scope.

(** * Signed Logic **)
Fixpoint wordToZ sz (w : word sz) : Z :=
  if wmsb w true then
    (** Negative **)
    match wordToN (wneg w) with
      | N0 => 0%Z
      | Npos x => Zneg x
    end
  else
    (** Positive **)
    match wordToN w with
      | N0 => 0%Z
      | Npos x => Zpos x
    end.

(** * Comparison Predicates and Deciders **)
Definition wlt sz (l r : word sz) : Prop :=
  Nlt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  Zlt (wordToZ l) (wordToZ r).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70) : word_scope.

Definition wlt_dec : forall sz (l r : word sz), {l < r} + {l >= r}.
  refine (fun sz l r =>
    match Ncompare (wordToN l) (wordToN r) as k return Ncompare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
  refine (fun sz l r =>
    match Zcompare (wordToZ l) (wordToZ r) as c return Zcompare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

(* Ordering Lemmas **)
Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Proof.
  unfold wlt, Nlt. intros sz a b H H0. rewrite <- Ncompare_antisym in H0. rewrite H in H0. simpl in *. congruence.
Qed.
Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Proof.
  intros; subst. unfold wlt, Nlt. rewrite Ncompare_refl. congruence.
Qed.
Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
Proof.
  induction a as [|b ? a IHa]; intro b0; rewrite (shatter_word b0); intro H; intuition.
  simpl in H.
  destruct b; destruct (whd b0); intros.
  f_equal. eapply IHa. eapply N.succ_double_inj in H.
  destruct (wordToN a); destruct (wordToN (wtl b0)); try congruence.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  f_equal. eapply IHa.
  destruct (wordToN a); destruct (wordToN (wtl b0)); simpl in *; try congruence.
Qed.
Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
Proof.
  intros sz a b1 b2 H *.
  transitivity (b1 ^+ wzero _).
  rewrite wplus_comm. rewrite wplus_unit. auto.
  transitivity (b1 ^+ (a ^+ b2)). congruence.
  rewrite wplus_assoc.
  rewrite (wplus_comm b1). rewrite H. rewrite wplus_unit. auto.
Qed.
Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.
Proof.
  intros sz a b H. destruct (weq (wneg b) (wneg a)) as [e|n].
  transitivity (a ^+ (^~ b ^+ b)).
  rewrite (wplus_comm (^~ b)). rewrite wminus_inv.
  rewrite wplus_comm. rewrite wplus_unit. auto.
  rewrite e. rewrite wplus_assoc. rewrite wminus_inv. rewrite wplus_unit. auto.
  unfold wminus in H.
  generalize (unique_inverse a (wneg a) (^~ b)).
  intro H0. elimtype False. apply n. symmetry; apply H0.
  apply wminus_inv.
  auto.
Qed.

Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.
Proof.
  intros sz a b H H0; destruct (wlt_dec b a) as [?|n]; auto.
  elimtype False. apply H0. unfold wlt, Nlt in *.
  eapply wordToN_inj. eapply Ncompare_eq_correct.
  case_eq ((wordToN a ?= wordToN b)%N); auto; try congruence.
  intros H1. rewrite <- Ncompare_antisym in n. rewrite H1 in n. simpl in *. congruence.
Qed.


Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.

Ltac shatter_word x :=
  match type of x with
    | word 0 => try rewrite (shatter_word_0 x) in *
    | word (S ?N) =>
      let x' := fresh in
      let H := fresh in
      destruct (@shatter_word_S N x) as [ ? [ x' H ] ];
      rewrite H in *; clear H; shatter_word x'
  end.


(** Uniqueness of equality proofs **)
Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),
  weq a b = left _ pf.
Proof.
  intros sz a b *; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal.
  eapply UIP_dec. eapply weq.
Qed.


(** * Some more useful derived facts *)

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.
  destruct sz as [|sz]; intros n m; intuition.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  do 2 match goal with H : _ |- _ => rewrite H; clear H end.
  match goal with
  | [ |- context[?n - ?x * pow2 (S ?sz) + (?m - ?x0 * pow2 (S ?sz))] ]
    => replace (n - x * pow2 (S sz) + (m - x0 * pow2 (S sz))) with (n + m - x * pow2 (S sz) - x0 * pow2 (S sz))
      by omega
  end.
  repeat rewrite drop_sub; auto; omega.
Qed.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.
  intros sz n; change (S n) with (1 + n); apply natToWord_plus.
Qed.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> (n < pow2 sz)%nat
  -> (m < pow2 sz)%nat
  -> n = m.
  intros sz n m H H0 H1.
  apply (f_equal (@wordToNat _)) in H.
  destruct (wordToNat_natToWord sz n) as [x H2].
  destruct (wordToNat_natToWord sz m) as [x0 H3].
  intuition.
  match goal with
  | [ H : wordToNat ?x = wordToNat ?y, H' : wordToNat ?x = ?a, H'' : wordToNat ?y = ?b |- _ ]
    => let H0 := fresh in assert (H0 : a = b) by congruence; clear H H' H''; rename H0 into H
  end.
  assert (x = 0).
  destruct x; auto.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; auto.
  simpl in *.
  generalize dependent (x0 * pow2 sz).
  intros.
  omega.
  subst; simpl in *; omega.
Qed.

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.
  intros sz n H.
  destruct (wordToNat_natToWord sz n) as [x]; intuition.
  destruct x as [|x].
  simpl in *; omega.
  simpl in *.
  apply Nlt_out in H.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.

Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.
  intros sz a b c H.
  apply (f_equal (fun x => x ^+ ^~ c)) in H.
  repeat rewrite <- wplus_assoc in H.
  rewrite wminus_inv in H.
  repeat rewrite (wplus_comm _ (wzero sz)) in H.
  repeat rewrite wplus_unit in H.
  assumption.
Qed.
