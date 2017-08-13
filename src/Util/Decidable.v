(** Typeclass for decidable propositions *)

Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.HProp.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith_dec.
Require Import Coq.NArith.BinNat.

Local Open Scope type_scope.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.
Notation DecidableRel R := (forall x y, Decidable (R x y)).

Global Instance hprop_eq_dec {A} `{DecidableRel (@eq A)} : IsHPropRel (@eq A) | 10.
Proof. repeat intro; apply UIP_dec; trivial with nocore. Qed.

Global Instance eq_dec_hprop {A} {x y : A} {hp : IsHProp A} : Decidable (@eq A x y) | 5.
Proof. left; auto. Qed.

Ltac no_equalities_about x0 y0 :=
  lazymatch goal with
  | [ H' : x0 = y0 |- _ ] => fail
  | [ H' : y0 = x0 |- _ ] => fail
  | [ H' : x0 <> y0 |- _ ] => fail
  | [ H' : y0 <> x0 |- _ ] => fail
  | _ => idtac
  end.

Ltac destruct_decidable_step :=
  match goal with
  | [ H : Decidable _ |- _ ] => destruct H
  | [ H : forall x y : ?A, Decidable (x = y), x0 : ?A, y0 : ?A  |- _ ]
    => no_equalities_about x0 y0; destruct (H x0 y0)
  | [ H : forall a0 (x y : _), Decidable (x = y), x0 : ?A, y0 : ?A  |- _ ]
    => no_equalities_about x0 y0; destruct (H _ x0 y0)
  end.
Ltac destruct_decidable := repeat destruct_decidable_step.

Ltac pre_decide_destruct_sigma_step :=
  match goal with
  | [ H : sigT _ |- _ ] => destruct H
  | [ H : sig _ |- _ ] => destruct H
  | [ H : ex _ |- _ ] => destruct H
  end.
Ltac pre_decide_destruct_sigma := repeat pre_decide_destruct_sigma_step.

Ltac pre_decide :=
  repeat (intros
          || destruct_decidable
          || split
          || pre_decide_destruct_sigma
          || unfold Decidable in *
          || hnf).

(** Put the [subst] and reasoning about equalities after the [left]
    and [right]; opaque equality proofs should not block decidability
    proofs. *)
Ltac post_decide :=
  repeat (intros
          || subst
          || pre_hprop).

Ltac solve_decidable_transparent_with tac :=
  pre_decide;
  try solve [ left; abstract (post_decide; tac)
            | right; abstract (post_decide; tac)
            | decide equality; eauto with nocore ].

Ltac solve_decidable_transparent := solve_decidable_transparent_with firstorder.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Local Hint Extern 1 => progress inversion_sigma : core.

Global Instance dec_True : Decidable True | 10 := left I.
Global Instance dec_False : Decidable False | 10 := right (fun x => x).
Global Instance dec_or {A B} `{Decidable A, Decidable B} : Decidable (A \/ B) | 10. exact _. Defined.
Global Instance dec_and {A B} `{Decidable A, Decidable B} : Decidable (A /\ B) | 10. exact _. Defined.
Global Instance dec_impl {A B} `{Decidable (B \/ ~A)} : Decidable (A -> B) | 10. exact _. Defined.
Global Instance dec_impl_simple {A B} `{Decidable A, Decidable B} : Decidable (A -> B) | 10. exact _. Defined.
Global Instance dec_iff {A B} `{Decidable A, Decidable B} : Decidable (A <-> B) | 10. exact _. Defined.
Lemma dec_not {A} `{Decidable A} : Decidable (~A).
Proof. solve_decidable_transparent. Defined.
(** Disallow infinite loops of dec_not *)
Hint Extern 0 (Decidable (~?A)) => apply (@dec_not A) : typeclass_instances.
Global Instance dec_eq_unit : DecidableRel (@eq unit) | 10. exact _. Defined.
Global Instance dec_eq_bool : DecidableRel (@eq bool) | 10. exact _. Defined.
Global Instance dec_eq_Empty_set : DecidableRel (@eq Empty_set) | 10. exact _. Defined.
Global Instance dec_eq_prod {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A * B)) | 10. exact _. Defined.
Global Instance dec_eq_option {A} `{DecidableRel (@eq A)} : DecidableRel (@eq (option A)) | 10. exact _. Defined.
Global Instance dec_eq_list {A} `{DecidableRel (@eq A)} : DecidableRel (@eq (list A)) | 10. exact _. Defined.
Global Instance dec_eq_list_nil_r {A} {ls} : Decidable (ls = @nil A) | 10.
Proof. destruct ls; [ left; reflexivity | right; abstract congruence ]. Defined.
Global Instance dec_eq_list_nil_l {A} {ls} : Decidable (@nil A = ls) | 10.
Proof. destruct ls; [ left; reflexivity | right; abstract congruence ]. Defined.
Global Instance dec_eq_sum {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A + B)) | 10. exact _. Defined.
Global Instance dec_eq_sigT_hprop {A P} `{DecidableRel (@eq A), forall a : A, IsHProp (P a)} : DecidableRel (@eq (@sigT A P)) | 10. exact _. Defined.
Global Instance dec_eq_sig_hprop {A} {P : A -> Prop} `{DecidableRel (@eq A), forall a : A, IsHProp (P a)} : DecidableRel (@eq (@sig A P)) | 10. exact _. Defined.
Global Instance dec_eq_comparison : DecidableRel (@eq comparison) | 10. exact _. Defined.

Global Instance dec_eq_nat : DecidableRel (@eq nat) | 10. exact _. Defined.
Global Instance dec_le_nat : DecidableRel le := Compare_dec.le_dec.
Global Instance dec_lt_nat : DecidableRel lt := Compare_dec.lt_dec.
Global Instance dec_ge_nat : DecidableRel ge := Compare_dec.ge_dec.
Global Instance dec_gt_nat : DecidableRel gt := Compare_dec.gt_dec.

Global Instance dec_eq_N : DecidableRel (@eq N) | 10 := N.eq_dec.

Global Instance dec_eq_Z : DecidableRel (@eq Z) | 10 := Z.eq_dec.
Global Instance dec_lt_Z : DecidableRel BinInt.Z.lt := ZArith_dec.Z_lt_dec.
Global Instance dec_le_Z : DecidableRel BinInt.Z.le := ZArith_dec.Z_le_dec.
Global Instance dec_gt_Z : DecidableRel BinInt.Z.gt := ZArith_dec.Z_gt_dec.
Global Instance dec_ge_Z : DecidableRel BinInt.Z.ge := ZArith_dec.Z_ge_dec.

Global Instance dec_match_pair {A B} {P : A -> B -> Prop} {x : A * B}
       {HD : Decidable (P (fst x) (snd x))}
  : Decidable (let '(a, b) := x in P a b) | 1.
Proof. edestruct (_ : _ * _); assumption. Defined.

Lemma not_not P {d:Decidable P} : not (not P) <-> P.
Proof. destruct (dec P); intuition. Qed.

Global Instance dec_ex_forall_not : forall T (P:T->Prop) {d:Decidable (exists b, P b)}, Decidable (forall b, ~ P b).
Proof.
  intros T P d.
  destruct (dec (~ exists b, P b)) as [Hd|Hd]; [left|right];
    [abstract eauto | let Hd := Hd in abstract (rewrite not_not in Hd by eauto; destruct Hd; eauto) ].
Defined.

Lemma eqsig_eq {T} {U} {Udec:DecidableRel (@eq U)} (f g:T->U) (x x':T) pf pf' :
  (exist (fun x => f x = g x) x pf) = (exist (fun x => f x = g x) x' pf') <-> (x = x').
Proof. apply path_sig_hprop_iff; auto using UIP_dec, Udec. Qed.

Lemma Decidable_respects_iff A B (H : A <-> B) : (Decidable A -> Decidable B) * (Decidable B -> Decidable A).
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_impl A B (H : A <-> B) : Decidable A -> Decidable B.
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_flip_impl A B (H : A <-> B) : Decidable B -> Decidable A.
Proof. solve_decidable_transparent. Defined.

Global Instance dec_eq_positive : DecidableRel (@eq BinNums.positive) | 10 := BinPos.Pos.eq_dec.
Global Instance dec_lt_positive : DecidableRel BinPos.Pos.lt.
Proof. eauto using Decidable_iff_to_impl, Pos.ltb_lt with typeclass_instances. Defined.
Global Instance dec_le_positive : DecidableRel BinPos.Pos.le.
Proof. eauto using Decidable_iff_to_impl, Pos.leb_le with typeclass_instances. Defined.
Global Instance dec_gt_positive : DecidableRel BinPos.Pos.gt.
Proof. eauto using Decidable_iff_to_flip_impl, Pos.gt_lt_iff with typeclass_instances. Defined.
Global Instance dec_ge_positive : DecidableRel BinPos.Pos.ge.
Proof. eauto using Decidable_iff_to_flip_impl, Pos.ge_le_iff with typeclass_instances. Defined.

Lemma dec_of_semidec {P : Prop} (H : option P) (H_complete : H = None -> ~P) : Decidable P.
Proof. destruct H; [ left; assumption | right; apply H_complete, eq_refl ]. Defined.

Lemma dec_rel_of_semidec_rel {A} {R : A -> A -> Prop} (H : forall x y, option (R x y))
      (H_complete : forall x y, H x y = None -> ~R x y) : DecidableRel R.
Proof. eauto using dec_of_semidec. Defined.

Lemma dec_of_bool_dec {P : Prop} (b : bool) (Hbl : b = true -> P) (Hlb : P -> b = true)
  : Decidable P.
Proof. destruct b; [ left; apply Hbl; reflexivity | right; intro p; apply Bool.diff_false_true, Hlb, p ]. Defined.

Lemma dec_rel_of_bool_dec_rel {A} {R : A -> A -> Prop} (b : A -> A -> bool)
      (Hbl : forall x y, b x y = true -> R x y) (Hlb : forall x y, R x y -> b x y = true)
  : DecidableRel R.
Proof. eauto using dec_of_bool_dec. Defined.

Lemma dec_bool : forall {P} {Pdec:Decidable P}, (if dec P then true else false) = true -> P.
Proof. intros. destruct dec; solve [ auto | discriminate ]. Qed.

Ltac vm_decide_no_check := apply dec_bool; vm_cast_no_check (eq_refl true).
Ltac lazy_decide_no_check := apply dec_bool; exact_no_check (eq_refl true).

Ltac vm_decide := abstract vm_decide_no_check.
Ltac lazy_decide := abstract lazy_decide_no_check.

(** For dubious compatibility with [eauto using]. *)
Hint Extern 2 (Decidable _) => progress unfold Decidable : typeclass_instances core.

Definition cast_if_eq {T} `{DecidableRel (@eq T)} {P} (t t' : T) (v : P t) : option (P t')
  := match dec (t = t'), dec (t' = t') with
     | left pf, left pf' => Some (eq_rect _ P v _ (eq_trans pf (eq_sym pf')))
     | _, right pf' => match pf' eq_refl with end
     | right pf, _ => None
     end.

Lemma cast_if_eq_refl {T H P} t v : @cast_if_eq T H P t t v = Some v.
Proof.
  compute; clear; destruct (H t t) as [ [] |e];
    [ reflexivity | destruct (e eq_refl) ].
Qed.
