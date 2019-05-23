(** * Some lemmas about [Bool.reflect] *)
Require Import Coq.Classes.CMorphisms.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith_dec.
Require Import Coq.NArith.BinNat.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Comparison.
Require Import Crypto.Util.Tactics.DestructHead.
Require Crypto.Util.PrimitiveProd.

Lemma reflect_to_dec_iff {P b1 b2} : reflect P b1 -> (b1 = b2) <-> (if b2 then P else ~P).
Proof.
  intro H; destruct H, b2; split; trivial; repeat intro; abstract (exfalso; intuition congruence).
Qed.

Lemma reflect_to_dec {P b1 b2} : reflect P b1 -> (b1 = b2) -> (if b2 then P else ~P).
Proof. intro; apply reflect_to_dec_iff; assumption. Qed.

Lemma reflect_of_dec {P} {b1 b2 : bool} : reflect P b1 -> (if b2 then P else ~P) -> (b1 = b2).
Proof. intro; apply reflect_to_dec_iff; assumption. Qed.

Lemma reflect_of_brel {A R Rb} (bl : forall a a' : A, Rb a a' = true -> (R a a' : Prop))
      (lb : forall a a' : A, R a a' -> Rb a a' = true)
  : forall x y, reflect (R x y) (Rb x y).
Proof.
  intros x y; specialize (bl x y); specialize (lb x y).
  destruct (Rb x y); constructor; auto; repeat intro; abstract (exfalso; intuition congruence).
Qed.

Lemma reflect_to_brel {A R Rb} (H : forall x y : A, reflect (R x y) (Rb x y))
  : (forall a a' : A, Rb a a' = true -> R a a')
    /\ (forall a a' : A, R a a' -> Rb a a' = true).
Proof.
  split; intros x y; specialize (H x y); destruct H; trivial; repeat intro; abstract (exfalso; intuition congruence).
Qed.

Lemma reflect_of_beq {A beq} (bl : forall a a' : A, beq a a' = true -> a = a')
      (lb : forall a a' : A, a = a' -> beq a a' = true)
  : forall x y, reflect (x = y) (beq x y).
Proof. apply reflect_of_brel; assumption. Qed.

Lemma reflect_to_beq {A beq} (H : forall x y : A, reflect (x = y) (beq x y))
  : (forall a a' : A, beq a a' = true -> a = a')
    /\ (forall a a' : A, a = a' -> beq a a' = true).
Proof. apply reflect_to_brel; assumption. Qed.

Lemma reflect_rect_dep {P b} (Q : reflect P b -> Type)
      (H : forall pf : if b then P else ~P,
          (if b return (reflect P b -> Type) -> (if b then P else ~P) -> Type
           then fun Q pf => Q (ReflectT _ pf)
           else fun Q pf => Q (ReflectF _ pf))
            Q pf)
  : forall x, Q x.
Proof. intro x; destruct x; apply H. Defined.

Definition mark {T} (v : T) := v.

Ltac induction_reflect x :=
  let G := lazymatch goal with |- ?G => G end in
  change (mark G);
  generalize dependent x;
  let Q := lazymatch goal with |- forall y, @?Q y => Q end in
  refine (@reflect_rect_dep _ _ Q _);
  intros; cbv beta delta [mark].

Section encode_decode.
  Context {P : Prop}.

  Definition code (b : bool) : Type
    := if b then P else ~P.
  Definition encode {b} : reflect P b -> code b
    := fun r => match r with
                | ReflectT x => x
                | ReflectF x => x
                end.
  Definition decode {b} : code b -> reflect P b
    := if b return code b -> reflect P b then @ReflectT P else @ReflectF P.
  Lemma endecode {b} x : encode (@decode b x) = x.
  Proof. destruct b; reflexivity. Defined.
  Lemma deencode {b} x : decode (@encode b x) = x.
  Proof. destruct x; reflexivity. Defined.
End encode_decode.

Ltac beq_to_eq beq bl lb :=
  let lem := constr:(@reflect_of_beq _ beq bl lb) in
  repeat match goal with
         | [ |- context[bl ?x ?y ?pf] ] => generalize dependent (bl x y pf); try clear pf; intros
         | [ H : beq ?x ?y = true |- _ ] => apply (@reflect_to_dec _ _ true (lem x y)) in H; cbv beta iota in H
         | [ H : beq ?x ?y = false |- _ ] => apply (@reflect_to_dec _ _ false (lem x y)) in H; cbv beta iota in H
         | [ |- beq ?x ?y = true ] => refine (@reflect_of_dec _ _ true (lem x y) _)
         | [ |- beq ?x ?y = false ] => refine (@reflect_of_dec _ _ false (lem x y) _)
         | [ H : beq ?x ?y = true |- ?G ]
           => change (mark G); generalize dependent (bl x y H); clear H;
              intros; cbv beta delta [mark]
         | [ H : context[beq ?x ?x] |- _ ] => rewrite (lb x x eq_refl) in H
         | [ |- context[beq ?x ?x] ] => rewrite (lb x x eq_refl)
         end.

Existing Class reflect.
Definition decb (P : Prop) {b : bool} {H : reflect P b} := b.
Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).
Definition decb_rel {A B} (P : A -> B -> Prop) {b : A -> B -> bool} {H : reflect_rel P b} := b.

Lemma decb_true_iff P {b} {H : reflect P b} : @decb P b H = true <-> P.
Proof. symmetry; apply reflect_iff, H. Qed.
Lemma decb_bp P {b} {H : reflect P b} : @decb P b H = true -> P.
Proof. apply decb_true_iff. Qed.
Lemma decb_pb P {b} {H : reflect P b} : P -> @decb P b H = true.
Proof. apply decb_true_iff. Qed.
Lemma decb_false_iff P {b} {H : reflect P b} : @decb P b H = false <-> ~P.
Proof. generalize (decb P), (decb_true_iff P); clear; intros []; intros; intuition congruence. Qed.
Lemma decb_false_bp P {b} {H : reflect P b} : @decb P b H = false -> ~P.
Proof. apply decb_false_iff. Qed.
Lemma decb_false_pb P {b} {H : reflect P b} : ~P -> @decb P b H = false.
Proof. apply decb_false_iff. Qed.

Global Instance dec_of_reflect P {b} {H : reflect P b} : Decidable P | 15
  := (if b as b return reflect P b -> Decidable P
      then fun H => left (decb_bp P eq_refl)
      else fun H => right (decb_false_bp P eq_refl)) H.

Global Instance eq_decb_hprop {A} {x y : A} {hp : IsHProp A} : reflect (@eq A x y) true | 5.
Proof. left; auto. Qed.

Lemma ishprop_reflect_all_eq_gen {A} {beq} {H : forall x y : A, reflect (x = y) (beq x y)}
  : forall x y, (beq x y = true \/ IsHProp (x <> y)) -> IsHProp (reflect (x = y) (beq x y)).
Proof.
  intros x y H' p q.
  induction_reflect p; induction_reflect q.
  destruct (beq x y); f_equal.
  { apply Eqdep_dec.UIP_dec; intros x' y'; specialize (H x' y'); eapply @dec_of_reflect; eassumption. }
  { destruct H' as [H'|H']; [ congruence | now apply H' ]. }
Qed.

Lemma eq_reflect_to_dec_true_gen {A beq} {H : forall x y : A, reflect (x = y) (beq x y)}
      {x y pf H'}
  : @reflect_to_dec (x = y) (beq x y) true H' pf = @reflect_to_dec (x = y) (beq x y) true (H _ _) pf.
Proof.
  apply f_equal2; [ | reflexivity ].
  apply ishprop_reflect_all_eq_gen; left; assumption.
Qed.

Lemma eq_reflect_to_dec_true_refl {A beq} {H : forall x y : A, reflect (x = y) (beq x y)}
      {x pf H'}
  : @reflect_to_dec (x = x) (beq x x) true H' pf = eq_refl.
Proof.
  apply Eqdep_dec.UIP_dec; intros; eapply @dec_of_reflect; eauto.
Qed.

Ltac generalize_reflect_to_dec_rel_refl_using beq R :=
  let A := lazymatch type of beq with ?A -> _ -> _ => A end in
  let do_gen b x R' H :=
      (let G := match goal with |- ?G => G end in
       change (mark G); generalize (@eq_reflect_to_dec_true_refl A beq R x H R');
       change (beq x x) with b in *;
       generalize dependent (@reflect_to_dec (@eq A x x) b true R' H);
       try clear H;
       let H' := fresh in
       intro H'; intros; subst H'; cbv beta delta [mark]) in
  repeat match goal with
         | [ H : context[@reflect_to_dec (@eq A ?x ?x) ?b true ?R' ?H'] |- _ ]
           => do_gen b x R' H'
         | [ |- context[@reflect_to_dec (@eq A ?x ?x) ?b true ?R' ?H'] ]
           => do_gen b x R' H'
         end.

Ltac generalize_reflect_to_dec :=
  repeat match goal with
         | [ H : context[@reflect_to_dec ?P ?b true ?R ?H] |- ?G ]
           => change (mark G); generalize dependent (@reflect_to_dec P b true R H); try clear H; intros; cbv beta delta [mark]
         | [ |- context[@reflect_to_dec ?P ?b true ?R ?H] ]
           => let G := match goal with |- ?G => G end in
              change (mark G); generalize dependent (@reflect_to_dec P b true R H); try clear H; intros; cbv beta delta [mark]
         end.

Ltac reflect_beq_to_eq_using R :=
  let beq := lazymatch type of R with forall x y, reflect (x = y) (?beq x y) => beq end in
  let lem_to_dec := constr:(fun b x y => @reflect_to_dec (x = y) (beq x y) b (R x y)) in
  let lem_of_dec := constr:(fun b x y => @reflect_of_dec (x = y) (beq x y) b (R x y)) in
  generalize_reflect_to_dec_rel_refl_using beq R;
  generalize_reflect_to_dec;
  repeat match goal with
         | [ H : beq ?x ?y = true |- _ ] => apply (lem_to_dec true x y) in H; cbv beta iota in H
         | [ H : beq ?x ?y = false |- _ ] => apply (lem_to_dec false x y) in H; cbv beta iota in H
         | [ |- beq ?x ?y = true ] => refine (lem_of_dec true x y _)
         | [ |- beq ?x ?y = false ] => refine (lem_of_dec false x y _)
         | [ H : context[beq ?x ?x] |- _ ] => rewrite (lem_of_dec true x x eq_refl) in H
         | [ |- context[beq ?x ?x] ] => rewrite (lem_of_dec true x x eq_refl)
         | [ H : context[@reflect_to_dec ?P (beq ?x ?y) true ?R ?H] |- ?G ]
           => change (mark G); generalize dependent (@reflect_to_dec P (beq x y) true R H); try clear H; intros; cbv beta delta [mark]
         | [ |- context[@reflect_to_dec ?P (beq ?x ?y) true ?R ?H] ]
           => let G := match goal with |- ?G => G end in
              change (mark G); generalize dependent (@reflect_to_dec P (beq x y) true R H); try clear H; intros; cbv beta delta [mark]
         end.

Ltac reflect_beq_to_eq beq :=
  let R := constr:(_ : forall x y, reflect (x = y) (beq x y)) in
  reflect_beq_to_eq_using R.

Ltac solve_reflect_step :=
  first [ match goal with
          | [ H : reflect _ ?b |- _ ] => tryif is_var b then destruct H else (inversion H; clear H)
          | [ |- reflect _ _ ] => constructor
          | [ |- reflect (?R ?x ?y) (?Rb ?x ?y) ] => apply (@reflect_of_brel _ R Rb)
          | [ H : forall x y, reflect (?R x y) (?Rb x y) |- _ ] => apply (@reflect_to_brel _ R Rb) in H
          end
        | progress destruct_head'_and
        | progress intros
        | progress subst
        | solve [ eauto ]
        | progress destruct_head'_or
        | apply conj
        | repeat intro; abstract (exfalso; firstorder (auto; try discriminate))
            (*
          | [ H :
          | [ H : forall x y : ?A, reflect (x = y) _, x0 : ?A, y0 : ?A  |- _ ]
            => no_equalities_about x0 y0; let H' := fresh in pose proof (H x0 y0) as H'; inversion H'; clear H'
          | [ H : forall a0 (x y : _), reflect (x = y) _, x0 : ?A, y0 : ?A  |- _ ]
            => no_equalities_about x0 y0; let H' := fresh in pose proof (H _ x0 y0) as H'; inversion H'; clear H'
          | [ H : true = ?x |- context[?x] ] => rewrite <- H
          | [ H : false = ?x |- context[?x] ] => rewrite <- H
          end
        | progress intros
        | split
        | progress inversion_sigma
        | progress inversion_prod
        | progress pre_decide_destruct_sigma
        | progress destruct_head'_bool
        | progress destruct_head'_prod
        | progress subst
        | progress cbn in *
        | progress hnf
        | progress pre_hprop
        | solve [ left; firstorder (auto; try discriminate)
                | right; firstorder (auto; try discriminate)
                | firstorder (auto; try discriminate) ] *) ].


Ltac solve_reflect := repeat solve_reflect_step.

Hint Constructors reflect : typeclass_instances.

Local Hint Resolve -> Bool.eqb_true_iff : core.
Local Hint Resolve <- Bool.eqb_true_iff : core.
Local Hint Resolve internal_prod_dec_bl internal_prod_dec_lb
      PrimitiveProd.Primitive.prod_dec_bl PrimitiveProd.Primitive.prod_dec_lb
      internal_option_dec_bl internal_option_dec_lb
      internal_list_dec_bl internal_list_dec_lb
      internal_sum_dec_bl internal_sum_dec_lb
      sigT_dec_bl sigT_dec_lb
      sigT_dec_bl_hprop sigT_dec_lb_hprop
      sig_dec_bl sig_dec_lb
      sig_dec_bl_hprop sig_dec_lb_hprop
      internal_comparison_dec_bl internal_comparison_dec_lb
  : core.

Local Hint Extern 0 => solve [ solve_reflect ] : typeclass_instances.
Local Hint Extern 1 => progress inversion_sigma : core.

Global Instance reflect_True : reflect True true | 10 := ReflectT _ I.
Global Instance reflect_False : reflect False false | 10 := ReflectF _ (fun x => x).
Global Instance reflect_or {A B a b} `{reflect A a, reflect B b} : reflect (A \/ B) (orb a b) | 10. exact _. Qed.
Global Instance reflect_and {A B a b} `{reflect A a, reflect B b} : reflect (A /\ B) (andb a b) | 10. exact _. Qed.
Global Instance reflect_impl_or {A B bona} `{reflect (B \/ ~A) bona} : reflect (A -> B) bona | 15. exact _. Qed.
Global Instance reflect_impl {A B a b} `{reflect A a, reflect B b} : reflect (A -> B) (implb a b) | 10. exact _. Qed.
Global Instance reflect_iff {A B a b} `{reflect A a, reflect B b} : reflect (A <-> B) (Bool.eqb a b) | 10. exact _. Qed.
Lemma reflect_not {A a} `{reflect A a} : reflect (~A) (negb a).
Proof. exact _. Qed.

(** Disallow infinite loops of reflect_not *)
Hint Extern 0 (reflect (~?A) _) => eapply (@reflect_not A) : typeclass_instances.
Hint Extern 0 (reflect _ (negb ?b)) => eapply (@reflect_not _ b) : typeclass_instances.

Global Instance reflect_eq_unit : reflect_rel (@eq unit) (fun _ _ => true) | 10. exact _. Qed.
Global Instance reflect_eq_bool : reflect_rel (@eq bool) Bool.eqb | 10. exact _. Qed.
Global Instance reflect_eq_Empty_set : reflect_rel (@eq Empty_set) (fun _ _ => true) | 10. exact _. Qed.
Global Instance reflect_eq_prod {A B eqA eqB} `{reflect_rel (@eq A) eqA, reflect_rel (@eq B) eqB} : reflect_rel (@eq (A * B)) (prod_beq A B eqA eqB) | 10. exact _. Qed.
Global Instance reflect_eq_option {A eqA} `{reflect_rel (@eq A) eqA} : reflect_rel (@eq (option A)) (option_beq eqA) | 10. exact _. Qed.
Global Instance reflect_eq_list {A eqA} `{reflect_rel (@eq A) eqA} : reflect_rel (@eq (list A)) (list_beq A eqA) | 10. exact _. Qed.
Global Instance reflect_eq_list_nil_r {A eqA} {ls} : reflect (ls = @nil A) (list_beq A eqA ls (@nil A)) | 10.
Proof. destruct ls; [ left; reflexivity | right; abstract congruence ]. Qed.
Global Instance reflect_eq_list_nil_l {A eqA} {ls} : reflect (@nil A = ls) (list_beq A eqA (@nil A) ls) | 10.
Proof. destruct ls; [ left; reflexivity | right; abstract congruence ]. Qed.
Global Instance reflect_eq_sum {A B eqA eqB} `{reflect_rel (@eq A) eqA, reflect_rel (@eq B) eqB} : reflect_rel (@eq (A + B)) (sum_beq A B eqA eqB) | 10. exact _. Qed.
Global Instance reflect_eq_sigT_hprop {A P eqA} `{reflect_rel (@eq A) eqA, forall a : A, IsHProp (P a)} : reflect_rel (@eq (@sigT A P)) (sigT_beq eqA (fun _ _ _ _ => true)) | 10. exact _. Qed.
Global Instance reflect_eq_sig_hprop {A eqA} {P : A -> Prop} `{reflect_rel (@eq A) eqA, forall a : A, IsHProp (P a)} : reflect_rel (@eq (@sig A P)) (sig_beq eqA (fun _ _ _ _ => true)) | 10. exact _. Qed.
Global Instance reflect_eq_comparison : reflect_rel (@eq comparison) comparison_beq | 10. exact _. Qed.

Module Export Primitive.
  Import PrimitiveProd.
  Import PrimitiveProd.Primitive.
  Global Instance reflect_eq_prod {A B eqA eqB} `{reflect_rel (@eq A) eqA, reflect_rel (@eq B) eqB} : reflect_rel (@eq (A * B)) (@Primitive.prod_beq A B eqA eqB) | 10. exact _. Qed.
End Primitive.

Module Nat.
  Definition geb_spec0 : reflect_rel ge (fun x y => Nat.leb y x) := fun _ _ => Nat.leb_spec0 _ _.
  Definition gtb_spec0 : reflect_rel gt (fun x y => Nat.ltb y x) := fun _ _ => Nat.ltb_spec0 _ _.
End Nat.
Global Existing Instance Nat.eqb_spec | 10.
Global Existing Instances Nat.leb_spec0 Nat.ltb_spec0 Nat.geb_spec0 Nat.gtb_spec0.

Module N.
  Lemma geb_spec0 : reflect_rel N.ge (fun x y => N.leb y x).
  Proof. intros x y; generalize (N.leb_spec0 y x); intro H; destruct H; constructor; rewrite N.ge_le_iff; assumption. Qed.
  Lemma gtb_spec0 : reflect_rel N.gt (fun x y => N.ltb y x).
  Proof. intros x y; generalize (N.ltb_spec0 y x); intro H; destruct H; constructor; rewrite N.gt_lt_iff; assumption. Qed.
End N.
Global Existing Instance N.eqb_spec | 10.
Global Existing Instances N.leb_spec0 N.ltb_spec0 N.geb_spec0 N.gtb_spec0.

Module Z.
  Lemma geb_spec0 : reflect_rel Z.ge Z.geb.
  Proof. intros x y; generalize (Z.leb_spec0 y x); rewrite Z.geb_leb; intro H; destruct H; constructor; rewrite Z.ge_le_iff; assumption. Qed.
  Lemma gtb_spec0 : reflect_rel Z.gt Z.gtb.
  Proof. intros x y; generalize (Z.ltb_spec0 y x); rewrite Z.gtb_ltb; intro H; destruct H; constructor; rewrite Z.gt_lt_iff; assumption. Qed.
End Z.
Global Existing Instance Z.eqb_spec | 10.
Global Existing Instances Z.leb_spec0 Z.ltb_spec0 Z.geb_spec0 Z.gtb_spec0.

Module Pos.
  Lemma geb_spec0 : reflect_rel Pos.ge (fun x y => Pos.leb y x).
  Proof. intros x y; generalize (Pos.leb_spec0 y x); intro H; destruct H; constructor; rewrite Pos.ge_le_iff; assumption. Qed.
  Lemma gtb_spec0 : reflect_rel Pos.gt (fun x y => Pos.ltb y x).
  Proof. intros x y; generalize (Pos.ltb_spec0 y x); intro H; destruct H; constructor; rewrite Pos.gt_lt_iff; assumption. Qed.
End Pos.
Global Existing Instance Pos.eqb_spec | 10.
Global Existing Instances Pos.leb_spec0 Pos.ltb_spec0 Pos.geb_spec0 Pos.gtb_spec0.

Global Instance reflect_Forall {A P Pb} {HD : forall x : A, reflect (P x) (Pb x)} {ls}
  : reflect (List.Forall P ls) (List.forallb Pb ls) | 10.
Proof.
  induction ls as [|x xs IHxs]; cbn [List.forallb]; [ left | destruct (HD x), IHxs; [ left | right.. ] ];
    [ constructor; assumption | constructor; assumption | intro Hn.. ];
    clear HD;
    try abstract (inversion Hn; subst; tauto).
Qed.
Global Instance reflect_Exists {A P Pb} {HD : forall x : A, reflect (P x) (Pb x)} {ls}
  : reflect (List.Exists P ls) (List.existsb Pb ls) | 10.
Proof.
  induction ls as [|x xs IHxs]; cbn [List.existsb]; [ right | destruct (HD x), IHxs; [ left.. | right ] ];
    [ intro Hn | constructor; assumption.. | intro Hn ];
    clear HD;
    try abstract (inversion Hn; subst; tauto).
Qed.

Global Instance reflect_match_pair {A B} {P : A -> B -> Prop} {Pb : A -> B -> bool} {x : A * B}
       {HD : reflect (P (fst x) (snd x)) (Pb (fst x) (snd x))}
  : reflect (let '(a, b) := x in P a b) (let '(a, b) := x in Pb a b) | 1.
Proof. edestruct (_ : _ * _); assumption. Qed.

Definition reflect_if_bool {x : bool} {A B a b} {HA : reflect A a} {HB : reflect B b}
  : reflect (if x then A else B) (if x then a else b)
  := if x return reflect (if x then A else B) (if x then a else b)
     then HA
     else HB.

Hint Extern 1 (reflect _ (match ?x with true => ?a | false => ?b end))
=> eapply (@reflect_if_bool x _ _ a b) : typeclass_instances.
Hint Extern 1 (reflect (match ?x with true => ?A | false => ?B end) _)
=> eapply (@reflect_if_bool x A B) : typeclass_instances.

Global Instance reflect_ex_forall_not : forall T (P:T->Prop) (exPb:bool) {d:reflect (exists b, P b) exPb}, reflect (forall b, ~ P b) (negb exPb).
Proof.
  intros T P exPb d; destruct d; constructor; firstorder.
Qed.

Global Polymorphic Instance reflect_Proper_iff
  : Proper (iff ==> eq ==> iffT) reflect | 10.
Proof.
  intros A B H b b' ?; subst b'; split; intro H'; destruct H, H'; constructor; auto.
Qed.

Global Polymorphic Instance reflect_Proper_arrow
  : Proper (iff ==> eq ==> arrow) reflect | 10.
Proof.
  repeat intro; eapply reflect_Proper_iff; try eassumption; easy.
Qed.

Global Polymorphic Instance reflect_Proper_flip_arrow
  : Proper (iff ==> eq ==> flip arrow) reflect | 10.
Proof.
  repeat intro; eapply reflect_Proper_iff; try eassumption; easy.
Qed.

Lemma reflect_bool : forall {P b} {Preflect:reflect P b}, b = true -> P.
Proof. intros P b Preflect; destruct Preflect; solve [ auto | discriminate ]. Qed.

Ltac vm_reflect_no_check := apply reflect_bool; vm_cast_no_check (eq_refl true).
Ltac lazy_reflect_no_check := apply reflect_bool; exact_no_check (eq_refl true).

Ltac vm_reflect := abstract vm_reflect_no_check.
Ltac lazy_reflect := abstract lazy_reflect_no_check.
