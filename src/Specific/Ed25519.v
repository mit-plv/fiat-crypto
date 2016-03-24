Require Import Bedrock.Word.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.Encoding Crypto.Spec.PointEncoding.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.Util.IterAssocOp.

Local Infix "++" := Word.combine.
Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).
Local Arguments H {_} _.
Local Arguments scalarMultM1 {_} {_} _ _.
Local Arguments unifiedAddM1 {_} {_} _ _.

Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.
Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.

Axiom point_eqb : forall {prm : TwistedEdwardsParams}, point -> point -> bool.
Axiom point_eqb_correct : forall P Q, point_eqb P Q = if point_eq_dec P Q then true else false.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
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

Axiom decode_scalar : word b -> option N.
Local Existing Instance Ed25519.FlEncoding.
Axiom decode_scalar_correct : forall x, decode_scalar x = option_map (fun x : F (Z.of_nat Ed25519.l) => Z.to_N x) (dec x).

Local Infix "==?" := point_eqb (at level 70) : E_scope.

Axiom negate : point -> point.
Definition point_sub P Q := (P + negate Q)%E.
Infix "-" := point_sub : E_scope.
Axiom solve_for_R : forall A B C, (A ==? B + C)%E = (B ==? A - C)%E.

Axiom negateExtended : extendedPoint -> extendedPoint.
Axiom negateExtended_correct : forall P, negate (unExtendedPoint P) = unExtendedPoint (negateExtended P).

Local Existing Instance PointEncoding.
Axiom decode_point_eq : forall (P_ Q_ : word (S (b-1))) (P Q:point), dec P_ = Some P -> dec Q_ = Some Q -> weqb P_ Q_ = (P ==? Q)%E.

Lemma decode_test_encode_test : forall S_ X, option_rect (fun _ : option point => bool)
 (fun S : point => (S ==? X)%E) false (dec S_) = weqb S_ (enc X).
Proof.
  intros.
  destruct (dec S_) eqn:H.
  { symmetry; eauto using decode_point_eq, encoding_valid. }
  { simpl @option_rect.
    destruct (weqb S_ (enc X)) eqn:Heqb; trivial.
    apply weqb_true_iff in Heqb. subst. rewrite encoding_valid in H; discriminate. }
Qed.

Lemma sharper_verify : forall pk l msg sig, { verify | verify = ed25519_verify pk l msg sig}.
Proof.
  eexists; intros.
  cbv [ed25519_verify EdDSA.verify
                      ed25519params curve25519params
                      EdDSA.E EdDSA.B EdDSA.b EdDSA.l EdDSA.H
                      EdDSA.PointEncoding EdDSA.FlEncoding EdDSA.FqEncoding].

  etransitivity.
  Focus 2.
  { repeat match goal with
           | [ |- ?x = ?x ] => reflexivity
           | [ |- _ = match ?a with None => ?N | Some x => @?S x end :> ?T ]
             => etransitivity;
               [
               | refine (_ : option_rect (fun _ => T) _ N a = _);
                 let S' := match goal with |- option_rect _ ?S' _ _ = _ => S' end in
                 refine (option_rect (fun a' => option_rect (fun _ => T) S' N a' = match a' with None => N | Some x => S x end)
                                     (fun x => _) _ a); intros; simpl @option_rect ];
               [ reflexivity | .. ]
           end.
    set_evars.
    rewrite<- point_eqb_correct.
    rename x0 into R. rename x1 into S. rename x into A.
    rewrite solve_for_R.
    let p1 := constr:(scalarMultM1_rep eq_refl) in
    let p2 := constr:(unifiedAddM1_rep eq_refl) in
    repeat match goal with
           | |- context [(_ * ?P)%E] =>
              rewrite <-(unExtendedPoint_mkExtendedPoint P);
               rewrite <-p1
           | |- context [(?P + unExtendedPoint _)%E] =>
             rewrite <-(unExtendedPoint_mkExtendedPoint P);
               rewrite p2
           end;
      rewrite ?Znat.Z_nat_N, <-?Word.wordToN_nat;
      subst_evars;
      reflexivity.
    } Unfocus.

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

  etransitivity.
  Focus 2.
  { do 2 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
    symmetry; apply decode_test_encode_test.
  } Unfocus.

  etransitivity.
  Focus 2.
  { do 2 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
    unfold point_sub. rewrite negateExtended_correct.
    let p := constr:(unifiedAddM1_rep eq_refl) in rewrite p.
    reflexivity.
  } Unfocus.

  cbv [scalarMultM1 iter_op].
  cbv iota zeta delta [test_and_op].
  Local Arguments funexp {_} _ {_} {_}. (* do not display the initializer and iteration bound for now *)

  Axiom rep : forall {m}, list Z -> F m -> Prop.
  Axiom decode_point_limbs : word (S (b-1)) -> option (list Z * list Z).
  Axiom point_dec_rep : forall P_ P lx ly, dec P_ = Some P -> decode_point_limbs P_ = Some (lx, ly) -> rep lx (fst (proj1_sig P)) /\ rep ly (fst (proj1_sig P)).
Admitted.