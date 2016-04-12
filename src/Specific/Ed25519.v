Require Import Bedrock.Word.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import ModularArithmetic.ModularArithmeticTheorems.
Require Import ModularArithmetic.PrimeFieldTheorems.
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

Local Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.
Local Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.

Lemma funexp_proj {T T'} (proj : T -> T') (f : T -> T) (f' : T' -> T') x n
      (f_proj : forall a, proj (f a) = f' (proj a))
  : proj (funexp f x n) = funexp f' (proj x) n.
Proof.
  revert x; induction n as [|n IHn]; simpl; congruence.
Qed.

Lemma iter_op_proj {T T'} (proj : T -> T') (op : T -> T -> T) (op' : T' -> T' -> T') x y z
      (op_proj : forall a b, proj (op a b) = op' (proj a) (proj b))
  : proj (iter_op op x y z) = iter_op op' (proj x) y (proj z).
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

Axiom point_eqb : forall {prm : TwistedEdwardsParams}, point -> point -> bool.
Axiom point_eqb_correct : forall P Q, point_eqb P Q = if point_eq_dec P Q then true else false.

Axiom Bc : F q * F q.
Axiom B_proj : proj1_sig B = Bc.

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
Local Infix "==?" := ModularArithmeticTheorems.F_eq_dec (at level 70) : F_scope.

Axiom negate : point -> point.
Definition point_sub P Q := (P + negate Q)%E.
Infix "-" := point_sub : E_scope.
Axiom solve_for_R : forall A B C, (A ==? B + C)%E = (B ==? A - C)%E.

Axiom negateExtendedc : extended -> extended.
Definition negateExtended : extendedPoint -> extendedPoint.
Proof.
  intro x.
  exists (negateExtendedc (proj1_sig x)).
  admit.
Defined.
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

Definition enc' : F q * F q -> word (S (b - 1)).
Proof.
  intro x.
  let enc' := (eval hnf in (@enc (@point curve25519params) _ _)) in
  match (eval cbv [proj1_sig] in (fun pf => enc' (exist _ x pf))) with
  | (fun _ => ?enc') => exact enc'
  end.
Defined.

Definition enc'_correct : @enc (@point curve25519params) _ _ = (fun x => enc' (proj1_sig x))
  := eq_refl.

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

  rewrite enc'_correct.
  cbv [unExtendedPoint unifiedAddM1 negateExtended scalarMultM1].
  unfold proj1_sig at 1 2 5 6.
  etransitivity.
  Focus 2.
  { do 2 (eapply option_rect_Proper_nd; [intro|reflexivity..]).
    set_evars.
    repeat match goal with
           | [ |- appcontext[@proj1_sig ?A ?P (@iter_op ?T ?f ?x ?y ?z)] ]
             => erewrite (@iter_op_proj T A (@proj1_sig _ _)) by reflexivity
           end.
    subst_evars.
    reflexivity. }
  Unfocus.

  cbv [mkExtendedPoint zero mkPoint].
  unfold proj1_sig at 1 2 3 5 6 7.
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

  Set Printing Depth 1000000.
  Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended X Y Z T).
  Local Notation "2" := (ZToField 2) : F_scope.

  cbv iota beta delta [point_dec_coordinates sign_bit dec FqEncoding modular_word_encoding CompleteEdwardsCurveTheorems.solve_for_x2 sqrt_mod_q].

  Axiom FRep : Type.
  Axiom F2rep : F Ed25519.q -> FRep.
  Axiom rep2F : FRep -> F Ed25519.q.
  Axiom rep2F_F2rep : forall x, x = rep2F (F2rep x).
  Axiom wire2rep_F : word (b-1) -> option FRep.
  Axiom wire2rep_F_correct : forall x, Fm_dec x = option_map rep2F (wire2rep_F x).
  rewrite wire2rep_F_correct.

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
  rewrite <-!(option_rect_option_map rep2F).

  etransitivity.
  Focus 2. {
    do 1 (eapply option_rect_Proper_nd; [|reflexivity..]). cbv beta delta [pointwise_relation]. intro.

    unfold option_rect at 1.
    cbv beta iota delta [q d CompleteEdwardsCurve.a enc].
    let RHS' := constr:(
     @option_rect FRep (fun _ : option FRep => bool)
       (fun x : FRep =>
        let x2 := ((rep2F x ^ 2 - 1) / (Ed25519.d * rep2F x ^ 2 - Ed25519.a))%F in
        let x0 :=
          let b := (x2 ^ Z.to_N (Ed25519.q / 8 + 1))%F in
          if (b ^ 2 ==? x2)%F then b else (@sqrt_minus1 Ed25519.q * b)%F in
        if (x0 ^ 2 ==? x2)%F
        then
         let p :=
           (if Bool.eqb (@whd (b - 1) pk)
                 (@wordToN (b - 1) (@Fm_enc Ed25519.q (b - 1) (@opp Ed25519.q x0)) <?
                  @wordToN (b - 1) (@Fm_enc Ed25519.q (b - 1) x0))%N
            then x0
            else @opp Ed25519.q x0, rep2F x) in
       @weqb (S (b - 1)) (sig [:b])
         (enc'
            (@extendedToTwisted curve25519params
               (@unifiedAddM1' curve25519params
                  (@iter_op (@extended curve25519params) 
                     (@unifiedAddM1' curve25519params) 
                     (@twistedToExtended curve25519params (0%F, 1%F)) a
                     (@twistedToExtended curve25519params Bc))
                  (negateExtendedc
                     (@iter_op (@extended curve25519params) 
                        (@unifiedAddM1' curve25519params) 
                        (@twistedToExtended curve25519params (0%F, 1%F))
                        (@wordToN (b + b) (@H (b + (b + l)) (sig [:b] ++ pk ++ msg)))
                        (twistedToExtended p))))))
        else false) false
       (wire2rep_F (@wtl (b - 1) pk))
                )
    in match goal with [ |- _ = ?RHS] => replace RHS with RHS' end.
    reflexivity.
    {
      unfold option_rect.
      repeat progress match goal with [ |- context [match ?x with _ => _ end] ] => destruct x; trivial end.
    }
  } Unfocus.
  
  Axiom FRepMul : FRep -> FRep -> FRep.
  Axiom FRepMul_correct : forall x y, (rep2F x * rep2F y)%F = rep2F (FRepMul x y).
  
  Axiom FRepAdd : FRep -> FRep -> FRep.
  Axiom FRepAdd_correct : forall x y, (rep2F x + rep2F y)%F = rep2F (FRepAdd x y).
  
  Axiom FRepSub : FRep -> FRep -> FRep.
  Axiom FRepSub_correct : forall x y, (rep2F x - rep2F y)%F = rep2F (FRepSub x y).

  Lemma unfoldDiv : forall {m} (x y:F m), (x/y = x * inv y)%F. Proof. unfold div. congruence. Qed.

  etransitivity.
  Focus 2. {
    do 1 (eapply option_rect_Proper_nd; [|reflexivity..]). cbv beta delta [pointwise_relation]. intro.
    do 1 (eapply option_rect_Proper_nd; [|reflexivity..]). cbv beta delta [pointwise_relation]. intro.
    rewrite !F_pow_2_r.
    rewrite !unfoldDiv.
    rewrite (rep2F_F2rep Ed25519.d), (rep2F_F2rep Ed25519.a), (rep2F_F2rep 1%F).
    rewrite !FRepMul_correct.
    rewrite !FRepSub_correct.
    cbv zeta.
    rewrite F_pow_2_r.
    
  cbv beta delta [twistedToExtended].
  
  cbv beta iota delta
      [iter_op test_and_op unifiedAddM1' extendedToTwisted twistedToExtended enc' snd
       point_dec_coordinates PrimeFieldTheorems.sqrt_mod_q ].
Admitted.
