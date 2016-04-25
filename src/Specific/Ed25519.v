Require Import Bedrock.Word.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import ModularArithmetic.ModularArithmeticTheorems.
Require Import ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.Encoding Crypto.Spec.PointEncoding.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.Util.IterAssocOp.

Local Infix "++" := Word.combine.
Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).
Local Arguments H {_} _.
Local Arguments scalarMultM1 {_} {_} _ _ _.
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

Axiom xB : F q.
Axiom yB : F q.
Axiom B_proj : proj1_sig B = (xB, yB).

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

Axiom square_opp : forall (x:F q), (opp x ^ 2 = x ^ 2)%F.

Program Definition negate (P:point) : point := let '(x, y) := proj1_sig P in (opp x, y).
Next Obligation.
Proof.
  pose (proj2_sig P) as H; rewrite <-Heq_anonymous in H; simpl in H.
  rewrite square_opp; trivial.
Qed.

Definition point_sub P Q := (P + negate Q)%E.
Infix "-" := point_sub : E_scope.

Lemma opp0 m : opp (0 : F m) = 0%F.
Proof.
  Fdefn; rewrite Zdiv.Zminus_mod, !Zdiv.Z_mod_same_full, !Zdiv.Zmod_0_l; eauto. (* TODO: ring? *)
Qed.

Lemma negate_zero : negate zero = zero.
Proof.
  pose proof opp0.
  unfold negate, zero; eapply point_eq'; congruence.
Qed.

Lemma negate_add : forall P Q, negate (P + Q)%E = (negate P + negate Q)%E. Admitted.
  
Lemma negate_scalarMult : forall n P, negate (scalarMult n P) = scalarMult n (negate P).
Proof.
  pose proof negate_add; pose proof negate_zero.
  induction n; simpl; intros; congruence.
Qed.

Axiom solve_for_R : forall A B C, (A ==? B + C)%E = (B ==? A - C)%E.

Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended X Y Z T).
Local Notation "2" := (ZToField 2) : F_scope.

Lemma mul_opp_1 : forall x y : F q, (opp x * y = opp (x * y))%F.
  (* field *)
Admitted.

Lemma div_opp_1 : forall x y : F q, (opp x / y = opp (x / y))%F.
  (* field *)
Admitted.

Definition negateExtended' P := let '(X, Y, Z, T) := P in (opp X, Y, Z, opp T).
Program Definition negateExtended (P:extendedPoint) : extendedPoint := negateExtended' (proj1_sig P).
Next Obligation.
Proof.
  unfold negateExtended', rep; destruct P as [[X Y Z T] H]; simpl. destruct H as [[[] []] ?]; subst.
  repeat rewrite ?div_opp_1, ?mul_opp_1, ?square_opp; repeat split; trivial.
Qed.

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

    Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
    Global Instance Let_In_Proper_nd {A P}
      : Proper (eq ==> pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => P)).
    Proof.
      lazy; intros; congruence.
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
    Local Ltac replace_let_in_with_Let_In :=
      repeat match goal with
             | [ |- context G[let x := ?y in @?z x] ]
               => let G' := context G[Let_In y z] in change G'
             | [ |- _ = Let_In _ _ ]
               => apply Let_In_Proper_nd; [ reflexivity | cbv beta delta [pointwise_relation]; intro ]
             end.
    Local Ltac simpl_option_rect := (* deal with [option_rect _ _ _ None] and [option_rect _ _ _ (Some _)] *)
      repeat match goal with
             | [ |- context[option_rect ?P ?S ?N None] ]
               => change (option_rect P S N None) with N
             | [ |- context[option_rect ?P ?S ?N (Some ?x) ] ]
               => change (option_rect P S N (Some x)) with (S x); cbv beta
             end.

Axiom SRep : Type.
Axiom S2rep : N -> SRep.
Axiom rep2S : SRep -> N.
Axiom rep2S_S2rep : forall x, x = rep2S (S2rep x).

Axiom FRep : Type.
Axiom F2rep : F Ed25519.q -> FRep.
Axiom rep2F : FRep -> F Ed25519.q.
Axiom rep2F_F2rep : forall x, x = rep2F (F2rep x).
Axiom wire2rep_F : word (b-1) -> option FRep.
Axiom wire2rep_F_correct : forall x, Fm_dec x = option_map rep2F (wire2rep_F x).

Axiom FRepMul : FRep -> FRep -> FRep.
Axiom FRepMul_correct : forall x y, (rep2F x * rep2F y)%F = rep2F (FRepMul x y).

Axiom FRepAdd : FRep -> FRep -> FRep.
Axiom FRepAdd_correct : forall x y, (rep2F x + rep2F y)%F = rep2F (FRepAdd x y).

Axiom FRepSub : FRep -> FRep -> FRep.
Axiom FRepSub_correct : forall x y, (rep2F x - rep2F y)%F = rep2F (FRepSub x y).

Axiom FRepInv : FRep -> FRep.
Axiom FRepInv_correct : forall x, inv (rep2F x)%F = rep2F (FRepInv x).

Axiom FSRepPow : FRep -> SRep -> FRep.
Axiom FSRepPow_correct : forall x n, (rep2F x ^ rep2S n)%F = rep2F (FSRepPow x n).

Axiom FRepOpp : FRep -> FRep.
Axiom FRepOpp_correct : forall x, opp (rep2F x) = rep2F (FRepOpp x).
Axiom wltu : forall {b}, word b -> word b -> bool.

Axiom wltu_correct : forall {b} (x y:word b), wltu x y = (wordToN x <? wordToN y)%N.
Axiom compare_enc : forall x y, F_eqb x y = weqb (@enc _ _ FqEncoding x) (@enc _ _ FqEncoding y).
Axiom enc_rep2F : FRep -> word (b-1).
Axiom enc_rep2F_correct : forall x, enc_rep2F x = @enc _ _ FqEncoding (rep2F x).

Lemma unfoldDiv : forall {m} (x y:F m), (x/y = x * inv y)%F. Proof. unfold div. congruence. Qed.

Definition rep2E (r:FRep * FRep * FRep * FRep) : extended :=
  match r with (((x, y), z), t) => mkExtended (rep2F x) (rep2F y) (rep2F z) (rep2F t) end.

Lemma unifiedAddM1Rep_sig : forall a b : FRep * FRep * FRep * FRep, { unifiedAddM1Rep | rep2E unifiedAddM1Rep = unifiedAddM1' (rep2E a) (rep2E b) }.
Proof.
  unfold rep2E. cbv beta delta [unifiedAddM1'].
  eexists; instantiate (1 := (((_,_), _), _)).
Admitted.
Definition unifiedAddM1Rep (a b:FRep * FRep * FRep * FRep) : FRep * FRep * FRep * FRep := Eval hnf in proj1_sig (unifiedAddM1Rep_sig a b).
Definition unifiedAddM1Rep_correct a b : rep2E (unifiedAddM1Rep a b) = unifiedAddM1' (rep2E a) (rep2E b)  := Eval hnf in proj2_sig (unifiedAddM1Rep_sig a b).

Lemma if_map : forall {T U} (f:T->U) (b:bool) (x y:T), (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; trivial.
Qed.

Local Ltac Let_In_rep2F :=
  match goal with
  | [ |- appcontext G[Let_In (rep2F ?x) ?f] ]
    => change (Let_In (rep2F x) f) with (Let_In x (fun y => f (rep2F y))); cbv beta
  end.

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
    rewrite solve_for_R; unfold point_sub.
    rewrite negate_scalarMult.
    let p1 := constr:(scalarMultM1_rep eq_refl) in
    let p2 := constr:(unifiedAddM1_rep eq_refl) in
    repeat match goal with
           | |- context [(_ * negate ?P)%E] =>
              rewrite <-(unExtendedPoint_mkExtendedPoint P);
              rewrite negateExtended_correct;
              rewrite <-p1
           | |- context [(_ * ?P)%E] =>
              rewrite <-(unExtendedPoint_mkExtendedPoint P);
              rewrite <-p1
           | _ => rewrite p2
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

  rewrite enc'_correct.
  cbv [unExtendedPoint unifiedAddM1 negateExtended scalarMultM1].
  (* Why does this take too long?
  lazymatch goal with |- context [ proj1_sig ?x ] =>
                  fail 5
  end. *)
  unfold proj1_sig at 1 2.
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

  cbv [mkExtendedPoint zero mkPoint].
  unfold proj1_sig at 1 2 3 5 6 7 8.
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

  cbv iota beta delta [point_dec_coordinates sign_bit dec FqEncoding modular_word_encoding CompleteEdwardsCurveTheorems.solve_for_x2 sqrt_mod_q].

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
  rewrite wire2rep_F_correct.

  etransitivity.
  Focus 2. {
    eapply option_rect_Proper_nd; [|reflexivity..]. cbv beta delta [pointwise_relation]. intro.
    rewrite <-!(option_rect_option_map rep2F).
    eapply option_rect_Proper_nd; [|reflexivity..]. cbv beta delta [pointwise_relation]. intro.
    rewrite !F_pow_2_r.
    rewrite (rep2F_F2rep 1%F).
    pattern Ed25519.d at 1. rewrite (rep2F_F2rep Ed25519.d) at 1.
    pattern Ed25519.a at 1. rewrite (rep2F_F2rep Ed25519.a) at 1.
    rewrite !FRepMul_correct.
    rewrite !FRepSub_correct.
    rewrite !unfoldDiv.
    rewrite !FRepInv_correct.
    rewrite !FRepMul_correct.
    Let_In_rep2F.
    rewrite (rep2S_S2rep (Z.to_N (Ed25519.q / 8 + 1))).
    eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro].
    etransitivity. Focus 2. eapply Let_In_Proper_nd; [|cbv beta delta [pointwise_relation]; intro;reflexivity]. {
      rewrite FSRepPow_correct.
      Let_In_rep2F.
      etransitivity. Focus 2. eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro]. {
        set_evars.
        rewrite !F_pow_2_r.
        rewrite !FRepMul_correct.
        rewrite if_F_eq_dec_if_F_eqb.
        rewrite compare_enc.
        rewrite <-!enc_rep2F_correct.
        rewrite (rep2F_F2rep sqrt_minus1).
        rewrite !FRepMul_correct.
        rewrite (if_map rep2F).
        subst_evars.
        reflexivity. } Unfocus.
      match goal with |- ?e = Let_In ?xval (fun x => rep2F (@?f x)) => change (e = rep2F (Let_In xval f)) end.
      reflexivity. } Unfocus.
    Let_In_rep2F.
    eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro].
    set_evars.
    rewrite !F_pow_2_r.
    rewrite !FRepMul_correct.
    rewrite if_F_eq_dec_if_F_eqb.
    rewrite compare_enc.
    rewrite <-!enc_rep2F_correct.
    subst_evars.
    lazymatch goal with  |- _ = if ?b then ?t else ?f => apply (f_equal2 (fun x y => if b then x else y)) end; [|reflexivity].

    set_evars.
    rewrite !FRepOpp_correct.
    rewrite <-!enc_rep2F_correct.
    rewrite <-wltu_correct.
    rewrite (if_map rep2F).
    lazymatch goal with
      |- ?e = Let_In (rep2F ?x, rep2F ?y) (fun p => @?r p) =>
        change (e = Let_In (x, y) (fun p => r (rep2F (fst p), rep2F (snd p)))); cbv beta zeta
    end.
    subst_evars.
    eapply Let_In_Proper_nd; [reflexivity|cbv beta delta [pointwise_relation]; intro].

    set_evars; erewrite (f_equal2 (@weqb b)); subst_evars; [|reflexivity|symmetry]. Focus 2. {
      unfold twistedToExtended.
      rewrite F_mul_0_l.
      unfold curve25519params, q. (* TODO: do we really wanna do it here? *)
      rewrite (rep2F_F2rep 0%F).
      rewrite (rep2F_F2rep 1%F).
      rewrite (rep2F_F2rep xB%F).
      rewrite (rep2F_F2rep yB%F).
      rewrite !FRepMul_correct.
      repeat match goal with |- appcontext [ ?E ] =>
                      match E with (rep2F ?x, rep2F ?y, rep2F ?z, rep2F ?t) =>
                                   change E with (rep2E (((x, y), z), t))
                      end
      end.
      lazymatch goal with |- context [negateExtended' (rep2E ?E)] =>
                          replace (negateExtended' (rep2E E)) with (rep2E (((((FRepOpp (fst (fst (fst E)))), (snd (fst (fst E)))), (snd (fst E))), (FRepOpp (snd E))))) by (simpl; rewrite !FRepOpp_correct; reflexivity)
      end; simpl fst; simpl snd. (* we actually only want to simpl in the with clause *)
      do 2 erewrite <- (fun x y z => iter_op_proj rep2E unifiedAddM1Rep unifiedAddM1' x y z N.testbit_nat) by apply unifiedAddM1Rep_correct.
      rewrite <-unifiedAddM1Rep_correct.
      
      
      etransitivity. Focus 2. {
        apply f_equal.
        Definition rep2T (P:FRep * FRep) := (rep2F (fst P), rep2F (snd P)).
        Definition erep2trep (P:FRep * FRep * FRep * FRep) := Let_In P (fun P => Let_In (FRepInv (snd (fst P))) (fun iZ => (FRepMul (fst (fst (fst P))) iZ, FRepMul (snd (fst (fst P))) iZ))).
        Lemma erep2trep_correct : forall P, rep2T (erep2trep P) = extendedToTwisted (rep2E P).
        Proof.
          unfold rep2T, rep2E, erep2trep, extendedToTwisted; destruct P as [[[]]]; simpl.
          rewrite !unfoldDiv, <-!FRepMul_correct, <-FRepInv_correct. reflexivity.
        Qed.
        rewrite <-erep2trep_correct; cbv beta delta [erep2trep].
        reflexivity. } Unfocus.
        
    reflexivity. } Unfocus.
    (*
    cbv beta iota delta
      [iter_op test_and_op unifiedAddM1' extendedToTwisted twistedToExtended enc' snd
       point_dec_coordinates PrimeFieldTheorems.sqrt_mod_q].
    *)
  reflexivity.
Admitted.
