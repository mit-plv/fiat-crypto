Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Crypto.Specific.GF25519.
Require Export Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519Reflective.Reified.Add.
Require Import Crypto.Specific.GF25519Reflective.Reified.Sub.
Require Import Crypto.Specific.GF25519Reflective.Reified.Mul.
Require Import Crypto.Specific.GF25519Reflective.Common9_4Op.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Bedrock.Word.

Definition radd_coordinatesZ' var twice_d P1 P2
  := @Extended.add_coordinates_gen
       _
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig raddZ_sig var)))
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig rsubZ_sig var)))
       (fun x y => LetIn (Pair x y) (invert_Abs (proj1_sig rmulZ_sig var)))
       twice_d _
       (fun x y z w => (x, y, z, w)%expr)
       (fun v f => LetIn v
                         (fun k => f (SmartVarf k)))
       P1 P2.

Local Notation eta x := (fst x, snd x).

Definition radd_coordinatesZ'' : Syntax.Expr _ _ _
  := Linearize
       (ExprEta
          (fun var
           => Abs (fun twice_d_P1_P2 : interp_flat_type _ (_ * ((_ * _ * _ * _) * (_ * _ * _ * _)))
                   => let '(twice_d, ((P10, P11, P12, P13), (P20, P21, P22, P23)))
                          := twice_d_P1_P2 in
                      radd_coordinatesZ'
                        var (SmartVarf twice_d)
                        (SmartVarf P10, SmartVarf P11, SmartVarf P12, SmartVarf P13)
                        (SmartVarf P20, SmartVarf P21, SmartVarf P22, SmartVarf P23)))).

Definition add_coordinates
  := fun twice_d P10 P11 P12 P13 P20 P21 P22 P23
     => @Extended.add_coordinates
          _ add sub mul
          twice_d (P10, P11, P12, P13) (P20, P21, P22, P23).

Definition uncurried_add_coordinates
  := fun twice_d_P1_P2
     => let twice_d := fst twice_d_P1_P2 in
        let (P1, P2) := eta (snd twice_d_P1_P2) in
        @Extended.add_coordinates
          _ add sub mul
          twice_d P1 P2.

Local Notation rexpr_sigPf T uncurried_op rexprZ x :=
  (Interp interp_op (t:=T) rexprZ x = uncurried_op x)
    (only parsing).
Local Notation rexpr_sigP T uncurried_op rexprZ :=
  (forall x, rexpr_sigPf T uncurried_op rexprZ x)
    (only parsing).
Local Notation rexpr_sig T uncurried_op :=
  { rexprZ | rexpr_sigP T uncurried_op rexprZ }
    (only parsing).

Local Ltac fold_interpf' :=
  let k := (eval unfold interpf, interpf_step in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  change k with k'; clearbody k'; subst k'.

Local Ltac fold_interpf :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  change k with k'; clearbody k'; subst k';
  fold_interpf'.

Local Ltac repeat_step_interpf :=
  let k := (eval unfold interpf in (@interpf base_type interp_base_type op interp_op)) in
  let k' := fresh in
  let H := fresh in
  pose k as k';
  assert (H : @interpf base_type interp_base_type op interp_op = k') by reflexivity;
  repeat (unfold k'; change k with k'; unfold interpf_step);
  clearbody k'; subst k'.

Lemma radd_coordinatesZ_sigP' : rexpr_sigP _ uncurried_add_coordinates radd_coordinatesZ''.
Proof.
  cbv [radd_coordinatesZ''].
  intro x; rewrite InterpLinearize, InterpExprEta.
  cbv [domain interp_flat_type] in x.
  destruct x as [twice_d [ [ [ [P10_ P11_] P12_] P13_] [ [ [P20_ P21_] P22_] P23_] ] ].
  repeat match goal with
         | [ H : prod _ _ |- _ ] => let H0 := fresh H in let H1 := fresh H in destruct H as [H0 H1]
         end.
  cbv [invert_Abs domain codomain Interp interp SmartVarf smart_interp_flat_map fst snd].
  cbv [radd_coordinatesZ' add_coordinates Extended.add_coordinates_gen uncurried_add_coordinates SmartVarf smart_interp_flat_map]; simpl @fst; simpl @snd.
  repeat match goal with
         | [ |- appcontext[@proj1_sig ?A ?B ?v] ]
           => let k := fresh "f" in
              let k' := fresh "f" in
              let H := fresh in
              set (k := v);
                set (k' := @proj1_sig A B k);
                pose proof (proj2_sig k) as H;
                change (proj1_sig k) with k' in H;
                clearbody k'; clear k;
                  cbv beta in *
         end.
  cbv [Interp Curry.curry2] in *.
  unfold interpf, interpf_step; fold_interpf.
  cbv beta iota delta [Extended.add_coordinates interp_flat_type interp_base_type GF25519.fe25519].
  Time
    abstract (
      repeat match goal with
             | [ |- (dlet x := ?y in @?z x) = (let x' := ?y' in @?z' x') ]
               => refine ((fun pf0 pf1 => @Proper_Let_In_nd_changebody _ _ Logic.eq _ y y' pf0 z z' pf1)
                            (_ : y = y')
                            (_ : forall x, z x = z' x));
                    cbv beta; intros;
                      [ cbv [Let_In] | ]
             end;
        repeat match goal with
               | _ => rewrite !interpf_invert_Abs
               | _ => rewrite_hyp !*
               | [ |- ?x = ?x ] => reflexivity
               | _ => rewrite <- !surjective_pairing
               end
    ).
Time Defined.
Lemma radd_coordinatesZ_sigP : rexpr_sigP _ uncurried_add_coordinates radd_coordinatesZ''.
Proof.
  exact radd_coordinatesZ_sigP'.
Qed.
Definition radd_coordinatesZ_sig
  := exist (fun v => rexpr_sigP _ _ v) radd_coordinatesZ'' radd_coordinatesZ_sigP.

Definition radd_coordinates_input_bounds
  := (ExprUnOp_bounds, ((ExprUnOp_bounds, ExprUnOp_bounds, ExprUnOp_bounds, ExprUnOp_bounds),
                        (ExprUnOp_bounds, ExprUnOp_bounds, ExprUnOp_bounds, ExprUnOp_bounds))).

Time Definition radd_coordinatesW := Eval vm_compute in rword_of_Z radd_coordinatesZ_sig.
Lemma radd_coordinatesW_correct_and_bounded_gen : correct_and_bounded_genT radd_coordinatesW radd_coordinatesZ_sig.
Proof. Time rexpr_correct. Time Qed.
Definition radd_coordinates_output_bounds := Eval vm_compute in compute_bounds radd_coordinatesW radd_coordinates_input_bounds.

Local Obligation Tactic := intros; vm_compute; constructor.

(*
Program Definition radd_coordinatesW_correct_and_bounded
  := Expr9_4Op_correct_and_bounded
       radd_coordinatesW uncurried_add_coordinates radd_coordinatesZ_sig radd_coordinatesW_correct_and_bounded_gen
       _ _.
 *)

Local Open Scope string_scope.
Compute ("Add_Coordinates", compute_bounds_for_display radd_coordinatesW radd_coordinates_input_bounds).
Compute ("Add_Coordinates overflows? ", sanity_compute radd_coordinatesW radd_coordinates_input_bounds).
Compute ("Add_Coordinates overflows (error if it does)? ", sanity_check radd_coordinatesW radd_coordinates_input_bounds).
