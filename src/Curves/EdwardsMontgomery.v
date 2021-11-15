Require Import Coq.PArith.BinPosDef.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Spec.CompleteEdwardsCurve  Crypto.Curves.Edwards.AffineProofs.
Require Import Coq.setoid_ring.Field_theory.
Require Import Field_tac.
Require Import UniquePose.

Module M.
  Section EdwardsMontgomery.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Program Definition opp (P:@M.point F Feq Fadd Fmul a b) : @M.point F Feq Fadd Fmul a b :=
      match P return F*F+∞ with
      | inl (x, y) => inl (x, -y)
      | ∞ => ∞
      end.
    Next Obligation. Proof. destruct_head @M.point; cbv; break_match; trivial; fsatz. Qed.

    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Local Notation "2" := (1+1).
    Local Notation "3" := (1+2).

    Context {ae de: F} {Hae: ae=(a+2)/b} {Hde: de=(a-2)/b}
            {nonzero_ae : ae <> 0}
            {square_ae : exists sqrt_ae, sqrt_ae^2 = ae}
            {nonsquare_de : forall x, x^2 <> de}.

    Add Field _field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).

    Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul ae de).
    Local Notation Eadd := (@E.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 ae de).
    Program Definition to_Edwards (P:@point) : Epoint :=
      match M.coordinates P return F*F with
      | inl (u, v) => if dec (u + 1 <> 0 /\ v <> 0) 
                      then (u/v , (u-1)/(u+1)) 
                      else (0, 0 - 1)
      | ∞ => (0, 1)
      end.
    Next Obligation.
    (* Note: perhaps we can deal with u = -1 or v = 0 case in a better way*)
    Proof. destruct_head' @point; cbv; break_match; trivial; try fsatz.
    destruct H.
    assert (f + 1 <> 0) by auto.
    assert (f0 <> 0) by auto.
    fsatz.
    Qed.

    Program Definition of_Edwards (P:Epoint) : point :=
      match E.coordinates P return F*F+∞ with
      | (x, y) => if dec (x = 0 /\ y = 0 - 1) 
                  then inl (0, 0) 
                  else if dec (x = 0 /\ y = 1)
                       then inr tt
                       else inl ((1+y)/(1-y), (1+y)/(x*(1-y)))
      end.
    Next Obligation.
    Proof. destruct_head' @Epoint; cbv; break_match; trivial; try fsatz. 
    assert (f <> 0). {
      unfold not. intros Hf. rewrite -> Hf in y.
      destruct (dec (f0 = 1)).
      - auto.
      - assert (f0 = 0 - 1). fsatz. auto.
    }
    assert (f0 <> 1) by fsatz.
    fsatz.
    Qed.

    Lemma no_roots: forall x : F, x^2 + a * x + 1 <> 0.
    Proof. 
      unfold not. intros x H.
      destruct square_ae.
      destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
      field_simplify_eq; try split; fsatz.
    Qed.
    
    Lemma My_zero_then_Mx_zero: forall x y : F, y = 0 -> b * y ^ 2 = x ^ 3 + a * x ^ 2 + x -> x = 0.
    Proof. intros. pose proof (no_roots x). fsatz. Qed.

    Lemma Mx_not_neg1: forall x y : F, b * y ^ 2 = x ^ 3 + a * x ^ 2 + x -> x + 1 <> 0.
    Proof.
      intros. unfold not. intros.
      destruct nonsquare_de with (x:=y). fsatz.
    Qed.

    Lemma not_and_True_l: forall A B: Prop, Decidable A -> Decidable B -> A -> ~ (A /\ ~ B) <-> B.
    Proof. intros. destruct (dec A), (dec B); intuition. Qed.

    Lemma not_and_decidable: forall P Q: Prop, Decidable P -> Decidable Q -> ~ (P /\ Q) <-> ~ P \/ ~ Q.
    Proof. intros. destruct (dec Q), (dec P); intuition trivial. Qed.

    Ltac t :=
      repeat
        match goal with
        | _ => solve [ trivial ]
        | _ => progress intros
        | _ => progress subst
        | _ => progress Tactics.DestructHead.destruct_head' @M.point
        | _ => progress Tactics.DestructHead.destruct_head' @prod
        | _ => progress Tactics.DestructHead.destruct_head' @sum
        | _ => progress Tactics.DestructHead.destruct_head' @and
        | _ => progress Sum.inversion_sum
        | _ => progress Prod.inversion_prod
        | _ => progress Tactics.BreakMatch.break_match_hyps
        | _ => progress Tactics.BreakMatch.break_match
        | _ => progress cbv [M.coordinates M.add M.zero M.eq M.opp proj1_sig
                             E.coordinates E.add E.zero E.eq E.opp
           of_Edwards to_Edwards fst snd] in *
        | |- _ <-> _ => split
        end.

    Ltac t2 :=
      repeat match goal with
          | H: ~ ( _ = _ /\ _ = _) |- _ => apply not_and_decidable in H; [ | exact _ ..]
          | _ => progress auto 
          | H: ?x = 0 |- _ => progress (rewrite H in * )
          | _ => progress fsatz
          | H: _ \/ _ |- _ => destruct H
          end. 

    Ltac t3 :=
      repeat match goal with
          | H: False |- _ => destruct H
          | _ => progress fsatz
          | H: ?x = ?y |- _ => rewrite H in *
          | _ => try intuition
          end.

    Ltac t4 :=
      repeat match goal with
          | H: ?x = ?y |- _ => rewrite H in * |-
          | H: ~ ( _ /\ _ ) |- _ => destruct H; split
          | _ => fsatz
          end.

    Ltac t5 :=
      repeat match goal with
          | H: b * ?x ^ 2 = _ |-  _ => 
              match goal with
              | G: ?x = 0 |- _ => unique pose proof (My_zero_then_Mx_zero _ _ G H)
              | _ => unique pose proof (Mx_not_neg1 _ _ H)
              end
          | H: context [?a /\ _] |- _ => 
              match goal with G: a |- _ => 
                  rewrite not_and_True_l in H; [ | exact _ | exact _ | trivial ]
              end
          | H: ?x = 0 |- _ => rewrite H in *
          | H: 0 <> - 0 |- _ => destruct H; field
          | _ => try auto
          end.
    
    Ltac field_simpl_fsatz := field_simplify_eq; [fsatz | repeat split; try auto].

    Ltac t_destruct H := unfold not; intros; destruct H; field_simpl_fsatz.

    Ltac sqrt_de_witness y := unfold not; intros; destruct nonsquare_de with (x:= y); fsatz.

    Definition Feq_refl:= RelationClasses.reflexivity (R:= Feq).
    Hint Immediate Feq_refl: core.

    Global Instance EdwardsMontgomeryIsomorphism {_1 _2 _3 _4}
           {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12}
      :
      @Group.isomorphic_commutative_groups
        (@E.point F Feq Fone Fadd Fmul ae de)
        E.eq
        (@E.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field _1 _2 ae de nonzero_ae square_ae nonsquare_de)
        (E.zero(nonzero_a:=nonzero_ae))
        (@E.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field _2 ae de nonzero_ae)

        (@M.point F Feq Fadd Fmul a b)
        M.eq
        (M.add(char_ge_3:=_1)(b_nonzero:=_3))
        M.zero
        (M.opp(b_nonzero:=_4))

        (of_Edwards)
        (to_Edwards).
    Proof.
      eapply Group.commutative_group_by_isomorphism.
      { eapply (E.edwards_curve_commutative_group(a:=ae)(d:=de)(nonzero_a:=nonzero_ae)(square_a:=square_ae)(nonsquare_d:=nonsquare_de)). }   
      { (* Bijection, not automated due to non-local case analysis *)
        t; split.
        all: try solve [t2].
        all: assert (f <> 0) by t2; assert (f0 <> 1) by fsatz; destruct H1; split; fsatz.
      }
      { (* Equality *)
        t.
        7: t5.
        all: try split; t3.
      }
      { (* Addition: numerous calls to clear below are needed to make fsatz run in reasonable time *)
        t.

        4, 21-25: split; fsatz.
        7, 13-15, 19: split; t5; fsatz.
        10, 13-14: t5; destruct H0; split; fsatz.
        8-9: clear H1; t4.
        2-3, 5-6: t4.

        {
          split.
          - fsatz.
          - field_simpl_fsatz.
            destruct square_ae; assert (x <> 0) by fsatz.
            sqrt_de_witness (f0 ^ 2 / (f ^ 2 * x)).
        }
        {
          split.
          - field_simpl_fsatz; fsatz.
          - fsatz.
        }
        {
          rewrite H in * |-.
          assert (f2 = f0) by fsatz.
          assert (f <> 0) by fsatz.
          destruct (dec (f = 1)).
          - split; fsatz.
          - destruct H1. split.
            + sqrt_de_witness (f0 * (f + 1) / (f ^ 2 - f)).
            + destruct square_ae; assert (x <> 0) by fsatz.
              sqrt_de_witness (f0 ^ 2 / (f ^ 2 * x)).
        }
        {
          assert (Epoint1: ae * (f1 / f2) ^ 2 + ((f1 - 1) / (f1 + 1)) ^ 2 = 1 + de * (f1 / f2) ^ 2 * ((f1 - 1) / (f1 + 1)) ^ 2). {
            clear y H H2 H3 H0 H5 f f0.
            fsatz.
          }
          assert (Epoint: ae * (f / f0) ^ 2 + ((f - 1) / (f + 1)) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2). {
            clear y0 H H1 H4 H0 H5 f1 f2 Epoint1.
            fsatz.
          }
          pose proof (Pre.denominator_nonzero_x _ nonzero_ae square_ae _ nonsquare_de _ _ Epoint1 _ _ Epoint) as denom_nonzero_x.
          pose proof (Pre.denominator_nonzero_y _ nonzero_ae square_ae _ nonsquare_de _ _ Epoint1 _ _ Epoint) as denom_nonzero_y.
          assert (f - f1 <> 0) by fsatz.
          split; rewrite Hae, Hde in *; 
          clear Epoint Epoint1 square_ae nonzero_ae nonsquare_de Hae Hde ae de;
          field_simpl_fsatz.
          - t_destruct denom_nonzero_x.
          - t_destruct H5.
          - t_destruct denom_nonzero_y.
          - t_destruct H0.
        }
        { 
          remember (b * ((f0 - f2) / (f - f1)) ^ 2 - a - f1 - f) as u.
          remember ((2 * f1 + f + a) * ((f0 - f2) / (f - f1)) - b * ((f0 - f2) / (f - f1)) ^ 3 - f2) as v.
          assert (uv_Mpoint: b * v ^ 2 = u ^ 3 + a * u ^ 2 + u). {
            rewrite Hequ, Heqv.
            clear H0 H1 H2 H3 H4 Hequ Heqv.
            fsatz.
          }
          t5.
          rewrite Hequ in H6.
          rewrite Heqv in H0.
          clear u v Hequ Heqv H5 H7 uv_Mpoint.
          assert (Epoint1: ae * (f1 / f2) ^ 2 + ((f1 - 1) / (f1 + 1)) ^ 2 = 1 + de * (f1 / f2) ^ 2 * ((f1 - 1) / (f1 + 1)) ^ 2). {
            clear y H H2 H3 H0 H6 f f0.
            fsatz.
          }
          assert (Epoint: ae * (f / f0) ^ 2 + ((f - 1) / (f + 1)) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2). {
            clear y0 H H1 H4 H0 H6 f1 f2 Epoint1.
            fsatz.
          }
          pose proof (Pre.denominator_nonzero_x _ nonzero_ae square_ae _ nonsquare_de _ _ Epoint1 _ _ Epoint) as denom_nonzero_x.
          pose proof (Pre.denominator_nonzero_y _ nonzero_ae square_ae _ nonsquare_de _ _ Epoint1 _ _ Epoint) as denom_nonzero_y.
          split; rewrite Hae, Hde in *;
          clear Epoint Epoint1 square_ae nonzero_ae nonsquare_de Hae Hde ae de;
          field_simpl_fsatz.
          - t_destruct denom_nonzero_x.
          - t_destruct denom_nonzero_y.
        }
      }
      { (* Inverses *)
        t.
        2-3: t4.
        all: split; fsatz.
      }
      (* Zero *)
      t; auto.
    Qed.

  End EdwardsMontgomery.
End M.

