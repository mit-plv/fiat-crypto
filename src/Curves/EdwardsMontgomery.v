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
    (* Local Notation "( x , y )" := (inl (pair x y)). *)
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
    Local Notation "4" := (1+1+1+1).
    (* Local Notation "9" := (3*3).
    Local Notation "27" := (4*4 + 4+4 +1+1+1).

    Context {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}. *)

    Context {ae de: F} {Hae: ae=(a+2)/b} {Hde: de=(a-2)/b}
            {nonzero_ae : ae <> 0}
            {square_ae : exists sqrt_ae, sqrt_ae^2 = ae}
            {nonsquare_de : forall x, x^2 <> de}.


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
        | |- _ /\ _ => split | |- _ <-> _ => split
        end.

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
      Time all:t.
      Add Field _field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
      fsatz. 
      fsatz. 
      fsatz. 
      fsatz. 
      fsatz. 
      fsatz.
      { 
        assert (f <> 0). {
          unfold not. intros Hf. rewrite -> Hf in y.
          destruct (dec (f0 = 1)).
          - auto.
          - assert (f0 = 0 - 1). fsatz. auto.
        } fsatz.
      }
      {
        assert (f <> 0). {
          unfold not. intros Hf. rewrite -> Hf in y.
          destruct (dec (f0 = 1)).
          - auto.
          - assert (f0 = 0 - 1) by fsatz. auto.
        } fsatz.
      }
      {
        assert (f <> 0). {
          unfold not. intros Hf. rewrite -> Hf in y.
          destruct (dec (f0 = 1)).
          - auto.
          - assert (f0 = 0 - 1) by fsatz. auto.
        }
        assert (f0 <> 1) by fsatz.
        destruct H1.
        split; fsatz.
      }
      {
        assert (f <> 0). {
          unfold not. intros Hf. rewrite -> Hf in y.
          destruct (dec (f0 = 1)).
          - auto.
          - assert (f0 = 0 - 1) by fsatz. auto.
        }
        assert (f0 <> 1) by fsatz.
        destruct H1.
        split; fsatz.
      }
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      {
        destruct (dec (f + 1 = 0 \/ f0 = 0)).
        - destruct o.
          + destruct H. rewrite H2. auto.
          + fsatz.
        - destruct H0. intuition.
      }
      {
        destruct (dec (f + 1 = 0 \/ f0 = 0)).
        - destruct o.
          + destruct H. rewrite H2. auto.
          + fsatz.
        - destruct H0. intuition.
      }
      fsatz.
      fsatz.
      {
        rewrite -> H2 in H.
        rewrite -> H3 in H.
        destruct H.
        auto.
      }
      {
        rewrite -> H2 in H.
        rewrite -> H3 in H.
        destruct H.
        auto.
      }
      {   
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f + 1 = 0 \/ f0 = 0)).
          - destruct o.
            + destruct H3. auto.
            + auto.
          - destruct H0. intuition.
        }
        assert (f2 = 0). {
          destruct (dec (f1 + 1 = 0 \/ f2 = 0)).
          - destruct o.
            + destruct H4. auto.
            + auto.
          - destruct H. intuition.
        }
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        fsatz.
      }
      {
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f + 1 = 0 \/ f0 = 0)).
          - destruct o.
            + destruct H3. auto.
            + auto.
          - destruct H0. intuition.
        }
        assert (f2 = 0). {
          destruct (dec (f1 + 1 = 0 \/ f2 = 0)).
          - destruct o.
            + destruct H4. auto.
            + auto.
          - destruct H. intuition.
        }
        fsatz.
      }
      fsatz.
      fsatz.
      fsatz.
      destruct H1.
      destruct H1.
      fsatz.
      fsatz.
      destruct H0.
      fsatz.
      destruct H1.
      destruct H1.
      fsatz.
      fsatz.
      destruct H0.
      fsatz.
      fsatz.
      fsatz.
      {
        rewrite -> H.
        rewrite -> H0.
        assert (f <> 0) by fsatz.
        assert (pt_on_e: ((f - 1) / (f + 1)) ^ 2 + ae * (f / f0) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2) by fsatz.
        assert (nonzero_denom: (1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2) <> 0). {
          unfold not. intros contra_de.
          assert (contra_ae: ((f - 1) / (f + 1)) ^ 2 + ae * (f / f0) ^ 2 = 0) by fsatz.
          assert (f <> 1) by fsatz. 
          destruct square_ae.
          assert (x <> 0) by fsatz.
          destruct nonsquare_de with (x:= f0 ^ 2 / (f ^ 2 * x)).
          fsatz.
        }
        fsatz.
      }
      {
        rewrite -> H in H1.
        assert (f0 <> 0) by fsatz.
        destruct H2. auto.
      }
      {
        rewrite -> H in H1.
        assert (f0 <> 0) by fsatz.
        destruct H2. auto.
      }
      {
        rewrite <- H in H2.
        assert (f2 <> 0) by fsatz.
        destruct H1. auto.
      }
      {
        rewrite <- H in H2.
        assert (f2 <> 0) by fsatz.
        destruct H1. auto.
      }
      fsatz.
      fsatz.
      field_simplify_eq; repeat split; auto; fsatz.
      fsatz.
      {
        rewrite <- H in H3.
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H3. auto.
        }
        fsatz.
      }
      {
        rewrite <- H in H3.
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H3. auto.
        }
        fsatz.
      }
      {
        rewrite -> H in H2.
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H2. auto.
        }
        fsatz.
      }
      {
        rewrite -> H in H2.
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H2. auto.
        }
        fsatz.
      }
      {
        assert (f0 <> 0) by fsatz.
        assert (f + 1 = 0). {
          destruct (dec (f + 1 = 0)).
          - auto.
          - destruct H3. auto.
        }
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        destruct H7. auto.
      }
      {
        assert (f0 <> 0) by fsatz.
        assert (f + 1 = 0). {
          destruct (dec (f + 1 = 0)).
          - auto.
          - destruct H3. auto.
        }
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        destruct H7. auto.
      }
      {
        assert (f2 = f0) by fsatz.
        rewrite -> H.
        rewrite -> H6.
        rewrite -> H in H1.
        rewrite -> H6 in H1.
        assert (f <> 0) by fsatz.
        destruct (dec (f = 1)).
        - fsatz.
        - destruct H1. split.
          + unfold not. intros contra.
            destruct nonsquare_de with (x:= f0 * (f + 1) / (f ^ 2 - f)).
            fsatz.  
          + unfold not. intros contra.
            destruct square_ae.
            assert (x <> 0) by fsatz.
            destruct nonsquare_de with (x:= f0 ^ 2 / (f ^ 2 * x)).
            fsatz.
      } 
      {
        assert (f2 = f0) by fsatz.
        rewrite -> H.
        rewrite -> H6.
        rewrite -> H in H1.
        rewrite -> H6 in H1.
        assert (f <> 0) by fsatz.
        destruct (dec (f = 1)).
        - fsatz.
        - destruct H1. split.
          + unfold not. intros contra.
            destruct nonsquare_de with (x:= f0 * (f + 1) / (f ^ 2 - f)).
            fsatz.  
          + unfold not. intros contra.
            destruct square_ae.
            assert (x <> 0) by fsatz.
            destruct nonsquare_de with (x:= f0 ^ 2 / (f ^ 2 * x)).
            fsatz.
      }
      {
        rewrite <- H in H3.
        assert (f0 <> 0) by fsatz.
        destruct H3. auto.
      }
      {
        rewrite <- H in H3.
        assert (f0 <> 0) by fsatz.
        destruct H3. auto.
      }
      {
        rewrite -> H in H2.
        assert (f2 <> 0) by fsatz.
        destruct H2. auto.
      }
      {
        rewrite -> H in H2.
        assert (f2 <> 0) by fsatz.
        destruct H2. auto.
      }
      fsatz.
      {
        rewrite -> H in H2.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H3. auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H2. auto.
        }
        fsatz.
      }
      all: revgoals. (* deal with easier goals first *)
      reflexivity.
      reflexivity.
      reflexivity.
      fsatz.
      fsatz.
      fsatz.
      destruct H; split; fsatz.
      destruct H; split; fsatz.
      destruct H0; split; fsatz.
      destruct H0; split; fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      } 
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        destruct H0; split; fsatz. 
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        destruct H0; split; fsatz. 
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        destruct H0; split; fsatz. 
      } 
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        destruct H0; split; fsatz. 
      }
      all: cycle 2. (* Put the hardest cases last *)
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.   
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.   
        assert (f1 + 1 <> 0). {
          unfold not. intros Hf.
          assert (f2 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f2). auto.
        }
        assert (f2 = 0). {
          destruct (dec (f2 = 0)).
          - auto.
          - destruct H1. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.   
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        fsatz.
      }
      {
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (f ^ 2 + a * f + 1 <> 0) by apply no_roots.
        assert (f1 ^ 2 + a * f1 + 1 <> 0) by apply no_roots.   
        assert (f + 1 <> 0). {
          unfold not. intros Hf.
          assert (f0 ^ 2 = de) by fsatz.
          destruct nonsquare_de with (x:=f0). auto.
        }
        assert (f0 = 0). {
          destruct (dec (f0 = 0)).
          - auto.
          - destruct H2. auto.
        }
        fsatz.
      }
      (* 4 goals remaining; goals 1 and 2 should be directly fsatz-able *)
      {
        assert (Epoint1: ae * (f1 / f2) ^ 2 + ((f1 - 1) / (f1 + 1)) ^ 2 = 1 + de * (f1 / f2) ^ 2 * ((f1 - 1) / (f1 + 1)) ^ 2). {
          clear y H H2 H3 H0 H5 f f0.
          fsatz.
        }
        assert (Epoint: ae * (f / f0) ^ 2 + ((f - 1) / (f + 1)) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2). {
          clear y0 H H1 H4 H0 H5 f1 f2 Epoint1.
          fsatz.
        }
        assert (1 - de * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1)) <> 0). {
          unfold not. intros contra.
          clear H0 H5 y0 y.
          destruct square_ae; clear square_ae.
          clear Hae Hde b_nonzero _3 _4 a b.
          rewrite <- H0 in Epoint.
          rewrite <- H0 in Epoint1.
          clear nonzero_ae H0 ae.
          remember (f / f0) as x1.
          remember ((f - 1) / (f + 1)) as y1.
          remember (f1 / f2) as x2.
          remember ((f1 - 1) / (f1 + 1)) as y2.
          clear H H1 H2 H3 H4 f f0 f1 f2 Heqx1 Heqy1 Heqx2 Heqy2.
          assert (x1 <> 0) by fsatz.
          assert (x2 <> 0) by fsatz.
          assert (y1 <> 0) by fsatz.
          assert (y2 <> 0) by fsatz.
          assert (square_pos: (x * x1 + y1) ^ 2 = (x * x2 + y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          assert (square_neg: (x * x1 - y1) ^ 2 = (x * x2 - y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          destruct (dec (x * x1 + y1 = 0)).
          - assert (x * x1 - y1 <> 0) by fsatz.
            destruct nonsquare_de with (x:= (x * x2 - y2) / (x2 * y2 * (x * x1 - y1))).
            fsatz.
          - destruct nonsquare_de with (x:= (x * x2 + y2) / (x2 * y2 * (x * x1 + y1))).
            fsatz.
        }
        rewrite Hae.
        rewrite Hde.
        rewrite Hde in H6.
        clear Epoint Epoint1 square_ae nonzero_ae nonsquare_de Hae Hde ae de.
        enough ((b * (f0 - f2) ^ 2 - (a + f1 + f + 1) * (f - f1) ^ 2) * (b * f0 * f2 * (f + 1)  * (f1 + 1) - (a - 2) * (f - 1) * (f1 - 1) * f * f1) = (b * (f0 - f2) ^ 2 - (a + f1 + f - 1) * (f - f1) ^ 2) * (b * f0 * f2 * (f - 1) * (f1 - 1) - (a + 2) * (f + 1) * (f1 + 1) * f * f1)). {
          clear y y0 H5. fsatz.
        }
        clear H H0 H1 H2 H3 H4 H5 H6.
        fsatz.
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
        assert (1 + de * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1)) <> 0). {
          unfold not. intros contra.
          clear H0 H5 y0 y.
          destruct square_ae; clear square_ae.
          clear Hae Hde b_nonzero _3 _4 a b.
          rewrite <- H0 in Epoint.
          rewrite <- H0 in Epoint1.
          clear nonzero_ae H0 ae.
          remember (f / f0) as x1.
          remember ((f - 1) / (f + 1)) as y1.
          remember (f1 / f2) as x2.
          remember ((f1 - 1) / (f1 + 1)) as y2.
          clear H H1 H2 H3 H4 f f0 f1 f2 Heqx1 Heqy1 Heqx2 Heqy2.
          assert (x1 <> 0) by fsatz.
          assert (x2 <> 0) by fsatz.
          assert (y1 <> 0) by fsatz.
          assert (y2 <> 0) by fsatz.
          assert (square_pos: (x * x1 + y1) ^ 2 = (x * x2 - y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          assert (square_neg: (x * x1 - y1) ^ 2 = (x * x2 + y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          destruct (dec (x * x1 + y1 = 0)).
          - assert (x * x1 - y1 <> 0) by fsatz.
            destruct nonsquare_de with (x:= (x * x2 + y2) / (x2 * y2 * (x * x1 - y1))).
            fsatz.
          - destruct nonsquare_de with (x:= (x * x2 - y2) / (x2 * y2 * (x * x1 + y1))).
            fsatz.
        }
        rewrite Hde.
        rewrite Hde in H6.
        clear Epoint Epoint1 square_ae nonzero_ae nonsquare_de Hae Hde ae de.
        enough ((b * ((f0 - f2) / (f - f1)) ^ 2 - a - f1 - f) * (1 + (a - 2) / b * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1))) = ((2 * f1 + f + a) * ((f0 - f2) / (f - f1)) - b * ((f0 - f2) / (f - f1)) ^ 3 - f2) * (f1 / f2 * ((f - 1) / (f + 1)) + (f1 - 1) / (f1 + 1) * (f / f0))). {
         clear y y0 H0. fsatz.
        }
        enough ((f - f1) * (b * (f0 - f2) ^ 2 - (a + f1 + f) * (f - f1) ^ 2) * (b * f0 * f2 * (f + 1) * (f1 + 1) + (a - 2) * f * f1 * (f - 1) * (f1 - 1)) = ((2 * f1 + f + a) * (f - f1) ^ 2 * (f0 - f2) - b * (f0 - f2) ^ 3 - f2 * (f - f1) ^ 3) * (f0 * (f1 + 1) * f1 * (f - 1) + f2 * (f + 1) * f * (f1 - 1)) * b). {
          clear y y0 H0 H5 H6. fsatz.
        }
        clear H H0 H1 H2 H3 H4 H5 H6.
        fsatz.
      }
      {
        remember (b * ((f0 - f2) / (f - f1)) ^ 2 - a - f1 - f) as u.
        remember ((2 * f1 + f + a) * ((f0 - f2) / (f - f1)) - b * ((f0 - f2) / (f - f1)) ^ 3 - f2) as v.
        assert (uv_Mpoint: b * v ^ 2 = u ^ 3 + a * u ^ 2 + u). {
          rewrite Hequ.
          rewrite Heqv.
          clear H0 H1 H2 H3 H4 Hequ Heqv.
          fsatz.
        }
        assert (u + 1 <> 0). {
          unfold not. intros contra.
          destruct nonsquare_de with (x := v).
          clear H0 H1 H2 H3 H4 Hequ Heqv H f f0 f1 f2 y y0.
          fsatz.
        }
        assert (v = 0). {
          destruct (dec (v = 0)).
          - auto.
          - destruct H0. auto.
        }
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          clear H H0 H1 H2 H3 H4 H5 H6 y y0 f f0 f1 f2 Hequ Heqv u v uv_Mpoint.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (no_factor_u: u ^ 2 + a * u + 1 <> 0) by apply no_roots.
        assert (u = 0). {
          clear H H0 H1 H2 H3 H4 H5 no_roots Hequ Heqv y y0 f f0 f1 f2.
          fsatz.
        }
        clear no_roots no_factor_u H5 uv_Mpoint H0.
        rename H6 into zero_v.
        rename H7 into zero_u.
        rewrite Hequ in zero_u.
        rewrite Heqv in zero_v.
        clear u v Hequ Heqv.
        assert (Epoint1: ae * (f1 / f2) ^ 2 + ((f1 - 1) / (f1 + 1)) ^ 2 = 1 + de * (f1 / f2) ^ 2 * ((f1 - 1) / (f1 + 1)) ^ 2). {
          clear y H H2 H3 zero_u zero_v f f0.
          fsatz.
        }
        assert (Epoint: ae * (f / f0) ^ 2 + ((f - 1) / (f + 1)) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2). {
          clear y0 H H1 H4 zero_u zero_v f1 f2 Epoint1.
          fsatz.
        }
        assert (1 - de * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1)) <> 0). {
          unfold not. intros contra.
          clear y y0 zero_u zero_v.
          destruct square_ae; clear square_ae.
          clear Hae Hde b_nonzero _3 _4 a b.
          rewrite <- H0 in Epoint.
          rewrite <- H0 in Epoint1.
          clear nonzero_ae H0 ae.
          remember (f / f0) as x1.
          remember ((f - 1) / (f + 1)) as y1.
          remember (f1 / f2) as x2.
          remember ((f1 - 1) / (f1 + 1)) as y2.
          clear H H1 H2 H3 H4 f f0 f1 f2 Heqx1 Heqy1 Heqx2 Heqy2.
          assert (x1 <> 0) by fsatz.
          assert (x2 <> 0) by fsatz.
          assert (y1 <> 0) by fsatz.
          assert (y2 <> 0) by fsatz.
          assert (square_pos: (x * x1 + y1) ^ 2 = (x * x2 + y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          assert (square_neg: (x * x1 - y1) ^ 2 = (x * x2 - y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          destruct (dec (x * x1 + y1 = 0)).
          - assert (x * x1 - y1 <> 0) by fsatz.
            destruct nonsquare_de with (x:= (x * x2 - y2) / (x2 * y2 * (x * x1 - y1))).
            fsatz.
          - destruct nonsquare_de with (x:= (x * x2 + y2) / (x2 * y2 * (x * x1 + y1))).
            fsatz.
        }
        enough (ae * (f1 / f2) * (f / f0) - ((f1 - 1) / (f1 + 1) * ((f - 1) / (f + 1))) = 1 - de * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1))). {
          clear y y0 Epoint Epoint1 zero_u zero_v.
          fsatz.
        }
        clear H0 Epoint Epoint1.
        rewrite Hae.
        rewrite Hde.
        clear Hae Hde nonzero_ae square_ae nonsquare_de ae de.
        fsatz.
      }
      {
        remember (b * ((f0 - f2) / (f - f1)) ^ 2 - a - f1 - f) as u.
        remember ((2 * f1 + f + a) * ((f0 - f2) / (f - f1)) - b * ((f0 - f2) / (f - f1)) ^ 3 - f2) as v.
        assert (uv_Mpoint: b * v ^ 2 = u ^ 3 + a * u ^ 2 + u). {
          rewrite Hequ.
          rewrite Heqv.
          clear H0 H1 H2 H3 H4 Hequ Heqv.
          fsatz.
        }
        assert (u + 1 <> 0). {
          unfold not. intros contra.
          destruct nonsquare_de with (x := v).
          clear H0 H1 H2 H3 H4 Hequ Heqv H f f0 f1 f2 y y0.
          fsatz.
        }
        assert (v = 0). {
          destruct (dec (v = 0)).
          - auto.
          - destruct H0. auto.
        }
        assert (no_roots: forall x : F, x^2 + a * x + 1 <> 0). {
          intros x. unfold not. intros Hx.
          destruct square_ae.
          clear H H0 H1 H2 H3 H4 H5 H6 y y0 f f0 f1 f2 Hequ Heqv u v uv_Mpoint.
          assert (x0 <> 0) by fsatz.
          destruct nonsquare_de with (x := (2 * x + a) / (b * x0)).
          fsatz.
        }
        assert (no_factor_u: u ^ 2 + a * u + 1 <> 0) by apply no_roots.
        assert (u = 0). {
          clear H H0 H1 H2 H3 H4 H5 no_roots Hequ Heqv y y0 f f0 f1 f2.
          fsatz.
        }
        clear no_roots no_factor_u H5 uv_Mpoint H0.
        rename H6 into zero_v.
        rename H7 into zero_u.
        rewrite Hequ in zero_u.
        rewrite Heqv in zero_v.
        clear u v Hequ Heqv.
        assert (Epoint1: ae * (f1 / f2) ^ 2 + ((f1 - 1) / (f1 + 1)) ^ 2 = 1 + de * (f1 / f2) ^ 2 * ((f1 - 1) / (f1 + 1)) ^ 2). {
          clear y H H2 H3 zero_u zero_v f f0.
          fsatz.
        }
        assert (Epoint: ae * (f / f0) ^ 2 + ((f - 1) / (f + 1)) ^ 2 = 1 + de * (f / f0) ^ 2 * ((f - 1) / (f + 1)) ^ 2). {
          clear y0 H H1 H4 zero_u zero_v f1 f2 Epoint1.
          fsatz.
        }
        assert (1 + de * (f1 / f2) * (f / f0) * ((f1 - 1) / (f1 + 1)) * ((f - 1) / (f + 1)) <> 0). {
          unfold not. intros contra.
          clear y y0 zero_u zero_v.
          destruct square_ae; clear square_ae.
          clear Hae Hde b_nonzero _3 _4 a b.
          rewrite <- H0 in Epoint.
          rewrite <- H0 in Epoint1.
          clear nonzero_ae H0 ae.
          remember (f / f0) as x1.
          remember ((f - 1) / (f + 1)) as y1.
          remember (f1 / f2) as x2.
          remember ((f1 - 1) / (f1 + 1)) as y2.
          clear H H1 H2 H3 H4 f f0 f1 f2 Heqx1 Heqy1 Heqx2 Heqy2.
          assert (x1 <> 0) by fsatz.
          assert (x2 <> 0) by fsatz.
          assert (y1 <> 0) by fsatz.
          assert (y2 <> 0) by fsatz.
          assert (square_pos: (x * x1 + y1) ^ 2 = (x * x2 - y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          assert (square_neg: (x * x1 - y1) ^ 2 = (x * x2 + y2) ^ 2 / (de * x2 ^ 2 * y2 ^ 2)) by fsatz.
          destruct (dec (x * x1 + y1 = 0)).
          - assert (x * x1 - y1 <> 0) by fsatz.
            destruct nonsquare_de with (x:= (x * x2 + y2) / (x2 * y2 * (x * x1 - y1))).
            fsatz.
          - destruct nonsquare_de with (x:= (x * x2 - y2) / (x2 * y2 * (x * x1 + y1))).
            fsatz.
        }
        enough (f1 / f2 * ((f - 1) / (f + 1)) + (f1 - 1) / (f1 + 1) * (f / f0) = 0). {
          clear y y0 Epoint Epoint1 zero_u zero_v.
          fsatz.
        }
        clear H0 Epoint Epoint1 Hae Hde nonzero_ae square_ae nonsquare_de ae de.
        fsatz.
      }
      Qed.

  End EdwardsMontgomery.
End M.

