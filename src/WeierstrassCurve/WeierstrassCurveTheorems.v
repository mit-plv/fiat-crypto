Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.
Require Import BinPos.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_3:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {char_gt_11:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul 11%positive} (* FIXME: we shouldn't need this *)
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation eq := (@W.eq F Feq Fadd Fmul a b).
    Local Notation point := (@W.point F Feq Fadd Fmul a b).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2). Local Notation "4" := (1+3).
    Local Notation "8" := (1+(1+(1+(1+4)))). Local Notation "12" := (1+(1+(1+(1+8)))).
    Local Notation "16" := (1+(1+(1+(1+12)))). Local Notation "20" := (1+(1+(1+(1+16)))).
    Local Notation "24" := (1+(1+(1+(1+20)))). Local Notation "27" := (1+(1+(1+24))).
    Local Notation "x ^ 2" := (x*x) (at level 30). Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Context {discriminant_nonzero:4*a^3 + 27*b^2 <> 0}.

    Lemma same_x_same_y
          (xA yA : F)
          (A : yA ^ 2 = xA ^ 3 + a * xA + b)
          (xB yB : F)
          (B : yB ^ 2 = xB ^ 3 + a * xB + b)
          (Hx: xA = xB)
          (Hy:yB <> Fopp yA)
      : yB = yA.
    Proof. fsatz. Qed.

    Definition is_redundant {T} (x:T) := x.
    Global Arguments is_redundant : simpl never.
    Ltac clear_marked_redundant :=
      repeat match goal with
               [H:?P, Hr:is_redundant ?P |- _] => clear H Hr
             end.

    Ltac t_step :=
      match goal with
      | _ => exact _
      | _ => intro
      | [ A : ?yA ^ 2 = ?xA ^ 3 + a * ?xA + b,
              B : ?yB ^ 2 = ?xB ^ 3 + a * ?xB + b,
                  Hx: ?xA = ?xB,
                      Hy: ?yB <> Fopp ?yA
          |- _] => unique pose proof (same_x_same_y _ _ A _ _ B Hx Hy)
      | |- Equivalence _ => split
      | |- abelian_group => split | |- group => split | |- monoid => split
      | |- is_associative => split | |- is_commutative => split 
      | |- is_left_inverse => split | |- is_right_inverse => split
      | |- is_left_identity => split | |- is_right_identity => split
      | p:point |- _ => destruct p
      | _ => progress destruct_head' sum
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' unit
      | _ => progress destruct_head' and
      | |- context[?P] =>
        unique pose proof (proj2_sig P);
        unique pose proof (proj2_sig P:(is_redundant _))
      | _ => progress cbv [eq W.eq W.add W.coordinates proj1_sig] in *
      | _ => progress simpl in *
      | _ => progress break_match
      | |- _ /\ _ => split | |- _ <-> _ => split
      | _ => abstract (trivial || contradiction || clear_marked_redundant; fsatz)
      end.
    Ltac t := repeat t_step.

    Program Definition inv (P:point) : point
      := exist
           _
           (match W.coordinates P return _ with
            | inl (x1, y1) => inl (x1, Fopp y1)
            | _ => P
            end)
           _.
    Next Obligation. t. Qed.

    Global Instance commutative_group : abelian_group(eq:=W.eq)(op:=W.add)(id:=W.zero)(inv:=inv).
    Proof. Time t. Time Qed.
  End W.
End W.

(*
Times for individual subgoal of the associativity proof:
Finished transaction in 0.169 secs (0.17u,0.s) (successful)
Finished transaction in 0.16 secs (0.159u,0.s) (successful)
Finished transaction in 0.722 secs (0.723u,0.s) (successful)
Finished transaction in 3.375 secs (3.373u,0.003s) (successful)
Finished transaction in 7.166 secs (7.166u,0.s) (successful)
Finished transaction in 1.862 secs (1.856u,0.003s) (successful)
Finished transaction in 3.6 secs (3.603u,0.s) (successful)
Finished transaction in 0.571 secs (0.569u,0.s) (successful)
Finished transaction in 1.956 secs (1.959u,0.s) (successful)
Finished transaction in 3.186 secs (3.186u,0.s) (successful)
Finished transaction in 1.265 secs (1.266u,0.s) (successful)
Finished transaction in 1.884 secs (1.883u,0.s) (successful)
Finished transaction in 0.762 secs (0.763u,0.s) (successful)
Finished transaction in 2.431 secs (2.433u,0.s) (successful)
Finished transaction in 1.662 secs (1.663u,0.s) (successful)
Finished transaction in 1.846 secs (1.846u,0.s) (successful)
Finished transaction in 1.853 secs (1.853u,0.s) (successful)
Finished transaction in 1.727 secs (1.73u,0.s) (successful)
Finished transaction in 1.771 secs (1.769u,0.s) (successful)
Finished transaction in 2.07 secs (2.073u,0.s) (successful)
Finished transaction in 5.765 secs (5.766u,0.s) (successful)
Finished transaction in 9.965 secs (9.966u,0.s) (successful)
Finished transaction in 3.917 secs (3.916u,0.s) (successful)
Finished transaction in 6.101 secs (6.099u,0.003s) (successful)
Finished transaction in 2.042 secs (2.043u,0.s) (successful)
Finished transaction in 5.398 secs (5.399u,0.s) (successful)
Finished transaction in 6.346 secs (6.346u,0.s) (successful)
Finished transaction in 4.726 secs (4.726u,0.s) (successful)
Finished transaction in 5.872 secs (5.876u,0.s) (successful)
Finished transaction in 1.852 secs (1.853u,0.s) (successful)
Finished transaction in 3.189 secs (3.189u,0.s) (successful)
Finished transaction in 1.489 secs (1.49u,0.s) (successful)
Finished transaction in 6.602 secs (6.603u,0.s) (successful)
Finished transaction in 12.172 secs (12.169u,0.003s) (successful)
Finished transaction in 4.668 secs (4.669u,0.s) (successful)
Finished transaction in 8.451 secs (8.449u,0.003s) (successful)
Finished transaction in 1.304 secs (1.303u,0.s) (successful)
Finished transaction in 4.818 secs (4.816u,0.003s) (successful)
Finished transaction in 7.557 secs (7.559u,0.s) (successful)
Finished transaction in 4.435 secs (4.436u,0.s) (successful)
Finished transaction in 7.915 secs (7.916u,0.s) (successful)
Finished transaction in 0.623 secs (0.623u,0.s) (successful)
Finished transaction in 2.145 secs (2.146u,0.s) (successful)
Finished transaction in 1.436 secs (1.436u,0.s) (successful)
Finished transaction in 2.091 secs (2.09u,0.s) (successful)
Finished transaction in 1.459 secs (1.46u,0.s) (successful)
Finished transaction in 1.371 secs (1.373u,0.s) (successful)
Finished transaction in 1.417 secs (1.416u,0.s) (successful)
Finished transaction in 1.757 secs (1.756u,0.s) (successful)
Finished transaction in 5.275 secs (5.276u,0.s) (successful)
Finished transaction in 8.736 secs (8.736u,0.s) (successful)
Finished transaction in 3.415 secs (3.416u,0.s) (successful)
Finished transaction in 5.508 secs (5.506u,0.003s) (successful)
Finished transaction in 1.881 secs (1.883u,0.s) (successful)
Finished transaction in 21.631 secs (21.629u,0.003s) (successful)
Finished transaction in 312.734 secs (312.723u,0.036s) (successful)
Finished transaction in 4.439 secs (4.436u,0.s) (successful)
Finished transaction in 6.267 secs (6.266u,0.003s) (successful)
Finished transaction in 1.241 secs (1.24u,0.s) (successful)
Finished transaction in 1.603 secs (1.603u,0.s) (successful)
Finished transaction in 1.824 secs (1.823u,0.s) (successful)
Finished transaction in 8.099 secs (8.099u,0.s) (successful)
Finished transaction in 16.461 secs (16.456u,0.003s) (successful)
Finished transaction in 4.722 secs (4.723u,0.s) (successful)
Finished transaction in 9.305 secs (9.306u,0.s) (successful)
Finished transaction in 1.398 secs (1.396u,0.s) (successful)
Finished transaction in 4.721 secs (4.723u,0.s) (successful)
Finished transaction in 7.226 secs (7.226u,0.s) (successful)
Finished transaction in 3.282 secs (3.283u,0.s) (successful)
Finished transaction in 4.536 secs (4.539u,0.s) (successful)
Finished transaction in 0.379 secs (0.38u,0.s) (successful)
Finished transaction in 0.438 secs (0.436u,0.s) (successful)
Finished transaction in 0.323 secs (0.326u,0.s) (successful)
Finished transaction in 0.372 secs (0.369u,0.s) (successful)
Finished transaction in 0.378 secs (0.376u,0.s) (successful)
Finished transaction in 0.438 secs (0.44u,0.s) (successful)
Finished transaction in 0.33 secs (0.329u,0.s) (successful)
Finished transaction in 0.368 secs (0.369u,0.s) (successful)
Finished transaction in 0.088 secs (0.086u,0.s) (successful)
Finished transaction in 0.087 secs (0.09u,0.s) (successful)
Finished transaction in 0.371 secs (0.369u,0.s) (successful)
Finished transaction in 0.441 secs (0.44u,0.s) (successful)
Finished transaction in 0.322 secs (0.319u,0.s) (successful)
Finished transaction in 0.37 secs (0.373u,0.s) (successful)
Finished transaction in 0.089 secs (0.086u,0.s) (successful)
Finished transaction in 0.091 secs (0.093u,0.s) (successful)
Finished transaction in 0.088 secs (0.089u,0.s) (successful)
Finished transaction in 0.086 secs (0.086u,0.s) (successful)

Finished transaction in 268.648 secs (268.609u,0.096s) (successful)
*)