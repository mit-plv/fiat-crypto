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
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive} (* FIXME: we shouldn't need this *)
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

    Program Definition inv (P:point) : point
      := match W.coordinates P return F*F+_ with
         | inl (x1, y1) => inl (x1, Fopp y1)
         | _ => P
         end.
    Next Obligation. destruct P as [[[??]|[]]?]; cbv; trivial; fsatz. Qed.

    Lemma same_x_same_y
          (xA yA : F)
          (A : yA ^ 2 = xA ^ 3 + a * xA + b)
          (xB yB : F)
          (B : yB ^ 2 = xB ^ 3 + a * xB + b)
          (Hx: xA = xB)
          (Hy:yB <> Fopp yA)
      : yB = yA.
    Proof. fsatz. Qed.

    Let is_redundant {T} (x:T) := x.
    Ltac clear_marked_redundant :=
      repeat match goal with
               [H:?P, Hr:is_redundant ?P |- _] => clear H Hr
             end.
    Ltac t_step :=
      match goal with
      | _ => solve [ contradiction | trivial | exact _ ]
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
      | _ => progress cbv [inv W.eq W.zero W.add W.coordinates proj1_sig] in *
      | _ => progress break_match
      | |- _ /\ _ => split | |- _ <-> _ => split
      end.
    Ltac t := repeat t_step; clear_marked_redundant.

    Global Instance commutative_group : abelian_group(eq:=W.eq)(op:=W.add)(id:=W.zero)(inv:=inv).
    Proof. t. all:try (abstract fsatz). Qed.
    
  End W.
End W.
