Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings Crypto.Util.Notations.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ForLoop.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_5:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 5}.
    Delimit Scope F_scope with F.
    Local Open Scope F_scope.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd : F_scope. Local Infix "*" := Fmul : F_scope.
    Local Infix "-" := Fsub : F_scope. Local Infix "/" := Fdiv : F_scope.
    Local Notation "x ^ 2" := (x*x) : F_scope.
    Local Notation "0" := Fzero : F_scope.  Local Notation "1" := Fone : F_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y , .. , z )" := (inl (pair .. (pair x y) .. z)) : F_scope.

    Context {a b: F} {b_nonzero:b <> 0}.
    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation opp := (M.opp(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Program Definition to_xz (P:point) : F*F :=
      match M.coordinates P with
      | (x, y) => (x, 1)%core
      | ∞ => (1, 0)%core
      end.

    Let char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two)).
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto; vm_decide. Qed.

    (* From Curve25519 paper by djb, appendix B. Credited to Montgomery *)
    Context {a24:F} {a24_correct:(1+1+1+1)*a24 = a-(1+1)}.
    Definition xzladderstep (x1:F) (Q Q':F*F) : ((F*F)*(F*F)) :=
      match Q, Q' with
        pair x z, pair x' z' =>
        dlet A := x+z in
        dlet B := x-z in
        dlet AA := A^2 in
        dlet BB := B^2 in
        dlet x2 := AA*BB in
        dlet E := AA-BB in
        dlet z2 := E*(AA + a24*E) in
        dlet C := x'+z' in
        dlet D := x'-z' in
        dlet CB := C*B in
        dlet DA := D*A in
        dlet x3 := (DA+CB)^2 in
        dlet z3 := x1*(DA-CB)^2 in
        ((x2, z2), (x3, z3))%core
      end.

    (* optimized version from curve25519-donna by Adam Langley *)
    Definition donnaladderstep (x1:F) (Q Q':F*F) : (F*F)*(F*F) :=
      match Q, Q' with
        pair x z, pair x' z'=>
        dlet origx := x in
        dlet x := x + z in
        dlet z := origx - z in
        dlet origx' := x' in
        dlet x' := x' + z' in
        dlet z' := origx' - z' in
        dlet xx' := x' * z in
        dlet zz' := x * z' in
        dlet origx' := xx' in
        dlet xx' := xx' + zz' in
        dlet zz' := origx' - zz' in
        dlet x3 := xx'^2 in
        dlet zzz' := zz'^2 in
        dlet z3 := zzz' * x1 in
        dlet xx := x^2 in
        dlet zz := z^2 in
        dlet x2 := xx * zz in
        dlet zz := xx - zz in
        dlet zzz := zz * a24 in
        dlet zzz := zzz + xx in
        dlet z2 := zz * zzz in
        ((x2, z2), (x3, z3))%core
      end.

    Context {cswap:bool->F*F->F*F->(F*F)*(F*F)}.

    Local Notation xor := Coq.Init.Datatypes.xorb.

    (* Ideally, we would verify that this corresponds to x coordinate
       multiplication *)
    Local Open Scope core_scope.
    Definition montladder (bound : positive) (testbit:Z->bool) (u:F) :=
      let '(P1, P2, swap) :=
          for (int i = BinInt.Z.pos bound; i >= 0; i--)
              updating ('(P1, P2, swap) = ((1%F, 0%F), (u, 1%F), false)) {{
            dlet s_i := testbit i in
            dlet swap := xor swap s_i in
            let '(P1, P2) := cswap swap P1 P2 in
            dlet swap := s_i in
            let '(P1, P2) := xzladderstep u P1 P2 in
            (P1, P2, swap)
      }} in
      let '((x, z), _) := cswap swap P1 P2 in
      x * Finv z.

  End MontgomeryCurve.
End M.
