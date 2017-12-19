Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings Crypto.Util.Notations.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Experiments.Loops.
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

    Context {ap2d4:F} {ap2d4_correct:(1+1+1+1)*a24 = a+1+1}.
    Definition boringladderstep (x1:F) (Q Q':F*F) : (F*F)*(F*F) :=
      match Q, Q' with
        pair x2 z2, pair x3 z3 =>
        dlet tmp0l := x3 - z3 in
        dlet tmp1l := x2 - z2 in
        dlet x2l := x2 + z2 in
        dlet z2l := x3 + z3 in
        dlet z3 := tmp0l * x2l in
        dlet z2 := z2l * tmp1l in
        dlet tmp0 := tmp1l^2 in
        dlet tmp1 := x2l^2 in
        dlet x3l := z3 + z2 in
        dlet z2l := z3 - z2 in
        dlet x2 := tmp1 * tmp0 in
        dlet tmp1l := tmp1 - tmp0 in
        dlet z2 := z2l^2 in
        dlet z3 := ap2d4 * tmp1l in
        dlet x3 := x3l^2 in
        dlet tmp0l := tmp0 + z3 in
        dlet z3 := x1 * z2 in
        dlet z2 := tmp1l * tmp0l in
        ((x2, z2), (x3, z3))%core
      end.
 
    Context {cswap:bool->F->F->F*F}.
    Local Notation xor := Coq.Init.Datatypes.xorb.
    Local Open Scope core_scope.

    (* TODO: make a nice notations for loops like here *)
    Definition montladder (scalarbits : Z) (testbit:Z->bool) (x1:F) : F :=
      let '(x2, z2, x3, z3, swap, _) := (* names of variables as used after the loop *)
          (while (fun '(_, i) => BinInt.Z.geb i 0) (* the test of the loop *)
          (fun '(x2, z2, x3, z3, swap, i) => (* names of variables as used in the loop; we should reuse the same names as for after the loop *)
            dlet b := testbit i in (* the body... *)
            dlet swap := xor swap b in
            let (x2, x3) := cswap swap x2 x3 in
            let (z2, z3) := cswap swap z2 z3 in
            dlet swap := b in
            let '((x2, z2), (x3, z3)) := xzladderstep x1 (x2, z2) (x3, z3) in
            let i := BinInt.Z.pred i in (* the third "increment" component of a for loop; either between the test and body or just inlined into the body like here *)
            (x2, z2, x3, z3, swap, i)) (* the "return value" of the body is always the exact same variable names as in the beginning of the body because we shadow the original binders, but I think for now this will be unavoidable boilerplate. *)
          (BinInt.Z.to_nat scalarbits) (* bound on number of loop iterations, should come between test and body *)
          (1%F, 0%F, x1, 1%F, false, BinInt.Z.pred scalarbits)) in (* initial values, these should come before the test and body *)
      let (x2, x3) := cswap swap x2 x3 in
      let (z2, z3) := cswap swap z2 z3 in
      x2 * Finv z2.
  End MontgomeryCurve.
End M.
