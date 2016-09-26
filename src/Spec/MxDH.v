Require Crypto.Algebra.

Module MxDH. (* from RFC7748 *)
  Section MontgomeryLadderKeyExchange.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "4" := (2+2).

    Context {a b: F}. (* parameters of the Montgomery curve *)
    Context {nonsquare_aa_m4:~exists sqrt, sqrt^2 = a^2-4} {five_neq_zero:1+4<>0}.

    (* Implemention from RFC7748. Note that this differs from EFD and
       Montgomery '87 in the choice of which precomputed constant to use
       for [a] *)
    (* Ideally we would want to verify that this correspons to
       x-coordinate addition on the relevant elliptic curve, as
       specified by addition formulas in Montgomery coordinates.
       However, even if we did get to doing that, we still would not
       want to change the type of the ladder function to talk about
       points that are on the curve -- there are contexts where this
       can be, carefully, used with values that are not verified to
       be on the curve *)
    Context {a24:F} {a24_correct:4*a24 = a-2}.
    Definition ladderstep (X1:F) (P1 P2:F*F) : (F*F)*(F*F) :=
      match P1, P2 return _ with
        (X2, Z2), (X3, Z3) => 
          let A := X2+Z2 in
          let AA := A^2 in
          let B := X2-Z2 in
          let BB := B^2 in
          let E := AA-BB in
          let C := X3+Z3 in
          let D := X3-Z3 in
          let DA := D*A in
          let CB := C*B in
          let X5 := (DA+CB)^2 in
          let Z5 := X1*(DA-CB)^2 in
          let X4 := AA*BB in
          let Z4 := E*(AA + a24*E) in
          ((X4, Z4), (X5, Z5))
        end.

    Context {S:Type} {testbit:S->nat->bool} {cswap:bool->F*F->F*F->(F*F)*(F*F)}.

    Fixpoint downto_iter (i:nat) : list nat :=
      match i with
      | Datatypes.S i' => i'::downto_iter i'
      | O => nil
      end.

    Definition downto {state} init count (step:state->nat->state) : state :=
      List.fold_left step (downto_iter count) init.
    
    Local Notation xor := Coq.Init.Datatypes.xorb.

    (* Ideally, we would verify that this corresponds to x coordinate
    multiplication *)
    Definition montladder bound (s:S) (u:F) :=
      let '(_, _, P1, P2, swap) :=
          downto
            (s, u, (1, 0), (u, 1), false)
            bound
            (fun state i =>
               let '(s, x, P1, P2, swap) := state in
               let s_i := testbit s i in
               let swap := xor swap s_i in
               let '(P1, P2) := cswap swap P1 P2 in
               let swap := s_i in
               let '(P1, P2) := ladderstep x P1 P2 in
               (s, x, P1, P2, swap)
            ) in
      let '((x, z), _) := cswap swap P1 P2 in
      x/z.
  End MontgomeryLadderKeyExchange.
End MxDH.

(* see [Test.Curve25519SpecTestVectors] for sanity-checks *)