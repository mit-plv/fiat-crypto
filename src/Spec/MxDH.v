Require Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Notations.
(*Require Crypto.Curves.Montgomery.XZ.*)

Module MxDH. (* from RFC7748 *)
  Section MontgomeryLadderKeyExchange.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq}.
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
    Section generic.
      Context (F4 : Type)
              (pair4 : F -> F -> F -> F -> F4)
              (let_in : F -> (F -> F4) -> F4).
      Local Notation "'llet' x := y 'in' z" := (let_in y (fun x => z)).
      Definition ladderstep_gen (X1:F) (P1 P2:F * F) : F4 :=
        let '(X2, Z2) := P1 in
        let '(X3, Z3) := P2 in
        llet A := X2+Z2 in
        llet AA := A^2 in
        llet B := X2-Z2 in
        llet BB := B^2 in
        llet E := AA-BB in
        llet C := X3+Z3 in
        llet D := X3-Z3 in
        llet DA := D*A in
        llet CB := C*B in
        llet X5 := (DA+CB)^2 in
        llet Z5 := X1*(DA-CB)^2 in
        llet X4 := AA*BB in
        llet Z4 := E*(AA + a24*E) in
        pair4 X4 Z4 X5 Z5.
    End generic.

    (** TODO: Make this the only ladderstep? *)
    Definition ladderstep_other_assoc (X1:F) (P1 P2:F*F) : F*F*F*F :=
      Eval cbv beta delta [ladderstep_gen] in
        @ladderstep_gen
            (F*F*F*F)
            (fun X3 Y3 Z3 T3 => (X3, Y3, Z3, T3))
            (fun x f => let y := x in f y)
            X1 P1 P2.

    Definition ladderstep (X1:F) (P1 P2:F*F) : (F*F)*(F*F) :=
      Eval cbv beta delta [ladderstep_gen] in
        @ladderstep_gen
            ((F*F)*(F*F))
            (fun X3 Y3 Z3 T3 => ((X3, Y3), (Z3, T3)))
            (fun x f => let y := x in f y)
            X1 P1 P2.

    (*Import Curves.Montgomery.XZ.
    Goal forall X1 P1 P2, Logic.eq (ladderstep X1 P1 P2) (@M.xzladderstep F Fadd Fsub Fmul a24 X1 P1 P2).
    Proof.
      intros ? [? ?] [? ?].
      reflexivity.
    Qed.*)

    Context {cswap:bool->F*F->F*F->(F*F)*(F*F)}.

    Fixpoint downto_iter (i:nat) : list nat :=
      match i with
      | Datatypes.S i' => cons i' (downto_iter i')
      | O => nil
      end.

    Definition downto {state} init count (step:state->nat->state) : state :=
      List.fold_left step (downto_iter count) init.

    Local Notation xor := Coq.Init.Datatypes.xorb.

    (* Ideally, we would verify that this corresponds to x coordinate
    multiplication *)
    Definition montladder bound (testbit:nat->bool) (u:F) :=
      let '(P1, P2, swap) :=
          downto
            ((1, 0), (u, 1), false)
            bound
            (fun state i =>
               let '(P1, P2, swap) := state in
               let s_i := testbit i in
               let swap := xor swap s_i in
               let '(P1, P2) := cswap swap P1 P2 in
               let swap := s_i in
               let '(P1, P2) := ladderstep u P1 P2 in
               (P1, P2, swap)
            ) in
      let '((x, z), _) := cswap swap P1 P2 in
      x * Finv z.
  End MontgomeryLadderKeyExchange.
End MxDH.

(* see [Test.Curve25519SpecTestVectors] for sanity-checks *)
