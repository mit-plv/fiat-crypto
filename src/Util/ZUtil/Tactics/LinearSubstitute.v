Require Import Coq.omega.Omega Coq.ZArith.ZArith.
Require Import Crypto.Util.Tactics.Contains.
Require Import Crypto.Util.Tactics.Not.
Local Open Scope Z_scope.

Module Z.
  Lemma move_R_pX x y z : x + y = z -> x = z - y.
  Proof. omega. Qed.
  Lemma move_R_mX x y z : x - y = z -> x = z + y.
  Proof. omega. Qed.
  Lemma move_R_Xp x y z : y + x = z -> x = z - y.
  Proof. omega. Qed.
  Lemma move_R_Xm x y z : y - x = z -> x = y - z.
  Proof. omega. Qed.
  Lemma move_L_pX x y z : z = x + y -> z - y = x.
  Proof. omega. Qed.
  Lemma move_L_mX x y z : z = x - y -> z + y = x.
  Proof. omega. Qed.
  Lemma move_L_Xp x y z : z = y + x -> z - y = x.
  Proof. omega. Qed.
  Lemma move_L_Xm x y z : z = y - x -> y - z = x.
  Proof. omega. Qed.

  (** [linear_substitute x] attempts to maipulate equations using only
      addition and subtraction to put [x] on the left, and then
      eliminates [x].  Currently, it only handles equations where [x]
      appears once; it does not yet handle equations like [x - x + x =
      5]. *)
  Ltac linear_solve_for_in_step for_var H :=
    let LHS := match type of H with ?LHS = ?RHS => LHS end in
    let RHS := match type of H with ?LHS = ?RHS => RHS end in
    first [ match RHS with
            | ?a + ?b
              => first [ contains for_var b; apply move_L_pX in H
                       | contains for_var a; apply move_L_Xp in H ]
            | ?a - ?b
              => first [ contains for_var b; apply move_L_mX in H
                       | contains for_var a; apply move_L_Xm in H ]
            | for_var
              => progress symmetry in H
            end
          | match LHS with
            | ?a + ?b
              => first [ not contains for_var b; apply move_R_pX in H
                       | not contains for_var a; apply move_R_Xp in H ]
            | ?a - ?b
              => first [ not contains for_var b; apply move_R_mX in H
                       | not contains for_var a; apply move_R_Xm in H ]
            end ].
  Ltac linear_solve_for_in for_var H := repeat linear_solve_for_in_step for_var H.
  Ltac linear_solve_for for_var :=
    match goal with
    | [ H : for_var = _ |- _ ] => idtac
    | [ H : context[for_var] |- _ ]
      => linear_solve_for_in for_var H;
         lazymatch type of H with
         | for_var = _ => idtac
         | ?T => fail 0 "Could not fully solve for" for_var "in" T "(hypothesis" H ")"
         end
    end.
  Ltac linear_substitute for_var := linear_solve_for for_var; subst for_var.
  Ltac linear_substitute_all :=
    repeat match goal with
           | [ v : Z |- _ ] => linear_substitute v
           end.
End Z.
