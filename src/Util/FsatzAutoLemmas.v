Require Import Coq.Program.Program.
Require Import Coq.Classes.Morphisms.

Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Notations.

Create HintDb fsatz_lookup discriminated.

Module F.
  Section with_field.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).

    Local Obligation Tactic := abstract (intros; fsatz).

    Program Definition eq_opp__eq_zero a : a = Fopp a -> a = 0 := _.
    Program Definition neq_opp__neq_zero a : a <> Fopp a -> a <> 0 := _.
    Program Definition twice_eq_zero a : a + a = 0 -> a = 0 := _.
    Program Definition twice_neq_zero a : a + a <> 0 -> a <> 0 := _.
    Program Definition inv_cube_eq_zero__neq_zero__absurd a : Finv (a^3) = 0 -> a <> 0 -> False := _.
    Program Definition sub_eq_zero_eq a b : a - b = 0 -> a = b := _.
    Program Definition sub_eq_zero_eq_sym a b : a - b = 0 -> b = a := _.
    Program Definition sub_neq_zero_eq a b : a - b <> 0 -> a <> b := _.
    Program Definition sub_neq_zero_eq_sym a b : a - b <> 0 -> b <> a := _.
    Program Definition mul3_nonzero_drop_mid a b c : (a * b) * c <> 0 -> a * c <> 0 := _.
    Program Definition mul_nonzero_l a b : a * b <> 0 -> a <> 0 := _.
    Program Definition mul_nonzero_r a b : a * b <> 0 -> b <> 0 := _.
    Program Definition factor_difference_of_squares a b c : a^2 - b^2 = c -> (a - b) * (a + b) = c := _.
    Program Definition expand_square_sum a b : (a + b)^2 - (a^2 + b^2) = 0 -> a * b = 0 := _.
    Program Definition expand_square_sum_neq a b : (a + b)^2 - (a^2 + b^2) <> 0 -> a * b <> 0 := _.
    Program Definition expand_square_sum_sub a b : (a + b)^2 - a^2 - b^2 = 0 -> a * b = 0 := _.
    Program Definition expand_square_sum_sub_neq a b : (a + b)^2 - a^2 - b^2 <> 0 -> a * b <> 0 := _.
    Program Definition factor_square_sum a b : a * b = 0 -> (a + b)^2 - (a^2 + b^2) = 0 := _.
    Program Definition factor_square_sum_neq a b : a * b <> 0 -> (a + b)^2 - (a^2 + b^2) <> 0 := _.
    Program Definition factor_square_sum_sub a b : a * b = 0 -> (a + b)^2 - a^2 - b^2 = 0 := _.
    Program Definition factor_square_sum_sub_neq a b : a * b <> 0 -> (a + b)^2 - a^2 - b^2 <> 0 := _.
    Program Definition mul_eq_0_r_nz a b : a * b = 0 -> a <> 0 -> b = 0 := _.
    Program Definition mul_eq_0_l_nz a b : a * b = 0 -> b <> 0 -> a = 0 := _.
    Program Definition mul_eq_0_l a b : a = 0 -> a * b = 0 := _.
    Program Definition mul_eq_0_r a b : b = 0 -> a * b = 0 := _.
    Program Definition mul_neq_0 a b : a <> 0 -> b <> 0 -> a * b <> 0 := _.
    Program Definition helper1 a b c : a + b * c = 0 -> a <> Fopp (c * b) -> False := _.
    Program Definition helper2 a b c d : a - b * c <> d -> b = 1 -> a - c <> d := _.
    Program Definition helper3 a b c d : a - b * c = d -> b = 1 -> a - c = d := _.
    Program Definition helper4 a b c d e : a - b * c * d <> e -> b = 1 -> a - c * d <> e := _.
    Program Definition helper5 a b c d e : a - b * c * d = e -> b = 1 -> a - c * d = e := _.
    Program Definition helper6 a b c d : a - b * c^2 <> d -> c = 1 -> a - b <> d := _.
    Program Definition helper7 a b c d : a - b * c^2 = d -> c = 1 -> a - b = d := _.
    Program Definition helper8 a b c d : a - b + c <> d -> b = 0 -> a + c <> d := _.
    Program Definition helper9 a b c : a - b <> c -> b = 0 -> a <> c := _.
    Program Definition helper10 a b c d : a * b + c <> d -> a = 0 -> c <> d := _.
    Program Definition helper11 a b c d : a * b + c <> d -> b = 0 -> c <> d := _.
    Program Definition helper12 a b c : a * b <> c -> a = 0 -> c <> 0 := _.
    Program Definition helper13 a b c : a * b <> c -> b = 0 -> c <> 0 := _.
    Program Definition helper14 a b c : Fopp (a * b) <> c -> a = 0 -> c <> 0 := _.
    Program Definition helper15 a b c : Fopp (a * b) <> c -> b = 0 -> c <> 0 := _.
    Program Definition helper16 a b c : a * b^3 = c -> b = 0 -> c = 0 := _.
    Program Definition helper17 a b c : a * b = c -> a = 0 -> c = 0 := _.
    Program Definition helper18 a b c : a * b - c <> 0 -> a = 0 -> c <> 0 := _.
    Program Definition helper19 a b c : a * b - c <> 0 -> b = 0 -> c <> 0 := _.
    Program Definition helper20 a b c : a * b - c = 0 -> a = 0 -> c = 0 := _.
    Program Definition helper21 a b c : a * b - c = 0 -> b = 0 -> c = 0 := _.
    Program Definition helper22 a b c : a - b * c = 0 -> c = 0 -> a = 0 := _.
    Program Definition helper23 a b c d : a * (b * b^2) - c <> d -> a * (b^3) - c <> d := _.
    Program Definition helper24 a b c d : a * (b * b^2) - c = d -> a * (b^3) - c = d := _.
    Program Definition helper25 a b c d : a - (b * b^2) * c <> d -> a - (b^3) * c <> d := _.
    Program Definition helper26 a b c d : a - (b * b^2) * c = d -> a - (b^3) * c = d := _.
    Program Definition helper27 a b : a * (b * b^2) = 0 -> b <> 0 -> a = 0 := _.
    Program Definition helper28 a b c : c <> 0 -> a * (b * c) = 0 -> a * b = 0 := _.
    Program Definition helper29 a b c : a = 0 -> a * b + c = 0 -> c = 0 := _.
    Program Definition helper30 a b c d : a * b^3 + d * c^3 = 0 -> a * (b * b^2) - c * c^2 * d = 0 -> a * b^3 = 0 := _.
    Program Definition helper31 a b c d : a * Finv (b^2) <> c * Finv (d^2) -> b <> 0 -> d <> 0 -> a * (d^2) <> c * (b^2) := _.
    Program Definition helper32 a b c d : a * Finv (b^2) = c * Finv (d^2) -> b <> 0 -> d <> 0 -> a * (d^2) = c * (b^2) := _.
    Program Definition helper33 a b c d : a * Finv (b^3) = Fopp (c * Finv (d^3)) -> b <> 0 -> d <> 0 -> a * (d^3) = Fopp (c * (b^3)) := _.
    Program Definition helper34 a b c d : a * Finv (b^3) <> Fopp (c * Finv (d^3)) -> b <> 0 -> d <> 0 -> a * (d^3) <> Fopp (c * (b^3)) := _.
    Program Definition helper35 a b c : a = Fopp (b * c) -> a - c * b = 0 -> a = 0 := _.
    Program Definition helper36 a b c : a <> Fopp (b * c) -> a - c * b = 0 -> a * b * c <> 0 := _.
    Program Definition helper37 X Y X' Y' A B C C' : Y^2 = C^3 + A * C * (X^2)^2 + B * (X^3)^2 -> Y'^2 = C'^3 + A * C' * (X'^2)^2 + B * (X'^3)^2 -> C' * X^2 - C * X'^2 = 0 -> (Y' * (X^3))^2 - ((X'^3) * Y)^2 = 0 := _.
    Program Definition helper38 X Y X' Y' A B C C' : Y^2 = C^3 + A * C * (X^2)^2 + B * (X^3)^2 -> Y'^2 = C'^3 + A * C' * (X'^2)^2 + B * (X'^3)^2 -> C' * X^2 = C * X'^2 -> (Y' * (X^3))^2 - ((X'^3) * Y)^2 = 0 := _.
    Program Definition helper39 a : a <> 0 -> Finv (a^2) = (Finv a)^2 := _.
    Program Definition helper40 a : a <> 0 -> Finv (a^3) = (Finv a)^3 := _.
    Program Definition helper41 a : a <> 0 -> Finv (Finv a) = a := _.
    Program Definition helper42 a b : (a + b)^2 - a^2 - b^2 = (1+1) * a * b := _.
    Program Definition helper42' a b : (a + b)^2 - (a^2 + b^2) = (1+1) * a * b := _.
    Program Definition helper43 a b : a * b <> 0 -> Finv (a * b) = Finv a * Finv b := _.
    Program Definition helper_zero_1 a b c : a = b * c -> b = 0 -> a = 0 := _.
    Program Definition helper44 x y z w A B C D
            (H0 : x * y^3 = A * B^3)
            (H1 : x * z^3 - B^3 * D = 0)
            (H2 : D * C^3 = w * z^3)
            (H3 : A * C^3 - y^3 * w <> 0)
            (Hz : z <> 0)
            (HB : B <> 0)
            : False := _.
    Program Definition helper45 x y z w A B C D
            (H0 : x * y^3 = A * B^3)
            (H1 : x * z^3 - B^3 * D <> 0)
            (H2 : D * C^3 = w * z^3)
            (H3 : A * C^3 - y^3 * w = 0)
            (Hy : y <> 0)
            (HC : C <> 0)
      : False := _.
    Program Definition helper46 x y z w A B C D
            (H0 : x * y^2 = A * B^2)
            (H1 : x * z^2 - D * B^2 = 0)
            (H2 : D * C^2 = w * z^2)
            (H3 : A * C^2 - w * y^2 <> 0)
            (Hz : z <> 0)
            (HB : B <> 0)
      : False := _.
    Program Definition helper47 x y z w A B C D
            (H0 : A * B^2 = x * y^2)
            (H1 : x * z^2 - D * B^2 = 0)
            (H2 : w * z^2 = D * C^2)
            (H3 : A * C^2 - w * y^2 <> 0)
            (Hz : z <> 0)
            (HB : B <> 0)
      : False := _.

    Record dyn := { ty : Prop ; lem : ty }.

    Local Notation "[ x , .. , z ]"
      := (cons {| lem := x |} .. (cons {| lem := z |} nil) .. ).

    (* grep -o 'Program Definition [^ ]*' src/Util/FsatzAutoLemmas.v  | sed s'/Program Definition /, /g' *)
    Definition all_lemmas
      := [I
          , eq_opp__eq_zero
          , neq_opp__neq_zero
          , twice_eq_zero
          , twice_neq_zero
          , inv_cube_eq_zero__neq_zero__absurd
          , sub_eq_zero_eq
          , sub_eq_zero_eq_sym
          , sub_neq_zero_eq
          , sub_neq_zero_eq_sym
          , mul3_nonzero_drop_mid
          , mul_nonzero_l
          , mul_nonzero_r
          , factor_difference_of_squares
          , expand_square_sum
          , expand_square_sum_neq
          , expand_square_sum_sub
          , expand_square_sum_sub_neq
          , factor_square_sum
          , factor_square_sum_neq
          , factor_square_sum_sub
          , factor_square_sum_sub_neq
          , mul_eq_0_r_nz
          , mul_eq_0_l_nz
          , mul_eq_0_l
          , mul_eq_0_r
          , mul_neq_0
          , helper1
          , helper2
          , helper3
          , helper4
          , helper5
          , helper6
          , helper7
          , helper8
          , helper9
          , helper10
          , helper11
          , helper12
          , helper13
          , helper14
          , helper15
          , helper16
          , helper17
          , helper18
          , helper19
          , helper20
          , helper21
          , helper22
          , helper23
          , helper24
          , helper25
          , helper26
          , helper27
          , helper28
          , helper29
          , helper30
          , helper31
          , helper32
          , helper33
          , helper34
          , helper35
          , helper36
          , helper37
          , helper38
          , helper39
          , helper40
          , helper41
          , helper42
          , helper42'
          , helper43
          , helper_zero_1
          , helper44
          , helper45
          , helper46
          , helper47
         ].
  End with_field.

  Ltac get_package_on fld :=
    let pkg := constr:(all_lemmas (field:=fld)) in
    let pkg := (eval cbv [all_lemmas] in pkg) in
    pkg.

  Ltac lookup_lemma_on pkg ty :=
    lazymatch pkg with
    | context[@Build_dyn ty ?lem] => lem
    end.

  Ltac lookup_lemma ty :=
    let fld := guess_field in
    let pkg := get_package_on fld in
    lookup_lemma_on fld ty.

  Ltac with_lemma_on pkg ty tac :=
    let H := lookup_lemma_on pkg ty in
    tac H.

  Ltac goal_exact_lemma_on pkg :=
    lazymatch goal with
    | [ |- ?G ] => with_lemma_on pkg G ltac:(fun H' => exact H')
    end.
  Ltac goal_apply_lemma_on pkg ty :=
    with_lemma_on pkg ty ltac:(fun H' => apply H').
  Ltac apply_lemma_in_on pkg H ty :=
    with_lemma_on pkg ty ltac:(fun H' => apply H' in H).
  Ltac apply2_lemma_in_on pkg H0 H1 ty :=
    with_lemma_on pkg ty ltac:(fun H' => apply H' in H0; [ | exact H1 ]).
  Ltac apply_lemma_in_on' pkg H ty preapp :=
    with_lemma_on pkg ty ltac:(fun H' => let H' := preapp H' in apply H' in H).
End F.
