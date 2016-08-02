(*** Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [Z].  We follow Wikipedia. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Structures.Equalities.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Declare Module Nop : Nop.
Module Import ImportEquivModuloInstances := Z.EquivModuloInstances Nop.

Local Existing Instance eq_Reflexive. (* speed up setoid_rewrite as per https://coq.inria.fr/bugs/show_bug.cgi?id=4978 *)

Local Open Scope Z_scope.
Delimit Scope montgomery_naive_scope with montgomery_naive.
Delimit Scope montgomery_scope with montgomery.
Definition montgomeryZ := Z.
Bind Scope montgomery_scope with montgomeryZ.

Section montgomery.
  Context (N : Z)
          (N_reasonable : N <> 0)
          (R : Z)
          (R_good : Z.gcd N R = 1).
  Local Notation "x ≡ y" := (Z.equiv_modulo N x y) : type_scope.
  Local Notation "x ≡ᵣ y" := (Z.equiv_modulo R x y) : type_scope.
  Context (R' : Z)
          (R'_good : R * R' ≡ 1).
  (** Quoting Wikipedia <https://en.wikipedia.org/wiki/Montgomery_modular_multiplication>: *)
  (** In modular arithmetic computation, Montgomery modular
      multiplication, more commonly referred to as Montgomery
      multiplication, is a method for performing fast modular
      multiplication, introduced in 1985 by the American mathematician
      Peter L. Montgomery. *)
  (** Given two integers [a] and [b], the classical modular
      multiplication algorithm computes [ab mod N]. Montgomery
      multiplication works by transforming [a] and [b] into a special
      representation known as Montgomery form. For a modulus [N], the
      Montgomery form of [a] is defined to be [aR mod N] for some
      constant [R] depending only on [N] and the underlying computer
      architecture. If [aR mod N] and [bR mod N] are the Montgomery
      forms of [a] and [b], then their Montgomery product is [abR mod
      N]. Montgomery multiplication is a fast algorithm to compute the
      Montgomery product. Transforming the result out of Montgomery
      form yields the classical modular product [ab mod N]. *)

  Lemma R'_good' : R' * R ≡ 1.
  Proof. rewrite <- R'_good; apply f_equal2; lia. Qed.

  Definition to_montgomery_naive (x : Z) : montgomeryZ := x * R.
  Definition from_montgomery_naive (x : montgomeryZ) : Z := x * R'.
  Lemma to_from_montgomery_naive x : to_montgomery_naive (from_montgomery_naive x) ≡ x.
  Proof.
    unfold to_montgomery_naive, from_montgomery_naive.
    rewrite <- Z.mul_assoc, R'_good'.
    autorewrite with zsimplify; reflexivity.
  Qed.
  Lemma from_to_montgomery_naive x : from_montgomery_naive (to_montgomery_naive x) ≡ x.
  Proof.
    unfold to_montgomery_naive, from_montgomery_naive.
    rewrite <- Z.mul_assoc, R'_good.
    autorewrite with zsimplify; reflexivity.
  Qed.

  (** * Modular arithmetic and Montgomery form *)
  Section general.
    (** Addition and subtraction in Montgomery form are the same as
        ordinary modular addition and subtraction because of the
        distributive law: *)
    (** [aR + bR = (a+b)R], *)
    (** [aR - bR = (a-b)R]. *)
    (** This is a consequence of the fact that, because [gcd(R, N) =
        1], multiplication by [R] is an isomorphism on the additive
        group [ℤ/Nℤ]. *)

    Definition add : montgomeryZ -> montgomeryZ -> montgomeryZ := fun aR bR => aR + bR.
    Definition sub : montgomeryZ -> montgomeryZ -> montgomeryZ := fun aR bR => aR - bR.
    Local Infix "+" := add : montgomery_scope.
    Local Infix "-" := sub : montgomery_scope.

    Lemma add_correct_naive x y : from_montgomery_naive (x + y) = from_montgomery_naive x + from_montgomery_naive y.
    Proof. unfold from_montgomery_naive, add; lia. Qed.
    Lemma add_correct_naive_to x y : to_montgomery_naive (x + y) = (to_montgomery_naive x + to_montgomery_naive y)%montgomery.
    Proof. unfold to_montgomery_naive, add; lia. Qed.
    Lemma sub_correct_naive x y : from_montgomery_naive (x - y) = from_montgomery_naive x - from_montgomery_naive y.
    Proof. unfold from_montgomery_naive, sub; lia. Qed.
    Lemma sub_correct_naive_to x y : to_montgomery_naive (x - y) = (to_montgomery_naive x - to_montgomery_naive y)%montgomery.
    Proof. unfold to_montgomery_naive, sub; lia. Qed.

    (** Multiplication in Montgomery form, however, is seemingly more
        complicated. The usual product of [aR] and [bR] does not
        represent the product of [a] and [b] because it has an extra
        factor of R: *)
    (** [(aR mod N)(bR mod N) mod N = (abR)R mod N]. *)
    (** Computing products in Montgomery form requires removing the
        extra factor of [R]. While division by [R] is cheap, the
        intermediate product [(aR mod N)(bR mod N)] is not divisible
        by [R] because the modulo operation has destroyed that
        property. *)
    (** Removing the extra factor of R can be done by multiplying by
        an integer [R′] such that [RR' ≡ 1 (mod N)], that is, by an
        [R′] whose residue class is the modular inverse of [R] mod
        [N]. Then, working modulo [N], *)
    (** [(aR mod N)(bR mod N)R' ≡ (aR)(bR)R⁻¹ ≡ (ab)R  (mod N)]. *)

    Definition mul_naive : montgomeryZ -> montgomeryZ -> montgomeryZ
      := fun aR bR => aR * bR * R'.
    Local Infix "*" := mul_naive : montgomery_scope.

    Theorem mul_correct_naive x y : from_montgomery_naive (x * y) = from_montgomery_naive x * from_montgomery_naive y.
    Proof. unfold from_montgomery_naive, mul_naive; lia. Qed.
    Theorem mul_correct_naive_to x y : to_montgomery_naive (x * y) ≡ (to_montgomery_naive x * to_montgomery_naive y)%montgomery.
    Proof.
      unfold to_montgomery_naive, mul_naive.
      rewrite <- !Z.mul_assoc, R'_good.
      autorewrite with zsimplify; apply (f_equal2 Z.modulo); lia.
    Qed.
  End general.

  (** * The REDC algorithm *)
  Section redc.
    (** While the above algorithm is correct, it is slower than
        multiplication in the standard representation because of the
        need to multiply by [R′] and divide by [N]. Montgomery
        reduction, also known as REDC, is an algorithm that
        simultaneously computes the product by [R′] and reduces modulo
        [N] more quickly than the naive method. The speed is because
        all computations are done using only reduction and divisions
        with respect to [R], not [N]: *)
    (**
<<
function REDC is
    input: Integers R and N with gcd(R, N) = 1,
           Integer N′ in [0, R − 1] such that NN′ ≡ −1 mod R,
           Integer T in the range [0, RN − 1]
    output: Integer S in the range [0, N − 1] such that S ≡ TR⁻¹ mod N

    m ← ((T mod R)N′) mod R
    t ← (T + mN) / R
    if t ≥ N then
        return t − N
    else
        return t
    end if
end function
>> *)
    Context (N' : Z)
            (N'_in_range : 0 <= N' < R)
            (N'_good : N * N' ≡ᵣ -1).
    Section redc.
      Context (T : Z).

      Lemma N'_good' : N' * N ≡ᵣ -1.
      Proof. rewrite <- N'_good; apply f_equal2; lia. Qed.

      Let m := ((T mod R) * N') mod R.
      Let t := (T + m * N) / R.
      Definition reduce : montgomeryZ
        := if N <=? t then
             t - N
           else
             t.

      Lemma N'_good'_alt x : (((x mod R) * (N' mod R)) mod R) * (N mod R) ≡ᵣ x * -1.
      Proof.
        rewrite <- N'_good', Z.mul_assoc.
        unfold Z.equiv_modulo; push_Zmod.
        reflexivity.
      Qed.

      Lemma reduce_correct_helper : t ≡ T * R'.
      Proof.
        transitivity ((T + m * N) * R').
        { subst t m.
          autorewrite with zstrip_div; push_Zmod.
          rewrite N'_good'_alt.
          autorewrite with zsimplify pull_Zmod.
          reflexivity. }
        unfold Z.equiv_modulo; push_Zmod; autorewrite with zsimplify; reflexivity.
      Qed.

      Lemma reduce_correct : reduce ≡ T * R'.
      Proof.
        unfold reduce.
        break_match; rewrite reduce_correct_helper; unfold Z.equiv_modulo;
          autorewrite with push_Zmod zsimplify; reflexivity.
      Qed.

      Lemma reduce_in_range : 0 <= T < R * N -> 0 <= reduce < N.
      Proof.
        intro.
        assert (0 <= m < R) by (subst m; auto with zarith).
        assert (0 <= T + m * N < 2 * R * N) by nia.
        assert (0 <= t < 2 * N) by (subst t; auto with zarith lia).
        unfold reduce; break_match; Z.ltb_to_lt; nia.
      Qed.
    End redc.

    (** * Arithmetic in Montgomery form *)
    Section arithmetic.
      (** Many operations of interest modulo [N] can be expressed
          equally well in Montgomery form. Addition, subtraction,
          negation, comparison for equality, multiplication by an
          integer not in Montgomery form, and greatest common divisors
          with [N] may all be done with the standard algorithms. *)
      (** When [R > N], most other arithmetic operations can be
          expressed in terms of REDC. This assumption implies that the
          product of two representatives [mod N] is less than [RN],
          the exact hypothesis necessary for REDC to generate correct
          output. In particular, the product of [aR mod N] and [bR mod
          N] is [REDC((aR mod N)(bR mod N))]. The combined operation
          of multiplication and REDC is often called Montgomery
          multiplication. *)
      Definition mul : montgomeryZ -> montgomeryZ -> montgomeryZ
        := fun aR bR => reduce (aR * bR).
      Local Infix "*" := mul : montgomery_scope.

      (** Conversion into Montgomery form is done by computing
          [REDC((a mod N)(R² mod N))]. Conversion out of Montgomery
          form is done by computing [REDC(aR mod N)]. The modular
          inverse of [aR mod N] is [REDC((aR mod N)⁻¹(R³ mod
          N))]. Modular exponentiation can be done using
          exponentiation by squaring by initializing the initial
          product to the Montgomery representation of 1, that is, to
          [R mod N], and by replacing the multiply and square steps by
          Montgomery multiplies. *)
      Definition to_montgomery (a : Z) : montgomeryZ := reduce (a * (R*R mod N)).
      Definition from_montgomery (aR : montgomeryZ) : Z := reduce aR.
      Lemma to_from_montgomery a : to_montgomery (from_montgomery a) ≡ a.
      Proof.
        unfold to_montgomery, from_montgomery.
        transitivity ((a * 1) * 1); [ | apply f_equal2; lia ].
        rewrite <- !R'_good, !reduce_correct.
        unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
        apply f_equal2; lia.
      Qed.
      Lemma from_to_montgomery a : from_montgomery (to_montgomery a) ≡ a.
      Proof.
        unfold to_montgomery, from_montgomery.
        rewrite !reduce_correct.
        transitivity (a * ((R * (R * R' mod N) * R') mod N)).
        { unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
          apply f_equal2; lia. }
        { repeat first [ rewrite R'_good
                       | reflexivity
                       | push_Zmod; pull_Zmod; progress autorewrite with zsimplify
                       | progress unfold Z.equiv_modulo ]. }
      Qed.

      Theorem mul_correct x y : from_montgomery (x * y) ≡ from_montgomery x * from_montgomery y.
      Proof.
        unfold from_montgomery, mul.
        rewrite !reduce_correct; apply f_equal2; lia.
      Qed.
      Theorem mul_correct_to x y : to_montgomery (x * y) ≡ (to_montgomery x * to_montgomery y)%montgomery.
      Proof.
        unfold to_montgomery, mul.
        rewrite !reduce_correct.
        transitivity (x * y * R * 1 * 1 * 1);
          [ rewrite <- R'_good at 1
          | rewrite <- R'_good at 1 2 3 ];
          autorewrite with zsimplify;
          unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
        { apply f_equal2; lia. }
        { apply f_equal2; lia. }
      Qed.
    End arithmetic.
  End redc.
End montgomery.

Infix "+" := add : montgomery_scope.
Infix "-" := sub : montgomery_scope.
Infix "*" := mul_naive : montgomery_naive_scope.
Infix "*" := mul : montgomery_scope.

Module Import LocalizeEquivModuloInstances := Z.RemoveEquivModuloInstances Nop.
