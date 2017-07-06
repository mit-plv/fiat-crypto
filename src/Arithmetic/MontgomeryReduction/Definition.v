(*** Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [Z].  We follow Wikipedia. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.
Delimit Scope montgomery_naive_scope with montgomery_naive.
Delimit Scope montgomery_scope with montgomery.
Definition montgomeryZ := Z.
Bind Scope montgomery_scope with montgomeryZ.

Section montgomery.
  Context (N : Z)
          (R : Z)
          (R' : Z). (* R' is R⁻¹ mod N *)
  Local Notation "x ≡ y" := (Z.equiv_modulo N x y) : type_scope.
  Local Notation "x ≡ᵣ y" := (Z.equiv_modulo R x y) : type_scope.
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

  Definition to_montgomery_naive (x : Z) : montgomeryZ := x * R.
  Definition from_montgomery_naive (x : montgomeryZ) : Z := x * R'.

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
    Context (N' : Z). (* N' is (-N⁻¹) mod R *)
    Section redc.
      Context (T : Z).

      Let m := ((T mod R) * N') mod R.
      Let t := (T + m * N) / R.
      Definition prereduce : montgomeryZ := t.

      Definition partial_reduce : montgomeryZ
        := if R <=? t then
             prereduce - N
           else
             prereduce.

      Definition partial_reduce_alt : montgomeryZ
        := let v0 := (T + m * N) in
           let v := (v0 mod (R * R)) / R in
           if R * R <=? v0 then
             (v - N) mod R
           else
             v.

      Definition reduce : montgomeryZ
        := if N <=? t then
             prereduce - N
           else
             prereduce.

      Definition reduce_via_partial : montgomeryZ
        := if N <=? partial_reduce then
             partial_reduce - N
           else
             partial_reduce.

      Definition reduce_via_partial_alt : montgomeryZ
        := if N <=? partial_reduce_alt then
             partial_reduce_alt - N
           else
             partial_reduce_alt.
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
    End arithmetic.
  End redc.
End montgomery.

Infix "+" := add : montgomery_scope.
Infix "-" := sub : montgomery_scope.
Infix "*" := mul_naive : montgomery_naive_scope.
Infix "*" := mul : montgomery_scope.
