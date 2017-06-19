(*** Compute the modular inverse of a ℤ *)
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.
Module Z.
  (** Quoting https://stackoverflow.com/a/9758173:
<<
def egcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)

def modinv(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    else:
        return x % m
>> *)
  (** We run on fuel, because the well-foundedness lemmas for [Z] are
    opaque, so we can't use them to compute. *)
  Fixpoint egcd (fuel : nat) (a b : Z) : option (Z * Z * Z)
    := match fuel with
       | O => None
       | S fuel'
         => if a <? 0
            then None
            else if a =? 0
                 then Some (b, 0, 1)
                 else
                   match @egcd fuel' (b mod a) a with
                   | Some (g, y, x) => Some (g, x - (b / a) * y, y)
                   | None => None
                   end
       end.
  Definition modinv_fueled (fuel : nat) (a m : Z) : option Z
    := if a <? 0
       then match egcd fuel (-a) m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some ((-x) mod m)
            | None => None
            end
       else match egcd fuel a m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some (x mod m)
            | None => None
            end.
  (** We way over-estimate the fuel by taking [max a m].  We can assume
    that [Z.to_nat (Z.log2 (max a m))] is fast, because we already
    have a ~unary representation of [Z.log2 a] and [Z.log2 m].  It is
    empirically the case that pulling successors off [2^k] is fast, so
    we can use that for fuel. *)
  Definition modinv (a m : Z) : option Z
    := modinv_fueled (2^Z.to_nat (Z.log2 (Z.max a m))) a m.
End Z.
