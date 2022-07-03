Require Export Crypto.Util.GlobalSettings.
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
  Definition egcd_by_wf (wf : well_founded (fun x y => 0 <= x < y)) (a b : Z) : option (Z * Z * Z)
    := Fix wf (fun _ => Z -> option (Z * Z * Z))
           (fun a egcd b
            => (if (0 <? a) as b return ((0 <? a) = b -> _)
               then fun pf
                    => match @egcd (b mod a) (Z.mod_pos_bound _ _ (proj1 (Z.ltb_lt _ _) ltac:(eassumption))) a with
                      | Some (g, y, x) => Some (g, x - (b / a) * y, y)
                      | None => None
                      end
               else fun _
                    => if a =? 0
                      then Some (b, 0, 1)
                      else None) eq_refl)
           a b.
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
  Definition modinv_by_wf (wf : well_founded (fun x y => 0 <= x < y)) (a m : Z) : option Z
    := if a <? 0
       then match egcd_by_wf wf (-a) m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some ((-x) mod m)
            | None => None
            end
       else match egcd_by_wf wf a m with
            | Some (g, x, y)
              => if negb (g =? 1)
                 then None
                 else Some (x mod m)
            | None => None
            end.
  Definition modinv_by_wf_fuel (fuel : nat) (a m : Z) : option Z
    := modinv_by_wf (Acc_intro_generator fuel (Z.lt_wf 0)) a m.
  (** We way over-estimate the fuel by taking [max a m].  We can assume
    that [Z.to_nat (Z.log2 (max a m))] is fast, because we already
    have a ~unary representation of [Z.log2 a] and [Z.log2 m].  It is
    empirically the case that pulling successors off [2^k] is fast, so
    we can use that for fuel. *)
  Definition modinv' (a m : Z) : option Z
    := modinv_fueled (2^Z.to_nat (Z.log2 (Z.max a m))) a m.
  (** For the actual version, which we want to perform well under
      [cbv], we will simply add the log2 representations of [a] and
      [m].  We expect to pull at least about 1 bit off the top each
      round of the gcd calculation. *)
  Definition modinv (a m : Z) : option Z
    := modinv_by_wf (Acc_intro_generator (S (S (Z.to_nat (Z.log2_up (Z.abs a) + Z.log2_up (Z.abs m))))) (Z.lt_wf 0)) a m.
End Z.
