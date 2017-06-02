(* Test vectors from <https://tools.ietf.org/html/rfc7748#section-5.2>,
   with hex values converted to decimal using python like this:
   > int.from_bytes(binascii.unhexlify('deadbeef'), 'little') *)
Require Import Spec.ModularArithmetic Spec.MxDH Crypto.Util.Decidable.
Definition F := F (2^255 - 19).
Definition a : F := F.of_Z _ 486662.
Definition a24 : F := ((a - F.of_Z _ 2) / F.of_Z _ 4)%F.
Definition cswap {T} (swap:bool) (a b:T) := if swap then (b, a) else (a, b).
Definition monty s : F -> F := @MxDH.montladder F F.zero F.one F.add F.sub F.mul F.inv a24 cswap 255 (BinNat.N.testbit_nat s).

Example one_basepoint : F.to_Z (monty 1 (F.of_Z _ 9)) = 9%Z.
Proof. vm_decide_no_check. Qed.

Example testvector_one : F.to_Z (monty
   31029842492115040904895560451863089656472772604678260265531221036453811406496%N
   (F.of_Z _ 34426434033919594451155107781188821651316167215306631574996226621102155684838%Z)) = 37325765543539916631701301279660700968428932651319597985674090122993663859395%Z.
Proof. vm_decide_no_check. Qed.

Example testvector_two : F.to_Z (monty
   35156891815674817266734212754503633747128614016119564763269015315466259359304%N
   (F.of_Z _ 8883857351183929894090759386610649319417338800022198945255395922347792736741%Z)) = 39566196721700740701373067725336211924689549479508623342842086701180565506965%Z.
Proof. vm_decide_no_check. Qed.
