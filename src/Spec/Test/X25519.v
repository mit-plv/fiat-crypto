(* Test vectors from <https://tools.ietf.org/html/rfc7748#section-5.2>,
   with hex values converted to decimal using python like this:
   > int.from_bytes(binascii.unhexlify('deadbeef'), 'little') *)
From Coq Require Import ZArith.
Require Import Spec.ModularArithmetic Spec.Curve25519 Spec.MxDH Crypto.Util.Decidable.
Definition cswap {T} (swap:bool) (a b:T) := if swap then (b, a) else (a, b).
Definition monty s : Zmod p -> Zmod p := @MxDH.montladder _ Zmod.zero Zmod.one Zmod.add Zmod.sub Zmod.mul Zmod.inv M.a24 cswap 255 (fun i => Z.testbit s (Z.of_nat i)).

Example one_basepoint : Zmod.unsigned (monty 1 (Zmod.of_Z _ 9)) = 9%Z.
Proof. vm_decide_no_check. Qed.

Example testvector_one : Zmod.unsigned (monty
   31029842492115040904895560451863089656472772604678260265531221036453811406496%Z
   (Zmod.of_Z _ 34426434033919594451155107781188821651316167215306631574996226621102155684838%Z)) = 37325765543539916631701301279660700968428932651319597985674090122993663859395%Z.
Proof. vm_decide_no_check. Qed.

Example testvector_two : Zmod.unsigned (monty
   35156891815674817266734212754503633747128614016119564763269015315466259359304%Z
   (Zmod.of_Z _ 8883857351183929894090759386610649319417338800022198945255395922347792736741%Z)) = 39566196721700740701373067725336211924689549479508623342842086701180565506965%Z.
Proof. vm_decide_no_check. Qed.

Example order_basepoint : Zmod.unsigned (monty l (Zmod.of_Z _ 9)) = 0%Z.
Proof. vm_decide_no_check. Qed. (* note: ideally we'd check that z=0 *)

Definition double x := (* takes as input affine x, returns projective x/z *)
  fst (@MxDH.ladderstep _ Zmod.add Zmod.sub Zmod.mul M.a24 (Zmod.of_Z _ 0) (x, Zmod.of_Z _ 1) (x, Zmod.of_Z _ 1)).
(* EllipticCurve(GF(2^255 - 19), [0,486662,0,1,0]).torsion_polynomial(8).roots(multiplicities=False) *)
(* Point of order 2: *)
Lemma double_zero : snd (double (Zmod.of_Z _ 0)) = Zmod.of_Z _ 0. vm_decide_no_check. Qed.
(* Points of order 4: *)
Lemma double_one  : fst (double (Zmod.of_Z _ 1)) = Zmod.of_Z _ 0. vm_decide_no_check. Qed.
Lemma double_minusone:fst(double(Zmod.of_Z _(-1)))=Zmod.of_Z _ 0. vm_decide_no_check. Qed.
(* Points of order 8: *)
Definition order8_x1 := Zmod.of_Z p 39382357235489614581723060781553021112529911719440698176882885853963445705823.
Definition order8_x2 := Zmod.of_Z p 325606250916557431795983626356110631294008115727848805560023387167927233504.
Lemma double_order8_x1 : fst (double order8_x1) = snd (double order8_x1). vm_decide_no_check. Qed.
Lemma double_order8_x2 : fst (double order8_x2) = snd (double order8_x2). vm_decide_no_check. Qed.
