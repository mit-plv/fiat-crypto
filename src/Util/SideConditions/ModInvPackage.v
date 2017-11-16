Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.SideConditions.CorePackages.

Local Open Scope Z_scope.

Definition modinv_evar_package (modinv_fuel : nat) (a modulus : Z)
  := evar_Prop_package
       (fun a' => (a * a') mod modulus = 1).

Ltac autosolve else_tac :=
  lazymatch goal with
  | [ |- modinv_evar_package ?modinv_fuel ?a ?modulus ]
    => let v0 := constr:(Option.invert_Some (Z.modinv_fueled modinv_fuel a modulus)) in
       let v := (eval vm_compute in v0) in
       let v := lazymatch type of v with (* if the computation failed, display a reasonable error message about the attempted computation *)
                | Z => v
                | _ => (eval cbv -[Option.invert_Some Z.modinv_fueled] in v0)
                end in
       let v := (eval vm_compute in (v <: Z)) in
       (exists v); vm_compute; reflexivity
  | _ => else_tac ()
  end.
