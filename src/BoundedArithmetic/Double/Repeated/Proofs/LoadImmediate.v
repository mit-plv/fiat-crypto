Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.LoadImmediate.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Arguments Z.mul !_ !_.
Local Arguments Z.pow : simpl never.
Local Arguments Z.of_nat : simpl never.
Local Opaque tuple_decoder.

Section load_immediate.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {ldi : load_immediate W}
          {is_ldi : is_load_immediate ldi}.

  Fixpoint is_load_immediate_repeated_double {exp : nat} : is_load_immediate (load_immediate_repeated_double (exp:=exp)).
  Proof. is_cls_fixpoint_t decode n exp is_ldi (@is_load_immediate_repeated_double). Qed.
  Global Existing Instance is_load_immediate_repeated_double.
End load_immediate.
