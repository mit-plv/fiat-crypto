Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Rewriter.TestRules.

Local Ltac start_proof :=
  cbv [snd]; hnf; cbv [PrimitiveHList.hlist];
  repeat apply PrimitiveProd.Primitive.pair; try exact tt.
Lemma test_rewrite_rules_proofs
  : PrimitiveHList.hlist (@snd bool Prop) test_rewrite_rulesT.
Proof using Type.
  start_proof.
  all: try reflexivity.
  (** If testing out rules, change Qed to Admitted *)
Qed.
(*
Admitted.
*)
