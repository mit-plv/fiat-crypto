Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Util.Sigma.Lift.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.BinPos.

Definition wt (i:nat) : Z := Z.shiftl 1 (64*Z.of_nat i).
Definition r := Eval compute in (2^64)%positive.
Definition sz := 4%nat.
Definition p256 :=
  Eval vm_compute in
    ((Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (2^256-2^224+2^192+2^96-1))).

Definition mulmod_256 : { f:Tuple.tuple Z 4 -> Tuple.tuple Z 4 -> Tuple.tuple Z 5
                           | forall (A B : Tuple.tuple Z 4),
                               f A B =
                               (redc (r:=r)(R_numlimbs:=4) p256 A B 1)
                            }.
Proof.
  eapply (lift2_sig (fun A B c => c = (redc (r:=r)(R_numlimbs:=4) p256 A B 1)
                           )); eexists.
  cbv [
      r wt sz p256
       CPSUtil.to_list_cps CPSUtil.to_list'_cps CPSUtil.to_list_cps' CPSUtil.flat_map_cps CPSUtil.fold_right_cps
       CPSUtil.map_cps CPSUtil.Tuple.left_append_cps CPSUtil.firstn_cps CPSUtil.combine_cps CPSUtil.on_tuple_cps CPSUtil.update_nth_cps CPSUtil.from_list_default_cps CPSUtil.from_list_default'_cps
       fst snd length List.seq List.hd List.app
       redc redc_cps redc_loop_cps redc_body_cps
       Positional.to_associational_cps
       Saturated.divmod_cps
       Saturated.scmul_cps
       Saturated.uweight
       Saturated.Columns.mul_cps
       Saturated.Associational.mul_cps
       Z.of_nat Pos.of_succ_nat  Nat.pred
       Z.pow Z.pow_pos Z.mul Pos.iter Pos.mul Pos.succ
       Saturated.Columns.from_associational_cps
       (*
       Saturated.Associational.multerm_cps
       Saturated.Columns.from_associational_cps Positional.place_cps Saturated.Columns.cons_to_nth_cps Saturated.Columns.nils
Tuple.append
Tuple.from_list Tuple.from_list'
Tuple.from_list_default Tuple.from_list_default'
Tuple.hd
Tuple.repeat
Tuple.tl
Tuple.tuple *)
       (* Saturated.add_cps Saturated.divmod_cps Saturated.drop_high_cps Saturated.scmul_cps Saturated.zero Saturated.Columns.mul_cps Saturated.Columns.add_cps Saturated.uweight Saturated.T *)
            (*
            CPSUtil.to_list_cps CPSUtil.to_list'_cps CPSUtil.to_list_cps'
Positional.zeros
Tuple.to_list
Tuple.to_list'
List.hd
List.tl
Nat.max
Positional.to_associational_cps
Z.of_nat *)
      ].
  (* stuck on [("fix app" ... ) (cps_returned_opaque_list) _] *)
  cbv [Decidable.dec Decidable.dec_eq_Z Z.eq_dec Z.modulo].
  cbv [List.app].
  (* cbv -[runtime_add runtime_mul LetIn.Let_In Definitions.Z.add_get_carry_full Definitions.Z.mul_split]. *)

  (* basesystem_partial_evaluation_RHS. *)
Abort.
