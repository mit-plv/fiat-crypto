Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.

(* Parameters for Secp256k1 field. *)
Section Field.
  Definition m : Z := (2^256 - 2^32 - 977)%Z.

  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok.
  Definition prefix : string := "secp256k1_"%string.

  (* Define Secp256k1 field *)
  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (m))) in
    (* 'A' parameter *)
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("secp256k1_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a + F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Definition to_mont_string := (prefix ++ "to_mont")%string.
  Definition from_mont_string := (prefix ++ "from_mont")%string.

  (* Call fiat-crypto pipeline on all field operations *)
  Instance secp256k1_ops : @word_by_word_Montgomery_ops from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _ (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

  Local Ltac begin_derive_bedrock2_func :=
        lazymatch goal with
        | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
        | |- context [spec_of_UnOp un_square] => eapply square_func_correct
        | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
        | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
        | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
        | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
        | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
        | |- context [spec_of_selectznz] => eapply select_znz_func_correct
        | |- context [spec_of_felem_copy] => eapply felem_copy_func_correct
        | |- context [spec_of_UnOp un_from_mont] => eapply (from_mont_func_correct _ _ _ from_mont_string to_mont_string)
        | |- context [spec_of_UnOp un_to_mont] => eapply (to_mont_func_correct _ _ _ from_mont_string to_mont_string)
        end.

  Ltac epair :=
    lazymatch goal with
    | f := _ : string * Syntax.func |- _ =>
             let p := open_constr:((_, _)) in
             unify f p;
             subst f
    end.

  Ltac derive_bedrock2_func op :=
    epair;
    begin_derive_bedrock2_func;
    (* this goal fills in the evar, so do it first for [abstract] to be happy *)
    try lazymatch goal with
      | |- _ = b2_func _ => vm_compute; reflexivity
      end;
    (* solve all the remaining goals *)
    lazymatch goal with
    | |- _ = @ErrorT.Success ?ErrT unit tt =>
        abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
    | |- Func.valid_func _ =>
        eapply Func.valid_func_bool_iff;
        abstract vm_cast_no_check (eq_refl true)
    | |- (_ = _)%Z => vm_compute; reflexivity
    end.

  Local Notation functions_contain functions f :=
    (Interface.map.get functions (fst f) = Some (snd f)).

  Derive secp256k1_felem_copy
         SuchThat (forall functions,
                      functions_contain functions secp256k1_felem_copy ->
                      spec_of_felem_copy
                        (field_representation:=field_representation_raw m)
                        functions)
         As secp256k1_felem_copy_correct.
  Proof. Time derive_bedrock2_func felem_copy_op. Qed.

  Derive secp256k1_from_bytes
         SuchThat (forall functions,
                      functions_contain functions secp256k1_from_bytes ->
                      spec_of_from_bytes
                        (field_representation:=field_representation_raw m)
                        functions)
         As secp256k1_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive secp256k1_to_bytes
         SuchThat (forall functions,
                      functions_contain functions secp256k1_to_bytes ->
                      spec_of_to_bytes
                        (field_representation:=field_representation_raw m)
                        functions)
         As secp256k1_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive secp256k1_opp
         SuchThat (forall functions,
                      functions_contain functions secp256k1_opp ->
                      spec_of_UnOp un_opp
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_opp_correct.
  Proof. Time derive_bedrock2_func opp_op. Qed.

  Derive secp256k1_mul
         SuchThat (forall functions,
                      functions_contain functions secp256k1_mul ->
                      spec_of_BinOp bin_mul
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive secp256k1_square
         SuchThat (forall functions,
                      functions_contain functions secp256k1_square ->
                      spec_of_UnOp un_square
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive secp256k1_add
         SuchThat (forall functions,
                      functions_contain functions secp256k1_add ->
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive secp256k1_sub
         SuchThat (forall functions,
                      functions_contain functions secp256k1_sub ->
                      spec_of_BinOp bin_sub
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  Derive secp256k1_select_znz
           SuchThat (forall functions,
                      functions_contain functions secp256k1_select_znz ->
                      spec_of_selectznz
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_select_znz_correct.
  Proof. Time derive_bedrock2_func select_znz_op. Qed.

  Derive secp256k1_from_mont
         SuchThat (forall functions,
                      functions_contain functions secp256k1_from_mont ->
                      spec_of_UnOp un_from_mont
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_from_mont_correct.
  Proof. Time derive_bedrock2_func from_mont_op. Unshelve. 1,2: auto. Qed.

  Derive secp256k1_to_mont
         SuchThat (forall functions,
                      functions_contain functions secp256k1_to_mont ->
                      spec_of_UnOp un_to_mont
                        (field_representation:=field_representation m)
                        functions)
         As secp256k1_to_mont_correct.
  Proof. Time derive_bedrock2_func to_mont_op. Unshelve. 1,2: auto. Qed.

  #[export] Instance frep256k1_ok : FieldRepresentation_ok(field_representation:=field_representation m).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    auto.
  Qed.
End Field.

(* Require Import bedrock2.Syntax. *)

(* Definition funcs : list (string * func) := *)
(*   [ secp256k1_opp; *)
(*     secp256k1_mul; *)
(*     secp256k1_add; *)
(*     secp256k1_sub; *)
(*     secp256k1_square; *)
(*     secp256k1_to_bytes; *)
(*     secp256k1_from_bytes; *)
(*     secp256k1_from_mont; *)
(*     secp256k1_to_mont; *)
(*     secp256k1_select_znz *)
(*   ]. *)

(* Compute ToCString.c_module funcs. *)
