Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).
Local Open Scope sep_scope.

(* Parameters for p224 field. *)
Section Field.
  Definition n : nat := 4.
  Definition m : Z := (2^224 - 2^96 + 1)%Z.

  Existing Instances Defaults32.default_parameters
           Defaults32.default_parameters_ok.
  Definition prefix : string := "p224_"%string.

  (* Define p224 field *)
  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (m))) in
    (* curve 'A' parameter *)
    let a := constr:(F.of_Z M (m - 3)) in
    let prefix := constr:("p224_felem_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Call fiat-crypto pipeline on all field operations *)
  Instance p224_ops : @word_by_word_Montgomery_ops from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _ _ _ _ (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.


  Goal False.
    Local Notation ttype := Language.Compilers.type.type.
    Local Notation tbase := Language.Compilers.type.base.
    Local Notation ttype_base := Language.Compilers.base.type.type_base.
    Local Notation btype := Language.Compilers.base.type.type.
    Local Notation blist := Language.Compilers.base.type.list.
    Require Import IdentifiersBasicGENERATED.
    Local Notation eAbs := Language.Compilers.expr.Abs.
    Local Notation eApp := Language.Compilers.expr.App.
    Local Notation eVar := Language.Compilers.expr.Var.
    Local Notation eLetIn := Language.Compilers.expr.LetIn.
    Local Notation eIdent := Language.Compilers.expr.Ident.
    pose add_op.
    cbn [add_op p224_ops] in c.

  Abort.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

        Local Ltac begin_derive_bedrock2_func :=
        lazymatch goal with
        | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
        | |- context [spec_of_UnOp un_square] => eapply square_func_correct
        | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
        | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
        | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
        (* | |- context [spec_of_UnOp un_scmula24] => eapply scmula24_func_correct *)
        | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
        | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
        end.

      Ltac derive_bedrock2_func op :=
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


      Require Import Crypto.Language.API.
      Import API.Compilers.
      Print Func.valid_func_bool.
      Locate API.expr.
      Definition cmd_bool
                 {t} (e : @API.expr (fun _ => unit) t) : bool :=
        match e return bool with
        | expr.LetIn
            (type.base (base.type.prod
                          (base.type.type_base a)
                          (base.type.type_base b)))
            (type.base c) x f =>
          true
        | expr.LetIn
            (type.base (base.type.type_base a))
            (type.base b) x f =>
          true
        | expr.App (type.base s) _ f x =>
          true
        | expr.Ident _ i => true
        | _ => false
        end.
      Fixpoint func_bool {t} (e : @API.expr (fun _ => unit) t) : bool :=
        match e with
        | expr.Abs _ _ f =>func_bool (f tt)
        | _ => cmd_bool e
        end.
      Lemma valid_expr_bool_if_base_LetIn {A B} (x : API.expr A) (f : unit -> API.expr B) :
        Cmd.valid_expr_bool_if_base (expr.LetIn x f) = false.
      Proof.
        cbv [Cmd.valid_expr_bool_if_base].
        destruct B; reflexivity.
      Qed.
      
  Derive p224_add
         SuchThat (forall functions,
                      Cmd.spec_of_add_carryx (add_carryx:=Defaults.add_carryx) functions ->
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation m)
                        (p224_add :: functions))
         As p224_add_correct.
  Proof.
    begin_derive_bedrock2_func.
    4:{
      eapply Func.valid_func_bool_iff.
      cbn [add_op p224_ops res].
      cbv [Func.valid_func_bool].
      repeat  lazymatch goal with
              | |- context [Func.valid_cmd_bool_if_base (eAbs ?x)] =>
                change (Func.valid_cmd_bool_if_base (eAbs x)) with false
              end.
      cbv [Func.valid_cmd_bool_if_base].
      cbv [Cmd.valid_cmd_bool].
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite valid_expr_bool_if_base_LetIn.
      rewrite !valid_expr_bool_if_base_LetIn.
      Set Printing Depth 100000.
      repeat match goal with
             | |- context [Cmd.valid_expr_bool_if_base ?x] =>
               change (Cmd.valid_expr_bool_if_base x) with false
             end.
      cbn iota.
      cbv [Cmd.valid_cons_App1_bool
             Cmd.valid_cons_App2_bool
             Cmd.is_cons_ident
             Cmd.is_nil_ident].
      repeat lazymatch goal with
             | |- context [Expr.valid_expr_bool true ?x] =>
               change (Expr.valid_expr_bool true x) with true
             end.
      cbn [orb andb].
      lazymatch goal with
      | |- context [Expr.valid_expr_bool true ?x] =>
        pose (e:=Expr.valid_expr_bool true x);
          assert (Expr.valid_expr true x)
      end.
      {
        lazy in e.
        Unset Printing Notations.
        repeat lazymatch goal with
               | |- Expr.valid_expr
                     _ (expr.App (expr.App (expr.Ident Compilers.ident_Z_cast) _)  _) =>
                 apply Expr.valid_cast1; [ | reflexivity .. ]
               | |- Expr.valid_expr _ (expr.Var _) =>
                 apply Expr.valid_var_z
               | _ => apply Expr.valid_binop; [ cbn; congruence | | ]
               end.
        Print Expr.valid_expr.
        (* zselect recursively calls valid_expr, which now fails because of the [0,1] bound *)
      cbv in e.
    Locate begin_derive_bedrock2_func.
    Time derive_bedrock2_func add_op.
  Qed.
  Print p224_add.

  Derive p224_from_bytes
         SuchThat (forall functions,
                      spec_of_from_bytes
                        (field_representation:=field_representation_raw m)
                        (p224_from_bytes :: functions))
         As p224_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive p224_to_bytes
         SuchThat (forall functions,
                      spec_of_to_bytes
                        (field_representation:=field_representation_raw m)
                        (p224_to_bytes :: functions))
         As p224_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive p224_mul
         SuchThat (forall functions,
                      spec_of_BinOp bin_mul
                        (field_representation:=field_representation m)
                        (p224_mul :: functions))
         As p224_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive p224_square
         SuchThat (forall functions,
                      spec_of_UnOp un_square
                        (field_representation:=field_representation m)
                        (p224_square :: functions))
         As p224_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive p224_add
         SuchThat (forall functions,
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation m)
                        (p224_add :: functions))
         As p224_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive p224_sub
         SuchThat (forall functions,
                      spec_of_BinOp bin_sub
                        (field_representation:=field_representation m)
                        (p224_sub :: functions))
         As p224_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  (*TODO: adapt derive_bedrock2_func to also derive the remaining functions.*)
  Derive p224_from_mont
         SuchThat (forall functions,
                      spec_of_UnOp un_from_mont
                        (field_representation:=field_representation m)
                        (p224_from_mont :: functions))
         As p224_from_mont_correct.
  Proof.
    eapply (from_mont_func_correct _ _ _ from_mont_string to_mont_string).
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve.
            + auto.
            + auto.
  Qed.

  Derive p224_to_mont
         SuchThat (forall functions,
                      spec_of_UnOp un_to_mont
                        (field_representation:=field_representation m)
                        (p224_to_mont :: functions))
         As to_from_mont_correct.
  Proof.
    eapply (to_mont_func_correct _ _ _ from_mont_string to_mont_string).
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve. all: auto.
     Qed.

  Derive p224_select_znz
           SuchThat (forall functions,
                      spec_of_selectznz
                        (field_representation:=field_representation m)
                        (p224_select_znz :: functions))
         As select_znz_correct.
  Proof.
    eapply select_znz_func_correct. 1,2:auto.
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
     Qed.
End Field.
