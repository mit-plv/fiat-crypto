Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Signature.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Language.API.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Import ListNotations API.Compilers Types.Notations.
Import Language.Wf.Compilers.

Record computed_op
      {p : Types.parameters} {t}
      {op : Pipeline.ErrorT (API.Expr t)}
      {name : String.string}
      {insizes outsizes inlengths}
  :=
  { res : API.Expr t;
    b2_func : func;
    res_eq : op = ErrorT.Success res;
    func_eq :
      b2_func = make_bedrock_func
                  name insizes outsizes inlengths res;
  }.
Global Arguments computed_op {_} {_}.

Class unsaturated_solinas_ops
           {p : Types.parameters}
           {field_parameters : FieldParameters}
           {n s c machine_wordsize} : Type :=
  { mul_op :
      computed_op
        (UnsaturatedSolinas.carry_mul n s c machine_wordsize) Field.mul
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    add_op :
      computed_op
        (UnsaturatedSolinas.add n s c machine_wordsize) Field.add
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    sub_op :
      computed_op
        (UnsaturatedSolinas.sub n s c machine_wordsize) Field.sub
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    opp_op :
      computed_op
        (UnsaturatedSolinas.opp n s c machine_wordsize) Field.opp
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    square_op :
      computed_op
        (UnsaturatedSolinas.carry_square n s c machine_wordsize)
        Field.square
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    scmula24_op :
      computed_op
        (UnsaturatedSolinas.carry_scmul_const n s c Semantics.width
                                              (F.to_Z a24)) Field.scmula24
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    (* TODO: need bytes insizes/outsizes/lengths from Signature.v *)
    (*
    to_bytes_op :
      computed_op
        (UnsaturatedSolinas.to_bytes n s c Semantics.width) Field.to_bytes
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    from_bytes_op :
      computed_op
        (UnsaturatedSolinas.from_bytes n s c Semantics.width) Field.from_bytes
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
*)
  }.
Arguments unsaturated_solinas_ops {_ _} _ _ _ _.

Ltac make_computed_op :=
  eapply Build_computed_op;
  lazymatch goal with
  | |- _ = ErrorT.Success _ => vm_compute; reflexivity
  | _ => idtac
  end;
  vm_compute; reflexivity.

Section UnsaturatedSolinas.
  Context {p:Types.parameters} {p_ok : Types.ok}
          {field_parameters : FieldParameters}
          (varname_gen_is_default :
             varname_gen = default_varname_gen).
  Context (n : nat) (s : Z) (c : list (Z * Z))
          (M_eq : M = m s c)
          (check_args_ok :
             check_args n s c Semantics.width (ErrorT.Success tt)
             = ErrorT.Success tt)
          (* TODO: is this proven elsewhere/can it be proven in general? *)
          (tight_bounds_tighter_than:
             list_Z_tighter_than (tight_bounds n s c)
                                 (MaxBounds.max_bounds n))
          (loose_bounds_tighter_than:
             list_Z_tighter_than (loose_bounds n s c)
                                 (MaxBounds.max_bounds n)).
  Context (ops : unsaturated_solinas_ops n s c Semantics.width)
          mul_func add_func sub_func opp_func square_func
          scmula24_func
          (mul_func_eq : mul_func = b2_func mul_op)
          (add_func_eq : add_func = b2_func add_op)
          (sub_func_eq : sub_func = b2_func sub_op)
          (opp_func_eq : opp_func = b2_func opp_op)
          (square_func_eq : square_func = b2_func square_op)
          (scmula24_func_eq : scmula24_func = b2_func scmula24_op).
  Existing Instance semantics_ok.

  Local Notation weight :=
    (ModOps.weight (QArith_base.Qnum (limbwidth n s c))
                   (Z.pos (QArith_base.Qden (limbwidth n s c))))
      (only parsing).
  Local Instance field_representation : FieldRepresentation
    := field_representation
         n weight
         (UnsaturatedSolinasHeuristics.loose_bounds n s c)
         (UnsaturatedSolinasHeuristics.tight_bounds n s c).

  Local Ltac specialize_correctness_hyp Hcorrect :=
    cbv [feval bounded_by field_representation
               Signature.field_representation
               Representation.frep
               Representation.eval_words] in *;
    lazymatch type of Hcorrect with
    | forall x y, ?Px x -> ?Py y -> _ /\ _ =>
      match goal with
        | Hx : Px ?x, Hy : Py ?y |- _ =>
          specialize (Hcorrect x y Hx Hy)
      end
    | forall x, ?Px x -> _ /\ _ =>
      match goal with
        | Hx : Px ?x |- _ =>
          specialize (Hcorrect x Hx)
      end
    end.

  Lemma loose_bounds_eq : Field.loose_bounds = loose_bounds n s c.
  Proof. reflexivity. Qed.
  Lemma tight_bounds_eq : Field.tight_bounds = tight_bounds n s c.
  Proof. reflexivity. Qed.

  Local Hint Resolve
        relax_correct func_eq
        inname_gen_varname_gen_disjoint
        outname_gen_varname_gen_disjoint
        length_tight_bounds length_loose_bounds
    : helpers.

  Lemma mul_func_correct :
    valid_func (res mul_op _) ->
    expr.Wf3 (res mul_op) ->
    forall functions,
      spec_of_mul (mul_func :: functions).
  Proof.
    intros. cbv [spec_of_mul]. rewrite mul_func_eq.
    pose proof carry_mul_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq mul_op)
      as Hcorrect.

    eapply list_binop_correct with (res:=res mul_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.carry_mul_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.carry_mul_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma add_func_correct :
    valid_func (res add_op _) ->
    expr.Wf3 (res add_op) ->
    forall functions,
      spec_of_add (add_func :: functions).
  Proof.
    intros. cbv [spec_of_add]. rewrite add_func_eq.
    pose proof add_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq add_op)
      as Hcorrect.

    eapply list_binop_correct with (res:=res add_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.add_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.add_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma opp_func_correct :
    valid_func (res opp_op _) ->
    expr.Wf3 (res opp_op) ->
    forall functions,
      spec_of_opp (opp_func :: functions).
  Proof.
    intros. cbv [spec_of_opp]. rewrite opp_func_eq.
    pose proof opp_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq opp_op)
      as Hcorrect.

    eapply list_unop_correct with (res:=res opp_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.opp_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.opp_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

End UnsaturatedSolinas.

(* Prototyping full pipeline: *)

Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.

(* TODO: move somewhere common *)
Definition field_parameters_prefixed
           M_pos a24 (prefix: string) : FieldParameters :=
  Build_FieldParameters
    M_pos a24
    (prefix ++ "mul")
    (prefix ++ "add")
    (prefix ++ "sub")
    (prefix ++ "opp")
    (prefix ++ "square")
    (prefix ++ "scmula24")
    (prefix ++ "inv")
    (prefix ++ "from_bytes")
    (prefix ++ "to_bytes")
    (prefix ++ "copy")
    (prefix ++ "small_literal")
.

Local Ltac begin_derive_bedrock2_func :=
  lazymatch goal with
  | |- context [spec_of_mul] => eapply mul_func_correct
  | |- context [spec_of_add] => eapply add_func_correct
  | |- context [spec_of_opp] => eapply opp_func_correct
  end.

Local Ltac derive_bedrock2_func op :=
  begin_derive_bedrock2_func;
  (* this goal fills in the evar, so do it first for [abstract] to be happy *)
  try lazymatch goal with
      | |- _ = b2_func _ => vm_compute; reflexivity
      end;
  (* solve all the remaining goals *)
  lazymatch goal with
  | |- _ = @ErrorT.Success ?ErrT unit tt =>
    abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
  | |- list_Z_tighter_than _ _ =>
    abstract (vm_cast_no_check (@eq_refl bool true))
  | |- valid_func _ =>
    eapply valid_func_bool_iff;
    abstract vm_cast_no_check (eq_refl true)
  | |- expr.Wf3 _ => abstract (prove_Wf3 ()) (* this abstract is slow, but if it is removed the slowness moves to Qed instead *)
  | |- _ = m _ _ => vm_compute; reflexivity
  | |- _ = default_varname_gen => vm_compute; reflexivity
  end.

Section Tests.
  Definition n := 5%nat.
  Definition s := (2^255)%Z.
  Definition c := [(1, 19)]%Z.

  Existing Instances default_parameters default_parameters_ok semantics semantics_ok.
  Existing Instances no_select_size split_mul_to split_multiret_to.
  Instance machine_wordsize_opt : machine_wordsize_opt := machine_wordsize.

  Definition prefix : string := "fe25519_"%string.

  Instance field_parameters : FieldParameters.
  Proof.
    let M := (eval vm_compute in (Z.to_pos (m s c))) in
    let a := constr:(F.of_Z M 486662) in
    let prefix := constr:("fe25519_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Instance fe25519_ops : unsaturated_solinas_ops n s c machine_wordsize.
  Proof. Time constructor; make_computed_op. Defined.

  Derive fe25519_mul
         SuchThat (forall functions,
                      spec_of_mul
                        (field_representation:=field_representation n s c)
                        (fe25519_mul :: functions))
         As fe25519_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe25519_add
         SuchThat (forall functions,
                      spec_of_add
                        (field_representation:=field_representation n s c)
                        (fe25519_add :: functions))
         As fe25519_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe25519_opp
         SuchThat (forall functions,
                      spec_of_opp
                        (field_representation:=field_representation n s c)
                        (fe25519_opp :: functions))
         As fe25519_opp_correct.
  Proof. Time derive_bedrock2_func opp_op. Qed.
End Tests.

Print fe25519_add.
Print fe25519_opp.
(* Current status: mul/add/opp prototyped through full pipeline
   Done:
   - fix from_bytes proof in Signature.v
   Next:
   - prototype from_bytes through full pipeline
   - prototype to_bytes through full pipeline
   - add remaining operations
*)
