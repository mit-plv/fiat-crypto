Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.forward.
Require Import Rewriter.Language.Wf.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.SelectParameters.
Require Import Crypto.Bedrock.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.
Import ListNotations.
Import AbstractInterpretation.Compilers.
Import Language.Wf.Compilers.

Class bedrock2_unsaturated_solinas p n s c :=
  { carry_mul : bedrock_func;
    spec_of_carry_mul : spec_of (fst carry_mul) :=
      @spec_of_carry_mul p n s c (fst carry_mul);
    carry_mul_correct :
      forall functions,
        spec_of_carry_mul (carry_mul :: functions) }.
Arguments carry_mul {_ _ _ _ _}.
Arguments spec_of_carry_mul {_ _ _ _ _}.
Arguments carry_mul_correct {_ _ _ _ _}.

Record reified_op {p t}
       (start : ErrorT.ErrorT BoundsPipeline.Pipeline.ErrorMessage
                              (API.Expr t)) :=
  { res : API.Expr t;
    reified_eq : start = ErrorT.Success res;
    reified_Wf3 : expr.Wf3 res;
    reified_valid : Func.valid_func (p:=p) (res (fun _ => unit)) }.
Arguments res {_ _ _}.
Arguments reified_eq {_ _ _}.
Arguments reified_Wf3 {_ _ _}.
Arguments reified_valid {_ _ _}.

Section __.
  Let n := 10%nat.
  Let s := 2^255.
  Let c := [(1, 19)].
  Let machine_wordsize := 64.

  Definition carry_mul_name := "carry_mul"%string.

  Instance p : Types.parameters.
  Proof.
    let r := (eval cbv - [Defaults32.default_parameters
                            Defaults64.default_parameters] in
                 (select_parameters machine_wordsize)) in
        lazymatch r with
        | inl ?p => exact p
        | inr ?err => fail "Failed to select parameters: " err
        end.
  Defined.

  (* TODO: replace with prefix-based generators *)
  Definition inname_gen :=
    fun n => ("in" ++ Decimal.Z.to_string (Z.of_nat n))%string.
  Definition outname_gen :=
    fun n => ("out" ++ Decimal.Z.to_string (Z.of_nat n))%string.

  (* TODO: remove these axioms once there's a nice general proof for
     prefix-based varname generators *)
  Axiom inname_gen_varname_gen_ok :
    forall n m : nat, inname_gen n <> Types.varname_gen m.
  Axiom outname_gen_varname_gen_ok :
    forall n m : nat, outname_gen n <> Types.varname_gen m.
  Axiom outname_gen_inname_gen_ok :
      forall n m : nat, outname_gen n <> inname_gen m.
  Axiom inname_gen_unique :
    forall i j : nat, inname_gen i = inname_gen j <-> i = j.
  Axiom outname_gen_unique :
    forall i j : nat, outname_gen i = outname_gen j <-> i = j.

  Ltac handle_easy_preconditions :=
    lazymatch goal with
    | |- ZRange.type.option.is_tighter_than _ _ = true =>
      abstract (vm_compute; reflexivity)
    | |- UnsaturatedSolinas.check_args _ _ _ _ _ = _ =>
      abstract (native_compute; reflexivity)
    | |- Types.ok => solve [typeclasses eauto]
    | _ => first [ apply inname_gen_varname_gen_ok
                 | apply outname_gen_varname_gen_ok
                 | apply outname_gen_inname_gen_ok
                 | apply inname_gen_unique
                 | apply outname_gen_unique ]
    | |- ?g => fail "Unrecognized goal" g
    end.

  Ltac make_reified_op start :=
    assert (reified_op start)
    by (econstructor; [ | | apply valid_func_bool_iff ];
          [ vm_compute; reflexivity | | ];
          [ abstract (prove_Wf3 ())
          | abstract (vm_compute; reflexivity) ]).

  Instance test : bedrock2_unsaturated_solinas p n s c.
  Proof.
    make_reified_op
      (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
         n s c Semantics.width).
    lazymatch goal with
    | X : reified_op _ |- _ =>
      destruct X as [res ?]
    end.

    let carry_mul_func :=
        constr:(make_bedrock_func
                  (inname_gen:=inname_gen)
                  (outname_gen:=outname_gen)
                  n res) in
    apply Build_bedrock2_unsaturated_solinas
      with (carry_mul:= (carry_mul_name, carry_mul_func)).
    apply UnsaturatedSolinas.carry_mul_correct.

    all: try assumption.
    all: abstract (handle_easy_preconditions).
  Qed.
End __.
