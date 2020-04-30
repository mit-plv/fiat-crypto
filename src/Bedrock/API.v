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
  { carry_mul_name : string;
    carry_mul_func : (list string * list string * cmd)%type;
    carry_mul : bedrock_func := (carry_mul_name, carry_mul_func);
    spec_of_carry_mul : spec_of carry_mul_name :=
      @spec_of_carry_mul p n s c carry_mul_name;
    carry_mul_correct :
      forall functions,
        spec_of_carry_mul (carry_mul :: functions) }.
Arguments carry_mul_name {_ _ _ _ _}.
Arguments carry_mul_func {_ _ _ _ _}.
Arguments carry_mul {_ _ _ _ _}.
Arguments spec_of_carry_mul {_ _ _ _ _}.
Arguments carry_mul_correct {_ _ _ _ _}.

(* TODO: replace with prefix-based generators *)
Definition inname_gen :=
  fun n => ("in" ++ Decimal.Z.to_string (Z.of_nat n))%string.
Definition outname_gen :=
  fun n => ("out" ++ Decimal.Z.to_string (Z.of_nat n))%string.
Local Notation make_bedrock_func :=
  (@make_bedrock_func _ inname_gen outname_gen).

Record reified_op {p t} (n : nat)
       (start : ErrorT.ErrorT BoundsPipeline.Pipeline.ErrorMessage
                              (API.Expr t)) :=
  { res : API.Expr t;
    computed_bedrock_func : list string * list string * cmd;
    computed_bedrock_func_eq :
      computed_bedrock_func = make_bedrock_func n res;
    reified_eq : start = ErrorT.Success res;
    reified_Wf3 : expr.Wf3 res;
    reified_valid : Func.valid_func (p:=p) (res (fun _ => unit)) }.
Arguments res {_ _ _}.
Arguments reified_eq {_ _ _}.
Arguments reified_Wf3 {_ _ _}.
Arguments reified_valid {_ _ _}.

(* TODO: remove these axioms once there's a nice general proof for
     prefix-based varname generators *)
Axiom outname_gen_inname_gen_ok :
  forall n m : nat, outname_gen n <> inname_gen m.
Axiom inname_gen_varname_gen_ok :
  forall {p : Types.parameters} n m,
    inname_gen n <> Types.varname_gen m.
Axiom outname_gen_varname_gen_ok :
  forall {p : Types.parameters} n m,
    outname_gen n <> Types.varname_gen m.
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

Ltac make_reified_op n start :=
  assert (reified_op n start)
  by (econstructor; try apply valid_func_bool_iff;
      try match goal with
          | |- ?start = ErrorT.Success _ =>
            vm_compute; reflexivity
          end;
      [ vm_compute; reflexivity
      | abstract (prove_Wf3 ())
      | abstract (vm_compute; reflexivity) ]).

Ltac parameters_from_wordsize machine_wordsize :=
  let r := (eval cbv - [Defaults32.default_parameters
                          Defaults64.default_parameters] in
               (select_parameters machine_wordsize)) in
  lazymatch r with
  | inl ?p => p
  | inr ?err => fail "Failed to select parameters: " err
  end.

Ltac make_all_reified_ops n s c machine_wordsize :=
  make_reified_op
    n (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
         n s c machine_wordsize).

Ltac instantiate_ops carry_mul_name_value :=
  let n :=
      lazymatch goal with
      | |- bedrock2_unsaturated_solinas _ ?n _ _ => n end in
  let carry_mul_func_value := fresh "carry_mul_func" in
  let carry_mul_func_eq := fresh "carry_mul_func_eq" in
  lazymatch goal with
  | X : reified_op
          _
          (PushButtonSynthesis.UnsaturatedSolinas.carry_mul _ _ _ _)
    |- _ =>
    destruct X as [? carry_mul_func_value carry_mul_func_eq ]
  end;
  let name := eval vm_compute in carry_mul_name_value in
  apply Build_bedrock2_unsaturated_solinas
    with (carry_mul_name:=name)
         (carry_mul_func:=carry_mul_func_value);
  rewrite carry_mul_func_eq.

Module X25519_64.
  Let n := 10%nat.
  Let s := 2^255.
  Let c := [(1, 19)].
  Let machine_wordsize := 64.

  Definition carry_mul_name := "curve25519_carry_mul"%string.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance curve25519_bedrock2 : bedrock2_unsaturated_solinas p n s c.
  Proof.
    make_all_reified_ops n s c machine_wordsize.
    instantiate_ops carry_mul_name.
    apply UnsaturatedSolinas.carry_mul_correct.
    all: try assumption.
    all: abstract (handle_easy_preconditions).
  Defined.
(* Eval cbv [carry_mul API.carry_mul_name carry_mul_func
                      curve25519_bedrock2] in carry_mul. *)
End X25519_64.

Module X1305_32.
  Let n := 5%nat.
  Let s := 2^130.
  Let c := [(1, 5)].
  Let machine_wordsize := 32.

  Definition carry_mul_name := "poly1305_carry_mul"%string.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance poly1305_bedrock2 : bedrock2_unsaturated_solinas p n s c.
  Proof.
    make_all_reified_ops n s c machine_wordsize.
    instantiate_ops carry_mul_name.
    apply UnsaturatedSolinas.carry_mul_correct.

    all: try assumption.
    all: abstract (handle_easy_preconditions).
  Qed.
End X1305_32.

Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import bedrock2.Semantics.
Import Types.
Module Test.
  Import X25519_64.
  Existing Instance Defaults64.default_parameters.
  Existing Instance curve25519_bedrock2.
  Local Open Scope string_scope.
  Local Coercion name_of_func (f : bedrock_func) := fst f.

  (* test function; computes x * y * y *)
  Definition mul_twice : bedrock_func :=
    let x := "x" in
    let y := "y" in
    let xy := "xy" in
    let tmp := "tmp" in
    let out := "out" in
    ("mul_twice",
     ([x; y; out], [],
      (cmd.seq
         (cmd.call [] "curve25519_carry_mul" [expr.var x; expr.var y; expr.var out])
         (cmd.call [] "curve25519_carry_mul" [expr.var out; expr.var y; expr.var out])))).

  (* Notations to make the spec more readable *)
  Local Notation M := (X25519_64.s - Associational.eval X25519_64.c).
  Local Notation eval :=
    (Positional.eval
                (weight X25519_64.n X25519_64.s X25519_64.c)
                X25519_64.n).
  Local Notation loose_bounds :=
    (UnsaturatedSolinas.loose_bounds X25519_64.n X25519_64.s X25519_64.c).
  Local Notation tight_bounds :=
    (UnsaturatedSolinas.tight_bounds X25519_64.n X25519_64.s X25519_64.c).

  Instance spec_of_mul_twice : spec_of mul_twice :=
    fun functions =>
      forall x y px py pout bs t m
             (R : Interface.map.rep
                    (map:=Semantics.mem) -> Prop),
        list_Z_bounded_by loose_bounds x ->
        list_Z_bounded_by loose_bounds y ->
        length bs = (X25519_64.n * Z.to_nat word_size_in_bytes)%nat ->
        (* all 3 need to be separate, because we use out as an input with y *)
        sep (sep (Bignum px x)
                 (sep (Bignum py y)
                      (array ptsto (Interface.word.of_Z 1) pout bs)))
            R m ->
        WeakestPrecondition.call
          (p:=Types.semantics)
          functions mul_twice t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             Lift1Prop.ex1
               (fun out =>
                  sep
                    (sep (emp (eval out mod M
                               = (eval x * eval y * eval y) mod M
                               /\ list_Z_bounded_by tight_bounds out))
                         (Bignum pout out))
                    (sep (Bignum px x) (sep (Bignum py y) R))) m').

  About spec_of_carry_mul.
  Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
  Local Notation functions_t := (list function_t).

  (* TODO: currently this extra step is required so the literal string isn't
  hidden *)
  Instance spec_of_curve25519_carry_mul :
    spec_of "curve25519_carry_mul" := spec_of_carry_mul.

  Lemma mul_twice_correct :
    program_logic_goal_for_function! mul_twice.
  Proof.
    (* first step of straightline is inlined here so we can do a [change]
       instead of [replace] *)
    enter mul_twice. intros.
    WeakestPrecondition.unfold1_call_goal.
    (cbv beta match delta [WeakestPrecondition.call_body]).
    lazymatch goal with
    | |- if ?test then ?T else _ =>
      (* this change is a replace in the original straightline, but that hangs
      here for some reason *)
      change test with true; change_no_check T
    end.
    (cbv beta match delta [WeakestPrecondition.func]).

    repeat straightline.
    straightline_call;
      [ try ecancel_assumption .. | ];
      [ assumption .. | ].
    sepsimpl.
    repeat straightline.
    straightline_call;
      [ try ecancel_assumption .. | ].
    { apply relax_correct; assumption. }
    { assumption. }
    { (* TODO: lemma about length of encode_bytes *)
      admit. }
    {
      use_sep_assumption.
      rewrite (Bignum_to_bytes
                       (inname_gen:=inname_gen)
                       (outname_gen:=outname_gen)) by
          admit. (* currently has a million preconditions because admitted *)
      ecancel. }

    repeat straightline.

    repeat split; try reflexivity.
    sepsimpl_hyps.
    eexists; sepsimpl;
      [ | | ecancel_assumption ];
      [ | assumption ].
    repeat match goal with
           | H : eval _ mod _ = (eval _ * eval _) mod _ |- _ =>
             rewrite H
           | _ => progress Modulo.push_Zmod
           end.
    reflexivity.
  Admitted.
End Test.
