Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Synthesis.ReifiedOperation.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.
Import ListNotations.
Import AbstractInterpretation.Compilers.

Class bedrock2_unsaturated_solinas {p names n s c} :=
  { carry_mul : bedrock_func;
    carry_square : bedrock_func;
    carry : bedrock_func;
    add : bedrock_func;
    sub : bedrock_func;
    opp : bedrock_func;
    selectznz : bedrock_func;
    to_bytes : bedrock_func;
    from_bytes : bedrock_func;
    spec_of_carry_mul : spec_of (fst carry_mul) :=
      @spec_of_carry_mul p n s c names;
    spec_of_carry_square : spec_of (fst carry_square) :=
      @spec_of_carry_square p n s c names;
    spec_of_carry : spec_of (fst carry) :=
      @spec_of_carry p n s c names;
    spec_of_add : spec_of (fst add) :=
      @spec_of_add p n s c names;
    spec_of_sub : spec_of (fst sub) :=
      @spec_of_sub p n s c names;
    spec_of_opp : spec_of (fst opp) :=
      @spec_of_opp p n s c names;
    spec_of_selectznz : spec_of (fst selectznz) :=
      @spec_of_selectznz p n s c names;
    spec_of_to_bytes : spec_of (fst to_bytes) :=
      @spec_of_to_bytes p n s c names;
    spec_of_from_bytes : spec_of (fst from_bytes) :=
      @spec_of_from_bytes p n s c names;
    carry_mul_correct :
      forall functions,
        spec_of_carry_mul (carry_mul :: functions);
    carry_square_correct :
      forall functions,
        spec_of_carry_square (carry_square :: functions);
    carry_correct :
      forall functions,
        spec_of_carry (carry :: functions);
    add_correct :
      forall functions,
        spec_of_add (add :: functions);
    sub_correct :
      forall functions,
        spec_of_sub (sub :: functions);
    opp_correct :
      forall functions,
        spec_of_opp (opp :: functions);
    selectznz_correct :
      forall functions,
        spec_of_selectznz (selectznz :: functions);
    to_bytes_correct :
      forall functions,
        spec_of_to_bytes (to_bytes :: functions);
    from_bytes_correct :
      forall functions,
        spec_of_from_bytes (from_bytes :: functions) }.
Arguments bedrock2_unsaturated_solinas {_ _} _ _ _.

(* scalar multiplication is calculated separately since it requires an extra
   argument *)
Class bedrock2_unsaturated_solinas_scmul {p names n s c} {x : Z} :=
  { carry_scmul_const : bedrock_func;
    spec_of_carry_scmul_const : spec_of (fst carry_scmul_const) :=
      @spec_of_carry_scmul_const p n s c names x;
    carry_scmul_const_correct :
      forall functions,
        spec_of_carry_scmul_const (carry_scmul_const :: functions) }.
Arguments bedrock2_unsaturated_solinas_scmul {_ _} _ _ _ _.

(*** Synthesis tactics ***)

Ltac handle_easy_preconditions :=
  lazymatch goal with
  | |- ZRange.type.option.is_tighter_than _ _ = true =>
    abstract (vm_compute; reflexivity)
  | |- UnsaturatedSolinas.check_args _ _ _ _ _ = _ =>
    abstract (native_compute; reflexivity)
  | |- Types.ok => solve [typeclasses eauto]
  | _ => first [ apply inname_gen_varname_gen_disjoint
               | apply outname_gen_varname_gen_disjoint
               | apply outname_gen_inname_gen_disjoint
               | apply prefix_name_gen_unique ]
  | |- ?g => fail "Unrecognized goal" g
  end.

Ltac use_correctness_proofs :=
  match goal with
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_carry_mul] =>
    apply Interfaces.UnsaturatedSolinas.carry_mul_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_carry_square] =>
    apply Interfaces.UnsaturatedSolinas.carry_square_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_carry] =>
    apply Interfaces.UnsaturatedSolinas.carry_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_add] =>
    apply Interfaces.UnsaturatedSolinas.add_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_sub] =>
    apply Interfaces.UnsaturatedSolinas.sub_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_opp] =>
    apply Interfaces.UnsaturatedSolinas.opp_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_selectznz] =>
    apply Interfaces.UnsaturatedSolinas.selectznz_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_to_bytes] =>
    apply Interfaces.UnsaturatedSolinas.to_bytes_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_from_bytes] =>
    apply Interfaces.UnsaturatedSolinas.from_bytes_correct
  | |- context [Interfaces.UnsaturatedSolinas.spec_of_carry_scmul_const] =>
    apply Interfaces.UnsaturatedSolinas.carry_scmul_const_correct
  end.

Ltac make_all_reified_ops n s c machine_wordsize :=
  idtac "computing reified carry_mul (slow)...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.carry_mul n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
       n s c machine_wordsize);
  idtac "computing reified carry_square (slow)...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.carry_square n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_square
       n s c machine_wordsize);
  idtac "computing reified carry...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.carry n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry
       n s c machine_wordsize);
  idtac "computing reified add...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.add n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.add
       n s c machine_wordsize);
  idtac "computing reified sub...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.sub n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.sub
       n s c machine_wordsize);
  idtac "computing reified opp...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.opp n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.opp
       n s c machine_wordsize);
  idtac "computing reified selectznz...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.selectznz n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.selectznz
       n machine_wordsize);
  idtac "computing reified to_bytes (slow)...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.to_bytes n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.to_bytes
       n s c machine_wordsize);
  idtac "computing reified from_bytes (slow)...";
  make_reified_op
    (Interfaces.UnsaturatedSolinas.from_bytes n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.from_bytes
       n s c machine_wordsize).

Ltac instantiate_ops :=
  let carry_mul_func_value := fresh "carry_mul_func" in
  let carry_square_func_value := fresh "carry_square_func" in
  let carry_func_value := fresh "carry_func" in
  let add_func_value := fresh "add_func" in
  let sub_func_value := fresh "sub_func" in
  let opp_func_value := fresh "opp_func" in
  let selectznz_func_value := fresh "selectznz_func" in
  let to_bytes_func_value := fresh "to_bytes_func" in
  let from_bytes_func_value := fresh "from_bytes_func" in
  repeat match goal with
         | X : reified_op ?op _ |- _ =>
           lazymatch op with
           | context [Interfaces.UnsaturatedSolinas.carry_mul] =>
             destruct X as [? carry_mul_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.carry_square] =>
             destruct X as [? carry_square_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.carry] =>
             destruct X as [? carry_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.add] =>
             destruct X as [? add_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.sub] =>
             destruct X as [? sub_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.opp] =>
             destruct X as [? opp_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.selectznz] =>
             destruct X as [? selectznz_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.to_bytes] =>
             destruct X as [? to_bytes_func_value ?]
           | context [Interfaces.UnsaturatedSolinas.from_bytes] =>
             destruct X as [? from_bytes_func_value ?]
           end
         end;
  apply Build_bedrock2_unsaturated_solinas
    with (carry_mul:=carry_mul_func_value)
         (carry_square:=carry_square_func_value)
         (carry:=carry_func_value)
         (add:=add_func_value)
         (sub:=sub_func_value)
         (opp:=opp_func_value)
         (selectznz:=selectznz_func_value)
         (to_bytes:=to_bytes_func_value)
         (from_bytes:=from_bytes_func_value);
  subst carry_mul_func_value carry_square_func_value carry_func_value
        add_func_value sub_func_value opp_func_value selectznz_func_value
        to_bytes_func_value from_bytes_func_value.

Ltac make_bedrock2_unsaturated_solinas :=
  match goal with
    | |- @bedrock2_unsaturated_solinas ?p _ ?n ?s ?c =>
      make_all_reified_ops n s c (@Semantics.width (@Types.semantics p));
      instantiate_ops; use_correctness_proofs; try assumption;
      abstract (handle_easy_preconditions)
  end.

Ltac make_bedrock2_unsaturated_solinas_scmul :=
  match goal with
    |- @bedrock2_unsaturated_solinas_scmul ?p _ ?n ?s ?c ?x =>
    make_reified_op
      (Interfaces.UnsaturatedSolinas.carry_scmul_const n s c x)
      (PushButtonSynthesis.UnsaturatedSolinas.carry_scmul_const
         n s c (@Semantics.width (@Types.semantics p)) x)
  end;
  let scmul_func_value := fresh "scmul_func_value" in
  match goal with
  | X : reified_op ?op _ |- _ =>
    destruct X as [? scmul_func_value ?] end;
  apply Build_bedrock2_unsaturated_solinas_scmul
    with (carry_scmul_const:=scmul_func_value); subst scmul_func_value;
  use_correctness_proofs; try assumption;
  abstract (handle_easy_preconditions).

Ltac make_names_of_operations prefix :=
  match goal with
  | |- names_of_operations =>
    let n := eval vm_compute in (names_from_prefix prefix) in
        exact n
  end.

Ltac make_parameters machine_wordsize :=
  match goal with
  | |- Types.parameters =>
    let p := parameters_from_wordsize machine_wordsize in
    exact p
  end.
