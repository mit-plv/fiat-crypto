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

Class bedrock2_unsaturated_solinas_funcs :=
  { carry_mul : bedrock_func;
    carry_square : bedrock_func;
    carry : bedrock_func;
    add : bedrock_func;
    sub : bedrock_func;
    opp : bedrock_func;
    selectznz : bedrock_func;
    to_bytes : bedrock_func;
    from_bytes : bedrock_func }.

Class bedrock2_unsaturated_solinas_specs
      {funcs : bedrock2_unsaturated_solinas_funcs }:=
  { spec_of_carry_mul : spec_of (fst carry_mul);
    spec_of_carry_square : spec_of (fst carry_square);
    spec_of_carry : spec_of (fst carry);
    spec_of_add : spec_of (fst add);
    spec_of_sub : spec_of (fst sub);
    spec_of_opp : spec_of (fst opp);
    spec_of_selectznz : spec_of (fst selectznz);
    spec_of_to_bytes : spec_of (fst to_bytes);
    spec_of_from_bytes : spec_of (fst from_bytes) }.

Class bedrock2_unsaturated_solinas_correctness
      {funcs : bedrock2_unsaturated_solinas_funcs}
      {specs : bedrock2_unsaturated_solinas_specs} :=
  { carry_mul_correct :
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

Class bedrock2_unsaturated_solinas_scmul_func :=
  { carry_scmul_const : bedrock_func }.

Class bedrock2_unsaturated_solinas_scmul_spec
      {func : bedrock2_unsaturated_solinas_scmul_func }:=
  { spec_of_carry_scmul_const : spec_of (fst carry_scmul_const) }.

Class bedrock2_unsaturated_solinas_scmul_correctness
      {func : bedrock2_unsaturated_solinas_scmul_func}
      {spec : bedrock2_unsaturated_solinas_scmul_spec} :=
  { carry_scmul_const_correct :
      forall functions,
        spec_of_carry_scmul_const (carry_scmul_const :: functions) }.

Class names_of_operations :=
  { name_of_carry_mul : string;
    name_of_carry_square : string;
    name_of_carry : string;
    name_of_add : string;
    name_of_sub : string;
    name_of_opp : string;
    name_of_selectznz : string;
    name_of_to_bytes : string;
    name_of_from_bytes : string;
    name_of_carry_scmul_const : Z -> string }.

Record unsaturated_solinas_reified_ops
       {names : names_of_operations} {n s c machine_wordsize} :=
  { params : Types.parameters;
    reified_carry_mul :
      reified_op name_of_carry_mul
                 (@Interfaces.UnsaturatedSolinas.carry_mul params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
                    n s c machine_wordsize);
    reified_carry_square :
      reified_op name_of_carry_square
                 (@Interfaces.UnsaturatedSolinas.carry_square params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.carry_square
                    n s c machine_wordsize);
    reified_carry :
      reified_op name_of_carry
                 (@Interfaces.UnsaturatedSolinas.carry params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.carry
                    n s c machine_wordsize);
    reified_add :
      reified_op name_of_add
                 (@Interfaces.UnsaturatedSolinas.add params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.add
                    n s c machine_wordsize);
    reified_sub :
      reified_op name_of_sub
                 (@Interfaces.UnsaturatedSolinas.sub params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.sub
                    n s c machine_wordsize);
    reified_opp :
      reified_op name_of_opp
                 (@Interfaces.UnsaturatedSolinas.opp params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.opp
                    n s c machine_wordsize);
    reified_selectznz :
      reified_op name_of_selectznz
                 (@Interfaces.UnsaturatedSolinas.selectznz params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.selectznz
                    n machine_wordsize);
    reified_to_bytes :
      reified_op name_of_to_bytes
                 (@Interfaces.UnsaturatedSolinas.to_bytes params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.to_bytes
                    n s c machine_wordsize);
    reified_from_bytes :
      reified_op name_of_from_bytes
                 (@Interfaces.UnsaturatedSolinas.from_bytes params n s c)
                 (PushButtonSynthesis.UnsaturatedSolinas.from_bytes
                    n s c machine_wordsize) }.
Arguments unsaturated_solinas_reified_ops {names} n s c machine_wordsize.

Record unsaturated_solinas_reified_scmul
       {names : names_of_operations} {n s c machine_wordsize} {x : Z} :=
  { scmul_params : Types.parameters;
    reified_carry_scmul_const :
      reified_op (name_of_carry_scmul_const x)
                 (@Interfaces.UnsaturatedSolinas.carry_scmul_const
                    scmul_params n s c x)
                 (PushButtonSynthesis.UnsaturatedSolinas.carry_scmul_const
                    n s c machine_wordsize x) }.
Arguments unsaturated_solinas_reified_scmul
          {names} n s c machine_wordsize x.

(*** Helpers ***)

Definition names_from_prefix (prefix : string)
  : names_of_operations :=
  {| name_of_carry_mul := (prefix ++ "carry_mul")%string;
     name_of_carry_square := (prefix ++ "carry_square")%string;
     name_of_carry := (prefix ++ "carry")%string;
     name_of_add := (prefix ++ "add")%string;
     name_of_sub := (prefix ++ "sub")%string;
     name_of_opp := (prefix ++ "opp")%string;
     name_of_selectznz := (prefix ++ "selectznz")%string;
     name_of_to_bytes := (prefix ++ "to_bytes")%string;
     name_of_from_bytes := (prefix ++ "from_bytes")%string;
     name_of_carry_scmul_const :=
       fun x =>
         (prefix ++ "carry_scmul_const" ++ Decimal.Z.to_string x)%string
  |}.

(*** Synthesis Tactics ***)

Ltac scmul_func_from_ops ops :=
  let carry_scmul_const_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_carry_scmul_const ops))) in
  exact {| carry_scmul_const := carry_scmul_const_func_value |}.

Ltac scmul_spec_from_ops ops n s c :=
  let x := lazymatch type of ops with
           | unsaturated_solinas_reified_scmul _ _ _ _ ?x => x end in
  let p := (eval cbn [scmul_params ops] in (scmul_params ops)) in
  let carry_scmul_const_name :=
      (eval compute in (name_of_carry_scmul_const x)) in
  let carry_scmul_const_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.carry_scmul_const
                 Interfaces.UnsaturatedSolinas.spec_of_carry_scmul_const] in
          (@Interfaces.UnsaturatedSolinas.spec_of_carry_scmul_const
             p n s c x carry_scmul_const_name)) in
  exact {| spec_of_carry_scmul_const := carry_scmul_const_spec |}.

Ltac funcs_from_ops ops :=
  let carry_mul_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_carry_mul ops))) in
  let carry_square_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_carry_square ops))) in
  let carry_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_carry ops))) in
  let add_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_add ops))) in
  let sub_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_sub ops))) in
  let opp_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_opp ops))) in
  let selectznz_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_selectznz ops))) in
  let to_bytes_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_to_bytes ops))) in
  let from_bytes_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_from_bytes ops))) in
  exact {| carry_mul := carry_mul_func_value;
           carry_square := carry_square_func_value;
           carry := carry_func_value;
           add := add_func_value;
           sub := sub_func_value;
           opp := opp_func_value;
           selectznz := selectznz_func_value;
           to_bytes := to_bytes_func_value;
           from_bytes := from_bytes_func_value |}.

Ltac specs_from_ops ops n s c :=
  let p := eval cbn [params ops] in (params ops) in
  let carry_mul_name := (eval compute in name_of_carry_mul) in
  let carry_square_name := (eval compute in name_of_carry_square) in
  let carry_name := (eval compute in name_of_carry) in
  let add_name := (eval compute in name_of_add) in
  let sub_name := (eval compute in name_of_sub) in
  let opp_name := (eval compute in name_of_opp) in
  let selectznz_name := (eval compute in name_of_selectznz) in
  let to_bytes_name := (eval compute in name_of_to_bytes) in
  let from_bytes_name := (eval compute in name_of_from_bytes) in
  let carry_mul_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.carry_mul
                 Interfaces.UnsaturatedSolinas.spec_of_carry_mul] in
          (@Interfaces.UnsaturatedSolinas.spec_of_carry_mul
             p n s c carry_mul_name)) in
  let carry_square_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.carry_square
                 Interfaces.UnsaturatedSolinas.spec_of_carry_square] in
          (@Interfaces.UnsaturatedSolinas.spec_of_carry_square
             p n s c carry_square_name)) in
  let carry_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.carry
                 Interfaces.UnsaturatedSolinas.spec_of_carry] in
          (@Interfaces.UnsaturatedSolinas.spec_of_carry
             p n s c carry_name)) in
  let add_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.add
                 Interfaces.UnsaturatedSolinas.spec_of_add] in
          (@Interfaces.UnsaturatedSolinas.spec_of_add
             p n s c add_name)) in
  let sub_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.sub
                 Interfaces.UnsaturatedSolinas.spec_of_sub] in
          (@Interfaces.UnsaturatedSolinas.spec_of_sub
             p n s c sub_name)) in
  let opp_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.opp
                 Interfaces.UnsaturatedSolinas.spec_of_opp] in
          (@Interfaces.UnsaturatedSolinas.spec_of_opp
             p n s c opp_name)) in
  let selectznz_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.selectznz
                 Interfaces.UnsaturatedSolinas.spec_of_selectznz] in
          (@Interfaces.UnsaturatedSolinas.spec_of_selectznz
             p n s c selectznz_name)) in
  let to_bytes_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.to_bytes
                 Interfaces.UnsaturatedSolinas.spec_of_to_bytes] in
          (@Interfaces.UnsaturatedSolinas.spec_of_to_bytes
             p n s c to_bytes_name)) in
  let from_bytes_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.from_bytes
                 Interfaces.UnsaturatedSolinas.spec_of_from_bytes] in
          (@Interfaces.UnsaturatedSolinas.spec_of_from_bytes
             p n s c from_bytes_name)) in
  exact {| spec_of_carry_mul := carry_mul_spec;
           spec_of_carry_square := carry_square_spec;
           spec_of_carry := carry_spec;
           spec_of_add := add_spec;
           spec_of_sub := sub_spec;
           spec_of_opp := opp_spec;
           spec_of_selectznz := selectznz_spec;
           spec_of_to_bytes := to_bytes_spec;
           spec_of_from_bytes := from_bytes_spec |}.

Ltac handle_easy_preconditions :=
  lazymatch goal with
  | |- ZRange.type.option.is_tighter_than _ _ = true =>
    abstract (vm_compute; reflexivity)
  | |- Types.ok => solve [typeclasses eauto]
  | |- _ = ErrorT.Success _ => solve [apply reified_eq]
  | |- Wf.Compilers.expr.Wf3 _ => solve [apply reified_Wf3]
  | |- Func.valid_func _ => solve [apply reified_valid]
  | _ => first [ apply inname_gen_varname_gen_disjoint
               | apply outname_gen_varname_gen_disjoint
               | apply outname_gen_inname_gen_disjoint
               | apply prefix_name_gen_unique ]
  | |- ?g => fail "Unrecognized goal" g
  end.

Ltac use_correctness_proofs p n s c :=
  let Hc := fresh in
  match goal with
  | |- context [Interfaces.UnsaturatedSolinas.carry_mul] =>
    apply (@Interfaces.UnsaturatedSolinas.carry_mul_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.carry_square] =>
    apply (@Interfaces.UnsaturatedSolinas.carry_square_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.carry] =>
    apply (@Interfaces.UnsaturatedSolinas.carry_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.add] =>
    apply (@Interfaces.UnsaturatedSolinas.add_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.sub] =>
    apply (@Interfaces.UnsaturatedSolinas.sub_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.opp] =>
    apply (@Interfaces.UnsaturatedSolinas.opp_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.selectznz] =>
    apply (@Interfaces.UnsaturatedSolinas.selectznz_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.to_bytes] =>
    apply (@Interfaces.UnsaturatedSolinas.to_bytes_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.from_bytes] =>
    apply (@Interfaces.UnsaturatedSolinas.from_bytes_correct
             p default_inname_gen default_outname_gen n s c)
  | |- context [Interfaces.UnsaturatedSolinas.carry_scmul_const] =>
    apply (@Interfaces.UnsaturatedSolinas.carry_scmul_const_correct
             p default_inname_gen default_outname_gen n s c)
  end.

Ltac change_with_computed_func ops :=
  lazymatch goal with
  | |- context [carry_mul] =>
    change carry_mul with (computed_bedrock_func (reified_carry_mul ops))
  | |- context [carry_square] =>
    change carry_square with (computed_bedrock_func (reified_carry_square ops))
  | |- context [carry] =>
    change carry with (computed_bedrock_func (reified_carry ops))
  | |- context [add] =>
    change add with (computed_bedrock_func (reified_add ops))
  | |- context [sub] =>
    change sub with (computed_bedrock_func (reified_sub ops))
  | |- context [opp] =>
    change opp with (computed_bedrock_func (reified_opp ops))
  | |- context [selectznz] =>
    change selectznz with (computed_bedrock_func (reified_selectznz ops))
  | |- context [to_bytes] =>
    change to_bytes with (computed_bedrock_func (reified_to_bytes ops))
  | |- context [from_bytes] =>
    change from_bytes with (computed_bedrock_func (reified_from_bytes ops))
  | |- context [carry_scmul_const] =>
    change carry_scmul_const with (computed_bedrock_func (reified_carry_scmul_const ops))
  end.

Ltac prove_correctness ops n s c machine_wordsize :=
  assert (UnsaturatedSolinas.check_args
            n s c machine_wordsize (ErrorT.Success tt) =
          ErrorT.Success tt) by abstract (native_compute; reflexivity);
  lazymatch goal with
    | |- bedrock2_unsaturated_solinas_correctness => econstructor end;
  change_with_computed_func ops; rewrite computed_bedrock_func_eq;
  let p := (eval cbn [params ops] in (params ops)) in
  use_correctness_proofs p n s c; try assumption;
  handle_easy_preconditions.

Ltac prove_correctness_scmul ops n s c machine_wordsize :=
  assert (UnsaturatedSolinas.check_args
            n s c machine_wordsize (ErrorT.Success tt) =
          ErrorT.Success tt) by abstract (native_compute; reflexivity);
  lazymatch goal with
  | |- bedrock2_unsaturated_solinas_scmul_correctness =>
    econstructor end;
  change_with_computed_func ops; rewrite computed_bedrock_func_eq;
  let p := (eval cbn [scmul_params ops] in (scmul_params ops)) in
  use_correctness_proofs p n s c; try assumption;
  handle_easy_preconditions.

Ltac make_names_of_operations prefix :=
  match goal with
  | |- names_of_operations =>
    let n := eval vm_compute in (names_from_prefix prefix) in
        exact n
  end.

Ltac make_reified_ops :=
  lazymatch goal with
    |- unsaturated_solinas_reified_ops ?n ?s ?c ?machine_wordsize =>
    let p := parameters_from_wordsize machine_wordsize in
    eapply Build_unsaturated_solinas_reified_ops with (params:=p)
  end; prove_reified_op.

Ltac make_reified_scmul :=
  lazymatch goal with
    |- unsaturated_solinas_reified_scmul ?n ?s ?c ?machine_wordsize ?x =>
    let p := parameters_from_wordsize machine_wordsize in
    eapply Build_unsaturated_solinas_reified_scmul with (scmul_params:=p)
  end;
  prove_reified_op.
