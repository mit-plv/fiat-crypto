Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.
Import ListNotations.
Import AbstractInterpretation.Compilers.

Class bedrock2_wbwmontgomery_funcs :=
  { mul : func;
    square : func;
    add : func;
    sub : func;
    opp : func;
    to_montgomery : func;
    from_montgomery : func;
    nonzero : func;
    selectznz : func;
    to_bytes : func;
    from_bytes : func }.

Class bedrock2_wbwmontgomery_specs
      {funcs : bedrock2_wbwmontgomery_funcs }:=
  { spec_of_mul : spec_of (fst mul);
    spec_of_square : spec_of (fst square);
    spec_of_add : spec_of (fst add);
    spec_of_sub : spec_of (fst sub);
    spec_of_opp : spec_of (fst opp);
    spec_of_to_montgomery : spec_of (fst to_montgomery);
    spec_of_from_montgomery : spec_of (fst from_montgomery);
    spec_of_nonzero : spec_of (fst nonzero);
    spec_of_selectznz : spec_of (fst selectznz);
    spec_of_to_bytes : spec_of (fst to_bytes);
    spec_of_from_bytes : spec_of (fst from_bytes) }.

Class bedrock2_wbwmontgomery_correctness
      {funcs : bedrock2_wbwmontgomery_funcs}
      {specs : bedrock2_wbwmontgomery_specs} :=
  { mul_correct :
      forall functions,
        spec_of_mul (mul :: functions);
    square_correct :
      forall functions,
        spec_of_square (square :: functions);
    add_correct :
      forall functions,
        spec_of_add (add :: functions);
    sub_correct :
      forall functions,
        spec_of_sub (sub :: functions);
    opp_correct :
      forall functions,
        spec_of_opp (opp :: functions);
    to_montgomery_correct :
      forall functions,
        spec_of_to_montgomery (to_montgomery :: functions);
    from_montgomery_correct :
      forall functions,
        spec_of_from_montgomery (from_montgomery :: functions);
    nonzero_correct :
      forall functions,
        spec_of_nonzero (nonzero :: functions);
    selectznz_correct :
      forall functions,
        spec_of_selectznz (selectznz :: functions);
    to_bytes_correct :
      forall functions,
        spec_of_to_bytes (to_bytes :: functions);
    from_bytes_correct :
      forall functions,
        spec_of_from_bytes (from_bytes :: functions) }.

Class names_of_operations :=
  { name_of_mul : string;
    name_of_square : string;
    name_of_add : string;
    name_of_sub : string;
    name_of_opp : string;
    name_of_to_montgomery : string;
    name_of_from_montgomery : string;
    name_of_nonzero : string;
    name_of_selectznz : string;
    name_of_to_bytes : string;
    name_of_from_bytes : string }.

Record wbwmontgomery_reified_ops
  {width BW word mem locals env ext_spec varname_gen error}
  {parameters_sentinel : @Types.parameters width BW word mem locals env ext_spec varname_gen error}
       {names : names_of_operations} {m} :=
  { reified_mul :
      reified_op name_of_mul
                 (Generic.WordByWordMontgomery.mul m)
                 (PushButtonSynthesis.WordByWordMontgomery.mul m width);
    reified_square :
      reified_op name_of_square
                 (Generic.WordByWordMontgomery.square m)
                 (PushButtonSynthesis.WordByWordMontgomery.square m width);
    reified_add :
      reified_op name_of_add
                 (Generic.WordByWordMontgomery.add m)
                 (PushButtonSynthesis.WordByWordMontgomery.add m width);
    reified_sub :
      reified_op name_of_sub
                 (Generic.WordByWordMontgomery.sub m)
                 (PushButtonSynthesis.WordByWordMontgomery.sub m width);
    reified_opp :
      reified_op name_of_opp
                 (Generic.WordByWordMontgomery.opp m)
                 (PushButtonSynthesis.WordByWordMontgomery.opp m width);
    reified_to_montgomery :
      reified_op name_of_to_montgomery
                 (Generic.WordByWordMontgomery.to_montgomery m)
                 (PushButtonSynthesis.WordByWordMontgomery.to_montgomery m width);
    reified_from_montgomery :
      reified_op name_of_from_montgomery
                 (Generic.WordByWordMontgomery.from_montgomery m)
                 (PushButtonSynthesis.WordByWordMontgomery.from_montgomery m width);
    reified_nonzero :
      reified_op name_of_nonzero
                 (Generic.WordByWordMontgomery.nonzero m)
                 (PushButtonSynthesis.WordByWordMontgomery.nonzero m width);
    reified_selectznz :
      reified_op name_of_selectznz
                 (Generic.WordByWordMontgomery.selectznz m)
                 (PushButtonSynthesis.WordByWordMontgomery.selectznz m width);
    reified_to_bytes :
      reified_op name_of_to_bytes
                 (Generic.WordByWordMontgomery.to_bytes m)
                 (PushButtonSynthesis.WordByWordMontgomery.to_bytes m width);
    reified_from_bytes :
      reified_op name_of_from_bytes
                 (Generic.WordByWordMontgomery.from_bytes m)
                 (PushButtonSynthesis.WordByWordMontgomery.from_bytes m width) }.
Arguments wbwmontgomery_reified_ops {_ _ _ _ _ _ _ _ _ _ _} m.

(*** Helpers ***)

Definition names_from_prefix (prefix : string)
  : names_of_operations :=
  {| name_of_mul := (prefix ++ "mul")%string;
     name_of_square := (prefix ++ "square")%string;
     name_of_add := (prefix ++ "add")%string;
     name_of_sub := (prefix ++ "sub")%string;
     name_of_opp := (prefix ++ "opp")%string;
     name_of_to_montgomery := (prefix ++ "to_montgomery")%string;
     name_of_from_montgomery := (prefix ++ "from_montgomery")%string;
     name_of_nonzero := (prefix ++ "nonzero")%string;
     name_of_selectznz := (prefix ++ "selectznz")%string;
     name_of_to_bytes := (prefix ++ "to_bytes")%string;
     name_of_from_bytes := (prefix ++ "from_bytes")%string
  |}.

(*** Synthesis Tactics ***)

Ltac funcs_from_ops ops :=
  let mul_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_mul ops))) in
  let square_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_square ops))) in
  let add_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_add ops))) in
  let sub_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_sub ops))) in
  let to_montgomery_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_to_montgomery ops))) in
  let from_montgomery_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_from_montgomery ops))) in
  let opp_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_opp ops))) in
  let nonzero_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_nonzero ops))) in
  let selectznz_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_selectznz ops))) in
  let to_bytes_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_to_bytes ops))) in
  let from_bytes_func_value :=
      (eval lazy in
          (computed_bedrock_func (reified_from_bytes ops))) in
  exact {| mul := mul_func_value;
           square := square_func_value;
           add := add_func_value;
           sub := sub_func_value;
           opp := opp_func_value;
           to_montgomery := to_montgomery_func_value;
           from_montgomery := from_montgomery_func_value;
           nonzero := nonzero_func_value;
           selectznz := selectznz_func_value;
           to_bytes := to_bytes_func_value;
           from_bytes := from_bytes_func_value |}.

Ltac specs_from_ops ops m :=
  let p := lazymatch type of ops with wbwmontgomery_reified_ops(parameters_sentinel:=?p) _ => p end in
  let mul_name := (eval compute in name_of_mul) in
  let square_name := (eval compute in name_of_square) in
  let add_name := (eval compute in name_of_add) in
  let sub_name := (eval compute in name_of_sub) in
  let opp_name := (eval compute in name_of_opp) in
  let to_montgomery_name := (eval compute in name_of_to_montgomery) in
  let from_montgomery_name := (eval compute in name_of_from_montgomery) in
  let nonzero_name := (eval compute in name_of_nonzero) in
  let selectznz_name := (eval compute in name_of_selectznz) in
  let to_bytes_name := (eval compute in name_of_to_bytes) in
  let from_bytes_name := (eval compute in name_of_from_bytes) in
  let mul_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.mul
                 Generic.WordByWordMontgomery.spec_of_mul] in
          (Generic.WordByWordMontgomery.spec_of_mul
             (parameters_sentinel:=p) m mul_name)) in
  let square_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.square
                 Generic.WordByWordMontgomery.spec_of_square] in
          (Generic.WordByWordMontgomery.spec_of_square
             (parameters_sentinel:=p) m square_name)) in
  let add_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.add
                 Generic.WordByWordMontgomery.spec_of_add] in
          (Generic.WordByWordMontgomery.spec_of_add
             (parameters_sentinel:=p) m add_name)) in
  let sub_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.sub
                 Generic.WordByWordMontgomery.spec_of_sub] in
          (Generic.WordByWordMontgomery.spec_of_sub
             (parameters_sentinel:=p) m sub_name)) in
  let to_montgomery_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.to_montgomery
                 Generic.WordByWordMontgomery.spec_of_to_montgomery] in
          (Generic.WordByWordMontgomery.spec_of_to_montgomery
             (parameters_sentinel:=p) m to_montgomery_name)) in
  let from_montgomery_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.from_montgomery
                 Generic.WordByWordMontgomery.spec_of_from_montgomery] in
          (Generic.WordByWordMontgomery.spec_of_from_montgomery
             (parameters_sentinel:=p) m from_montgomery_name)) in
  let opp_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.opp
                 Generic.WordByWordMontgomery.spec_of_opp] in
          (Generic.WordByWordMontgomery.spec_of_opp
             (parameters_sentinel:=p) m opp_name)) in
  let nonzero_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.nonzero
                 Generic.WordByWordMontgomery.spec_of_nonzero] in
          (Generic.WordByWordMontgomery.spec_of_nonzero
             (parameters_sentinel:=p) m nonzero_name)) in
  let selectznz_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.selectznz
                 Generic.WordByWordMontgomery.spec_of_selectznz] in
          (Generic.WordByWordMontgomery.spec_of_selectznz
             (parameters_sentinel:=p) m selectznz_name)) in
  let to_bytes_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.to_bytes
                 Generic.WordByWordMontgomery.spec_of_to_bytes] in
          (Generic.WordByWordMontgomery.spec_of_to_bytes
             (parameters_sentinel:=p) m to_bytes_name)) in
  let from_bytes_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Generic.WordByWordMontgomery.from_bytes
                 Generic.WordByWordMontgomery.spec_of_from_bytes] in
          (Generic.WordByWordMontgomery.spec_of_from_bytes
             (parameters_sentinel:=p) m from_bytes_name)) in
  exact {| spec_of_mul := mul_spec;
           spec_of_square := square_spec;
           spec_of_add := add_spec;
           spec_of_sub := sub_spec;
           spec_of_opp := opp_spec;
           spec_of_to_montgomery := to_montgomery_spec;
           spec_of_from_montgomery := from_montgomery_spec;
           spec_of_nonzero := nonzero_spec;
           spec_of_selectznz := selectznz_spec;
           spec_of_to_bytes := to_bytes_spec;
           spec_of_from_bytes := from_bytes_spec |}.

Ltac handle_easy_preconditions :=
  lazymatch goal with
  | |- ZRange.type.option.is_tighter_than _ _ = true =>
    abstract vm_cast_no_check (eq_refl true)
  | |- Types.ok => solve [typeclasses eauto]
  | |- _ = ErrorT.Success _ => solve [apply reified_eq]
  | |- API.Wf _ => solve [apply reified_Wf]
  | |- Func.valid_func _ => solve [apply reified_valid]
  | _ => first [ apply inname_gen_varname_gen_disjoint
               | apply outname_gen_varname_gen_disjoint
               | apply outname_gen_inname_gen_disjoint
               | apply prefix_name_gen_unique ]
  | |- ?g => fail "Unrecognized goal" g
  end.

Ltac use_correctness_proofs p m :=
  let Hc := fresh in
  match goal with
  | |- context [Generic.WordByWordMontgomery.mul] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.mul_correct
  | |- context [Generic.WordByWordMontgomery.square] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.square_correct
  | |- context [Generic.WordByWordMontgomery.add] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.add_correct
  | |- context [Generic.WordByWordMontgomery.sub] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.sub_correct
  | |- context [Generic.WordByWordMontgomery.opp] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.opp_correct
  | |- context [Generic.WordByWordMontgomery.to_montgomery] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.to_montgomery_correct
  | |- context [Generic.WordByWordMontgomery.from_montgomery] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.from_montgomery_correct
  | |- context [Generic.WordByWordMontgomery.nonzero] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.nonzero_correct
  | |- context [Generic.WordByWordMontgomery.selectznz] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.selectznz_correct
  | |- context [Generic.WordByWordMontgomery.to_bytes] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.to_bytes_correct
  | |- context [Generic.WordByWordMontgomery.from_bytes] =>
    Coq.Program.Tactics.rapply @Generic.WordByWordMontgomery.from_bytes_correct
  end.

Ltac change_with_computed_func ops :=
  lazymatch goal with
  | |- context [mul] =>
    change mul with (computed_bedrock_func (reified_mul ops))
  | |- context [square] =>
    change square with (computed_bedrock_func (reified_square ops))
  | |- context [add] =>
    change add with (computed_bedrock_func (reified_add ops))
  | |- context [sub] =>
    change sub with (computed_bedrock_func (reified_sub ops))
  | |- context [opp] =>
    change opp with (computed_bedrock_func (reified_opp ops))
  | |- context [to_montgomery] =>
    change to_montgomery with (computed_bedrock_func (reified_to_montgomery ops))
  | |- context [from_montgomery] =>
    change from_montgomery with (computed_bedrock_func (reified_from_montgomery ops))
  | |- context [nonzero] =>
    change nonzero with (computed_bedrock_func (reified_nonzero ops))
  | |- context [selectznz] =>
    change selectznz with (computed_bedrock_func (reified_selectznz ops))
  | |- context [to_bytes] =>
    change to_bytes with (computed_bedrock_func (reified_to_bytes ops))
  | |- context [from_bytes] =>
    change from_bytes with (computed_bedrock_func (reified_from_bytes ops))
  end.

Ltac prove_correctness ops m :=
  let width := lazymatch type of ops with wbwmontgomery_reified_ops(width:=?width) _ => width end in
  assert (WordByWordMontgomery.check_args
            m width [] (ErrorT.Success tt) =
          ErrorT.Success tt) by abstract (native_compute; reflexivity);
  lazymatch goal with
    | |- bedrock2_wbwmontgomery_correctness => econstructor end;
  change_with_computed_func ops; rewrite computed_bedrock_func_eq;
  let p := lazymatch type of ops with wbwmontgomery_reified_ops(parameters_sentinel:=?p) _ => p end in
  use_correctness_proofs p m; try assumption;
  handle_easy_preconditions.

Ltac make_names_of_operations prefix :=
  match goal with
  | |- names_of_operations =>
    let n := eval vm_compute in (names_from_prefix prefix) in
        exact n
  end.

Ltac make_reified_ops :=
  lazymatch goal with
    |- wbwmontgomery_reified_ops ?m =>
    eapply Build_wbwmontgomery_reified_ops
  end; prove_reified_op.
