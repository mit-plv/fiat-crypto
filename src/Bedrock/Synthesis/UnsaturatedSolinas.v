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

Record names_of_operations :=
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

Class bedrock2_unsaturated_solinas :=
  { carry_mul : bedrock_func;
    carry_square : bedrock_func;
    carry : bedrock_func;
    add : bedrock_func;
    sub : bedrock_func;
    opp : bedrock_func;
    selectznz : bedrock_func;
    to_bytes : bedrock_func;
    from_bytes : bedrock_func;
    spec_of_carry_mul : spec_of (fst carry_mul);
    spec_of_carry_square : spec_of (fst carry_square);
    spec_of_carry : spec_of (fst carry);
    spec_of_add : spec_of (fst add);
    spec_of_sub : spec_of (fst sub);
    spec_of_opp : spec_of (fst opp);
    spec_of_selectznz : spec_of (fst selectznz);
    spec_of_to_bytes : spec_of (fst to_bytes);
    spec_of_from_bytes : spec_of (fst from_bytes);
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

(* scalar multiplication is calculated separately since it requires an extra
   argument *)
Class bedrock2_unsaturated_solinas_scmul {x : Z} :=
  { carry_scmul_const : bedrock_func;
    spec_of_carry_scmul_const : spec_of (fst carry_scmul_const);
    carry_scmul_const_correct :
      forall functions,
        spec_of_carry_scmul_const (carry_scmul_const :: functions) }.
Arguments bedrock2_unsaturated_solinas_scmul x : clear implicits.

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

(*** Synthesis tactics ***)

Ltac handle_easy_preconditions :=
  lazymatch goal with
  | |- ZRange.type.option.is_tighter_than _ _ = true =>
    abstract (vm_compute; reflexivity)
  | |- Types.ok => solve [typeclasses eauto]
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

Ltac make_all_reified_ops p names n s c machine_wordsize :=
  let carry_mul_name := (eval compute in (name_of_carry_mul names)) in
  let carry_square_name := (eval compute in (name_of_carry_square names)) in
  let carry_name := (eval compute in (name_of_carry names)) in
  let add_name := (eval compute in (name_of_add names)) in
  let sub_name := (eval compute in (name_of_sub names)) in
  let opp_name := (eval compute in (name_of_opp names)) in
  let selectznz_name := (eval compute in (name_of_selectznz names)) in
  let to_bytes_name := (eval compute in (name_of_to_bytes names)) in
  let from_bytes_name := (eval compute in (name_of_from_bytes names)) in
  idtac "computing reified carry_mul (slow)...";
  make_reified_op
    p carry_mul_name
    (@Interfaces.UnsaturatedSolinas.carry_mul p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
       n s c machine_wordsize);
  idtac "computing reified carry_square (slow)...";
  make_reified_op
    p carry_square_name
    (@Interfaces.UnsaturatedSolinas.carry_square p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_square
       n s c machine_wordsize);
  idtac "computing reified carry...";
  make_reified_op
    p carry_name
    (@Interfaces.UnsaturatedSolinas.carry p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry
       n s c machine_wordsize);
  idtac "computing reified add...";
  make_reified_op
    p add_name
    (@Interfaces.UnsaturatedSolinas.add p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.add
       n s c machine_wordsize);
  idtac "computing reified sub...";
  make_reified_op
    p sub_name
    (@Interfaces.UnsaturatedSolinas.sub p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.sub
       n s c machine_wordsize);
  idtac "computing reified opp...";
  make_reified_op
    p opp_name
    (@Interfaces.UnsaturatedSolinas.opp p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.opp
       n s c machine_wordsize);
  idtac "computing reified selectznz...";
  make_reified_op
    p selectznz_name
    (@Interfaces.UnsaturatedSolinas.selectznz p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.selectznz
       n machine_wordsize);
  idtac "computing reified to_bytes (slow)...";
  make_reified_op
    p to_bytes_name
    (@Interfaces.UnsaturatedSolinas.to_bytes p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.to_bytes
       n s c machine_wordsize);
  idtac "computing reified from_bytes (slow)...";
  make_reified_op
    p from_bytes_name
    (@Interfaces.UnsaturatedSolinas.from_bytes p n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.from_bytes
       n s c machine_wordsize).

Ltac instantiate_ops p names n s c :=
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
         | X : reified_op _ ?op _ |- _ =>
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
  let carry_mul_name := (eval compute in (name_of_carry_mul names)) in
  let carry_square_name := (eval compute in (name_of_carry_square names)) in
  let carry_name := (eval compute in (name_of_carry names)) in
  let add_name := (eval compute in (name_of_add names)) in
  let sub_name := (eval compute in (name_of_sub names)) in
  let opp_name := (eval compute in (name_of_opp names)) in
  let selectznz_name := (eval compute in (name_of_selectznz names)) in
  let to_bytes_name := (eval compute in (name_of_to_bytes names)) in
  let from_bytes_name := (eval compute in (name_of_from_bytes names)) in
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
    apply Build_bedrock2_unsaturated_solinas
      with (carry_mul:=carry_mul_func_value)
           (spec_of_carry_mul:=carry_mul_spec)
           (carry_square:=carry_square_func_value)
           (spec_of_carry_square:=carry_square_spec)
           (carry:=carry_func_value)
           (spec_of_carry:=carry_spec)
           (add:=add_func_value)
           (spec_of_add:=add_spec)
           (sub:=sub_func_value)
           (spec_of_sub:=sub_spec)
           (opp:=opp_func_value)
           (spec_of_opp:=opp_spec)
           (selectznz:=selectznz_func_value)
           (spec_of_selectznz:=selectznz_spec)
           (to_bytes:=to_bytes_func_value)
           (spec_of_to_bytes:=to_bytes_spec)
           (from_bytes:=from_bytes_func_value)
           (spec_of_from_bytes:=from_bytes_spec);
  subst carry_mul_func_value carry_square_func_value carry_func_value
        add_func_value sub_func_value opp_func_value selectznz_func_value
        to_bytes_func_value from_bytes_func_value.

Ltac make_bedrock2_unsaturated_solinas p names n s c machine_wordsize :=
  assert (UnsaturatedSolinas.check_args
            n s c machine_wordsize (ErrorT.Success tt) =
          ErrorT.Success tt) by abstract (native_compute; reflexivity);
  match goal with
    | |- bedrock2_unsaturated_solinas =>
      make_all_reified_ops p names n s c machine_wordsize;
      instantiate_ops p names n s c;
      use_correctness_proofs p n s c; try assumption;
      abstract (handle_easy_preconditions)
  end.

Ltac make_bedrock2_unsaturated_solinas_scmul
     p names n s c machine_wordsize :=
  assert (UnsaturatedSolinas.check_args
            n s c machine_wordsize (ErrorT.Success tt) =
          ErrorT.Success tt) by abstract (native_compute; reflexivity);
  let x := match goal with
             |- bedrock2_unsaturated_solinas_scmul ?x => x end in
  let carry_scmul_const_name :=
      (eval compute in (name_of_carry_scmul_const names x)) in
  make_reified_op
    p carry_scmul_const_name
    (@Interfaces.UnsaturatedSolinas.carry_scmul_const p n s c x)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_scmul_const
       n s c machine_wordsize x);
  let scmul_func_value := fresh "scmul_func_value" in
  match goal with
  | X : reified_op _ ?op _ |- _ =>
    destruct X as [? scmul_func_value ?] end;
  let carry_scmul_const_spec :=
      (eval cbv
            [fst snd precondition postcondition
                 Interfaces.UnsaturatedSolinas.carry_scmul_const
                 Interfaces.UnsaturatedSolinas.spec_of_carry_scmul_const] in
          (@Interfaces.UnsaturatedSolinas.spec_of_carry_scmul_const
             p n s c x carry_scmul_const_name)) in
  apply Build_bedrock2_unsaturated_solinas_scmul
    with (carry_scmul_const:=scmul_func_value)
         (spec_of_carry_scmul_const:=carry_scmul_const_spec);
  subst scmul_func_value;
  use_correctness_proofs p n s c; try assumption;
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

(*

Let n := 5%nat.
Let s := 2^130.
Let c := [(1, 5)].
Let machine_wordsize := 64.
Let prefix := "poly1305_"%string.

Definition names : names_of_operations.
make_names_of_operations prefix. Defined.

Instance poly1305_bedrock2 : bedrock2_unsaturated_solinas.
Proof.
  let p := parameters_from_wordsize machine_wordsize in
  make_bedrock2_unsaturated_solinas p names n s c machine_wordsize.
Time Defined.

Instance poly1305_bedrock2_scmul5 : bedrock2_unsaturated_solinas_scmul 5.
Proof.
  let p := parameters_from_wordsize machine_wordsize in
  make_bedrock2_unsaturated_solinas_scmul p names n s c machine_wordsize.
Time Defined.

*)
