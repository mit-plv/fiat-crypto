Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.forward.
Require Import coqutil.Word.Interface.
Require Import Rewriter.Language.Wf.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.
Import ListNotations.
Import AbstractInterpretation.Compilers.
Import Language.Wf.Compilers.

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

Local Notation make_bedrock_func :=
  (@make_bedrock_func _ default_inname_gen default_outname_gen).
Local Notation make_bedrock_func_with_sizes :=
  (@make_bedrock_func_with_sizes _ default_inname_gen default_outname_gen).

Record reified_op {p t}
       (op : operation t)
       (start : ErrorT.ErrorT BoundsPipeline.Pipeline.ErrorMessage
                              (API.Expr t)) :=
  { res : API.Expr t;
    computed_bedrock_func : bedrock_func;
    computed_bedrock_func_eq :
      computed_bedrock_func = make_bedrock_func op res;
    reified_eq : start = ErrorT.Success res;
    reified_Wf3 : expr.Wf3 res;
    reified_valid : Func.valid_func (p:=p) (res (fun _ => unit));
  }.
Arguments res {_ _ _}.
Arguments reified_eq {_ _ _}.
Arguments reified_Wf3 {_ _ _}.
Arguments reified_valid {_ _ _}.

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

Ltac make_reified_op op start :=
  assert (reified_op op start)
  by (econstructor; try apply valid_func_bool_iff;
      (* important to compute the function body first, before solving other
         subgoals *)
      lazymatch goal with
      | |- ?start = ErrorT.Success _ =>
        vm_compute; reflexivity
      | _ => idtac
      end;
      idtac "  computing bedrock2 translation...";
      [ match goal with
        | |- _ = make_bedrock_func _ _ =>
          vm_compute; reflexivity end | .. ];
      idtac "  proving Wf3 and valid_func...";
      match goal with
      | |- expr.Wf3 _ => abstract (prove_Wf3 ())
      | |- valid_func_bool ?x = true =>
        abstract (vm_compute; reflexivity)
      end).

Ltac parameters_from_wordsize machine_wordsize :=
  let r := (eval cbv - [Defaults32.default_parameters
                          Defaults64.default_parameters] in
               (select_parameters machine_wordsize)) in
  lazymatch r with
  | inl ?p => p
  | inr ?err => fail "Failed to select parameters: " err
  end.

Ltac make_all_reified_ops n s c machine_wordsize :=
  idtac "computing reified carry_mul (slow)...";
  make_reified_op
    (UnsaturatedSolinas.carry_mul n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
       n s c machine_wordsize);
  idtac "computing reified carry_square (slow)...";
  make_reified_op
    (UnsaturatedSolinas.carry_square n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry_square
       n s c machine_wordsize);
  idtac "computing reified carry...";
  make_reified_op
    (UnsaturatedSolinas.carry n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.carry
       n s c machine_wordsize);
  idtac "computing reified add...";
  make_reified_op
    (UnsaturatedSolinas.add n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.add
       n s c machine_wordsize);
  idtac "computing reified sub...";
  make_reified_op
    (UnsaturatedSolinas.sub n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.sub
       n s c machine_wordsize);
  idtac "computing reified opp...";
  make_reified_op
    (UnsaturatedSolinas.opp n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.opp
       n s c machine_wordsize);
  idtac "computing reified selectznz...";
  make_reified_op
    (UnsaturatedSolinas.selectznz n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.selectznz
       n machine_wordsize);
  idtac "computing reified to_bytes (slow)...";
  make_reified_op
    (UnsaturatedSolinas.to_bytes n s c)
    (PushButtonSynthesis.UnsaturatedSolinas.to_bytes
       n s c machine_wordsize);
  idtac "computing reified from_bytes (slow)...";
  make_reified_op
    (UnsaturatedSolinas.from_bytes n s c)
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
           | context [UnsaturatedSolinas.carry_mul] =>
             destruct X as [? carry_mul_func_value ?]
           | context [UnsaturatedSolinas.carry_square] =>
             destruct X as [? carry_square_func_value ?]
           | context [UnsaturatedSolinas.carry] =>
             destruct X as [? carry_func_value ?]
           | context [UnsaturatedSolinas.add] =>
             destruct X as [? add_func_value ?]
           | context [UnsaturatedSolinas.sub] =>
             destruct X as [? sub_func_value ?]
           | context [UnsaturatedSolinas.opp] =>
             destruct X as [? opp_func_value ?]
           | context [UnsaturatedSolinas.selectznz] =>
             destruct X as [? selectznz_func_value ?]
           | context [UnsaturatedSolinas.to_bytes] =>
             destruct X as [? to_bytes_func_value ?]
           | context [UnsaturatedSolinas.from_bytes] =>
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

(* TODO: move *)
Definition names_from_prefix (prefix : string) : names_of_operations :=
  {| name_of_carry_mul := (prefix ++ "carry_mul")%string;
     name_of_carry_square := (prefix ++ "carry_square")%string;
     name_of_carry := (prefix ++ "carry")%string;
     name_of_add := (prefix ++ "add")%string;
     name_of_sub := (prefix ++ "sub")%string;
     name_of_opp := (prefix ++ "opp")%string;
     name_of_selectznz := (prefix ++ "selectznz")%string;
     name_of_to_bytes := (prefix ++ "to_bytes")%string;
     name_of_from_bytes := (prefix ++ "from_bytes")%string;
     name_of_carry_scmul_const := (prefix ++ "carry_scmul_const")%string
  |}.
(* TODO: move *)
Ltac use_correctness_proofs :=
  match goal with
  | |- context [UnsaturatedSolinas.spec_of_carry_mul] =>
    apply UnsaturatedSolinas.carry_mul_correct
  | |- context [UnsaturatedSolinas.spec_of_carry_square] =>
    apply UnsaturatedSolinas.carry_square_correct
  | |- context [UnsaturatedSolinas.spec_of_carry] =>
    apply UnsaturatedSolinas.carry_correct
  | |- context [UnsaturatedSolinas.spec_of_add] =>
    apply UnsaturatedSolinas.add_correct
  | |- context [UnsaturatedSolinas.spec_of_sub] =>
    apply UnsaturatedSolinas.sub_correct
  | |- context [UnsaturatedSolinas.spec_of_opp] =>
    apply UnsaturatedSolinas.opp_correct
  | |- context [UnsaturatedSolinas.spec_of_selectznz] =>
    apply UnsaturatedSolinas.selectznz_correct
  | |- context [UnsaturatedSolinas.spec_of_to_bytes] =>
    apply UnsaturatedSolinas.to_bytes_correct
  | |- context [UnsaturatedSolinas.spec_of_from_bytes] =>
    apply UnsaturatedSolinas.from_bytes_correct
  | |- context [UnsaturatedSolinas.spec_of_carry_scmul_const] =>
    apply UnsaturatedSolinas.carry_scmul_const_correct
  end.

Module X25519_64.
  Let n := 10%nat.
  Let s := 2^255.
  Let c := [(1, 19)].
  Let machine_wordsize := 64.

  Local Instance names : names_of_operations.
  let n := eval cbv in (names_from_prefix "curve25519_") in
      exact n. Defined.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance curve25519_bedrock2 : bedrock2_unsaturated_solinas n s c.
  Proof.
    make_all_reified_ops n s c machine_wordsize.
    instantiate_ops.
    all: use_correctness_proofs.
    all: try assumption.
    all: try abstract (handle_easy_preconditions).
  Time Defined.
  (* Eval cbv [carry_mul curve25519_bedrock2] in carry_mul. *)

  Instance curve25519_bedrock2_scmul
    : bedrock2_unsaturated_solinas_scmul n s c 121666.
  Proof.
    let x := constr:(121666) in
    make_reified_op
      (UnsaturatedSolinas.carry_scmul_const n s c x)
      (PushButtonSynthesis.UnsaturatedSolinas.carry_scmul_const
         n s c machine_wordsize x).
    match goal with
    | X : reified_op ?op _ |- _ =>
      destruct X as [? scmul_func_value ?] end.
    apply Build_bedrock2_unsaturated_solinas_scmul
      with (carry_scmul_const:=scmul_func_value); subst scmul_func_value.
    all: use_correctness_proofs.
    all: try assumption.
    all: try abstract (handle_easy_preconditions).
  Time Defined.
  (* Eval cbv [carry_scmul_const curve25519_bedrock2_scmul]
       in carry_scmul_const. *)
End X25519_64.

Module X1305_32.
  Let n := 5%nat.
  Let s := 2^130.
  Let c := [(1, 5)].
  Let machine_wordsize := 32.

  Local Instance names : names_of_operations.
  let n := eval cbv in (names_from_prefix "poly1305_") in
      exact n. Defined.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance poly1305_bedrock2 : bedrock2_unsaturated_solinas n s c.
  Proof.
    make_all_reified_ops n s c machine_wordsize.
    instantiate_ops.
    all: use_correctness_proofs.
    all: try assumption.
    all: try abstract (handle_easy_preconditions).
  Time Defined.
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
  Existing Instances Defaults64.default_parameters names curve25519_bedrock2.
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
      forall x y old_out px py pout t m
             (R : Interface.map.rep
                    (map:=Semantics.mem) -> Prop),
        let xz := map word.unsigned x in
        let yz := map word.unsigned y in
        list_Z_bounded_by loose_bounds xz ->
        list_Z_bounded_by loose_bounds yz ->
        length old_out = X25519_64.n ->
        sep (sep (Bignum px x)
                 (sep (Bignum py y) (Bignum pout old_out)))
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
                  let outz := map word.unsigned out in
                  sep
                    (sep (emp (eval outz mod M
                               = (eval xz * eval yz * eval yz) mod M
                               /\ list_Z_bounded_by tight_bounds outz))
                         (Bignum pout out))
                    (sep (Bignum px x) (sep (Bignum py y) R))) m').

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
    enter mul_twice. cbv zeta. intros.
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
    straightline_call; sepsimpl;
      [ try ecancel_assumption .. | ];
      [ rewrite ?map_length; assumption .. | ].
    repeat straightline.

    lazymatch goal with
      H : postcondition _ _ ?out |- _ =>
      cbn [fst snd postcondition UnsaturatedSolinas.carry_mul] in H;
        repeat specialize (H ltac:(assumption)); cleanup
    end.
    straightline_call; sepsimpl;
      [ try ecancel_assumption .. | ].
    { apply relax_correct. assumption. }
    { assumption. }
    { eapply bounded_by_loose_bounds_length.
      apply relax_correct. eassumption. }

    repeat straightline.
    lazymatch goal with
      H : postcondition _ _ ?out |- _ =>
      cbn [fst snd postcondition UnsaturatedSolinas.carry_mul] in H;
        specialize (H ltac:(apply relax_correct; assumption));
        specialize (H ltac:(assumption)); cleanup
    end.

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
  Qed.
End Test.
