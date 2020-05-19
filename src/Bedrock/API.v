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
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.SelectParameters.
Require Import Crypto.Bedrock.UnsaturatedSolinas.
Require Import Crypto.Bedrock.VarnameGenerator.
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
        spec_of_carry_mul (carry_mul :: functions);
    add : bedrock_func;
    spec_of_add : spec_of (fst add) :=
      @spec_of_add p n s c (fst add);
    add_correct :
      forall functions,
        spec_of_add (add :: functions);
    to_bytes : bedrock_func;
    spec_of_to_bytes : spec_of (fst to_bytes) :=
      @spec_of_to_bytes p n s c (fst to_bytes);
    to_bytes_correct :
      forall functions,
        spec_of_to_bytes (to_bytes :: functions) }.
Arguments carry_mul {_ _ _ _ _}.
Arguments spec_of_carry_mul {_ _ _ _ _}.
Arguments carry_mul_correct {_ _ _ _ _}.
Arguments add {_ _ _ _ _}.
Arguments spec_of_add {_ _ _ _ _}.
Arguments add_correct {_ _ _ _ _}.
Arguments to_bytes {_ _ _ _ _}.
Arguments spec_of_to_bytes {_ _ _ _ _}.
Arguments to_bytes_correct {_ _ _ _ _}.

Local Notation make_bedrock_func :=
  (@make_bedrock_func _ default_inname_gen default_outname_gen).
Local Notation make_bedrock_func_with_sizes :=
  (@make_bedrock_func_with_sizes _ default_inname_gen default_outname_gen).

Record reified_op {p t}
       (sig : FunctionSignature t)
       (start : ErrorT.ErrorT BoundsPipeline.Pipeline.ErrorMessage
                              (API.Expr t)) :=
  { res : API.Expr t;
    computed_bedrock_func : bedrock_func;
    computed_bedrock_func_eq :
      computed_bedrock_func = make_bedrock_func sig res;
    reified_eq : start = ErrorT.Success res;
    reified_Wf3 : expr.Wf3 res;
    reified_valid : Func.valid_func (p:=p) (res (fun _ => unit));
    reified_output_sizes : output_sizes_obeyed sig res;
  }.
Arguments res {_ _ _}.
Arguments reified_eq {_ _ _}.
Arguments reified_Wf3 {_ _ _}.
Arguments reified_valid {_ _ _}.
Arguments reified_output_sizes {_ _ _}.

Class names_of_operations :=
  { name_of_carry_mul : string;
    name_of_add : string;
    name_of_to_bytes : string }.

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

Ltac make_reified_op sig start :=
  assert (reified_op sig start)
  by (econstructor; try apply valid_func_bool_iff;
      (* important to compute the function body first, before solving other
         subgoals *)
      lazymatch goal with
      | |- ?start = ErrorT.Success _ =>
        vm_compute; reflexivity
      | _ => idtac
      end).
(*
      [ vm_compute; reflexivity
      | abstract (prove_Wf3 ())
      | abstract (vm_compute; reflexivity) ]). *)

Ltac parameters_from_wordsize machine_wordsize :=
  let r := (eval cbv - [Defaults32.default_parameters
                          Defaults64.default_parameters] in
               (select_parameters machine_wordsize)) in
  lazymatch r with
  | inl ?p => p
  | inr ?err => fail "Failed to select parameters: " err
  end.

Ltac make_all_reified_ops names n s c machine_wordsize :=
  idtac "computing reified carry_mul (this one can be slow)...";
  make_reified_op
    (UnsaturatedSolinas.carry_mul n (@name_of_carry_mul names))
    (PushButtonSynthesis.UnsaturatedSolinas.carry_mul
       n s c machine_wordsize);
  idtac "computing reified add...";
  make_reified_op
    (UnsaturatedSolinas.add n (@name_of_add names))
    (PushButtonSynthesis.UnsaturatedSolinas.add
       n s c machine_wordsize);
  idtac "computing reified to_bytes...";
  make_reified_op
    (UnsaturatedSolinas.to_bytes n s c (@name_of_to_bytes names))
    (PushButtonSynthesis.UnsaturatedSolinas.to_bytes
       n s c machine_wordsize).

Ltac instantiate_ops names :=
    let carry_mul_func_value := fresh "carry_mul_func" in
    let carry_mul_func_eq := fresh "carry_mul_name_eq" in
    let add_func_value := fresh "add_func" in
    let add_func_eq := fresh "add_name_eq" in
    let to_bytes_func_value := fresh "to_bytes_func" in
    let to_bytes_func_eq := fresh "to_bytes_name_eq" in
    lazymatch goal with
    | X : reified_op
            _ (PushButtonSynthesis.UnsaturatedSolinas.carry_mul _ _ _ _)
      |- _ =>
      destruct X as [? carry_mul_func_value carry_mul_func_eq ]
    end;
      lazymatch goal with
      | X : reified_op
              _ (PushButtonSynthesis.UnsaturatedSolinas.add _ _ _ _)
        |- _ =>
        destruct X as [? add_func_value add_func_eq ]
      end;
      lazymatch goal with
      | X : reified_op
              _ (PushButtonSynthesis.UnsaturatedSolinas.to_bytes _ _ _ _)
        |- _ =>
        destruct X as [? to_bytes_func_value to_bytes_func_eq ]
      end;
  apply Build_bedrock2_unsaturated_solinas
    with (carry_mul:=carry_mul_func_value)
         (add:=add_func_value)
         (to_bytes:=to_bytes_func_value);
  rewrite ?carry_mul_func_eq, ?add_func_eq, ?to_bytes_func_eq.

Ltac use_correctness_proofs :=
  match goal with
  | |- context [UnsaturatedSolinas.spec_of_carry_mul] =>
    apply UnsaturatedSolinas.carry_mul_correct
  | |- context [UnsaturatedSolinas.spec_of_add] =>
    apply UnsaturatedSolinas.add_correct
  | |- context [UnsaturatedSolinas.spec_of_to_bytes] =>
    apply UnsaturatedSolinas.to_bytes_correct
  end.

Module X25519_64.
  Let n := 10%nat.
  Let s := 2^255.
  Let c := [(1, 19)].
  Let machine_wordsize := 64.

  Definition names : names_of_operations :=
    {| name_of_carry_mul := "curve25519_carry_mul"%string;
       name_of_add := "curve25519_add"%string;
       name_of_to_bytes := "curve25519_to_bytes"%string; |}.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance curve25519_bedrock2 : bedrock2_unsaturated_solinas p n s c.
  Proof.
    let sig :=
        constr:(UnsaturatedSolinas.add n (@name_of_add names)) in
    let start := constr:(PushButtonSynthesis.UnsaturatedSolinas.add
       n s c machine_wordsize) in
    assert (reified_op sig start).
     { econstructor; try apply valid_func_bool_iff;
      lazymatch goal with
          | |- ?start = ErrorT.Success _ =>
            vm_compute; reflexivity
          | _ => idtac
      end.
       all:
         try match goal with
             | |- _ = make_bedrock_func _ _ =>
               vm_compute; reflexivity
             | |- expr.Wf3 _ => abstract (prove_Wf3 ())
             | |- valid_func_bool ?x = true =>
               abstract (vm_compute; reflexivity)
             end.
       { cbn.
         cbv [output_sizes_obeyed]. intros.
         cbn - [Memory.bytes_per Types.semantics].
         repeat apply Forall_cons; try apply Forall_nil.
         all:match goal with
               |- _ <= PreExtra.ident.cast ?r ?x < 2 ^ ?y =>
               pose proof CastLemmas.ident.cast_bounded r x
                    ltac:(cbn [ident.literal ZRange.upper ZRange.lower]; lia);
                 let z := (eval vm_compute in (2 ^ y)) in
                 change (2 ^ y) with z
             end.
         all:cbv [ZRange.is_bounded_by_bool] in *;
           cbn [ZRange.lower ZRange.upper ident.literal] in *.
         all:match goal with
               H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H; destruct H
             end;
           LtbToLt.Z.ltb_to_lt.
         all:lia. } }
    make_all_reified_ops names n s c machine_wordsize.
    instantiate_ops names.
    all:use_correctness_proofs.
    all: try assumption.
    all: try abstract (handle_easy_preconditions).
    { cbn.
      cbv.
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
  Definition add_name := "poly1305_add"%string.
  Definition to_bytes_name := "poly1305_to_bytes"%string.

  Local Instance p : Types.parameters.
  let p := parameters_from_wordsize machine_wordsize in
  exact p. Defined.

  Local Instance p_ok : Types.ok. typeclasses eauto. Qed.

  Instance poly1305_bedrock2 : bedrock2_unsaturated_solinas p n s c.
  Proof.
    make_all_reified_ops n s c machine_wordsize.
    instantiate_ops carry_mul_name add_name to_bytes_name.
    all: use_correctness_proofs.
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
    sepsimpl.
    cbv [Solinas_carry_mul_correct] in *.
    repeat straightline.
    straightline_call; sepsimpl;
      [ try ecancel_assumption .. | ].
    { apply relax_correct; assumption. }
    { assumption. }
    { match goal with
      | H : list_Z_bounded_by tight_bounds ?x |- length ?x = _ =>
        apply relax_correct, bounded_by_loose_bounds_length in H;
          apply H
      end. }

    cbv [Solinas_carry_mul_correct] in *.
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
  Qed.
End Test.
