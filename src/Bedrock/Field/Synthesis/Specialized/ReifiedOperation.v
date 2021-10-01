
Require Import coqutil.Word.Interface.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.

Import API.Compilers.

(** This file contains a record that contains a fully computed bedrock2
translation of a function, as well as all information about the computed term
that is necessary to prove the preconditions of translate_func. This way,
computation of the full term is separated from the rest of the proofs, which has
performance benefits. **)

Record reified_op
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @Types.parameters width BW word mem locals env ext_spec varname_gen error}
    {t}
       {name : String.string}
       {op : operation t}
       {start : ErrorT.ErrorT Pipeline.ErrorMessage
                              (API.Expr t)} :=
  { res : API.Expr t;
    computed_bedrock_func : Syntax.func;
    computed_bedrock_func_eq :
      computed_bedrock_func = make_bedrock_func (inname_gen:=default_inname_gen) (outname_gen:=default_outname_gen) name op res;
    reified_eq : start = ErrorT.Success res;
    reified_Wf_via_start : forall res, start = ErrorT.Success res -> API.Wf res;
    reified_Wf : API.Wf res := reified_Wf_via_start _ reified_eq;
    reified_valid : Func.valid_func (res (fun _ => unit));
  }.
Global Arguments reified_op {_ _ _ _ _ _ _ _ _ _ t} name op start.

Ltac prove_reified_op :=
  lazymatch goal with |- reified_op _ _ _ => idtac end;
  econstructor;
  (* important to compute the function body first, before solving other
     subgoals *)
  lazymatch goal with
  | |- ?start = ErrorT.Success _ =>
    vm_compute; reflexivity
  | |- Func.valid_func _ => eapply valid_func_bool_iff
  | _ => idtac
  end;
  [ match goal with
    | |- _ = make_bedrock_func _ _ _ =>
      vm_compute; reflexivity end | .. ];
  lazymatch goal with
  | |- forall res, ?e = _ -> API.Wf _ =>
    (* Kludge around auto being bad (COQBUG(https://github.com/coq/coq/issues/14190)) and eauto not respecting Hint Opaque *)
    typeclasses eauto with wf_op_cache;
    idtac "Warning: Falling back to manually proving pipeline well-formedness for" e;
    PipelineTactics.prove_pipeline_wf ()
  | |- valid_func_bool ?x = true =>
    abstract vm_cast_no_check (eq_refl true)
  end.
Ltac make_reified_op parameters_sentinel name op start :=
  assert (reified_op (parameters_sentinel:=parameters_sentinel) _ name op start) by prove_reified_op.
