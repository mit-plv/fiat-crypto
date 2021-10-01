Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Tactics.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

(* convenience notations for readability *)
Notation foreach_arg F t :=
  (type.for_each_lhs_of_arrow F t) (only parsing).
Notation foreach_ret F t :=
  (F (type.base (type.final_codomain t))) (only parsing).

Section op.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {inname_gen outname_gen : nat -> string}.

  Definition make_bedrock_func_with_sizes
             {t} insizes outsizes inlengths (res : API.Expr t)
    : list string * list string * cmd.cmd :=
    fst (translate_func res
                        (make_innames (inname_gen:=inname_gen) _)
                        inlengths insizes
                        (make_outnames (outname_gen:=outname_gen) _)
                        outsizes).

  Record operation (t : API.type) :=
    { inbounds : foreach_arg ZRange.type.option.interp t;
      input_array_sizes : foreach_arg access_sizes t;
      output_array_sizes : foreach_ret access_sizes t;
      input_array_lengths : foreach_arg list_lengths t;
      output_array_lengths : foreach_ret list_lengths t;
      pipeline_out : Pipeline.ErrorT (API.Expr t);
      precondition : foreach_arg API.interp_type t -> Prop;
      postcondition : foreach_arg API.interp_type t
                      -> foreach_ret API.interp_type t -> Prop;
      check_args_ok : Prop;
      correctness :
        check_args_ok ->
        forall res,
          pipeline_out = ErrorT.Success res ->
          forall args,
            precondition args ->
            postcondition args (type.app_curried (API.Interp res) args)
    }.
 Global Arguments inbounds {_}.
 Global Arguments input_array_sizes {_}.
 Global Arguments output_array_sizes {_}.
 Global Arguments input_array_lengths {_}.
 Global Arguments output_array_lengths {_}.
 Global Arguments pipeline_out {_}.
 Global Arguments precondition {_}.
 Global Arguments postcondition {_}.
 Global Arguments check_args_ok {_}.
 Global Arguments correctness {_}.

  Definition make_bedrock_func
             {t} (name : string) (op : operation t) (res : API.Expr t)
    : func :=
    (name, make_bedrock_func_with_sizes
             (op.(input_array_sizes)) (op.(output_array_sizes))
             (op.(input_array_lengths)) res).

  Definition is_correct
             {t : API.type}
             (start : Pipeline.ErrorT (API.Expr t))
             (op : operation t)
             {name : string} (spec : spec_of name) : Prop :=
    (forall res : API.Expr t,
        start = ErrorT.Success res ->
        API.Wf res ->
        valid_func (res (fun _ : API.type => unit)) ->
        forall functions,
          spec (make_bedrock_func name op res :: functions)).
End op.

(* useful tactics for proving things about operations *)
Ltac specialize_to_args Hcorrect :=
  let A := fresh "A" in
  let A' := fresh "A" in
  match goal with
    a : type.for_each_lhs_of_arrow API.interp_type _ |- _ =>
    cbn in a; set (A:=a)
  end;
  repeat match type of A with
           (?xt * ?yt)%type =>
           specialize (Hcorrect (fst A));
           set (A':=snd A); subst A;
           rename A' into A
         end;
  subst A.

Ltac postcondition_from_correctness :=
  match goal with H : ?pre ?args |- ?post ?args _ =>
                  revert H end;
  cbn [type.app_curried API.interp_type
                        Language.Compilers.base.interp
                        Compilers.base_interp] in *;
  lazymatch goal with
  | Hcorrect : context [?res] |- ?pre ?args -> ?post ?args ?res =>
    (* first /\ together all preconditions *)
    let Htmp := fresh in
    repeat match type of Hcorrect with
           | ?P -> ?Q -> ?R =>
             rename Hcorrect into Htmp;
               assert (P /\ Q -> R) as Hcorrect
                 by (destruct 1; apply Htmp; auto); clear Htmp
           end;
    let Ppre := lazymatch type of Hcorrect with ?P -> _ => P end in
    let Ppost := lazymatch type of Hcorrect with _ -> ?P => P end in
    let Fpre := lazymatch (eval pattern args in Ppre) with
                | ?f _ => f end in
    let Fpost := lazymatch (eval pattern res in Ppost) with
                 | ?f _ => f end in
    let Fpost := lazymatch (eval pattern args in Fpost) with
                 | ?f _ => f end in
    let H := fresh in
    assert (H : Fpre args -> Fpost args res) by exact Hcorrect;
    exact H
  end.

Ltac assert_output_length prove_length :=
  let out := lazymatch goal with
             | H : postcondition _ _ ?out |- _ => out end in
  let op := lazymatch goal with
            | H : postcondition ?op _ _ |- _ => op end in
  let outlens := (eval cbn in (output_array_lengths op)) in
  assert
    (LoadStoreList.list_lengths_from_value out
     = op.(output_array_lengths));
  cbn [LoadStoreList.list_lengths_from_value type.final_codomain] in *;
  change (output_array_lengths op) with outlens in *;
  [ prove_length | ].

Ltac find_input_array :=
  match goal with
  | H : postcondition ?op ?args ?x |- postcondition ?op ?args ?y =>
    (* need to set args so the replace doesn't fire on them due to evar
           silliness *)
    let A := fresh in
    set (A:=args);
    replace y with x; [ exact H | ]; subst A
  end;
  repeat
    first [ erewrite byte_map_unsigned_of_Z,
            map_byte_wrap_bounded
            by eauto using byte_bounds_range_iff
          | congruence
          | solve [eauto] ].

Ltac post_sufficient :=
  repeat intro;
  try simplify_translate_func_postcondition;
  type_simplify;
  repeat match goal with
         | _ => progress ssplit; try congruence
         | |- exists _, _ => eexists
         | H : map word.unsigned _ = expr.interp _ _ _ |- _ =>
           rewrite <-H in *
         | _ => progress sepsimpl;
                [ solve [find_input_array] .. | ]
         | H:postcondition ?op ?args ?x
           |- postcondition ?op ?args ?y =>
           ssubst; replace y with x; [ exact H | solve [auto] .. ]
         end;
  ssubst.

Ltac apply_translate_func_correct Rout arg_ptrs out_array_ptrs :=
  let a := lazymatch goal with
           | H : postcondition _ ?args _ |- _ => args end in
  eapply Proper_call;
  [ | eapply translate_func_correct with
          (R:=Rout) (out_ptrs:=out_array_ptrs)
          (args:=a) (flat_args := arg_ptrs) ].

Ltac begin_proof :=
  match goal with
    |- is_correct _ ?def _ =>
    cbv [is_correct make_bedrock_func] in *; intros;
    sepsimpl;
    cbn [inbounds input_array_sizes output_array_sizes
                  input_array_lengths output_array_lengths
                  pipeline_out correctness] in *
  end;
  match goal with |- context [postcondition ?op ?args] =>
                  let H := fresh in
                  pose proof (correctness op) as H;
                  repeat specialize (H ltac:(assumption));
                  specialize (H args)
  end; cleanup.
