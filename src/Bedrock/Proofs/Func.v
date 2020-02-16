Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Proofs.Cmd.
Require Import Crypto.Bedrock.Proofs.Flatten.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Bedrock.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

Section Func.
  Context {p : parameters} {p_ok : @ok p}.
  Local Notation bedrock_func := (string * (list string * list string * cmd))%type.

  (* TODO: are these all needed? *)
  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.

  Inductive valid_func : forall {t}, @API.expr (fun _ => unit) t -> Prop :=
  | validf_Abs :
      forall {s d} f, valid_func (f tt) ->
                      valid_func (expr.Abs (s:=type.base s) (d:=d) f)
  | validf_base :
      forall {b} e, valid_cmd e -> valid_func (t:=type.base b) e
  .

  (* produces a separation-logic condition stating that the values of arguments are equivalent *)
  (* TODO: should this go in Types.v? *)
  Fixpoint equivalent_args {t}
    : type.for_each_lhs_of_arrow API.interp_type t -> (* fiat-crypto value *)
      type.for_each_lhs_of_arrow (rtype (listZ:=rep.listZ_mem)) t -> (* bedrock2 value *)
      Semantics.locals -> Semantics.mem -> Prop :=
    match t with
    | type.base b => fun _ _ _ _ => True
    | type.arrow (type.base a) b =>
      fun (x : base.interp a * _) (y : base_rtype a * _) locals =>
        sep (equivalent (fst x) (fst y) locals)
            (equivalent_args (snd x) (snd y) locals)
    | _ => fun _ _ _ _ => False
    end.

  (* TODO: use spec_of *)
  Lemma translate_func_correct {t}
        (* three exprs, representing the same Expr with different vars *)
        (e0 : @API.expr (fun _ => unit) t)
        (e1 : @API.expr API.interp_type t)
        (e2 : @API.expr ltype t)
        (* expressions are valid input to translate_func *)
        (e0_valid : valid_func e0) :
    (* exprs are all related with empty context *)
    wf3 [] e0 e1 e2 ->
    forall (fname : string)
           (retnames : base_ltype (type.final_codomain t))
           (argnames : type.for_each_lhs_of_arrow ltype t)
           (arglengths : type.for_each_lhs_of_arrow list_lengths t)
           (args1 : type.for_each_lhs_of_arrow API.interp_type t)
           (args2 : type.for_each_lhs_of_arrow rtype t),
      (* rets1 := fiat-crypto interpretation of e1 applied to args1 *)
      let rets1 : base.interp (type.final_codomain t) :=
          type.app_curried (API.interp e1) args1 in
      (* out := translation output for e2 (function arguments, rets, body) *)
      let out := translate_func e2 argnames arglengths retnames in
      let f : bedrock_func := (fname, out) in
      forall (tr : Semantics.trace)
             (mem : Semantics.mem)
             (flat_args : list Semantics.word)
             (functions : list bedrock_func)
             (P R : Semantics.mem -> Prop),
        (* argument values (in their 3 forms) are equivalent *)
        equivalent_args args1 args2 map.empty mem ->
        WeakestPrecondition.dexprs
          mem map.empty (flatten_args args2) flat_args ->
        (* TODO: make P say something about having the same shape as rets *)
        sep P R mem ->
        (* translated function produces equivalent results *)
        WeakestPrecondition.call
          ((fname, out) :: functions) fname tr mem flat_args
          (fun tr' mem' flat_rets =>
             tr = tr' /\
             (exists rets2 : base_rtype (type.final_codomain t),
                 WeakestPrecondition.dexprs
                   mem map.empty (flatten_rets rets2) flat_rets /\
                 sep (equivalent (listZ:=rep.listZ_mem) rets1 rets2 map.empty) R mem')).
  Proof.
    cbv zeta. intros; cbv [translate_func].
    cbn [WeakestPrecondition.call WeakestPrecondition.call_body WeakestPrecondition.func].
    rewrite eqb_refl.
    match goal with H : _ |- _ =>
                    pose proof H; eapply of_list_zip_flatten_argnames in H;
                      destruct H
    end.
    eexists; split; [ eassumption | ].
  Admitted.
End Func.
