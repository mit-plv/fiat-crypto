Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Proofs.Dexprs.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations Types.Types.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)


Section Flatten.
  Context {p : parameters} {p_ok : @ok p}.
  (* these conversions should happen before loading arguments and after
       storing return values, so they use in-memory lists *)
  Local Existing Instance rep.listZ_mem.
  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Lemma flatten_base_samelength {t} (lhs : base_ltype t) (rhs : base_rtype t) :
    length (flatten_base_ltype lhs) = length (flatten_base_rtype rhs).
  Proof.
    induction t;
      repeat match goal with
             | _ => progress cbn [flatten_base_ltype flatten_base_rtype]
             | _ => progress break_match 
             | _ => rewrite app_length
             | _ => solve [eauto]
             end.
  Qed.

  (* given these structures have the same type, they'll have the same size in
       flattened form *)
  Lemma flatten_args_samelength {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow rtype t) :
    length (flatten_args args) = length (flatten_argnames argnames).
  Proof.
    induction t;
      repeat match goal with
             | _ => progress cbn [flatten_args flatten_argnames]
             | _ => progress break_match 
             | _ => erewrite flatten_base_samelength
             | _ => rewrite app_length
             | _ => solve [eauto]
             end.
  Qed.

  Lemma of_list_zip_flatten_argnames {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow rtype t)
        (flat_args : list Semantics.word) mem :
    WeakestPrecondition.dexprs mem map.empty (flatten_args args) flat_args ->
    (exists l, map.of_list_zip (flatten_argnames argnames) flat_args = Some l).
  Proof.
    pose proof (flatten_args_samelength argnames args).
    let H := fresh in intro H; apply dexprs_length in H.
    apply map.sameLength_putmany_of_list.
    lia.
  Qed.
End Flatten.
