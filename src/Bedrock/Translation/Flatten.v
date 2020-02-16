Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Translation.Dexprs.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations Types.Types.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)


Section Flatten.
  Context {p : parameters}.
  (* these conversions should happen before loading arguments and after
       storing return values, so they use in-memory lists *)
  Local Existing Instance rep.listZ_mem.
  Local Existing Instance rep.Z.

  Fixpoint flatten_base_ltype {t}
    : base_ltype t -> list string :=
    match t with
    | base.type.prod a b =>
      fun x : base_ltype a * base_ltype b =>
        (flatten_base_ltype (fst x) ++ flatten_base_ltype (snd x))
    | base_listZ => fun x : string => [x] 
    | _ => fun x : string => [x] 
    end.

  Fixpoint flatten_base_rtype {t}
    : base_rtype t -> list Syntax.expr :=
    match t as t0 return base_rtype t0 -> _ with
    | base.type.prod a b =>
      fun x : base_rtype a * base_rtype b =>
        (flatten_base_rtype (fst x) ++ flatten_base_rtype (snd x))
    | base_listZ => fun x : Syntax.expr => [x] 
    | _ => fun x : Syntax.expr => [x]
    end.
  
  Fixpoint flatten_argnames {t}
    : type.for_each_lhs_of_arrow ltype t -> list string :=
    match t with
    | type.base b => fun _ : unit => []
    | type.arrow (type.base a) b =>
      fun x : base_ltype a * _ =>
        flatten_base_ltype (fst x) ++ flatten_argnames (snd x)
    | _ => fun _ => [] (* garbage; function arguments not allowed *)
    end.

  Fixpoint flatten_args {t}
    : type.for_each_lhs_of_arrow rtype t -> list Syntax.expr :=
    match t as t0 return type.for_each_lhs_of_arrow rtype t0 -> _ with
    | type.base b => fun _ => []
    | type.arrow (type.base a) b =>
      fun x : base_rtype a * _ =>
        flatten_base_rtype (fst x) ++ flatten_args (snd x)
    | _ => fun _ => [] (* garbage; function arguments not allowed *)
    end.

  Definition flatten_retnames {t}
    : base_ltype (type.final_codomain t) -> list string :=
    flatten_base_ltype.

  Definition flatten_rets {t}
    : base_rtype (type.final_codomain t) -> list Syntax.expr :=
    flatten_base_rtype.
    
  Section Proofs.
    Context {p_ok : @ok p}.

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
  End Proofs.
End Flatten.
