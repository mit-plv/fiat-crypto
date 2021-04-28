(** * Reification Cache *)
(** This file defines the cache that holds reified versions of
    operations, as well as the tactics that reify and apply things
    from the cache. *)
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.

Import
  Language.API.Compilers
  Language.Wf.Compilers.

Import Compilers.API.

Fixpoint pointwise_equal {t} : relation (type.interp base.interp t)
  := match t with
     | type.base t => Logic.eq
     | type.arrow s d
       => fun (f g : type.interp base.interp s -> type.interp base.interp d)
          => forall x, pointwise_equal (f x) (g x)
     end.

Definition is_reification_of' {t} (e : Expr t) (v : type.interp base.interp t) : Prop
  := pointwise_equal (Interp e) v /\ Wf e.

Notation is_reification_of rop op
  := (match @is_reification_of' (reify_type_of op) rop op with
      | T
        => ltac:(
             let T := (eval cbv [pointwise_equal is_reification_of' T] in T) in
             let T := (eval cbn [type.interp base.interp base.base_interp] in T) in
             exact T)
      end)
       (only parsing).

Ltac cache_reify _ :=
  split;
  [ intros;
    etransitivity;
    [
    | repeat match goal with |- _ = ?f' ?x => is_var x; apply (f_equal (fun f => f _)) end;
      Reify_rhs ();
      reflexivity ];
    subst_evars;
    reflexivity
  | prove_Wf () ].

Ltac apply_cached_reification op lem :=
  lazymatch goal with
  | [ |- _ = ?RHS ]
    => let f := head RHS in
       constr_eq f op;
       simple apply lem
  end.

Create HintDb reify_gen_cache discriminated.
Create HintDb wf_gen_cache discriminated.

Module Export Hints.
  Hint Resolve conj : reify_gen_cache wf_gen_cache.
  Hint Unfold Wf.Compilers.Wf : wf_gen_cache.
End Hints.
