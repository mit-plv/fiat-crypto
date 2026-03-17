(** * SIMD Batching Transformation — ARCHIVED / EXPERIMENTAL *)
(** This file attempts a generic PHOAS-level batching transformation
    ([BatchExpr]) that lifts any scalar expression to a list-mapped version.
    It has NOT been validated through BoundsPipeline or the equivalence checker.
    Uses an [Axiom todo] for unsupported higher-order cases.

    For working batched specs, use the manual definitions in
    [SIMDUnsaturatedSolinas.v] (e.g. [batched_addmod], [batched_submod],
    [batched_carry_mulmod]) which are reified and pipeline-tested. *)
From Coq Require Import List.
From Coq Require Import ZArith.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.

Import ListNotations.
Import API.Compilers APINotations.Compilers.

Local Open Scope etype_scope.

(** Lift every base type [b] to [list b]; recurse through arrows. *)
Fixpoint batch_type (t : API.type) : API.type :=
  match t with
  | type.base b    => type.base (base.type.list b)
  | type.arrow A B => type.arrow (batch_type A) (batch_type B)
  end.

(** Section fixes [var] as an ambient assumption so Coq does not generate
    fresh metavariables for it inside match branches. *)
Axiom todo : forall {A : Type}, A.

Section batch.
  Context {var : API.type -> Type}.
  Local Notation expr := (@expr.expr base.type ident var).

  (** Main recursive helper.

      Invariant at each call:
        [e]        : partially-applied expression of type  [base acc -> t]
        [combined] : list of input tuples accumulated so far, type  [list acc]

      Strategy: peel one [type.base s] arrow at a time from [t].
        - Introduce a new [Abs (list s)] argument [ys].
        - Uncurry [e] by pairing [acc] with [s] via [fst]/[snd].
        - Extend [combined] with [List.combine combined ys].
        - Recurse on the remaining type [d] with the uncurried [e] and new combined list.
      Base case (t = base b): apply [List.map e combined]. *)
  Fixpoint batch_with_acc (acc : base.type) (t : API.type)
      (e        : expr (type.base acc -> t))
      (combined : expr (type.base (base.type.list acc)))
      : expr (batch_type t) :=
    (match t as t' return
       (expr (type.base acc -> t') ->
        expr (batch_type t'))
     with
     | type.base b => fun e =>
         expr.App (expr.App (expr.Ident Compilers.ident_List_map) e) combined
     | type.arrow (type.base s) d => fun e =>
         expr.Abs (fun ys =>
           batch_with_acc (base.type.prod acc s) d
             (expr.Abs (fun p =>
                expr.App
                  (expr.App e (expr.App (expr.Ident Compilers.ident_fst) (expr.Var p)))
                  (expr.App (expr.Ident Compilers.ident_snd) (expr.Var p))))
             (expr.App
                (expr.App (expr.Ident Compilers.ident_List_combine) combined)
                (expr.Var ys)))
     | type.arrow (type.arrow _ _) _ => fun e =>
         (* Higher-order argument — not expected for first-order crypto primitives *)
         todo
     end) e.

  (** Top-level entry: peel the first [Abs (base s)] layer, then hand off to
      [batch_with_acc] with [combined = xs] (no accumulation yet). *)
  Definition batch_expr (t : API.type) (e : expr t) : expr (batch_type t) :=
    (match t as t' return expr t' -> expr (batch_type t') with
     | type.base b => fun e =>
         (* Closed expression: wrap the single value in a singleton list *)
         expr.App (expr.App (expr.Ident Compilers.ident_cons) e) (expr.Ident Compilers.ident_nil)
     | type.arrow (type.base s) d => fun e =>
         expr.Abs (fun xs =>
           batch_with_acc s d e (expr.Var xs))
     | type.arrow (type.arrow _ _) _ => fun e =>
         (* Higher-order argument — not expected *)
         todo
     end) e.

End batch.

(** Outer PHOAS wrapper. *)
Definition BatchExpr {t : API.type} (e : API.Expr t) : API.Expr (batch_type t) :=
  fun var => batch_expr t (e var).
