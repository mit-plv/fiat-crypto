(** * Examples of Using the Rewriter *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Rewriter.AllTactics.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Language.Pre.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Crypto.Util.PrimitiveHList.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Import Rewriter.AllTactics.Compilers.RewriteRules.GoalType.
Import Rewriter.AllTactics.Compilers.RewriteRules.Tactic.
Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.GoalType.
Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.Tactic.

(** We first define some helper notations, and then define the list of
    types of theorems we want to rewrite with. *)

Local Notation "' x" := (ident.literal x).
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).
Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.

Definition noruletypes : list (bool * Prop)
  := [].

(** Now we prove every theorem statement in the above list. *)

Lemma noruleproofs
  : PrimitiveHList.hlist (@snd bool Prop) noruletypes.
Proof. repeat constructor. Qed.

(** Next we define the rewriter package *)

Definition norules : VerifiedRewriter_with_args false noruleproofs.
Proof using All. make_rewriter. Defined.

(** Now we show some simple examples. *)

Example ex1 : forall x : nat, x = x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

(** ==== *)

Definition myruletypes : list (bool * Prop)
  := Eval cbv [mymap myapp] in
      myapp
        (mymap
           dont_do_again
           [(forall x, x + 0 = x)
            ; (forall A B x y, @fst A B (x, y) = x)
            ; (forall A B x y, @snd A B (x, y) = y)
            ; (forall A B f ls, @List.map A B f ls
                                = (ident.eagerly (@list_rect) _ _)
                                    []
                                    (fun x xs map_f_xs => f x :: map_f_xs)
                                    ls)
            ; (forall A xs ys, @List.app A xs ys
                               = (ident.eagerly (@list_rect) _ _)
                                   ys (fun x xs app_xs_ys => x :: app_xs_ys) xs)
            ; (forall A P N C ls,
                  @ident.Thunked.list_rect A P N C ls
                  = ident.eagerly (@ident.Thunked.list_rect) A P N C ls)
            ; (forall A P Q N C ls v,
                  @list_rect A (fun _ => P -> Q) N C ls v
                  = ident.eagerly (@list_rect) A (fun _ => P -> Q) N C ls v)])
        (mymap
           do_again
           [(forall A B f xs,
                @List.flat_map A B f xs
                = (list_rect _)
                    nil
                    (fun x _ flat_map_tl => f x ++ flat_map_tl)
                    xs)]).

(** Now we prove every theorem statement in the above list. *)

Lemma myruleproofs
  : PrimitiveHList.hlist (@snd bool Prop) myruletypes.
Proof.
  repeat constructor; cbn [snd]; cbv [ident.eagerly]; intros;
    try solve [ lia
              | now apply ListUtil.eq_app_list_rect ].
Qed.

(** Next we define the rewriter package *)

Definition myrules : VerifiedRewriter_with_args true myruleproofs.
Proof using All. make_rewriter. Defined.

(** Now we show some simple examples. *)

Example ex2 : forall x, x + 0 = x.
Proof.
  Rewrite_for myrules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Ltac test_rewrite :=
  Rewrite_for myrules;
  lazymatch goal with
  | [ |- ?x = ?y ] => first [ constr_eq x y; idtac "Success:" x; reflexivity
                            | fail 1 x "≢" y ]
  end.

Example ex3 : forall y e1 e2,
    map (fun x => y + x) (dlet z := e1 + e2 in [0; 1; 2; z; z+1])
    = dlet z := e1 + e2 in [y; y + 1; y + 2; y + z; y + (z + 1)].
Proof. test_rewrite. Qed.

Example ex4 : forall (x1 x2 x3 : Z),
    flat_map (fun a => [a; a; a]) [x1;x2;x3]
    = [x1; x1; x1; x2; x2; x2; x3; x3; x3].
Proof. test_rewrite. Qed.
