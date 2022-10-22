Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Local Set Implicit Arguments.
Module tree. (* for efficient debugging at various depths *)
  Section tree.
    Context (T : Type).
    Inductive t := empty | singleton (_ : T) | app (_ _ : t).
    (* deduplicates empties *)
    Definition smart_app (x y : t)
      := match x, y with
         | empty, _ => y
         | _, empty => x
         | _, _ => app x y
         end.
    Definition fold {A} (f : T -> A -> A)  :=
      fix fold (v : t) (init : A) : A
        := match v with
           | empty => init
           | singleton v => f v init
           | app l r => fold l (fold r init)
           end.
    Definition to_list (v : t) : list T := fold (@cons _) v nil.
  End tree.
  Global Arguments empty {_}.
End tree.
Definition DebugM {dbg : Type} (T : Type) : Type := unit * T.
Global Arguments DebugM {_} _, _ _.
Declare Scope debugM_scope.
Delimit Scope debugM_scope with debugM.
Bind Scope debugM_scope with DebugM.
Module Debug.
  Definition debug' {dbg} : (unit -> list dbg) -> @DebugM dbg unit
    := fun msg => (tt, tt).
  Notation debug v := (debug' (fun 'tt => v)).
  Local Notation eta x := (fst x, snd x).
  Definition bind {dbg A B} (x : DebugM dbg A) (k : A -> DebugM dbg B) : @DebugM dbg B
    := let x := x in
       let '(dbg1, a) := eta x in
       let ka := k a in
       let '(dbg2, b) := eta ka in
       (tt, b).
  Definition sequence {dbg A} (x : DebugM unit) (k : DebugM A) : @DebugM dbg A
    := bind x (fun 'tt => k).
  Definition map {dbg A B} (f : A -> B) (x : DebugM dbg A) : @DebugM dbg B
    := let x := x in
       let '(dbg, a) := eta x in
       (dbg, f a).
  Definition ret {dbg A} (a : A) : @DebugM dbg A
    := (tt, a).
  Definition eval_result {dbg A} : @DebugM dbg A -> A
    := @snd _ _.
  Definition copy_debug_info {dbg A} (x : DebugM A) : @DebugM dbg unit
    := bind x (fun _ => ret tt).
  Definition with_debug_info {dbg A B} (x : DebugM A) (y : DebugM B) : @DebugM dbg B
    := sequence (copy_debug_info x) y.
  Definition get_debug_info {dbg A} (v : DebugM dbg A) : list (unit -> list dbg)
    := nil.

  Lemma eval_result_bind dbg A B x k
    : eval_result (@bind dbg A B x k) = let y := eval_result x in eval_result (k y).
  Proof. reflexivity. Qed.
End Debug.

Notation "x <- y ; f" := (Debug.bind y (fun x => f%debugM)) : debugM_scope.
Notation "f ;; g" := (Debug.sequence f g) : debugM_scope.
