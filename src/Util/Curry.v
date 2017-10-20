Require Import Crypto.Util.Tactics.ChangeInAll.

Definition curry2 {A B C} (f : A -> B -> C) (x : A * B) : C
  := let '(a, b) := x in f a b.
Definition curry3 {A B C D} (f : A -> B -> C -> D) (x : A * B * C) : D
  := let '(a, b, c) := x in f a b c.
Definition curry4 {A B C D E} (f : A -> B -> C -> D -> E) (x : A * B * C * D) : E
  := let '(a, b, c, d) := x in f a b c d.

Ltac change_with_curried f :=
  cbv beta in f; (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=5430 *)
  lazymatch type of f with
  | ?A -> ?B -> ?C
    => let f' := fresh f in
       rename f into f';
       pose (fun (ab : A * B) => f' (fst ab) (snd ab)) as f;
       change_in_all f' (fun (a : A) (b : B) => f (a, b));
       subst f';
       cbv beta;
       change_with_curried f
  | _ => idtac
  end.
