Require Export Crypto.Util.FixCoqMistakes.

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context_by ident funl funr tac :=
  repeat match goal with
         | [ H : context p [ident] |- _ ] =>
           let H0 := context p[funl] in
           let H1 := context p[funr] in
           let H0' := (eval cbv beta in H0) in
           let H1' := (eval cbv beta in H1) in
           assert H0' by (tac H);
           assert H1' by (tac H);
           clear H
         end.
Ltac split_in_context ident funl funr :=
  split_in_context_by ident funl funr ltac:(fun H => apply H).

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_contravariant_or := split_in_context_by or (fun A B : Prop => A) (fun A B : Prop => B) ltac:(fun H => intros; eauto 100 using H, or_introl, or_intror, ex_intro, exist, existT with nocore).

Ltac split_and' :=
  repeat match goal with
         | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
                                                       assert (H0 := proj1 H); assert (H1 := proj2 H); clear H
         end.
Ltac split_prod' :=
  repeat match goal with
         | [ H : prod ?a ?b |- _ ] => let H0 := fresh in let H1 := fresh in
                                                         assert (H0 := fst H); assert (H1 := snd H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Type => a) (fun a b : Type => b).
Ltac split_prod := split_and'; split_in_context prod (fun a b : Type => a) (fun a b : Type => b).
