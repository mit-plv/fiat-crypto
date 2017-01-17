Require Export Crypto.Util.FixCoqMistakes.

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context_by ident funl funr tac :=
  repeat match goal with
         | [ H : context p [ident] |- _ ] =>
           let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (tac H);
                                          let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (tac H);
                                                                         clear H
         end.
Ltac split_in_context ident funl funr :=
  split_in_context_by ident funl funr ltac:(fun H => apply H).

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_and' :=
  repeat match goal with
         | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
                                                       assert (H0 := fst H); assert (H1 := snd H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Type => a) (fun a b : Type => b).
