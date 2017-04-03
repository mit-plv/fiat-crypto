(** * Lift foralls out of sig proofs *)

Definition lift1_sig {A C} (P:A->C->Prop)
           (op_sig : forall (a:A), {c | P a c})
: { op : A -> C | forall (a:A), P a (op a) }
:= exist
     (fun op => forall a, P a (op a))
     (fun a => proj1_sig (op_sig a))
     (fun a => proj2_sig (op_sig a)).

Definition lift2_sig {A B C} (P:A->B->C->Prop)
           (op_sig : forall (a:A) (b:B), {c | P a b c})
  : { op : A -> B -> C | forall (a:A) (b:B), P a b (op a b) }
  := exist
       (fun op => forall a b, P a b (op a b))
       (fun a b => proj1_sig (op_sig a b))
       (fun a b => proj2_sig (op_sig a b)).

Definition lift3_sig {A B C D} (P:A->B->C->D->Prop)
           (op_sig : forall (a:A) (b:B) (c:C), {d | P a b c d})
  : { op : A -> B -> C -> D | forall (a:A) (b:B) (c:C), P a b c (op a b c) }
  := exist
       (fun op => forall a b c, P a b c (op a b c))
       (fun a b c => proj1_sig (op_sig a b c))
       (fun a b c => proj2_sig (op_sig a b c)).

Definition lift4_sig {A B C D E} (P:A->B->C->D->E->Prop)
           (op_sig : forall (a:A) (b:B) (c:C) (d:D), {e | P a b c d e})
  : { op : A -> B -> C -> D -> E | forall (a:A) (b:B) (c:C) (d:D), P a b c d (op a b c d) }
  := exist
       (fun op => forall a b c d, P a b c d (op a b c d))
       (fun a b c d => proj1_sig (op_sig a b c d))
       (fun a b c d => proj2_sig (op_sig a b c d)).
