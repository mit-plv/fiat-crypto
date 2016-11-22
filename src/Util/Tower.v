Require Export Crypto.Util.FixCoqMistakes.

Section tower_nd.
  Context (A : Type) (B : Type).
  Fixpoint tower_nd (n : nat)
    := match n with
       | 0 => B
       | S n' => A -> tower_nd n'
       end.
End tower_nd.

Definition apply4 {AK BK PA PB ARR}
           (F : forall (A : AK) (B : BK), (PA A -> PB B) -> PB (ARR A B))
           {A0 A1 A2 A3 : AK} {B : BK}
           (f : PA A0 -> PA A1 -> PA A2 -> PA A3 -> PB B)
  : PB (ARR A0 (ARR A1 (ARR A2 (ARR A3 B)))).
Proof.
  repeat (apply F; intro); apply f; assumption.
Defined.

Definition apply4_nd {BK PA PB ARR}
           (F : forall (B : BK), (PA -> PB B) -> PB (ARR B))
           {B : BK}
           (f : tower_nd PA (PB B) 4)
  : PB (ARR (ARR (ARR (ARR B))))
  := @apply4 unit BK (fun _ => PA) PB (fun _ => ARR) (fun _ => F)
             tt tt tt tt B f.

Definition apply9 {AK BK PA PB ARR}
           (F : forall (A : AK) (B : BK), (PA A -> PB B) -> PB (ARR A B))
           {A0 A1 A2 A3 A4 A5 A6 A7 A8 : AK} {B : BK}
           (f : PA A0 -> PA A1 -> PA A2 -> PA A3 -> PA A4 -> PA A5 -> PA A6 -> PA A7 -> PA A8 -> PB B)
  : PB (ARR A0 (ARR A1 (ARR A2 (ARR A3 (ARR A4 (ARR A5 (ARR A6 (ARR A7 (ARR A8 B))))))))).
Proof.
  repeat (apply F; intro); apply f; assumption.
Defined.

Definition apply9_nd {BK PA PB ARR}
           (F : forall (B : BK), (PA -> PB B) -> PB (ARR B))
           {B : BK}
           (f : tower_nd PA (PB B) 9)
  : PB (ARR (ARR (ARR (ARR (ARR (ARR (ARR (ARR (ARR B)))))))))
  := @apply9 unit BK (fun _ => PA) PB (fun _ => ARR) (fun _ => F)
             tt tt tt tt tt tt tt tt tt B f.
