Require Import ZArith.BinInt.
Require Import List Util.ListUtil.


Section ScalarMult.
  Variable G : Type.
  Variable neutral : G.
  Variable add : G -> G -> G.
  Local Infix "+" := add.

  Fixpoint scalarMultSpec (n:nat) (g:G) : G :=
    match n with 
    | O => neutral
    | S n' => g + scalarMultSpec n' g
    end
  .

  (* ng = 
  *  (n/2)(g+g) + g if n odd
  *  (n/2)(g+g)     if n even
  *  g              if n == 1
  *)
  Fixpoint scalarMultPos (n:positive) (g:G) : G :=
    match n with
    | xI n' => scalarMultPos n' (g + g) + g
    | xO n' => scalarMultPos n' (g + g)
    | xH => g
    end
  .

  Definition scalarMultNat (n:nat) (g:G) : G :=
    match n with
    | O => neutral
    | S n' => scalarMultPos (Pos.of_succ_nat n') g
    end
  .

  Definition sel {T} (b:bool) (x y:T) := if b then y else x.
  Definition scalarMultStaticZ (bitLengthN:nat) (n:Z) (g:G): G :=
   fst (fold_right
     (fun (i : nat) (s : G * G) => let (Q, P) := s in
      let Q' := sel (Z.testbit (Z.of_nat i) n) Q (Q + P) in
      let P' := P+P in
        (Q',  P + P))
     (neutral, g) (* initial state *)
     (seq 0 bitLengthN)) (* range of i *)
  .
End ScalarMult.
