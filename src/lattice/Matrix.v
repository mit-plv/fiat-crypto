Require Import Coq.Lists.List.
Require Import Crypto.Util.Tuple.

Section matrix.
  Context (T : Type) (Tzero : T) (Tadd : T -> T -> T) (Tmul : T -> T -> T).
  Definition matrix n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)
  Definition get {n m} (A : matrix n m) (i j : nat) : T :=
    nth_default Tzero j (nth_default (repeat Tzero m) i A).
  Local Notation "A [ i ][ j ]" := (get A i j) (at level 0).
  Local Infix "*" := Tmul.

  Definition sum : list T -> T := fold_right Tadd Tzero.
  Definition mul n m p (A : matrix n m) (B : matrix m p) : matrix n p :=
    map (fun j => (* forall j := 0...n *)
           map (fun i => (* forall i := 0...p *)
                  (* AB[i][j] = sum_{k=0}{m} A[i][k] * B[k][j] *)
                  sum (List.map (fun k => A[i][k] * B[k][j]) (List.seq 0 m)))
               (seq 0 p))
        (seq 0 n).
  Definition transpose n m (A : matrix n m) : matrix m n :=
    map (fun j => map (fun i => A[j][i]) (seq 0 n)) (seq 0 m).
End matrix.
