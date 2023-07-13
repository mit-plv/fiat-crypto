Require Import Coq.Lists.List.
Require Import Crypto.Util.LetIn.
Require Import Coq.ZArith.ZArith.
Import ListNotations. Local Open Scope Z_scope.

Local Notation nth' := (fun i l d => (nth_default d l i)).

Definition if_then_else {A} (cond : bool) (if_thing : A) (else_thing : A) :=
  if cond then if_thing else else_thing.

Definition prod_at_i_first_part (n : nat) (x y : list Z) (i : nat) : Z :=
  fold_right Z.add 0 (map (fun j => (nth' j x 0 - nth' (i - j)%nat x 0) * (nth' (i - j)%nat y 0 - nth' j y 0))
                        (seq (i - (n - 1)) (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))).

(* we use this for all i s.t. i \neq 2 * n - 2 *)
Definition prod_at_i_lt_n (n : nat) (x y : list Z) (f : list Z) (i : nat) : Z :=
  prod_at_i_first_part n x y i +
    nth' i f 0.

Definition prod_at_i_geq_n_lt_2nm2 (n : nat) (x y : list Z) (f : list Z) (i : nat) : Z :=
  prod_at_i_first_part n x y i +
    (nth' i f 0 - nth' (i - n)%nat f 0).

Definition prod_at_2nm2 (n : nat) (x y : list Z) (high_product : Z) (i : nat) : Z :=
  prod_at_i_first_part n x y i +
    high_product.

Definition adk_mul' (n : nat) (x y : list Z) (high_product : Z) (f : list Z) : list Z :=
  map (prod_at_i_lt_n n x y f) (seq 0 n) ++ map (prod_at_i_geq_n_lt_2nm2 n x y f) (seq n (n - 1)) ++ map (prod_at_2nm2 n x y high_product) (seq (2*n - 2) (2 * n - 2 - n - (n - 1))).

Definition f products :=
  rev (fold_right (fun (y : Z) (x : list Z) => Let_In (Let_In (nth_default 0 x 0) (fun z => z + y :: x)) (fun z => z)) [] (rev products)).

Definition adk_mul (n : nat) (x y : list Z) : list Z :=
  dlet high_product : Z := (nth' (n - 1)%nat x 0) * (nth' (n - 1)%nat y 0) in
      let products : list Z := map (fun i => (nth' i x 0) * (nth' i y 0)) (seq 0 (n - 1)) ++ [high_product] ++ (repeat 0 (n - 1)) in
      adk_mul' n x y (nth' (n - 1)%nat products 0) (f products).

Definition adk_mul_inner := 5.
