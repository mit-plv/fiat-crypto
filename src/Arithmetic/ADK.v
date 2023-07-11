Require Import Coq.Lists.List.
Require Import Crypto.Util.LetIn.
Require Import Coq.ZArith.ZArith.
Import ListNotations. Local Open Scope Z_scope.

Print bool_rect.

Local Notation nth' := (fun i l d => (nth_default d l i)).

Definition if_then_else {A} (cond : bool) (if_thing : A) (else_thing : A) :=
  if cond then if_thing else else_thing.

Definition adk_mul_prod_at_i (n : nat) (x y products f : list Z) (i : nat) : Z :=
  fold_right Z.add 0 (map (fun j => (nth' j x 0 - nth' (i - j)%nat x 0) * (nth' (i - j)%nat y 0 - nth' j y 0))
                        (seq (i - (n - 1)) (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))) +
    (if_then_else (i =? 2 * n - 2)%nat
       (nth' (n - 1)%nat products 0)
       (if_then_else (i <? n)%nat (nth' i f 0) (nth' i f 0 - nth' (i - n)%nat f 0))).
  
Definition adk_mul' (n : nat) (x y products f : list Z) : list Z :=
  map (fun i => adk_mul_prod_at_i n x y products f i) (seq 0 (2*n - 1)).
  
Definition adk_mul (n : nat) (x y : list Z) : list Z :=
  dlet high_product : Z := (nth' (n - 1)%nat x 0) * (nth' (n - 1)%nat y 0) in
      let products : list Z := map (fun i => (nth' i x 0) * (nth' i y 0)) (seq 0 (n - 1)) ++ [high_product] ++ (repeat 0 (n - 1)) (*thye total length of products should be (2*n - 1), since this is
                                                                                                                                    what we want the length of f to be.*) in
      (list_rect
         (fun _ => list Z -> list Z)
         (fun f => adk_mul' n x y products (rev f))
         (fun p _ g => fun f' => Let_In ((nth' 0%nat f' 0) + p) (fun x => g (x :: f'))) 
         products) [].

Definition ident_adk_mul_prod_at_i := adk_mul_prod_at_i.

Definition ident_adk_mul := adk_mul.
