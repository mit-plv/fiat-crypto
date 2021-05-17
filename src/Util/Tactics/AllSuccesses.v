Require Import Crypto.Util.DynList.

Ltac all_successes' tac arg so_far :=
  let K := match constr:(Set) with
           | _ => let v := tac arg in
                  let __ := lazymatch so_far with
                            | context[DynList.cons v _] => fail
                            | _ => idtac
                            end in
                  fun again => again constr:(DynList.cons v so_far)
           | _ => fun again => so_far
           end in
  K ltac:(all_successes' tac arg).

Ltac all_successes tac arg := all_successes' tac arg constr:(DynList.nil).
