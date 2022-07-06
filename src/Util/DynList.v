Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Local Set Universe Polymorphism.
Inductive dyn_list := nil | cons {T} (x : T) (xs : dyn_list).
Declare Scope dyn_list_scope.
Delimit Scope dyn_list_scope with dyn_list.
Bind Scope dyn_list_scope with dyn_list.
Infix "::" := cons : dyn_list_scope.
Notation "[ ]" := nil (format "[ ]") : dyn_list_scope.
Notation "[ x ]" := (cons x nil) : dyn_list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : dyn_list_scope.

Module DynList.
  Ltac map_gen explicit f ls N C :=
    lazymatch ls with
    | nil => N
    | @cons ?T ?x ?xs
      => let fx := lazymatch explicit with
                   | true => f T x
                   | false => f x
                   end in
         let xs := map_gen explicit f xs N C in
         constr:(C fx xs)
    end.
  Ltac map_gen_dyn explicit f ls := map_gen explicit f ls constr:(nil) uconstr:(@cons _).
  Ltac map f xs := map_gen_dyn false f xs.

  Ltac map_gen_homogenous explicit f ls := map_gen explicit f ls uconstr:(Datatypes.nil) uconstr:(@Datatypes.cons _).
  Ltac map_homogenous f xs := map_gen_homogenous false f xs.
End DynList.
