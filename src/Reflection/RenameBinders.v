Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.

Ltac uncurry_f f :=
  let t := type of f in
  lazymatch eval compute in t with
  | prod ?a ?b -> ?R
    => uncurry_f (fun x y => f (@pair a b x y))
  | ?a -> ?R
    => let x := fresh in
       constr:(fun x : a => ltac:(let v := uncurry_f (f x) in exact v))
  | _ => f
  end.
Ltac make_destruct_specialize t with_destruct_specialize_tac :=
  let do_tac T1 T2 n1 mk_n2 :=
      pose tt as n1;
      make_destruct_specialize
        T1
        ltac:(fun destruct_specialize_ab
              => let n2 := mk_n2 () in
                 pose tt as n2;
                 make_destruct_specialize
                   T2
                   ltac:(fun destruct_specialize_cd
                         => with_destruct_specialize_tac
                              ltac:(fun arg f cont =>
                                      clear n1 n2;
                                      refine (let '(n1, n2)%core := arg in _);
                                      clear arg;
                                      destruct_specialize_ab
                                        n1 f
                                        ltac:(fun f => destruct_specialize_cd n2 f cont)))) in
  lazymatch eval compute in t with
  | prod (prod ?a ?b) (prod ?c ?d)
    => let arg1 := fresh "arg" in
       do_tac (prod a b) (prod c d) arg1 ltac:(fun _ => fresh "arg")
  | prod (prod ?a ?b) ?c
    => let arg1 := fresh "arg" in
       do_tac (prod a b) c arg1 ltac:(fun _ => fresh "x")
  | prod ?a (prod ?c ?d)
    => let arg1 := fresh "x" in
       do_tac a (prod c d) arg1 ltac:(fun _ => fresh "arg")
  | prod ?a ?b
    => let arg1 := fresh "x" in
       do_tac a b arg1 ltac:(fun _ => fresh "x")
  | _
    => with_destruct_specialize_tac ltac:(fun arg f cont => cont (f arg))
  end.
Ltac renamify input :=
  let t := type of input in
  let t := (eval compute in t) in
  let ret :=
      constr:(ltac:(
                let var := fresh "var" in
                intro var;
                let input := constr:(input var) in
                let input := (eval compute in input) in
                let arg := fresh "arg" in
                refine (Abs (fun arg => _));
                let input := constr:(invert_Abs input) in
                let t := type of arg in
                let t := (eval compute in t) in
                let input := uncurry_f input in
                let input := (eval cbv iota beta delta [invert_Abs] in input) in
                make_destruct_specialize
                  t ltac:(fun do_destruct_specialize
                          => do_destruct_specialize
                               arg input
                               ltac:(fun input => let input := (eval cbv beta in input) in
                                                  exact input))
              ) : t) in
  (eval cbv beta zeta in ret).
Notation renamify f :=
  (let t := _ in
   let renamify_F0 : t := f in
   ((fun renamify_F : t => ltac:(let v := renamify renamify_F in exact v))
      renamify_F0))
    (only parsing).
