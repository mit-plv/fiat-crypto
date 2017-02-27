(*****

This file provides a generalized version of arithmetic with "mixed
radix" numerical systems. Later, parameters are entered into the
general functions, and they are partially evaluated until only runtime
basic arithmetic operations remain.

CPS
---

Fuctions are written in continuation passing style (CPS). This means
that each operation is passed a "continuation" function, which it is
expected to call on its own output (like a callback). See the end of
this comment for a motivating example explaining why we do CPS,
despite a fair amount of resulting boilerplate code for each
operation. The code block for an operation called A would look like
this:

```
Definition A_cps x y {T} f : T := ...

Definition A x y := A_cps x y id.
Lemma A_cps_id x y : forall {T} f, @A_cps x y T f = f (A x y).
Hint Opaque A : uncps.
Hint Rewrite A_cps_id : uncps.

Lemma eval_A x y : eval (A x y) = ...
Hint Rewrite eval_A : push_basesystem_eval.
```

`A_cps` is the main, CPS-style definition of the operation (`f` is the
continuation function). `A` is the non-CPS version of `A_cps`, simply
defined by passing an identity function to `A_cps`. `A_cps_id` states
that we can replace the CPS version with the non-cps version. `eval_A`
is the actual correctness lemma for the operation, stating that it has
the correct arithmetic properties. In general, the middle block
containing `A` and `A_cps_id` is boring boilerplate and can be safely
ignored.

HintDbs
-------

+ `uncps` : Converts CPS operations to their non-CPS versions.
+ `push_basesystem_eval` : Contains all the correctness lemmas for
   operations in this file, which are in terms of the `eval` function.

Positional/Associational
------------------------

We represent mixed-radix numbers in a few different ways:

+ "Positional" : a tuple of numbers and a weight function (nat->Z),
which is evaluated by multiplying the `i`th element of the tuple by
`weight i`, and then summing the products.
+ "Associational" : a list of pairs of numbers--the first is the
weight, the second is the runtime value. Evaluated by multiplying each
pair and summing the products.

The associational representation is good for basic operations like
addition and multiplication; for addition, one can simply just append
two associational lists. But the end-result code should use the
positional representation (with each digit representing a machine
word). Since converting to and fro can be easily compiled away once
the weight function is known, we use associational to write most of
the operations and liberally convert back and forth to ensure correct
output. In particular, it is important to convert before carrying.

Runtime Operations
------------------

Since some instances of e.g. Z.add or Z.mul operate on (compile-time)
weights, and some operate on runtime values, we need a way to
differentiate these cases before partial evaluation. We define a
runtime_scope to mark certain additions/multiplications as runtime
values, so they will not be unfolded during partial evaluation. For
instance, if we have:

```
Definition f (x y : Z * Z) := (fst x + fst y, (snd x + snd y)%RT).
```

then when we are partially evaluating `f`, we can easily exclude the
runtime operations (`cbv - [runtime_add]`) and prevent Coq from trying
to simplify the second addition.


Why CPS?
--------

Let's suppose we want to add corresponding elements of two `list Z`s
(so on inputs `[1,2,3]` and `[2,3,1]`, we get `[3,5,4]`). We might
write our function like this :

```
Fixpoint add_lists (p q : list Z) :=
  match p, q with
  | p0 :: p', q0 :: q' =>
    dlet sum := p0 + q0 in
    sum :: add_lists p' q'
  | _, _ => nil
  end.
```

(Note : `dlet` is a notation for `Let_In`, which is just a dumb
wrapper for `let`. This allows us to `cbv - [Let_In]` if we want to
not simplify certain `let`s.)

A CPS equivalent of `add_lists` would look like this:

```
Fixpoint add_lists_cps (p q : list Z) {T} (f:list Z->T) :=
  match p, q with
  | p0 :: p', q0 :: q' =>
    dlet sum := p0 + q0 in
    add_lists_cps p' q' (fun r => f (sum :: r))
  | _, _ => f nil
  end.
```

Now let's try some partial evaluation. The expression we'll evaluate is:

```
Definition x := 
    (fun a0 a1 a2 b0 b1 b2 =>
      let r := add_lists [a0;a1;a2] [b0;b1;b2] in
      let rr := add_lists r r in
      add_lists rr rr).
```

Or, using `add_lists_cps`:

```
Definition y := 
    (fun a0 a1 a2 b0 b1 b2 =>
      add_lists_cps [a0;a1;a2] [b0;b1;b2]
                     (fun r => add_lists_cps r r
                     (fun rr => add_lists_cps rr rr id))).
```

If we run `Eval cbv -[Z.add] in x` and `Eval cbv -[Z.add] in y`, we get
identical output:

```
fun a0 a1 a2 b0 b1 b2 : Z =>
       [a0 + b0 + (a0 + b0) + (a0 + b0 + (a0 + b0));
       a1 + b1 + (a1 + b1) + (a1 + b1 + (a1 + b1));
       a2 + b2 + (a2 + b2) + (a2 + b2 + (a2 + b2))]
```

However, there are a lot of common subexpressions here--this is what
the `dlet` we put into the functions should help us avoid. Let's try
`Eval cbv -[Let_In Z.add] in x`:

```
fun a0 a1 a2 b0 b1 b2 : Z =>
       (fix add_lists (p q : list Z) {struct p} : 
        list Z :=
          match p with
          | [] => []
          | p0 :: p' =>
              match q with
              | [] => []
              | q0 :: q' =>
                  dlet sum := p0 + q0 in
                  sum :: add_lists p' q'
              end
          end)
         ((fix add_lists (p q : list Z) {struct p} : 
           list Z :=
             match p with
             | [] => []
             | p0 :: p' =>
                 match q with
                 | [] => []
                 | q0 :: q' =>
                     dlet sum := p0 + q0 in
                     sum :: add_lists p' q'
                 end
             end)
            (dlet sum := a0 + b0 in
             sum
             :: (dlet sum0 := a1 + b1 in
                 sum0 :: (dlet sum1 := a2 + b2 in
                          [sum1])))
            (dlet sum := a0 + b0 in
             sum
             :: (dlet sum0 := a1 + b1 in
                 sum0 :: (dlet sum1 := a2 + b2 in
                          [sum1]))))
         ((fix add_lists (p q : list Z) {struct p} : 
           list Z :=
             match p with
             | [] => []
             | p0 :: p' =>
                 match q with
                 | [] => []
                 | q0 :: q' =>
                     dlet sum := p0 + q0 in
                     sum :: add_lists p' q'
                 end
             end)
            (dlet sum := a0 + b0 in
             sum
             :: (dlet sum0 := a1 + b1 in
                 sum0 :: (dlet sum1 := a2 + b2 in
                          [sum1])))
            (dlet sum := a0 + b0 in
             sum
             :: (dlet sum0 := a1 + b1 in
                 sum0 :: (dlet sum1 := a2 + b2 in
                          [sum1]))))
```

Not so great. Because the `dlet`s are stuck in the inner terms, we
can't simplify the expression very nicely. Let's try that on the CPS
version (`Eval cbv -[Let_In Z.add] in y`):

```
fun a0 a1 a2 b0 b1 b2 : Z =>
       dlet sum := a0 + b0 in
       dlet sum0 := a1 + b1 in
       dlet sum1 := a2 + b2 in
       dlet sum2 := sum + sum in
       dlet sum3 := sum0 + sum0 in
       dlet sum4 := sum1 + sum1 in
       dlet sum5 := sum2 + sum2 in
       dlet sum6 := sum3 + sum3 in
       dlet sum7 := sum4 + sum4 in
       [sum5; sum6; sum7]
```

Isn't that lovely? Since we can push continuation functions "under"
the `dlet`s, we can end up with a nice, concise, simplified
expression.

One might suggest that we could just inline the `dlet`s and do common
subexpression elimination. But some of our terms have so many `dlet`s
that inlining them all would make a term too huge to process in
reasonable time, so this is not really an option.

*****)

Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef.
Local Open Scope Z_scope.

Require Import Crypto.Tactics.Algebra_syntax.Nsatz.
Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil Crypto.Util.Sigma.
Require Import Crypto.Util.CPSUtil Crypto.Util.Prod Crypto.Util.Tactics.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

Local Ltac prove_id :=
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with uncps push_id in * )
         | _ => break_if
         | _ => break_match
         | _ => contradiction
         | _ => reflexivity
         | _ => nsatz
         | _ => solve [auto]
         end.

Create HintDb push_basesystem_eval discriminated.
Local Ltac prove_eval := 
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with push_basesystem_eval uncps push_id cancel_pair in * )
         | _ => break_if
         | _ => break_match
         | _ => split 
         | H : _ /\ _ |- _ => destruct H
         | H : Some _ = Some _ |- _ => progress (inversion H; subst)
         | _ => discriminate
         | _ => reflexivity
         | _ => nsatz
         end.

Definition mod_eq m a b := a mod m = b mod m.
Global Instance mod_eq_equiv m : RelationClasses.Equivalence (mod_eq m).
Proof. constructor; congruence. Qed.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul.
Global Notation "a * b" := (runtime_mul a%RT b%RT) : runtime_scope.
Definition runtime_add := Z.add.
Global Notation "a + b" := (runtime_add a%RT b%RT) : runtime_scope. 
Definition runtime_fst {A B} := @fst A B.
Definition runtime_snd {A B} := @snd A B.

Module B.
  Local Definition limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Module Associational.
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.
    Hint Rewrite eval_nil eval_cons eval_app : push_basesystem_eval.

    Definition multerm (t t' : limb) : limb :=
      (fst t * fst t', (snd t * snd t')%RT).
    Lemma eval_map_multerm (a:limb) (q:list limb)
      : eval (List.map (multerm a) q) = fst a * snd a * eval q.
    Proof.
      induction q; cbv [multerm]; simpl List.map;
        autorewrite with push_basesystem_eval cancel_pair; nsatz.
    Qed. Hint Rewrite eval_map_multerm : push_basesystem_eval.

    Definition mul_cps (p q:list limb) {T} (f : list limb->T) :=
      flat_map_cps (fun t => @map_cps _ _ (multerm t) q) p f.

    Definition mul (p q:list limb) := mul_cps p q id.
    Lemma mul_cps_id p q: forall {T} f, @mul_cps p q T f = f (mul p q).
    Proof. cbv [mul_cps mul]; prove_id. Qed.
    Hint Opaque mul : uncps.
    Hint Rewrite mul_cps_id : uncps.

    Lemma eval_mul p q: eval (mul p q) = eval p * eval q.
    Proof. cbv [mul mul_cps]; induction p; prove_eval. Qed.
    Hint Rewrite eval_mul : push_basesystem_eval.

    Fixpoint split_cps (s:Z) (xs:list limb)
             {T} (f :list limb*list limb->T) :=
      match xs with
      | nil => f (nil, nil)
      | cons x xs' =>
        split_cps s xs'
              (fun sxs' =>
        if dec (fst x mod s = 0)
        then f (fst sxs',          cons (fst x / s, snd x) (snd sxs'))
        else f (cons x (fst sxs'), snd sxs'))
      end.

    Definition split s xs := split_cps s xs id.
    Lemma split_cps_id s p: forall {T} f,
        @split_cps s p T f = f (split s p).
    Proof.
      induction p;
        repeat match goal with
               | _ => rewrite IHp
               | _ => progress (cbv [split]; prove_id)
               end.
    Qed.
    Hint Opaque split : uncps.
    Hint Rewrite split_cps_id : uncps.

    Lemma eval_split s p (s_nonzero:s<>0):
      eval (fst (split s p)) + s*eval (snd (split s p)) = eval p.
    Proof.
      cbv [split];  induction p; prove_eval.
      match goal with
        H:_ |- _ =>
        unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
        end; nsatz.
    Qed. Hint Rewrite @eval_split using auto : push_basesystem_eval.

    Definition reduce_cps (s:Z) (c:list limb) (p:list limb)
               {T} (f : list limb->T) :=
      split_cps s p
                (fun ab => mul_cps c (snd ab)
                                  (fun rr =>f (fst ab ++ rr))).

    Definition reduce s c p := reduce_cps s c p id.
    Lemma reduce_cps_id s c p {T} f:
      @reduce_cps s c p T f = f (reduce s c p).
    Proof. cbv [reduce_cps reduce]; prove_id. Qed.
    Hint Opaque reduce : uncps.
    Hint Rewrite reduce_cps_id : uncps.
    
    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.
    Lemma eval_reduce s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0):
      mod_eq (s - eval c) (eval (reduce s c p)) (eval p).
    Proof.
      cbv [reduce reduce_cps mod_eq]; prove_eval;
        rewrite <-reduction_rule by auto; prove_eval.
    Qed.
    Hint Rewrite eval_reduce using (omega || assumption) : push_basesystem_eval.
    (* Why TF does this hint get picked up outside the section (while other eval_ hints do not?) *)

    Section Carries.
      Context {modulo div:Z->Z->Z}.
      Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.

      Definition carryterm_cps (w fw:Z) (t:limb) {T} (f:list limb->T) :=
        if dec (fst t = w)
        then dlet t2 := snd t in
             f ((w*fw, div t2 fw) :: (w, modulo t2 fw) :: @nil limb)
        else f [t].

      Definition carryterm w fw t := carryterm_cps w fw t id.
      Lemma carryterm_cps_id w fw t {T} f :
        @carryterm_cps w fw t T f
        = f (@carryterm w fw t).
      Proof. cbv [carryterm_cps carryterm Let_In]; prove_id. Qed.
      Hint Opaque carryterm : uncps.
      Hint Rewrite carryterm_cps_id : uncps.


      Lemma eval_carryterm w fw (t:limb) (fw_nonzero:fw<>0):
        eval (carryterm w fw t) = eval [t].
      Proof.
        cbv [carryterm_cps carryterm Let_In]; prove_eval.
        specialize (div_mod (snd t) fw fw_nonzero).
        nsatz.
      Qed. Hint Rewrite eval_carryterm using auto : push_basesystem_eval.

      Definition carry_cps(w fw:Z) (p:list limb) {T} (f:list limb->T) :=
        flat_map_cps (carryterm_cps w fw) p f.

      Definition carry w fw p := carry_cps w fw p id.
      Lemma carry_cps_id w fw p {T} f:
        @carry_cps w fw p T f = f (carry w fw p).
      Proof. cbv [carry_cps carry]; prove_id. Qed.
      Hint Opaque carry : uncps.
      Hint Rewrite carry_cps_id : uncps.

      Lemma eval_carry w fw p (fw_nonzero:fw<>0):
        eval (carry w fw p) = eval p.
      Proof. cbv [carry_cps carry]; induction p; prove_eval. Qed.
      Hint Rewrite eval_carry using auto : push_basesystem_eval.
    End Carries.

  End Associational.
  Hint Rewrite
      @Associational.carry_cps_id
      @Associational.carryterm_cps_id
      @Associational.reduce_cps_id
      @Associational.split_cps_id
      @Associational.mul_cps_id : uncps.

  Module Positional.
    Section Positional.
      Import Associational.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      (** Converting from positional to associational *)
      Definition to_associational_cps {n:nat} (xs:tuple Z n)
                 {T} (f:list limb->T) :=
        map_cps weight (seq 0 n)
                (fun r =>
                   to_list_cps n xs (fun rr => combine_cps r rr f)).
      
      Definition to_associational {n} xs :=
        @to_associational_cps n xs _ id.
      Lemma to_associational_cps_id {n} x {T} f:
        @to_associational_cps n x T f = f (to_associational x).
      Proof. cbv [to_associational_cps to_associational]; prove_id. Qed.
      Hint Opaque to_associational : uncps.
      Hint Rewrite @to_associational_cps_id : uncps.

      Definition eval {n} x :=
        @to_associational_cps n x _ Associational.eval.

      Lemma eval_to_associational {n} x :
        Associational.eval (@to_associational n x) = eval x.
      Proof.
        cbv [to_associational_cps eval to_associational]; prove_eval.
      Qed. Hint Rewrite @eval_to_associational : push_basesystem_eval.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof.
        cbv [eval Associational.eval to_associational_cps zeros];
          autorewrite with uncps; rewrite Tuple.to_list_from_list.
        generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz.
      Qed. Hint Rewrite eval_zeros : push_basesystem_eval.

      Definition add_to_nth_cps {n} i x t {T} (f:tuple Z n->T) :=
        @on_tuple_cps _ _ 0 (update_nth_cps i (runtime_add x)) n n t _ f.
      
      Definition add_to_nth {n} i x t := @add_to_nth_cps n i x t _ id.
      Lemma add_to_nth_cps_id {n} i x xs {T} f:
        @add_to_nth_cps n i x xs T f = f (add_to_nth i x xs).
      Proof.
        cbv [add_to_nth_cps add_to_nth]; erewrite !on_tuple_cps_correct
          by (intros; autorewrite with uncps; reflexivity); prove_id.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed.
      Hint Opaque add_to_nth : uncps.
      Hint Rewrite @add_to_nth_cps_id : uncps.
      
      Lemma eval_add_to_nth {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n):
        eval (@add_to_nth n i x xs) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational_cps add_to_nth add_to_nth_cps runtime_add].
        erewrite on_tuple_cps_correct by (intros; autorewrite with uncps; reflexivity).
        prove_eval.
        cbv [Tuple.on_tuple].
        rewrite !Tuple.to_list_from_list.
        autorewrite with uncps push_id.
        rewrite ListUtil.combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)); cbv [ListUtil.splice_nth id];
          repeat match goal with
                 | _ => progress (apply Zminus_eq; ring_simplify)
                 | _ => progress autorewrite with push_basesystem_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed. Hint Rewrite @eval_add_to_nth using omega : push_basesystem_eval.

      Fixpoint place_cps (t:limb) (i:nat) {T} (f:nat * Z->T) :=
        if dec (fst t mod weight i = 0)
        then f (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place_cps t i' f | O => f (O, fst t * snd t)%RT end.

      Definition place t i := place_cps t i id.
      Lemma place_cps_id t i {T} f :
        @place_cps t i T f = f (place t i).
      Proof. cbv [place]; induction i; prove_id. Qed.
      Hint Opaque place : uncps.
      Hint Rewrite place_cps_id : uncps.

      Lemma place_cps_in_range (t:limb) (n:nat)
        : (fst (place_cps t n id) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place_cps t i
        : weight (fst (place_cps t i id)) * snd (place_cps t i id)
          = fst t * snd t.
      Proof.
        induction i; cbv [id]; simpl place_cps; break_match;
          autorewrite with cancel_pair;
          try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto.
      Qed.

      Definition from_associational_cps n (p:list limb)
                 {T} (f:tuple Z n->T):=
        fold_right_cps
          (fun t st =>
             place_cps t (pred n)
                       (fun p=> add_to_nth_cps (fst p) (snd p) st id))
          (zeros n) p f.

      Definition from_associational n p := from_associational_cps n p id.
      Lemma from_associational_cps_id {n} p {T} f:
        @from_associational_cps n p T f = f (from_associational n p).
      Proof.
        cbv [from_associational_cps from_associational]; prove_id.
      Qed.
      Hint Opaque from_associational : uncps.
      Hint Rewrite @from_associational_cps_id : uncps.

      Lemma eval_from_associational {n} p (n_nonzero:n<>O):
        eval (from_associational n p) = Associational.eval p.
      Proof.
        cbv [from_associational_cps from_associational]; induction p;
          [|pose proof (place_cps_in_range a (pred n))]; prove_eval.
        cbv [place]; rewrite weight_place_cps. nsatz.
      Qed.
      Hint Rewrite @eval_from_associational using omega
        : push_basesystem_eval.

      Section Carries.
        Context {modulo div : Z->Z->Z}.
        Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.
        Definition carry_cps(index:nat) (p:list limb)
                   {T} (f:list limb->T) :=
          @Associational.carry_cps modulo div
                                   (weight index)
                                   (weight (S index) / weight index)
                                   p T f.

      Definition carry i p := carry_cps i p id.
      Lemma carry_cps_id i p {T} f:
        @carry_cps i p T f = f (carry i p).
      Proof.
        cbv [carry_cps carry]; prove_id; rewrite carry_cps_id; reflexivity.
      Qed.
      Hint Opaque carry : uncps. Hint Rewrite carry_cps_id : uncps.

      Lemma eval_carry i p: weight (S i) / weight i <> 0 ->
        Associational.eval (carry i p) = Associational.eval p.
      Proof. cbv [carry_cps carry]; intros; eapply @eval_carry; eauto. Qed.
      Hint Rewrite @eval_carry : push_basesystem_eval.

      (* TODO make a correctness proof for this *)
      Definition chained_carries (p:list limb) (idxs : list nat)
                 {T} (f:list limb->T) :=
        fold_right_cps2 carry_cps p idxs f.
      End Carries.
    End Positional.
  End Positional.
  Hint Rewrite
      @Associational.carry_cps_id
      @Associational.carryterm_cps_id
      @Associational.reduce_cps_id
      @Associational.split_cps_id
      @Associational.mul_cps_id
      @Positional.carry_cps_id
      @Positional.from_associational_cps_id
      @Positional.place_cps_id
      @Positional.add_to_nth_cps_id
      @Positional.to_associational_cps_id
    : uncps.
  Hint Rewrite
      @Associational.eval_mul
      @Positional.eval_to_associational
      @Associational.eval_carry
      @Associational.eval_carryterm
      @Associational.eval_reduce
      @Associational.eval_split
      @Positional.eval_carry
      @Positional.eval_from_associational
      @Positional.eval_add_to_nth
    using (omega || assumption) : push_basesystem_eval.
End B.
  
Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Import B.

Ltac basesystem_partial_evaluation_RHS := 
  let t0 := match goal with |- _ _ ?t => t end in
  let t := (eval cbv delta [
  (* this list must contain all definitions referenced by t that reference [Let_In], [runtime_add], or [runtime_mul] *)
Positional.to_associational_cps Positional.to_associational Positional.eval Positional.zeros Positional.add_to_nth_cps Positional.add_to_nth Positional.place_cps Positional.place Positional.from_associational_cps Positional.from_associational Positional.carry_cps Positional.carry Positional.chained_carries
Associational.eval Associational.multerm Associational.mul_cps Associational.mul Associational.split_cps Associational.split Associational.reduce_cps Associational.reduce Associational.carryterm_cps Associational.carryterm Associational.carry_cps Associational.carry 
                 ] in t0) in
  let t := (eval pattern @runtime_mul in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @runtime_add in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @Let_In in t) in
  let t := match t with ?t _ => t end in
  let t1 := fresh "t1" in
  pose t as t1;
  transitivity (t1
                  (@Let_In)
                  (@runtime_add)
                  (@runtime_mul));
  [replace_with_vm_compute t1; clear t1|reflexivity].

Ltac assert_preconditions :=
  repeat match goal with
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (wt 0%nat = 1) by (cbv; congruence)
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (forall i, wt i <> 0) by (intros; apply Z.pow_nonzero; try (cbv; congruence); solve [zero_bounds])
         | |- context [Positional.from_associational_cps ?wt ?n] =>
           unique assert (n <> 0%nat) by (cbv; congruence)
         | |- context [Positional.carry_cps?wt ?i] =>
           unique assert (wt (S i) / wt i <> 0) by (cbv; congruence)
         | |- context [Associational.reduce_cps ?s _] =>
           unique assert (s <> 0) by (cbv; congruence)
         | |- context [Associational.reduce_cps ?s ?c] =>
           unique assert (s - Associational.eval c <> 0) by (cbv; congruence)
         end.

(* matches out the `Prop` argument to `lift2_sig`, applies `lift2_sig` *)
Ltac lift2_sig :=
    lazymatch goal with
      |- @sig _ ?Pop
      => let P_ := constr:(fun op =>
                      ltac:(
                        lazymatch eval cbv beta in (Pop op) with
                          forall a b, @?P a b =>
                          exact (fun a b =>
                            ltac:(
                              let P := (eval cbv beta in (P a b)) in
                              let P := (eval pattern (op a b) in P) in
                              lazymatch P with ?P _ =>
                                exact P
                              end
                              )
                            )
                        end
                      )
                    ) in
         lazymatch P_ with
           fun _ => ?P => apply (lift2_sig P)
         end
    end.

Section Ops.
  Context
    (modulo : Z -> Z -> Z)
    (div : Z -> Z -> Z)
    (div_mod : forall a b : Z, b <> 0 ->
                               a = b * div a b + modulo a b).
  Local Infix "^" := tuple : type_scope.

  Let wt := fun i : nat => 2^(25 * (i / 2) + 26 * ((i + 1) / 2)).
  Let sz := 10%nat.
  Let s : Z := 2^255.
  Let c : list B.limb := [(1, 19)].

  Let m := Eval compute in s - Associational.eval c. (* modulus *)
  Let sz2 := Eval compute in ((sz * 2) - 1)%nat.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 eval (add a b) = eval a  + eval b }.
  Proof.
    let x := constr:(fun wt a b =>
        Positional.to_associational_cps (n := sz) wt a
          (fun r => Positional.to_associational_cps (n := sz) wt b
          (fun r0 => Positional.from_associational_cps wt sz (r ++ r0) id
                    ))) in
    lift2_sig; eexists;
    transitivity (Positional.eval wt (x wt a b));
      [|assert_preconditions; autorewrite with uncps push_id push_basesystem_eval; reflexivity].

    apply f_equal.
    
    basesystem_partial_evaluation_RHS.

    reflexivity.
  Defined.
  
  Definition mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 mod_eq m (eval (mul a b)) (eval a  * eval b)}.
  Proof.
    let x := constr:(fun w a b =>
         Positional.to_associational_cps (n := sz) w a
           (fun r => Positional.to_associational_cps (n := sz) w b
           (fun r0 => Associational.mul_cps r r0
           (fun r1 => Positional.from_associational_cps w sz2 r1
           (fun r2 => Positional.to_associational_cps w r2
           (fun r3 => Associational.reduce_cps s c r3       
           (fun r4 => Positional.from_associational_cps w sz r4
           (fun r5 => Positional.to_associational_cps w r5
           (fun r6 => Positional.chained_carries(div:=div)(modulo:=modulo) w r6 (seq 0 sz)
           (fun r13 => Positional.from_associational_cps w sz r13 id
             )))))))))) in
    lift2_sig; eexists;
    transitivity (Positional.eval wt (x wt a b));
    [|cbv [Positional.chained_carries fold_right_cps2 seq fold_right sz2 sz]; assert_preconditions; autorewrite with uncps push_id push_basesystem_eval; reflexivity].

    cbv [mod_eq].
    apply f_equal2; [|reflexivity].
    
    apply f_equal.

    basesystem_partial_evaluation_RHS.

    (* rough breakdown of synthesis time *)
    (* 1.2s for side conditions -- should improve significantly when [chained_carries] gets a correctness lemma *)
    (* basesystem_partial_evaluation_RHS (primarily vm_compute): 1.8s, which gets re-computed during defined *)

    (* doing [cbv -[Let_In runtime_add runtime_mul]] took 37s *)

    reflexivity.
  Defined. (* 3s *)
End Ops.

(*
Eval cbv [proj1_sig add_sig lift2_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig mul_sig lift2_sig] in
    (fun m d div_mod => proj1_sig (mul_sig m d div_mod)).
*)