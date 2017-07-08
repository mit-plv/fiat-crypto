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

Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Util.Decidable Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil Crypto.Util.Sigma.
Require Import Crypto.Util.CPSUtil Crypto.Util.Prod.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.VM.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.

Local Ltac prove_id :=
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with uncps push_id in * )
         | _ => break_innermost_match_step
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
         | _ => break_innermost_match_step
         | _ => split
         | H : _ /\ _ |- _ => destruct H
         | H : Some _ = Some _ |- _ => progress (inversion H; subst)
         | _ => discriminate
         | _ => reflexivity
         | _ => nsatz
         end.

Definition mod_eq (m:positive) a b := a mod m = b mod m.
Global Instance mod_eq_equiv m : RelationClasses.Equivalence (mod_eq m).
Proof. constructor; congruence. Qed.
Definition mod_eq_dec m a b : {mod_eq m a b} + {~ mod_eq m a b}
  := Z.eq_dec _ _.
Lemma mod_eq_Z2F_iff m a b :
  mod_eq m a b <-> Logic.eq (F.of_Z m a) (F.of_Z m b).
Proof. rewrite <-F.eq_of_Z_iff; reflexivity. Qed.

Delimit Scope runtime_scope with RT.

Definition runtime_mul := Z.mul.
Global Notation "a * b" := (runtime_mul a%RT b%RT) : runtime_scope.
Definition runtime_add := Z.add.
Global Notation "a + b" := (runtime_add a%RT b%RT) : runtime_scope.
Definition runtime_opp := Z.opp.
Global Notation "- a" := (runtime_opp a%RT) : runtime_scope.
Definition runtime_and := Z.land.
Global Notation "a &' b" := (runtime_and a%RT b%RT) : runtime_scope.
Definition runtime_shr := Z.shiftr.
Global Notation "a >> b" := (runtime_shr a%RT b%RT) : runtime_scope.
Definition runtime_lor := Z.lor.
Global Arguments runtime_lor (_ _)%RT.

Ltac cbv_runtime := cbv beta delta [runtime_add runtime_and runtime_lor runtime_mul runtime_opp runtime_shr].

Module B.
  Definition limb := (Z*Z)%type. (* position coefficient and run-time value *)
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
      induction p as [|?? IHp];
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

    Lemma reduction_rule a b s c m (m_eq:Z.pos m = s - c):
      (a + s * b) mod m = (a + c * b) mod m.
    Proof.
      rewrite m_eq. pose proof (Pos2Z.is_pos m).
      replace (a + s * b) with ((a + c*b) + b*(s-c)) by ring.
      rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by omega.
      trivial.
    Qed.
    Lemma eval_reduce s c p (s_nonzero:s<>0) m (m_eq : Z.pos m = s - eval c) :
      mod_eq m (eval (reduce s c p)) (eval p).
    Proof.
      cbv [reduce reduce_cps mod_eq]; prove_eval.
        erewrite <-reduction_rule by eauto; prove_eval.
    Qed.
    Hint Rewrite eval_reduce using (omega || assumption) : push_basesystem_eval.
    (* Why TF does this hint get picked up outside the section (while other eval_ hints do not?) *)


    Definition negate_snd_cps (p:list limb) {T} (f:list limb ->T) :=
      map_cps (fun cx => (fst cx, (-snd cx)%RT)) p f.

    Definition negate_snd p := negate_snd_cps p id.
    Lemma negate_snd_id p {T} f : @negate_snd_cps p T f = f (negate_snd p).
    Proof. cbv [negate_snd_cps negate_snd]; prove_id. Qed.
    Hint Opaque negate_snd : uncps.
    Hint Rewrite negate_snd_id : uncps.

    Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
    Proof.
      cbv [negate_snd_cps negate_snd]; induction p; prove_eval.
    Qed. Hint Rewrite eval_negate_snd : push_basesystem_eval.

    Section Carries.
      Context {modulo div:Z->Z->Z}.
      Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.

      Definition carryterm_cps (w fw:Z) (t:limb) {T} (f:list limb->T) :=
        if dec (fst t = w)
        then dlet t2 := snd t in
             dlet d2 := div t2 fw in
             dlet m2 := modulo t2 fw in
             f ((w*fw, d2) :: (w, m2) :: @nil limb)
        else f [t].

      Definition carryterm w fw t := carryterm_cps w fw t id.
      Lemma carryterm_cps_id w fw t {T} f :
        @carryterm_cps w fw t T f
        = f (@carryterm w fw t).
      Proof using Type. cbv [carryterm_cps carryterm Let_In]; prove_id. Qed.
      Hint Opaque carryterm : uncps.
      Hint Rewrite carryterm_cps_id : uncps.


      Lemma eval_carryterm w fw (t:limb) (fw_nonzero:fw<>0):
        eval (carryterm w fw t) = eval [t].
      Proof using Type*.
        cbv [carryterm_cps carryterm Let_In]; prove_eval.
        specialize (div_mod (snd t) fw fw_nonzero).
        nsatz.
      Qed. Hint Rewrite eval_carryterm using auto : push_basesystem_eval.

      Definition carry_cps (w fw:Z) (p:list limb) {T} (f:list limb->T) :=
        flat_map_cps (carryterm_cps w fw) p f.

      Definition carry w fw p := carry_cps w fw p id.
      Lemma carry_cps_id w fw p {T} f:
        @carry_cps w fw p T f = f (carry w fw p).
      Proof using Type. cbv [carry_cps carry]; prove_id. Qed.
      Hint Opaque carry : uncps.
      Hint Rewrite carry_cps_id : uncps.

      Lemma eval_carry w fw p (fw_nonzero:fw<>0):
        eval (carry w fw p) = eval p.
      Proof using Type*. cbv [carry_cps carry]; induction p; prove_eval. Qed.
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
      Proof using Type. cbv [to_associational_cps to_associational]; prove_id. Qed.
      Hint Opaque to_associational : uncps.
      Hint Rewrite @to_associational_cps_id : uncps.

      Definition eval {n} x :=
        @to_associational_cps n x _ Associational.eval.

      Lemma eval_single (x:Z) : eval (n:=1) x = weight 0%nat * x.
      Proof. cbv - [Z.mul Z.add]. ring. Qed.

      Lemma eval_unit : eval (n:=0) tt = 0.
      Proof. reflexivity. Qed.
      Hint Rewrite eval_unit eval_single : push_basesystem_eval.

      Lemma eval_to_associational {n} x :
        Associational.eval (@to_associational n x) = eval x.
      Proof using Type.
        cbv [to_associational_cps eval to_associational]; prove_eval.
      Qed. Hint Rewrite @eval_to_associational : push_basesystem_eval.

      (** (modular) equality that tolerates redundancy **)
      Definition eq {sz} m (a b : tuple Z sz) : Prop :=
        mod_eq m (eval a) (eval b).

      (** Converting from associational to positional *)

      Definition zeros n : tuple Z n := Tuple.repeat 0 n.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof using Type.
        cbv [eval Associational.eval to_associational_cps zeros].
        pose proof (seq_length n 0). generalize dependent (seq 0 n).
        intro xs; revert n; induction xs as [|?? IHxs]; intros n H;
          [autorewrite with uncps; reflexivity|].
        destruct n as [|n]; [distr_length|].
        specialize (IHxs n). autorewrite with uncps in *.
        rewrite !@Tuple.to_list_repeat in *.
        simpl List.repeat. rewrite map_cons, combine_cons, map_cons.
        simpl fold_right.  rewrite IHxs by distr_length. ring.
      Qed. Hint Rewrite eval_zeros : push_basesystem_eval.

      Definition add_to_nth_cps {n} i x t {T} (f:tuple Z n->T) :=
        @on_tuple_cps _ _ 0 (update_nth_cps i (runtime_add x)) n n t _ f.

      Definition add_to_nth {n} i x t := @add_to_nth_cps n i x t _ id.
      Lemma add_to_nth_cps_id {n} i x xs {T} f:
        @add_to_nth_cps n i x xs T f = f (add_to_nth i x xs).
      Proof using weight.
        cbv [add_to_nth_cps add_to_nth]; erewrite !on_tuple_cps_correct
          by (intros; autorewrite with uncps; reflexivity); prove_id.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed.
      Hint Opaque add_to_nth : uncps.
      Hint Rewrite @add_to_nth_cps_id : uncps.

      Lemma eval_add_to_nth {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n):
        eval (@add_to_nth n i x xs) = weight i * x + eval xs.
      Proof using Type.
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
      Proof using Type. cbv [place]; induction i; prove_id. Qed.
      Hint Opaque place : uncps.
      Hint Rewrite place_cps_id : uncps.

      Lemma place_cps_in_range (t:limb) (n:nat)
        : (fst (place_cps t n id) < S n)%nat.
      Proof using Type. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place_cps t i
        : weight (fst (place_cps t i id)) * snd (place_cps t i id)
          = fst t * snd t.
      Proof using Type*.
        induction i; cbv [id]; simpl place_cps; break_match;
          autorewrite with cancel_pair;
          try match goal with [H:_|-_] => apply Z_div_exact_full_2 in H end;
          nsatz || auto.
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
      Proof using Type.
        cbv [from_associational_cps from_associational]; prove_id.
      Qed.
      Hint Opaque from_associational : uncps.
      Hint Rewrite @from_associational_cps_id : uncps.

      Lemma eval_from_associational {n} p (n_nonzero:n<>O):
        eval (from_associational n p) = Associational.eval p.
      Proof using Type*.
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
        Definition carry_cps {n m} (index:nat) (p:tuple Z n)
                   {T} (f:tuple Z m->T) :=
          to_associational_cps p
            (fun P =>  @Associational.carry_cps
                         modulo div
                         (weight index)
                         (weight (S index) / weight index)
                         P T
             (fun R => from_associational_cps m R f)).

      Definition carry {n m} i p := @carry_cps n m i p _ id.
      Lemma carry_cps_id {n m} i p {T} f:
        @carry_cps n m i p T f = f (carry i p).
      Proof.
        cbv [carry_cps carry]; prove_id; rewrite carry_cps_id; reflexivity.
      Qed.
      Hint Opaque carry : uncps. Hint Rewrite @carry_cps_id : uncps.

      Lemma eval_carry {n m} i p: (n <> 0%nat) -> (m <> 0%nat) ->
                                weight (S i) / weight i <> 0 ->
        eval (carry (n:=n) (m:=m) i p) = eval p.
      Proof.
        cbv [carry_cps carry]; intros. prove_eval.
        rewrite @eval_carry by eauto.
        apply eval_to_associational.
      Qed.
      Hint Rewrite @eval_carry : push_basesystem_eval.

      (* N.B. It is important to reverse [idxs] here. Like
      [fold_right], [fold_right_cps2] is written such that the first
      terms in the list are actually used last in the computation. For
      example, running:

      `Eval cbv - [Z.add] in (fun a b c d => fold_right Z.add d [a;b;c]).`

      will produce [fun a b c d => (a + (b + (c + d)))].*)
      Definition chained_carries_cps {n} (p:tuple Z n) (idxs : list nat)
                 {T} (f:tuple Z n->T) :=
        fold_right_cps2 carry_cps p (rev idxs) f.

      Definition chained_carries {n} p idxs := @chained_carries_cps n p idxs _ id.
      Lemma chained_carries_id {n} p idxs : forall {T} f,
          @chained_carries_cps n p idxs T f = f (chained_carries p idxs).
      Proof using Type. cbv [chained_carries_cps chained_carries]; prove_id. Qed.
      Hint Opaque chained_carries : uncps.
      Hint Rewrite @chained_carries_id : uncps.

      Lemma eval_chained_carries {n} (p:tuple Z n) idxs :
        (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
        eval (chained_carries p idxs) = eval p.
      Proof using Type*.
        cbv [chained_carries chained_carries_cps]; intros;
          autorewrite with uncps push_id.
        apply fold_right_invariant; [|intro; rewrite <-in_rev];
          destruct n; prove_eval; auto.
      Qed. Hint Rewrite @eval_chained_carries : push_basesystem_eval.

      (* Reverse of [eval]; ranslate from Z to basesystem by putting
      everything in first digit and then carrying. This function, like
      [eval], is not defined using CPS. *)
      Definition encode {n} (x : Z) : tuple Z n :=
        chained_carries (from_associational n [(1,x)]) (seq 0 n).
      Lemma eval_encode {n} x : (n <> 0%nat) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval (@encode n x) = x.
      Proof using Type*. cbv [encode]; intros; prove_eval; auto. Qed.
      Hint Rewrite @eval_encode : push_basesystem_eval.

      End Carries.

      Section Wrappers.
        (* Simple wrappers for Associational definitions; convert to
        associational, do the operation, convert back. *)

        Definition add_cps {n} (p q : tuple Z n) {T} (f:tuple Z n->T) :=
          to_associational_cps p
            (fun P => to_associational_cps q
              (fun Q => from_associational_cps n (P++Q) f)).

        Definition mul_cps {n m} (p q : tuple Z n) {T} (f:tuple Z m->T) :=
          to_associational_cps p
            (fun P => to_associational_cps q
              (fun Q => Associational.mul_cps P Q
                (fun PQ => from_associational_cps m PQ f))).

        Definition reduce_cps {m n} (s:Z) (c:list B.limb) (p : tuple Z m)
                   {T} (f:tuple Z n->T) :=
          to_associational_cps p
            (fun P => Associational.reduce_cps s c P
               (fun R => from_associational_cps n R f)).

        Definition carry_reduce_cps {n div modulo}
                   (s:Z) (c:list limb) (p : tuple Z n)
                   {T} (f: tuple Z n ->T) :=
          carry_cps (div:=div) (modulo:=modulo) (n:=n) (m:=S n) (pred n) p
            (fun r => reduce_cps (m:=S n) (n:=n) s c r f).

        Definition negate_snd_cps {n} (p : tuple Z n)
                   {T} (f:tuple Z n->T) :=
          to_associational_cps p
            (fun P => Associational.negate_snd_cps P
              (fun R => from_associational_cps n R f)).

        Definition split_cps {n m1 m2} (s:Z) (p : tuple Z n)
                    {T} (f:(tuple Z m1 * tuple Z m2) -> T) :=
          to_associational_cps p
            (fun P => Associational.split_cps s P
            (fun split_P =>
              f (from_associational m1 (fst split_P),
                (from_associational m2 (snd split_P))))).

        Definition scmul_cps {n} (x : Z) (p: tuple Z n)
                    {T} (f:tuple Z n->T) :=
          to_associational_cps p
            (fun P => Associational.mul_cps P [(1, x)]
            (fun R => from_associational_cps n R f)).

        (* This version of sub does not add balance; bounds must be
        carefully handled. *)
        Definition unbalanced_sub_cps {n} (p q: tuple Z n)
                    {T} (f:tuple Z n->T) :=
          to_associational_cps p
            (fun P => to_associational_cps q
            (fun Q => Associational.negate_snd_cps Q
            (fun negQ => from_associational_cps n (P ++ negQ) f))).

      End Wrappers.
      Hint Unfold
           Positional.add_cps
           Positional.mul_cps
           Positional.reduce_cps
           Positional.carry_reduce_cps
           Positional.negate_snd_cps
           Positional.split_cps
           Positional.scmul_cps
           Positional.unbalanced_sub_cps
      .

      Section Subtraction.
        Context {m n} {coef : tuple Z n}
                {coef_mod : mod_eq m (eval coef) 0}.

        Definition sub_cps (p q : tuple Z n) {T} (f:tuple Z n->T):=
          add_cps coef p
            (fun cp => negate_snd_cps q
              (fun _q => add_cps cp _q f)).

        Definition sub p q := sub_cps p q id.
        Lemma sub_id p q {T} f : @sub_cps p q T f = f (sub p q).
        Proof using Type. cbv [sub_cps sub]; autounfold; prove_id. Qed.
        Hint Opaque sub : uncps.
        Hint Rewrite sub_id : uncps.

        Lemma eval_sub p q : mod_eq m (eval (sub p q)) (eval p - eval q).
        Proof using Type*.
          cbv [sub sub_cps]; autounfold; destruct n; prove_eval.
          transitivity (eval coef + (eval p - eval q)).
          { apply f_equal2; ring. }
          { cbv [mod_eq] in *; rewrite Z.add_mod_full, coef_mod, Z.add_0_l, Zmod_mod. reflexivity. }
        Qed.

        Definition opp_cps (p : tuple Z n) {T} (f:tuple Z n->T):=
          sub_cps (zeros n) p f.
      End Subtraction.

      (* Lemmas about converting to/from F. Will be useful in proving
      that basesystem is isomorphic to F.commutative_ring_modulo.*)
      Section F.
        Context {sz:nat} {sz_nonzero : sz<>0%nat} {m :positive}.
        Context (weight_divides : forall i : nat, weight (S i) / weight i <> 0).
        Context {modulo div:Z->Z->Z}
                {div_mod : forall a b:Z, b <> 0 ->
                                         a = b * (div a b) + modulo a b}.

        Definition Fencode (x : F m) : tuple Z sz :=
          encode (div:=div) (modulo:=modulo) (F.to_Z x).

        Definition Fdecode (x : tuple Z sz) : F m := F.of_Z m (eval x).

        Lemma Fdecode_Fencode_id x : Fdecode (Fencode x) = x.
        Proof using div_mod sz_nonzero weight_0 weight_divides weight_nonzero.
          cbv [Fdecode Fencode]; rewrite @eval_encode by auto.
          apply F.of_Z_to_Z.
        Qed.

        Lemma eq_Feq_iff a b :
          Logic.eq (Fdecode a) (Fdecode b) <-> eq m a b.
        Proof using Type. cbv [Fdecode]; rewrite <-F.eq_of_Z_iff; reflexivity. Qed.
      End F.


    End Positional.
    Hint Rewrite eval_unit eval_single : push_basesystem_eval.

    (* Helper lemmas and definitions for [eval] that to be in a
    separate section so the weight function can change. *)
    Section EvalHelpers.
      Lemma eval_step {n} (x:tuple Z n) : forall wt z,
        eval wt (Tuple.append z x) = wt 0%nat * z + eval (fun i => wt (S i)) x.
      Proof.
        destruct n; [reflexivity|].
        intros; cbv [eval to_associational_cps].
        autorewrite with uncps. rewrite map_S_seq. reflexivity.
      Qed.

      Lemma eval_left_append {n} : forall wt x xs,
          eval wt (Tuple.left_append (n:=n) x xs)
          = wt n * x + eval wt xs.
      Proof.
        induction n as [|n IHn]; intros wt x xs; try destruct xs;
          unfold Tuple.left_append; fold @Tuple.left_append;
            autorewrite with push_basesystem_eval; [ring|].
        rewrite (Tuple.subst_append xs), Tuple.hd_append, Tuple.tl_append.
        rewrite !eval_step, IHn. ring.
      Qed.
      Hint Rewrite @eval_left_append : push_basesystem_eval.

      Lemma eval_wt_equiv {n} :forall wta wtb (x:tuple Z n),
          (forall i, wta i = wtb i) -> eval wta x = eval wtb x.
      Proof.
        destruct n as [|n]; [reflexivity|].
        induction n as [|n IHn]; intros wta wtb x H; [rewrite !eval_single, H; reflexivity|].
        simpl tuple in *; destruct x.
        change (t, z) with (Tuple.append (n:=S n) z t).
        rewrite !eval_step. rewrite (H 0%nat). apply Group.cancel_left.
        apply IHn; auto.
      Qed.

      Definition eval_from {n} weight (offset:nat) (x : tuple Z n) : Z :=
        eval (fun i => weight (i+offset)%nat) x.

      Lemma eval_from_0 {n} wt x : @eval_from n wt 0 x = eval wt x.
      Proof. cbv [eval_from]. auto using eval_wt_equiv. Qed.
    End EvalHelpers.

    Section Select.
      Context {weight : nat -> Z}.

      Definition select_cps {n} (mask cond:Z) (p:tuple Z n)
                 {T} (f:tuple Z n->T) :=
        dlet t := Z.zselect cond 0 mask in Tuple.map_cps (runtime_and t) p f.

      Definition select {n} mask cond p := @select_cps n mask cond p _ id.
      Lemma select_id {n} mask cond p T f :
        @select_cps n mask cond p T f = f (select mask cond p).
      Proof.
        cbv [select select_cps Let_In]; autorewrite with uncps push_id;
          reflexivity.
      Qed.
      Hint Opaque select : uncps.

      Lemma map_and_0 {n} (p:tuple Z n) : Tuple.map (Z.land 0) p = zeros n.
      Proof.
        induction n as [|n IHn]; [destruct p; reflexivity | ].
        rewrite (Tuple.subst_append p), Tuple.map_append, Z.land_0_l, IHn.
        reflexivity.
      Qed.

      Lemma eval_select {n} mask cond x (H:Tuple.map (Z.land mask) x = x) :
        B.Positional.eval weight (@select n mask cond x) =
        if dec (cond = 0) then 0 else  B.Positional.eval weight x.
      Proof.
        cbv [select select_cps Let_In].
        autorewrite with uncps push_id.
        rewrite Z.zselect_correct; break_match.
        { rewrite map_and_0. apply B.Positional.eval_zeros. }
        {  change runtime_and with Z.land. rewrite H; reflexivity. }
      Qed.

    End Select.

  End Positional.

  Hint Unfold
      Positional.add_cps
      Positional.mul_cps
      Positional.reduce_cps
      Positional.carry_reduce_cps
      Positional.negate_snd_cps
      Positional.split_cps
      Positional.scmul_cps
      Positional.unbalanced_sub_cps
      Positional.opp_cps
  .
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
      @Positional.chained_carries_id
      @Positional.sub_id
      @Positional.select_id
    : uncps.
  Hint Rewrite
       @Associational.eval_mul
       @Positional.eval_single
       @Positional.eval_unit
       @Positional.eval_to_associational
       @Positional.eval_left_append
       @Associational.eval_carry
       @Associational.eval_carryterm
       @Associational.eval_reduce
       @Associational.eval_split
       @Positional.eval_zeros
       @Positional.eval_carry
       @Positional.eval_from_associational
       @Positional.eval_add_to_nth
       @Positional.eval_chained_carries
       @Positional.eval_sub
       @Positional.eval_select
    using (assumption || vm_decide) : push_basesystem_eval.
End B.

(* Modulo and div that do shifts if possible, otherwise normal mod/div *)
Section DivMod.
  Definition modulo (a b : Z) : Z :=
    if dec (2 ^ (Z.log2 b) = b)
    then let x := (Z.ones (Z.log2 b)) in (a &' x)%RT
    else Z.modulo a b.

  Definition div (a b : Z) : Z :=
    if dec (2 ^ (Z.log2 b) = b)
    then let x := Z.log2 b in (a >> x)%RT
    else Z.div a b.

  Lemma div_correct a b : div a b = Z.div a b.
  Proof.
    cbv [div]; intros. break_match; try reflexivity.
    rewrite Z.shiftr_div_pow2 by apply Z.log2_nonneg.
    congruence.
  Qed.

  Lemma modulo_correct a b : modulo a b = Z.modulo a b.
  Proof.
    cbv [modulo]; intros. break_match; try reflexivity.
    rewrite Z.land_ones by apply Z.log2_nonneg.
    congruence.
  Qed.

  Lemma div_mod a b (H:b <> 0) : a = b * div a b + modulo a b.
  Proof.
    cbv [div modulo]; intros. break_match; auto using Z.div_mod.
    rewrite Z.land_ones, Z.shiftr_div_pow2 by apply Z.log2_nonneg.
    pose proof (Z.div_mod a b H). congruence.
  Qed.
End DivMod.

Import B.

Ltac basesystem_partial_evaluation_RHS :=
  let t0 := match goal with |- _ _ ?t => t end in
  let t := (eval cbv delta [
  (* this list must contain all definitions referenced by t that reference [Let_In], [runtime_add], [runtime_opp], [runtime_mul], [runtime_shr], or [runtime_and] *)
Positional.to_associational_cps Positional.to_associational Positional.eval Positional.zeros Positional.add_to_nth_cps Positional.add_to_nth Positional.place_cps Positional.place Positional.from_associational_cps Positional.from_associational Positional.carry_cps Positional.carry Positional.chained_carries_cps Positional.chained_carries Positional.sub_cps Positional.sub Positional.split_cps Positional.scmul_cps Positional.unbalanced_sub_cps Positional.negate_snd_cps Positional.add_cps Positional.opp_cps Associational.eval Associational.multerm Associational.mul_cps Associational.mul Associational.split_cps Associational.split Associational.reduce_cps Associational.reduce Associational.carryterm_cps Associational.carryterm Associational.carry_cps Associational.carry Associational.negate_snd_cps Associational.negate_snd div modulo
                 ] in t0) in
  let t := (eval pattern @runtime_mul in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @runtime_add in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @runtime_opp in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @runtime_shr in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @runtime_and in t) in
  let t := match t with ?t _ => t end in
  let t := (eval pattern @Let_In in t) in
  let t := match t with ?t _ => t end in
  let t1 := fresh "t1" in
  pose t as t1;
  transitivity (t1
                  (@Let_In)
                  (@runtime_and)
                  (@runtime_shr)
                  (@runtime_opp)
                  (@runtime_add)
                  (@runtime_mul));
  [replace_with_vm_compute t1; clear t1|reflexivity].

(** This block of tactic code works around bug #5434
    (https://coq.inria.fr/bugs/show_bug.cgi?id=5434), that
    [vm_compute] breaks an invariant in pretyping/constr_matching.ml.
    So we refresh all of the names in match statements in the goal by
    crawling it.

    In particular, [replace_with_vm_compute] creates a [vm_compute]d
    term which has anonymous binders where pretyping expects there to
    be named binders.  This shows up when you try to match on the
    function (the branch statement of the match) with an Ltac pattern
    like [(fun x : ?T => ?C)] rather than [(fun x : ?T => @?C x)]; we
    use the former in reification to save the cost of many extra
    invocations of [cbv beta].  Luckily, patterns like [(fun x : ?T =>
    @?C x)] don't trigger this anomaly, so we can walk the term,
    fixing all match statements whose branches are functions whose
    binder names were eaten by [vm_compute] (note that in a match,
    every branch where the corresponding constructor takes arguments
    is represented internally as a function (lambda term)).  We fix
    the match statements by pulling out the branch with the [@?]
    pattern that doesn't trigger the anomaly, and then recreating the
    match with a destructuring [let] that hasn't been through
    [vm_compute], and therefore has name information that
    constr_matching is happy with. *)
Ltac replace_match_with_destructuring_match T :=
  match T with
  | ?F ?X
    => let F' := replace_match_with_destructuring_match F in
       let X' := replace_match_with_destructuring_match X in
       constr:(F' X')
  (* we must use [@?f a b] here and not [?f], or else we get an anomaly *)
  | match ?d with pair a b => @?f a b end
    => let d' := replace_match_with_destructuring_match d in
       let T' := fresh in
       constr:(let '(a, b) := d' in
               match f a b with
               | T' => ltac:(let v := (eval cbv beta delta [T'] in T') in
                             let v := replace_match_with_destructuring_match v in
                             exact v)
               end)
  | (fun a : ?A => @?f a)
    => let T' := fresh in
       let T' := fresh T' in
       let T' := fresh T' in
       constr:(fun a : A
               => match f a with
                  | T' => ltac:(let v := (eval cbv beta delta [T'] in T') in
                                let v := replace_match_with_destructuring_match v in
                                exact v)
                  end)
  | ?x => x
  end.
Ltac do_replace_match_with_destructuring_match_in_goal :=
  let G := get_goal in
  let G' := replace_match_with_destructuring_match G in
  change G'.

(* TODO : move *)
Lemma F_of_Z_opp {m} x : F.of_Z m (- x) = F.opp (F.of_Z m x).
Proof.
  cbv [F.opp]; intros. rewrite F.to_Z_of_Z, <-Z.sub_0_l.
  etransitivity; rewrite F.of_Z_mod;
    [rewrite Z.opp_mod_mod|]; reflexivity.
Qed.

Hint Rewrite <-@F.of_Z_add : pull_FofZ.
Hint Rewrite <-@F.of_Z_mul : pull_FofZ.
Hint Rewrite <-@F.of_Z_sub : pull_FofZ.
Hint Rewrite <-@F_of_Z_opp : pull_FofZ.

Ltac F_mod_eq :=
  cbv [Positional.Fdecode]; autorewrite with pull_FofZ;
  apply mod_eq_Z2F_iff.

Ltac solve_op_mod_eq wt x :=
  transitivity (Positional.eval wt x); repeat autounfold;
  [|autorewrite with uncps push_id push_basesystem_eval;
    reflexivity];
  cbv [mod_eq]; apply f_equal2; [|reflexivity];
  apply f_equal;
  basesystem_partial_evaluation_RHS;
  do_replace_match_with_destructuring_match_in_goal.

Ltac solve_op_F wt x := F_mod_eq; solve_op_mod_eq wt x.
