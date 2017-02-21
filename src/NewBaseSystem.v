Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn. 
Require Import ZArith Nsatz Psatz Coq.omega.Omega.

Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.
Require Import Crypto.Util.CPSUtil.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.
Require Import Recdef.

(* TODO: move *)
Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.
Create HintDb cancel_pair discriminated. Hint Rewrite @fst_pair @snd_pair : cancel_pair.

Lemma push_id {A} (a:A) : id a = a. reflexivity. Qed.
Create HintDb push_id discriminated. Hint Rewrite @push_id : push_id.

Ltac prove_id :=
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

Create HintDb push_eval discriminated.
Ltac prove_eval := 
  repeat match goal with
         | _ => progress intros
         | _ => progress simpl
         | _ => progress cbv [Let_In]
         | _ => progress (autorewrite with push_eval uncps push_id cancel_pair in * )
         | _ => break_if
         | _ => break_match
         | _ => split 
         | H : _ /\ _ |- _ => destruct H
         | H : Some _ = Some _ |- _ => progress (inversion H; subst)
         | _ => discriminate
         | _ => reflexivity
         | _ => nsatz
         end.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul. Global Infix "*" := runtime_mul : runtime_scope.
Definition runtime_add := Z.add. Global Infix "+" := runtime_add : runtime_scope. 
Definition runtime_div := Z.div. Global Infix "/" := runtime_div : runtime_scope. 
Definition runtime_modulo := Z.modulo. Global Infix "mod" := runtime_modulo : runtime_scope.
Definition runtime_fst {A B} := @fst A B.
Definition runtime_snd {A B} := @snd A B.

Module B.
  Let limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Module Associational.
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.
    Hint Rewrite eval_nil eval_cons eval_app : push_eval.

    Definition multerm (t t' : limb) : limb :=
      (fst t * fst t', (snd t * snd t')%RT).
    Definition mul (p q:list limb) {T} (f : list limb->T) :=
      flat_map_cps (fun t => @map_cps _ _ (multerm t) q) p f.
    Definition mul_noncps (p q:list limb) := mul p q id.
    Hint Opaque mul_noncps : uncps.
    Lemma eval_map_mul (a:limb) (q:list limb) : eval (List.map (multerm a) q) = fst a * snd a * eval q.
    Proof.
      induction q; cbv [multerm]; simpl List.map;
        autorewrite with push_eval cancel_pair; nsatz.
    Qed. Hint Rewrite eval_map_mul : push_eval.
    Lemma mul_id p q: forall {T} f,
      @mul p q T f = f (mul_noncps p q).
    Proof. cbv [mul mul_noncps]; prove_id. Qed. Hint Rewrite @mul_id : uncps.
    Lemma eval_mul_noncps p q:
      eval (mul_noncps p q) = eval p * eval q.
    Proof.
      cbv [mul_noncps mul]; induction p; prove_eval. Qed. Hint Rewrite eval_mul_noncps : push_eval.

    Fixpoint split (s:Z) (xs:list limb)
             {T} (f :list limb*list limb->T) :=
      match xs with
      | nil => f (nil, nil)
      | cons x xs' =>
        split s xs'
              (fun sxs' =>
        if dec (fst x mod s = 0)
        then f (fst sxs',          cons (fst x / s, snd x) (snd sxs'))
        else f (cons x (fst sxs'), snd sxs'))
      end.
    Definition split_noncps s xs := split s xs id.
    Hint Opaque split_noncps : uncps.
    Lemma split_id s p: forall {T} f,
        @split s p T f = f (split_noncps s p).
    Proof.
      induction p;
        repeat match goal with
               | _ => rewrite IHp
               | _ => progress (cbv [split_noncps]; prove_id)
               end.
    Qed. Hint Rewrite split_id : uncps.
    Lemma eval_split_noncps s p (s_nonzero:s<>0):
      eval (fst (split_noncps s p)) + s*eval (snd (split_noncps s p))  = eval p.
    Proof.
      cbv [split_noncps];  induction p; prove_eval.
        match goal with H:_ |- _ =>
                        unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
        end; nsatz.
    Qed. Hint Rewrite @eval_split_noncps using auto : push_eval.

    Definition reduce (s:Z) (c:list limb) (p:list limb)
               {T} (f : list limb->T) :=
      split s p (fun ab => mul c (snd ab) (fun rr =>f (fst ab ++ rr))).
    Definition reduce_noncps s c p := reduce s c p id.
    Hint Opaque reduce_noncps : uncps.
    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.
    Lemma reduce_id s c p {T} f:
      @reduce s c p T f = f (reduce_noncps s c p).
    Proof. cbv [reduce reduce_noncps]; prove_id. Qed. Hint Rewrite reduce_id : uncps.
    Lemma eval_reduce_noncps s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0):
      eval (reduce_noncps s c p) mod (s - eval c) = eval p mod (s - eval c).
    Proof.
      cbv [reduce_noncps reduce]; prove_eval;
        rewrite <-reduction_rule by auto; prove_eval.
    Qed. Hint Rewrite eval_reduce_noncps : push_eval.

    Section Carries.
      Context {modulo div:Z->Z->Z}.
      Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.

      Definition carryterm (w fw:Z) (t:limb) {T} (f:list limb->T) :=
        if dec (fst t = w)
        then dlet d := div (snd t) fw in
             dlet m := modulo (snd t) fw in
             f ((w*fw, d) :: (w, m) :: @nil limb)
        else f [t].
      Definition carry (w fw:Z) (p:list limb) {T} (f:list limb->T) :=
        flat_map_cps (carryterm w fw) p f.
      Definition carryterm_noncps w fw t := carryterm w fw t id.
      Hint Opaque carryterm_noncps : uncps.
      Definition carry_noncps w fw p := carry w fw p id.
      Hint Opaque carry_noncps : uncps.
      Lemma carryterm_id w fw t {T} f :
        @carryterm w fw t T f
        = f (@carryterm_noncps w fw t).
      Proof. cbv [carryterm carryterm_noncps Let_In]; prove_id. Qed. Hint Rewrite carryterm_id : uncps.
      Lemma eval_carryterm_noncps w fw (t:limb) (fw_nonzero:fw<>0):
        eval (carryterm_noncps w fw t) = eval [t].
      Proof.
        cbv [carryterm carryterm_noncps Let_In]; prove_eval.
        specialize (div_mod (snd t) fw fw_nonzero).
        nsatz.
      Qed. Hint Rewrite eval_carryterm_noncps using auto : push_eval.
      Lemma carry_id w fw p {T} f:
        @carry w fw p T f = f (carry_noncps w fw p).
      Proof. cbv [carry carry_noncps]; prove_id. Qed.
      Hint Rewrite carry_id : uncps.
      Lemma eval_carry_noncps w fw p (fw_nonzero:fw<>0):
        eval (carry_noncps w fw p) = eval p.
      Proof. cbv [carry carry_noncps]; induction p; prove_eval. Qed.
      Hint Rewrite eval_carry_noncps using auto : push_eval.
    End Carries.

    Section Saturated.
      Context {word_max : Z} {word_max_pos : 1 < word_max} 
              {add : Z -> Z -> Z * Z}
              {add_correct : forall x y, fst (add x y) + word_max * snd (add x y) = x + y}
              {mul : Z -> Z -> Z * Z}
              {mul_correct : forall x y, fst (mul x y) + word_max * snd (mul x y) = x * y}
              {end_wt:Z} {end_wt_pos : 0 < end_wt}
      .

      Definition sat_multerm (t t' : limb) {T} (f:list limb->T) :=
        dlet tt' := mul (snd t) (snd t') in
              f ((fst t*fst t', runtime_fst tt') :: (fst t*fst t'*word_max, runtime_snd tt') :: nil)%list.
      Definition sat_mul (p q : list limb) {T} (f:list limb->T) := 
        flat_map_cps (fun t => @flat_map_cps _ _ (sat_multerm t) q) p f.
      (* TODO (jgross): kind of an interesting behavior--it infers the type arguments like this but fails to check if I leave them implicit *)
      Definition sat_multerm_noncps t t' := sat_multerm t t' id.
      Definition sat_mul_noncps p q := sat_mul p q id.
      Hint Opaque sat_multerm_noncps sat_mul_noncps : uncps.
      Lemma sat_multerm_id t t' : forall {T} (f:list limb->T),
       sat_multerm t t' f = f (sat_multerm_noncps t t').
      Proof. reflexivity. Qed. Hint Rewrite sat_multerm_id : uncps.
      Lemma eval_map_sat_mul t q :
        eval (flat_map (fun x => sat_multerm t x id) q) = fst t * snd t * eval q.
      Proof.
        cbv [sat_multerm_noncps sat_multerm Let_In runtime_fst runtime_snd];
        induction q; prove_eval;
          try match goal with |- context [mul ?a ?b] =>
                              specialize (mul_correct a b) end;
          nsatz.
      Qed. Hint Rewrite eval_map_sat_mul : push_eval.
      Lemma sat_mul_id p q {T} f : @sat_mul p q T f = f (sat_mul_noncps p q).
      Proof. cbv [sat_mul sat_mul_noncps]; prove_id. Qed. Hint Rewrite sat_mul_id : uncps.
      Lemma eval_sat_mul_noncps p q : eval (sat_mul_noncps p q) = eval p * eval q.
      Proof. cbv [sat_mul_noncps sat_mul]; induction p; prove_eval.  Qed.
      Hint Rewrite eval_sat_mul_noncps : push_eval.

    End Saturated.
  End Associational.
  Hint Rewrite
      @Associational.sat_mul_id
      @Associational.sat_multerm_id
      @Associational.carry_id
      @Associational.carryterm_id
      @Associational.reduce_id
      @Associational.split_id
      @Associational.mul_id : uncps.

  Module Positional.
    Section Positional.
      Import Associational.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      (** Converting from positional to associational *)

      Definition to_associational {n:nat} (xs:tuple Z n)
                 {T} (f:list limb->T) :=
        map_cps weight (seq 0 n)
                (fun r =>
                   to_list_cps n xs (fun rr => combine_cps r rr f)).
      Definition to_associational_noncps {n} xs := @to_associational n xs _ id.
      Definition eval {n} x := @to_associational n x _ Associational.eval.
      Lemma to_associational_id {n} x {T} f:
        @to_associational n x T f = f (to_associational_noncps x).
      Proof. cbv [to_associational to_associational_noncps]; prove_id. Qed.
      Hint Rewrite @to_associational_id : uncps.
      Lemma eval_to_associational_noncps {n} x :
        Associational.eval (@to_associational_noncps n x) = eval x.
      Proof. cbv [to_associational eval to_associational_noncps]; prove_eval. Qed.
      Hint Rewrite @eval_to_associational_noncps : push_eval.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof.
        cbv [eval Associational.eval to_associational zeros];
          autorewrite with uncps; rewrite Tuple.to_list_from_list.
        generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz.
      Qed. Hint Rewrite eval_zeros : push_eval.

      Definition add_to_nth {n} i x t {T} (f:tuple Z n->T) :=
        @on_tuple_cps _ _ 0 (update_nth_cps i (runtime_add x)) n n t _ f.
      Definition add_to_nth_noncps {n} i x t := @add_to_nth n i x t _ id.
      Hint Opaque add_to_nth_noncps : uncps.
      Lemma add_to_nth_id {n} i x xs {T} f:
        @add_to_nth n i x xs T f = f (add_to_nth_noncps i x xs).
      Proof.
        cbv [add_to_nth add_to_nth_noncps]; erewrite !on_tuple_cps_correct
          by (intros; autorewrite with uncps; reflexivity); prove_id.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed. Hint Rewrite @add_to_nth_id : uncps.
      Lemma eval_add_to_nth_noncps {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n):
        eval (@add_to_nth_noncps n i x xs) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational add_to_nth_noncps add_to_nth runtime_add].
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
                 | _ => progress autorewrite with push_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia.
        Unshelve.
        intros; subst. autorewrite with uncps push_id. distr_length.
      Qed. Hint Rewrite @eval_add_to_nth_noncps using omega : push_eval.

      Fixpoint place (t:limb) (i:nat) {T} (f:nat * Z->T) :=
        if dec (fst t mod weight i = 0)
        then f (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place t i' f | O => f (O, fst t * snd t)%RT end.
      Lemma place_in_range (t:limb) (n:nat) : (fst (place t n id) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place t i : weight (fst (place t i id)) * snd (place t i id) = fst t * snd t.
      Proof.
        induction i; cbv [id]; simpl place; break_match;
          autorewrite with cancel_pair;
          try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto.
      Qed.
      Definition place_noncps t i := place t i id.
      Hint Opaque place_noncps : uncps.
      Lemma place_id t i {T} f :
        @place t i T f = f (place_noncps t i).
      Proof. cbv [place_noncps]; induction i; prove_id. Qed.
      Hint Rewrite place_id : uncps.
      Definition from_associational n (p:list limb) {T} (f:tuple Z n->T):=
        fold_right_cps (fun t st => place t (pred n) (fun p=> add_to_nth (fst p) (snd p) st id)) (zeros n) p f.
      Definition from_associational_noncps n p := from_associational n p id.
      Hint Opaque from_associational_noncps : uncps.
      Lemma from_associational_id {n} p {T} f:
        @from_associational n p T f = f (from_associational_noncps n p).
      Proof. cbv [from_associational from_associational_noncps]; prove_id. Qed.
      Hint Rewrite @from_associational_id : uncps.
      Lemma eval_from_associational_noncps {n} p (n_nonzero:n<>O):
        eval (from_associational_noncps n p) = Associational.eval p.
      Proof.
        cbv [from_associational from_associational_noncps]; induction p;
          [|pose proof (place_in_range a (pred n))]; prove_eval.
        cbv [place_noncps]; rewrite weight_place. nsatz.
      Qed. Hint Rewrite @eval_from_associational_noncps using omega : push_eval.

      Section Carries.
        Context {modulo div : Z->Z->Z}.
        Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.
      Definition carry (index:nat) (p:list limb) {T} (f:list limb->T) :=
        @Associational.carry modulo div (weight index) (weight (S index) / weight index) p T f.
      Definition carry_noncps i p := carry i p id.
      Hint Opaque carry_noncps : uncps.
      Lemma carry_id i p {T} f:
        @carry i p T f = f (carry_noncps i p).
      Proof. cbv [carry carry_noncps]; prove_id; rewrite carry_id; reflexivity. Qed.
      Hint Rewrite carry_id : uncps.
      Lemma eval_carry_noncps i p: weight (S i) / weight i <> 0 ->
        Associational.eval (carry_noncps i p) = Associational.eval p.
      Proof. cbv [carry carry_noncps]; intros; eapply @eval_carry_noncps; eauto. Qed.
      Hint Rewrite @eval_carry_noncps : push_eval.
      End Carries.
    End Positional.
  End Positional.
  Hint Rewrite
      @Associational.sat_mul_id
      @Associational.sat_multerm_id
      @Associational.carry_id
      @Associational.carryterm_id
      @Associational.reduce_id
      @Associational.split_id
      @Associational.mul_id
      @Positional.carry_id
      @Positional.from_associational_id
      @Positional.place_id
      @Positional.add_to_nth_id
      @Positional.to_associational_id
    : uncps.
  Hint Rewrite
      @Associational.eval_sat_mul_noncps
      @Associational.eval_mul_noncps
      @Positional.eval_to_associational_noncps
      @Associational.eval_carry_noncps
      @Associational.eval_carryterm_noncps
      @Associational.eval_reduce_noncps
      @Associational.eval_split_noncps
      @Positional.eval_carry_noncps
      @Positional.eval_from_associational_noncps
      @Positional.eval_add_to_nth_noncps
    using (omega || assumption) : push_eval.
End B.
  

Section Karatsuba.
  Context {T : Type} (eval : T -> Z)
          (sub : T -> T -> T)
          (eval_sub : forall x y, eval (sub x y) = eval x - eval y)
          (mul : T -> T -> T)
          (eval_mul : forall x y, eval (mul x y) = eval x * eval y)
          (add : T -> T -> T)
          (eval_add : forall x y, eval (add x y) = eval x + eval y)
          (scmul : Z -> T -> T)
          (eval_scmul : forall c x, eval (scmul c x) = c * eval x)
          (split : Z -> T -> T * T)
          (eval_split : forall s x, s <> 0 -> eval (fst (split s x)) + s * (eval (snd (split s x))) = eval x)
  .

  Definition karatsuba_mul s (x y : T) : T :=
      let xab := split s x in
      let yab := split s y in
      let xy0 := mul (fst xab) (fst yab) in
      let xy2 := mul (snd xab) (snd yab) in
      let xy1 := sub (mul (add (fst xab) (snd xab)) (add (fst yab) (snd yab))) (add xy2 xy0) in
      add (add (scmul (s^2) xy2) (scmul s xy1)) xy0.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval (karatsuba_mul s x y) = eval x * eval y.
  Proof. cbv [karatsuba_mul]; repeat rewrite ?eval_sub, ?eval_mul, ?eval_add, ?eval_scmul.
         rewrite <-(eval_split s x), <-(eval_split s y) by assumption; ring. Qed.


  Definition goldilocks_mul s (xs ys : T) : T :=
    let a_b := split s xs in
    let c_d := split s ys in
    let ac := mul (fst a_b) (fst c_d) in
    (add (add ac (mul (snd a_b) (snd c_d)))
         (scmul s (sub (mul (add (fst a_b) (snd a_b)) (add (fst c_d) (snd c_d))) ac))).

  Local Existing Instances Z.equiv_modulo_Reflexive RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval (goldilocks_mul s xs ys)) mod p = (eval xs * eval ys) mod p.
  Proof. cbv [goldilocks_mul]; Zmod_to_equiv_modulo.
    repeat rewrite ?eval_mul, ?eval_add, ?eval_sub, ?eval_scmul, <-?(eval_split s xs), <-?(eval_split s ys) by assumption; ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz. Qed.
End Karatsuba.

Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Import B.
Require Import Crypto.Algebra.

(* TODO : move *)
Definition lift_tuple2 {R S T n} f (g:R->S)
  (X : forall a b, {prod | g prod = f a b}) :
  { op : tuple T n -> tuple T n -> R & forall a b, g (op a b) = f a b }.
Proof.
  exists (fun a b => proj1_sig (X a b)).
  exact (fun a b => proj2_sig (X a b)).
Defined.

Fixpoint chained_carries wt modulo div n t {T} (f:list (Z*Z)->T) :=
  match n with
  | O => @Positional.carry wt modulo div 0 t _ f
  | S n' => chained_carries wt modulo div n' t (fun r => @Positional.carry wt modulo div n r _ f)
  end.
Definition chained_carries_noncps wt m d n t :=
  chained_carries wt m d n t id.
Hint Opaque chained_carries_noncps : uncps.
Lemma chained_carries_id wt m d n : forall t {T} f,
  @chained_carries wt m d n t T f = f (chained_carries_noncps wt m d n t).
Proof.
  cbv [chained_carries_noncps]; induction n; [prove_id|].
  intros; simpl chained_carries.
  etransitivity; rewrite IHn; [|reflexivity].
  rewrite Positional.carry_id.
  reflexivity.
Qed. Hint Rewrite chained_carries_id : uncps.
Lemma eval_chained_carries_noncps :
  forall wt modulo div,
    (forall a b : Z, b <> 0 -> a = b * div a b + modulo a b) ->
    forall (n : nat) (p : list B.limb),
      (forall i, (i <= n)%nat -> wt (S i) / wt i <> 0) ->
      Associational.eval (chained_carries_noncps wt modulo div n p)
      =  Associational.eval p.
Proof.
  induction n; intros; cbv [chained_carries_noncps]; simpl chained_carries.
  { apply Positional.eval_carry_noncps; auto. }
  { rewrite chained_carries_id.
    etransitivity;[|apply IHn; solve[auto]].
    apply Positional.eval_carry_noncps; auto. }
Qed. Hint Rewrite eval_chained_carries_noncps : push_eval.
  

Ltac assert_preconditions :=
  repeat match goal with
         | |- context [Positional.from_associational ?wt ?n] =>
           unique assert (wt 0%nat = 1) by (cbv; congruence)
         | |- context [Positional.from_associational ?wt ?n] =>
           unique assert (forall i, wt i <> 0) by (intros; apply Z.pow_nonzero; try (cbv; congruence); solve [zero_bounds])
         | |- context [Positional.from_associational ?wt ?n] =>
           unique assert (n <> 0%nat) by (cbv; congruence)
         | |- context [Positional.carry ?wt ?i] =>
           unique assert (wt (S i) / wt i <> 0) by (cbv; congruence)
         end.

Ltac op_simplify := 
  cbv - [runtime_add runtime_mul Let_In];
  cbv [runtime_add runtime_mul];
  repeat progress rewrite ?Z.mul_1_l, ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_0_r.

Ltac prove_op sz x :=
  cbv [Tuple.tuple Tuple.tuple'] in *;
  repeat match goal with p : _ * Z |- _ => destruct p end;
  apply (lift_tuple2 (n := sz));
  eexists; cbv zeta beta; intros;
  match goal with |- Positional.eval ?wt _ = ?op (Positional.eval ?wt ?a) (Positional.eval ?wt ?b) =>
                  transitivity (Positional.eval wt (x wt a b))
  end; 
  [ apply f_equal; op_simplify; reflexivity
  | assert_preconditions;
    progress autorewrite with uncps push_id push_eval;
    reflexivity ]
.

Section Ops.
  Context
    (add_get_carry : Z -> Z -> Z * Z)
    (mul : Z -> Z -> Z * Z)
    (modulo : Z -> Z -> Z)
    (div : Z -> Z -> Z)
    (div_mod : forall a b : Z, b <> 0 ->
                               a = b * div a b + modulo a b).
  Local Infix "^" := tuple : type_scope.

  Let wt := fun i : nat => 2^(25 * (i / 2) + 26 * ((i + 1) / 2)).
  Let sz := 10%nat.
  Let sz2 := 19%nat.

  Definition addT :
    { add : (Z^sz -> Z^sz -> Z^sz)%type &
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 eval (add a b) = eval a  + eval b }.
  Proof.
    prove_op sz (
        fun wt a b =>
        Positional.to_associational (n := sz) wt a
          (fun r => Positional.to_associational (n := sz) wt b
          (fun r0 => Positional.from_associational wt sz (r ++ r0) id
      ))).
  Defined.
  

  Definition mulT :
    { mul : (Z^sz -> Z^sz -> Z^sz2)%type &
               forall a b : Z^sz,
                 let eval {n} := Positional.eval (n := n) wt in
                 eval (mul a b) = eval a  * eval b }.
  Proof.
    prove_op sz (
        fun wt a b =>
        Positional.to_associational (n := sz) wt a
          (fun r => Positional.to_associational (n := sz) wt b
          (fun r0 => Associational.mul r r0
          (fun r1 => Positional.from_associational wt sz2 r1
          (fun r2 => Positional.to_associational wt r2
          (fun r3 => chained_carries wt modulo div 19 r3 
          (fun r13 => Positional.from_associational wt sz2 r3 id
      ))))))).
  Time Defined. (* Finished transaction in 124.656 secs *) 

  (*
  Eval cbv [projT1 addT lift_tuple2 proj1_sig] in (projT1 addT).
  Eval cbv [projT1 mulT lift_tuple2 proj1_sig] in (projT1 mulT).
  *)
  
End Ops.