Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn. 
Require Import ZArith Nsatz Psatz Coq.omega.Omega.

Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.
Require Import Recdef.

    (* TODO: move *)
    Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
    Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.
    Create HintDb cancel_pair discriminated. Hint Rewrite @fst_pair @snd_pair : cancel_pair.

    Lemma push_id {A} (a:A) : id a = a. reflexivity. Qed.
    Create HintDb push_id discriminated. Hint Rewrite @push_id : push_id.

    Lemma update_nth_id {T} i (xs:list T) : ListUtil.update_nth i id xs = xs.
    Proof.
      revert xs; induction i; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_snd_combine {A B} (xs:list A) (ys:list B) : List.map snd (List.combine xs ys) = List.firstn (length xs) ys.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma nth_default_seq_inbouns d s n i (H:(i < n)%nat) :
      List.nth_default d (List.seq s n) i = (s+i)%nat.
    Proof.
      progress cbv [List.nth_default].
      rewrite ListUtil.nth_error_seq.
      break_innermost_match; solve [ trivial | omega ].
    Qed.
    
    Lemma mod_add_mul_full a b c k m : m <> 0 -> c mod m = k mod m -> 
                                       (a + b * c) mod m = (a + b * k) mod m.
    Proof.
      intros; rewrite Z.add_mod, Z.mul_mod by auto.
      match goal with H : _ mod _ = _ mod _ |- _ => rewrite H end.
      rewrite <-Z.mul_mod, <-Z.add_mod by auto; reflexivity.
    Qed.
    
    Fixpoint find_remove_first' {A} (f : A->bool) (acc ls:list A) : (option A) * list A :=
      (match ls with
       | nil => (None, acc)
       | x :: tl =>
         if f x then (Some x, acc ++ tl) else find_remove_first' f (acc ++ x::nil) tl
       end)%list.
    
    Definition find_remove_first {A} (f:A -> bool) ls : (option A) * list A :=
      find_remove_first' f nil ls.

    Lemma find_remove_first_cons {A} f (x:A) tl : f x = true ->
                                                  find_remove_first f (x::tl) = (Some x, tl).
    Proof. intros; cbv [find_remove_first]. simpl find_remove_first'.
           break_if; try congruence; reflexivity. Qed.

    Lemma find_remove_first'_None {A} (f:A->bool) ls : forall acc,
        fst (find_remove_first' f acc ls) = None ->
        forall x, List.In x ls -> f x = false.
    Proof.
      induction ls; simpl find_remove_first'; simpl List.In; [tauto|].
      break_if; intros; [discriminate|].
      destruct H0; subst; auto; eapply IHls; eauto.
    Qed.
    Lemma find_remove_first_None {A} (f:A->bool) ls :
      fst (find_remove_first f ls) = None ->
      forall x, List.In x ls -> f x = false.
    Proof. cbv [find_remove_first]. apply find_remove_first'_None. Qed.

    Lemma length_find_remove_first' {A} (f:A -> bool) ls : forall acc,
        length (snd (@find_remove_first' _ f acc ls)) =
        match (fst (@find_remove_first' _ f acc ls)) with
        | None => length (acc ++ ls)
        | Some _ => (length (acc ++ ls) - 1)%nat
        end.
    Proof.
      induction ls; intros; simpl find_remove_first';
        repeat match goal with
               | |- _ => break_match; try discriminate
               | |- _ => progress (rewrite ?@fst_pair, ?@snd_pair in * )
               | |- _ => progress distr_length
               | |- _ => rewrite IHls
               end.
    Qed.

    Lemma length_find_remove_first {A} (f:A -> bool) ls :
      length (snd (find_remove_first f ls)) =
      match (fst (find_remove_first f ls)) with
      | None => length ls
      | Some _ => (length ls - 1)%nat
      end.
    Proof. cbv [find_remove_first]; rewrite length_find_remove_first'; distr_length. Qed. Hint Rewrite @length_find_remove_first : distr_length.

    Lemma to_nat_neg : forall x, x < 0 -> Z.to_nat x = 0%nat.
    Proof. destruct x; try reflexivity; intros. pose proof (Pos2Z.is_pos p). omega. Qed.

    Fixpoint map_cps {A B} (g : A->B) ls
             {T} (f:list B->T):=
      match ls with
      | nil => f nil
      | a :: t => map_cps g t (fun r => f (g a :: r))
      end.
    Lemma map_cps_correct {A B} g ls: forall {T} f,
        @map_cps A B g ls T f = f (map g ls).
    Proof. induction ls; simpl; intros; rewrite ?IHls; reflexivity. Qed.

    Fixpoint flat_map_cps {A B} (g:A->forall {T}, (list B->T)->T) (ls : list A) {T} (f:list B->T)  :=
      match ls with
      | nil => f nil
      | (x::tl)%list => g x (fun r => flat_map_cps g tl (fun rr => f (r ++ rr))%list)
      end.
    Lemma flat_map_cps_correct {A B} g ls: forall {T} (f:list B->T) g',
        (forall x T h, @g x T h = h (g' x)) ->
        @flat_map_cps A B g ls T f = f (List.flat_map g' ls).
    Proof.
      induction ls; intros; [reflexivity|].
      simpl flat_map_cps. simpl flat_map.
      rewrite H; erewrite IHls by eassumption.
      reflexivity.
    Qed.
    
    Fixpoint from_list_default'_cps {A} (d y:A) n xs:
      forall {T}, (Tuple.tuple' A n -> T) -> T:=
      match n as n0 return (forall {T}, (Tuple.tuple' A n0 ->T) ->T) with
      | O => fun T f => f y
      | S n' => fun T f =>
                  match xs with
                  | nil => from_list_default'_cps d d n' nil (fun r => f (r, y))
                  | x :: xs' => from_list_default'_cps d x n' xs' (fun r => f (r, y))
                  end
      end.
    Lemma from_list_default'_cps_correct {A} n : forall d y l {T} f,
        @from_list_default'_cps A d y n l T f = f (Tuple.from_list_default' d y n l).
    Proof.
      induction n; intros; simpl; [reflexivity|].
      break_match; subst; apply IHn.
    Qed.
    Definition from_list_default_cps {A} (d:A) n (xs:list A) :
      forall {T}, (Tuple.tuple A n -> T) -> T:=
      match n as n0 return (forall {T}, (Tuple.tuple A n0 ->T) ->T) with
      | O => fun T f => f tt
      | S n' => fun T f =>
                  match xs with
                  | nil => from_list_default'_cps d d n' nil f
                  | x :: xs' => from_list_default'_cps d x n' xs' f
                  end
      end.
    Lemma from_list_default_cps_correct {A} n : forall d l {T} f,
        @from_list_default_cps A d n l T f = f (Tuple.from_list_default d n l).
    Proof.
      destruct n; intros; simpl; [reflexivity|].
      break_match; auto using from_list_default'_cps_correct.
    Qed.
    Fixpoint to_list'_cps {A} n
             {T} (f:list A -> T) : Tuple.tuple' A n -> T :=
      match n as n0 return (Tuple.tuple' A n0 -> T) with
      | O => fun x => f [x]
      | S n' => fun (xs: Tuple.tuple' A (S n')) =>
                  let (xs', x) := xs in
                  to_list'_cps n' (fun r => f (x::r)) xs'
      end.
    Lemma to_list'_cps_correct {A} n: forall t {T} f,
        @to_list'_cps A n T f t = f (Tuple.to_list' n t).
    Proof.
      induction n; simpl; intros; [reflexivity|].
      destruct_head prod. apply IHn.
    Qed.
    Definition to_list_cps' {A} n {T} (f:list A->T)
      : Tuple.tuple A n -> T :=
      match n as n0 return (Tuple.tuple A n0 ->T) with
      | O => fun _ => f nil
      | S n' => to_list'_cps n' f
      end.
    Definition to_list_cps {A} n t {T} f :=
      @to_list_cps' A n T f t.
    Lemma to_list_cps_correct {A} n t {T} f :
      @to_list_cps A n t T f = f (Tuple.to_list n t).
    Proof. cbv [to_list_cps to_list_cps' Tuple.to_list]; break_match; auto using to_list'_cps_correct. Qed.
    
    Definition on_tuple_cps {A B} (d:B) (g:list A ->forall {T},(list B->T)->T) {n m}
               (xs : Tuple.tuple A n) {T} (f:tuple B m ->T) :=
      to_list_cps n xs (fun r => g r (fun rr => from_list_default_cps d m rr f)).
    Lemma on_tuple_cps_correct {A B} d g {n m} xs {T} f g' H
          (Hg : forall x {T} h, @g x T h = h (g' x)) : 
      @on_tuple_cps A B d g n m xs T f = f (@Tuple.on_tuple A B g' n m H xs).
    Proof.
      cbv [on_tuple_cps Tuple.on_tuple].
      rewrite to_list_cps_correct, Hg, from_list_default_cps_correct.
      rewrite (Tuple.from_list_default_eq _ _ _ (H _ (Tuple.length_to_list _))).
      reflexivity.
    Qed.

    Fixpoint update_nth_cps {A} n (g:A->A) xs {T} (f:list A->T) :=
      match n with
      | O => 
        match xs with
        | [] => f []
        | x' :: xs' => f (g x' :: xs')
        end
      | S n' =>
        match xs with
        | [] => f []
        | x' :: xs' => update_nth_cps n' g xs' (fun r => f (x' :: r))
        end
      end.
    Lemma update_nth_cps_correct {A} n g: forall xs T f,
        @update_nth_cps A n g xs T f = f (update_nth n g xs).
    Proof. induction n; intros; simpl; break_match; try apply IHn; reflexivity. Qed.

    Fixpoint combine_cps {A B} (la :list A) (lb : list B)
             {T} (f:list (A*B)->T) :=
      match la with
      | nil => f nil
      | a :: tla =>
        match lb with
        | nil => f nil
        | b :: tlb => combine_cps tla tlb (fun lab => f ((a,b)::lab))
        end
      end.
    Lemma combine_cps_correct {A B} la: forall lb {T} f,
        @combine_cps A B la lb T f = f (combine la lb).
    Proof.
      induction la; simpl combine_cps; simpl combine; intros;
        try break_match; try apply IHla; reflexivity.
    Qed.


    
    Definition fold_right_no_starter {A} (f:A->A->A) ls : option A :=
      match ls with
      | nil => None
      | cons x tl => Some (List.fold_right f x tl)
      end.
    Lemma fold_right_min ls x :
      x = List.fold_right Z.min x ls
      \/ List.In (List.fold_right Z.min x ls) ls.
    Proof.
      induction ls; intros; simpl in *; try tauto.
      match goal with |- context [Z.min ?x ?y] =>
                      destruct (Z.min_spec x y) as [[? Hmin]|[? Hmin]]
      end; rewrite Hmin; tauto.
    Qed.
    Lemma fold_right_no_starter_min ls : forall x,
        fold_right_no_starter Z.min ls = Some x ->
        List.In x ls.
    Proof.
      cbv [fold_right_no_starter]; intros; destruct ls; try discriminate.
      inversion H; subst; clear H.
      destruct (fold_right_min ls z); subst; simpl List.In; tauto.
    Qed.
    Fixpoint fold_right_cps {A B} (g:B->A->A) (a0:A) (l:list B) {T} (f:A->T) :=
      match l with
      | nil => f a0
      | cons a tl => fold_right_cps g a0 tl (fun r => f (g a r))
      end.
    Lemma fold_right_cps_correct {A B} g a0 l: forall {T} f,
        @fold_right_cps A B g a0 l T f = f (List.fold_right g a0 l).
    Proof. induction l; intros; simpl; rewrite ?IHl; auto. Qed.
    Definition fold_right_no_starter_cps {A} g ls {T} (f:option A->T) :=
      match ls with
      | nil => f None
      | cons x tl => f (Some (List.fold_right g x tl))
      end.
    Lemma fold_right_no_starter_cps_correct {A} g ls {T} f :
      @fold_right_no_starter_cps A g ls T f = f (fold_right_no_starter g ls).
    Proof.
      cbv [fold_right_no_starter_cps fold_right_no_starter]; break_match; reflexivity.
    Qed.        


Ltac find_continuation :=
  let a := fresh "x" in
  let Heqa := fresh "Heqx" in
  match goal with
    |- _ ?x = _ ?y =>
    remember (x-y) as a eqn:Heqa;
    replace x with (y+a) by (subst a; ring);
    ring_simplify in Heqa; subst a
  end;
  match goal with |- ?lhs = ?g ?y =>
                  match eval pattern y in lhs with
                  ?f _ =>
                  change (f y = g y)
                  end
  end;
  apply f_equal; reflexivity.

Ltac not_syntactically_equal a b :=
    match a with | b => fail 1 | _ => idtac end.

(* rewrites with a lemma of the form
                [forall x {T} f, <op> x T f = f (<op> x _ id)]
       only if the argument f is not syntactically equal to [id]
 *)
Ltac smart_rewrite1 lem :=
  match type of lem with
    forall _ _ f, ?op _ _ f = f (?op _ _ id) =>
    match goal with
      |- context [op _ _ ?f] =>
      match type of f with ?A -> _ =>
                           let t := (eval cbv [id] in f) in
                           let u := (eval cbv [id] in (@id A)) in
                           not_syntactically_equal t u;
                           rewrite (lem _ _ f)
      end
    end
  end.
Ltac smart_rewrite2 lem :=
  match type of lem with
    forall _ _ _ f, ?op _ _ _ f = f (?op _ _ _ id) =>
    match goal with
      |- context [op _ _ _ ?f] =>
      match type of f with ?A -> _ =>
                           let t := (eval cbv [id] in f) in
                           let u := (eval cbv [id] in (@id A)) in
                           not_syntactically_equal t u;
                           rewrite (lem _ _ _ f)
      end
    end
  end.
Ltac smart_rewrite3 lem :=
  match type of lem with
    forall _ _ _ _ f, ?op _ _ _ _ f = f (?op _ _ _ _ id) =>
    match goal with
      |- context [op _ _ _ _ ?f] =>
      match type of f with ?A -> _ =>
                           let t := (eval cbv [id] in f) in
                           let u := (eval cbv [id] in (@id A)) in
                           not_syntactically_equal t u;
                           rewrite (lem _ _ _ _ f)
      end
    end
  end.
Ltac smart_rewrite4 lem :=
  match type of lem with
    forall _ _ _ _ _ f, ?op _ _ _ _ _ f = f (?op _ _ _ _ _ id) =>
    match goal with
      |- context [op _ _ _ _ _ ?f] =>
      match type of f with ?A -> _ =>
                           let t := (eval cbv [id] in f) in
                           let u := (eval cbv [id] in (@id A)) in
                           not_syntactically_equal t u;
                           rewrite (lem _ _ _ _ _ f)
      end
    end
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
    Create HintDb push_eval discriminated. Hint Rewrite eval_nil eval_cons eval_app : push_eval.

    Definition multerm (t t' : limb) : limb :=
      (fst t * fst t', (snd t * snd t')%RT).
    Definition mul (p q:list limb) {T} (f : list limb->T) :=
      flat_map_cps (fun t => @map_cps _ _ (multerm t) q) p f.
    Lemma eval_map_mul (a:limb) (q:list limb) : eval (List.map (multerm a) q) = fst a * snd a * eval q.
    Proof.
      induction q; cbv [multerm]; simpl List.map;
        autorewrite with push_eval cancel_pair; nsatz.
    Qed. Hint Rewrite eval_map_mul : push_eval.
    Lemma mul_id p q: forall {T} f,
      @mul p q T f = f (mul p q id).
    Proof.
      induction p;intros; autorewrite with push_eval cancel_pair; [reflexivity|].
      cbv [mul] in *; simpl. rewrite !map_cps_correct, IHp.
      erewrite !flat_map_cps_correct by (intros; rewrite map_cps_correct; reflexivity).
      reflexivity.
    Qed.
    Lemma eval_mul_id p q:
      eval (mul p q id) = eval p * eval q.
    Proof.
      induction p; intros; autorewrite with push_eval cancel_pair; [reflexivity|].
      pose proof (@mul_id p q) as Hmul_id.
      cbv [mul] in *. simpl.
      rewrite map_cps_correct, Hmul_id.
      cbv [id] in *; autorewrite with push_eval.
      rewrite IHp. nsatz.
    Qed. Hint Rewrite eval_mul_id : push_eval.

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

    Lemma split_id s p: forall {T} f,
        @split s p T f = f (split s p id).
    Proof.
      induction p; intros;
        repeat match goal with
               | _ => progress simpl split
               | |- split _ _ ?f = _ (split _ _ ?g) =>
                 rewrite (IHp _ f); rewrite (IHp _ g)
               | _ => break_if
               | _ => reflexivity
               end.
    Qed.
    Lemma eval_split_id s p (s_nonzero:s<>0):
      eval (fst (split s p id)) + s*eval (snd (split s p id))  = eval p.
    Proof.
      induction p; intros;
        repeat match goal with
               | _ => progress simpl split
               | _ => progress (autorewrite with push_eval push_id cancel_pair)
               | _ => progress (rewrite split_id; autorewrite with push_id)
               | _ => break_if 
               | H:_ |- _ =>
                 unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
               | _ => nsatz
               end.
    Qed. Hint Rewrite @eval_split_id : push_eval.

    Definition reduce (s:Z) (c:list limb) (p:list limb)
               {T} (f : list limb->T) :=
      split s p (fun ab => mul c (snd ab) (fun rr =>f (fst ab ++ rr))).

    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.

    Lemma reduce_id s c p {T} f:
      @reduce s c p T f = f (reduce s c p id).
    Proof.
      repeat match goal with
             | _ => progress intros
             | _ => progress cbv [reduce]
             | _ => progress autorewrite with push_eval cancel_pair 
             | _ => smart_rewrite2 split_id 
             | _ => smart_rewrite2 mul_id
             | _ => reflexivity
             | _ => nsatz
             end.
    Qed.
    Lemma eval_reduce_id s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0):
      eval (reduce s c p id) mod (s - eval c) = eval p mod (s - eval c).
    Proof.
      cbv [reduce id].
      repeat match goal with
             | _ => progress intros
             | _ => progress autorewrite with push_eval cancel_pair
             | _ => smart_rewrite2 split_id; auto 
             | _ => smart_rewrite2 mul_id; auto
             | _ => rewrite <-reduction_rule by auto
             | _ => reflexivity
             | _ => assumption 
             | _ => nsatz
             end.
    Qed. Hint Rewrite eval_reduce_id : push_eval.

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

      Lemma carryterm_id w fw t {T} f :
        @carryterm w fw t T f
        = f (@carryterm w fw t _ id).
      Proof. cbv [carryterm Let_In]; break_if; reflexivity. Qed.
      Lemma eval_carryterm_id w fw (t:limb) (fw_nonzero:fw<>0):
        eval (@carryterm w fw t _ id) = eval [t].
      Proof.
        cbv [carryterm Let_In id].
        break_if; subst; [|reflexivity].
        autorewrite with push_eval cancel_pair.
        specialize (div_mod (snd t) fw fw_nonzero).
        nsatz.
      Qed. Hint Rewrite eval_carryterm_id : push_eval.
      
      Lemma carry_id w fw p {T} f:
        @carry w fw p T f = f (carry w fw p id).
      Proof.
        cbv [carry];  erewrite !flat_map_cps_correct
          by (intros; rewrite carryterm_id; reflexivity).
        reflexivity.
      Qed.
      Lemma eval_carry_id w fw p (fw_nonzero:fw<>0):
        eval (carry w fw p id) = eval p.
      Proof.
        cbv [carry]; induction p; intros; [reflexivity|].
        repeat match goal with
               | _ => progress simpl flat_map_cps
               | _ => progress (autorewrite with push_eval push_id cancel_pair in * ); auto
               | _ => erewrite !@flat_map_cps_correct in *
                   by (intros; rewrite carryterm_id; reflexivity)
               | _ => smart_rewrite3 carryterm_id
               | _ => nsatz
               end.
      Qed. Hint Rewrite eval_carry_id : push_eval.
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

      Lemma multerm_correct t t' : forall {T} (f:list limb->T),
       sat_multerm t t' f = f ([(fst t*fst t', fst (mul (snd t) (snd t'))); (fst t*fst t'*word_max, snd (mul (snd t) (snd t')))]).
      Proof. reflexivity. Qed.
      Lemma eval_map_sat_mul t q :
        flat_map_cps (sat_multerm t) q eval = fst t * snd t * eval q.
      Proof.
        induction q; intros; simpl flat_map_cps; [autorewrite with push_eval; nsatz|].
        rewrite multerm_correct.
        erewrite !@flat_map_cps_correct in * by apply multerm_correct.
        autorewrite with push_eval cancel_pair.
        rewrite IHq.
        repeat match goal with |- context [mul ?x ?y] =>
                               unique pose proof (mul_correct x y) end.
        nsatz.
      Qed. Hint Rewrite eval_map_sat_mul : push_eval. 
      Lemma eval_sat_mul p q : sat_mul p q eval = eval p * eval q.
      Proof.
        cbv [sat_mul];  erewrite !@flat_map_cps_correct
          by (intros; try apply flat_map_cps_correct; apply multerm_correct).
        induction p; intros; [reflexivity|].
        simpl flat_map; autorewrite with push_eval cancel_pair.
        rewrite IHp; erewrite <-flat_map_cps_correct by apply multerm_correct.
        rewrite eval_map_sat_mul; nsatz.
      Qed. Hint Rewrite eval_sat_mul : push_eval.

      Fixpoint find_remove_first'_cps {A} (g:A->forall {T}, (bool->T)->T) (acc ls:list A)
               {T} (f:option A * list A ->T) :=
        match ls with
        | [] => f (None, acc)
        | x :: tl =>
          g x (fun r =>
          if r
          then f (Some x, acc ++ tl)
          else
            find_remove_first'_cps g (acc ++ [x]) tl f)
        end.
      Definition find_remove_first_cps {A} g ls {T} f :=
        @find_remove_first'_cps A g nil ls T f.

      Lemma find_remove_first'_cps_correct
            {A} (g:A->forall {T}, (bool->T) -> T) ls {T} f
            (H: forall x {B} h, @g x B h = h (g x id)):
        forall acc,
          @find_remove_first'_cps A g acc ls T f =
          f (find_remove_first' (fun x => g x id) acc ls).
      Proof.
        induction ls; intros; simpl; try (rewrite H, IHls; break_if); reflexivity.
      Qed.
      Lemma find_remove_first_cps_correct
            {A} (g:A->forall {T}, (bool->T) -> T) ls {T} f
            (H: forall x {B} h, @g x B h = h (g x id)):
          @find_remove_first_cps A g ls T f =
          f (find_remove_first (fun x => g x id) ls).
      Proof. apply find_remove_first'_cps_correct; auto. Qed.

      Definition has_same_wt (cx a:limb) {T} (f:bool->T) :=
        if dec (fst cx = fst a) then f true else f false.
      Lemma has_same_wt_correct cx a {T} f:
        @has_same_wt cx a T f = f (if dec (fst cx = fst a) then true else false).
      Proof. cbv [has_same_wt]; break_if; reflexivity. Qed.

      Lemma find_remove_first'_cps_same_wt cx cx' p: forall acc,
        find_remove_first'_cps (has_same_wt cx) acc p fst = Some cx' ->
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + find_remove_first'_cps (has_same_wt cx) acc p (fun r =>eval (snd r)) = fst cx * snd cx + eval acc + eval p.
      Proof.
        cbv [has_same_wt];
        induction p; intros; simpl find_remove_first'_cps in *;
            repeat match goal with
                   | |- _ => progress (autorewrite with push_eval cancel_pair in * )
                   | H : Some _ = Some _ |- _ => progress (inversion H; subst)
                   | |- _ => erewrite (proj2 (IHp _ _)); erewrite (proj1 (IHp _ _))
                   | |- _ => break_if
                   | |- _ => split; subst 
                   | |- _ => discriminate
                   | |- _ => nsatz
                   end.
        Unshelve.
        assumption.
        2:eassumption.
      Qed.

      Lemma find_remove_first_cps_same_wt cx cx' p
        (H : find_remove_first_cps (has_same_wt cx) p fst = Some cx') :
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + find_remove_first_cps (has_same_wt cx) p (fun r => eval (snd r)) = fst cx * snd cx + eval p.
      Proof.
        cbv [find_remove_first_cps]; intros.
        erewrite (proj1 (find_remove_first'_cps_same_wt _ _ _ _ H)) by eauto.
        erewrite (proj2 (find_remove_first'_cps_same_wt _ _ _ _ H)) by eauto.
        autorewrite with push_eval; split; try ring.
      Qed.

      Fixpoint compact_no_carry' (acc p:list limb) {T} (f:list limb->T) :=
        match p with
        | nil => f acc
        | (cx::tl)%list =>
          find_remove_first_cps
            (has_same_wt cx) acc
            (fun r =>
               match (fst r) with
               | None => compact_no_carry' (cx::acc)%list tl f
               | Some l => compact_no_carry' ((fst cx, (snd cx + snd l)%RT)::snd r)%list tl f
               end)
        end.
      Definition compact_no_carry p {T} f := @compact_no_carry' nil p T f.

      Lemma compact_no_carry'_id p: forall acc {T} (f:list limb -> T),
        @compact_no_carry' acc p T f = f (compact_no_carry' acc p id).
      Proof.
        induction p; simpl compact_no_carry';
          repeat match goal with
                 | _ => progress intros
                 | _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 | _ => break_match; subst
                 | _ => reflexivity
                 | _ => solve [auto]
                 end.
      Qed.
      
      Lemma eval_compact_no_carry'_id p: forall acc,
        eval (compact_no_carry' acc p id) = eval acc + eval p.
      Proof.
        induction p; simpl;
          repeat match goal with
                 | |- _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 | |- _ => break_match
                 | |- _ => progress (intros;subst)
                 | |- _ => progress autorewrite with push_eval push_id cancel_pair in *
                 | |- _ => rewrite IHp
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   rewrite <-find_remove_first_cps_correct in H by apply has_same_wt_correct;
                     destruct (find_remove_first_cps_same_wt _ _ _ H); clear H
                 | |- _ => nsatz
                 end.
      Qed.
      Lemma length_compact_no_carry' p: forall acc,
          (compact_no_carry' acc p (@length _) <= length p + length acc)%nat.
      Proof.
        induction p; simpl;
          repeat match goal with
                 | |- _ => progress intros
                 | |- _ => progress distr_length
                 | |- _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 | |- _ => rewrite IHp
                 | |- _ => break_match
                 end.
      Qed.
      Lemma compact_no_carry_id p {T} f:
         @compact_no_carry p T f = f (compact_no_carry p id).
      Proof. cbv [compact_no_carry]; apply compact_no_carry'_id. Qed.
      Lemma eval_compact_no_carry_id p:
         eval (compact_no_carry p id) = eval p.
      Proof. cbv [compact_no_carry]; apply eval_compact_no_carry'_id. Qed.
      Hint Rewrite eval_compact_no_carry_id : push_eval.
      Lemma length_compact_no_carry p: (compact_no_carry p (@length _) <= length p)%nat. Proof. cbv [compact_no_carry]. rewrite length_compact_no_carry'. distr_length. Qed. Hint Rewrite length_compact_no_carry : distr_length.

      (* n is fuel, should be length of inp *)
      Fixpoint compact_cols_loop1 (carries out inp : list limb) (n:nat)
               {T} (f:list limb * list limb ->T):=
        match n with
        | O => f (carries, out)
        | S n' => 
          match inp with
          | nil => f (carries, out)
          | cons cx tl =>
            find_remove_first_cps
              (has_same_wt cx) tl
              (fun r =>
                 let found_ls := r in
                 match (fst found_ls) with
                 | None => compact_cols_loop1 carries (cx::out) tl n' f
                 | Some cx' =>
                   dlet sum_carry := add (snd cx) (snd cx') in
                   compact_no_carry
                     ((fst cx * word_max, runtime_snd sum_carry)::carries)
                              (fun rr =>
                                 compact_cols_loop1 rr out ((fst cx, runtime_fst sum_carry):: snd found_ls) n' f)
                 end)
          end
        end.

      Lemma compact_cols_loop1_id n:
        forall p out carries {T} (f:list limb * list limb ->T),
          compact_cols_loop1 carries out p n f
          = f (compact_cols_loop1 carries out p n id).
      Proof.
        induction n;
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In] 
                 | _ => progress simpl compact_cols_loop1
                 | _ => (rewrite @find_remove_first_cps_correct in *
                          by apply has_same_wt_correct )
                 | _ => smart_rewrite1 compact_no_carry_id
                 | _ => break_match
                 | _ => reflexivity
                 | _ => solve [auto] 
                 end.
      Qed.
        
      Lemma eval_compact_cols_loop1_id n :
        forall p (H0:length p = n) out carries,
          eval (snd (compact_cols_loop1 carries out p n id))
          + eval (fst (compact_cols_loop1 carries out p n id))
          = eval p + eval out + eval carries.
      Proof.
        induction n; destruct p;
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In runtime_fst runtime_snd] 
                 | _ => progress simpl compact_cols_loop1
                 | _ => progress subst 
                 | _ => progress (autorewrite with push_id
                        push_eval cancel_pair distr_length in * )
                 | _ => (rewrite @find_remove_first_cps_correct in *
                               by apply has_same_wt_correct )
                 | _ => smart_rewrite1 compact_no_carry_id
                 | _ => break_match
                 | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                   unique assert (length p > 0)%nat
                     by (destruct p; (discriminate || (simpl; omega)))
                 | _ => rewrite IHn by (distr_length; break_match; distr_length; discriminate)
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   rewrite <-find_remove_first_cps_correct in H
                     by apply has_same_wt_correct;
                     destruct (find_remove_first_cps_same_wt _ _ _ H);
                     clear H
                 | |- context[add ?x ?y] =>
                     specialize (add_correct x y)
                 | _ => discriminate
                 | _ => reflexivity
                 | _ => nsatz 
                 | _ => solve [auto] 
                 end.
      Qed. Hint Rewrite eval_compact_cols_loop1_id : push_eval.

      (* n is fuel, should be [length carries + length inp] *)
      Fixpoint compact_cols_loop2 (carries out inp :list limb) (n:nat)
               {T} (f:list limb->T) :=
        match n with
        | O => f (out++carries++inp)
        | S n' => 
          fold_right_no_starter_cps
            Z.min (List.map fst (inp ++ carries))
            (fun r =>
               match r with
               | None => f (out++carries++inp)
               | Some min =>
                 find_remove_first_cps
                   (has_same_wt (min, 0)) inp
                   (fun rr =>
                      let inp_found_ls := rr in
                      find_remove_first_cps
                        (has_same_wt (min, 0)) carries
                        (fun rrr =>
                           let car_found_ls := rrr in
                           match fst inp_found_ls, fst car_found_ls with
                           | None, None => f out (* never happens *)
                           | Some cx, None =>
                             compact_cols_loop2 carries (cx :: out) (snd inp_found_ls) n' f
                           | None, Some cx =>
                             compact_cols_loop2 (snd car_found_ls) (cx :: out) inp n' f
                           | Some icx, Some ccx =>
                             dlet sum_carry := add (snd icx) (snd ccx) in
                                 compact_no_carry 
                                   ((min * word_max, runtime_snd sum_carry)::(snd car_found_ls))
                                   (fun rrrr =>
                                      compact_cols_loop2
                                        rrrr
                                        ((min, runtime_fst sum_carry) :: out)
                                        (snd inp_found_ls) n' f)
                           end))
               end)
        end.

      Lemma compact_cols_loop2_id n:
        forall out p carries  {T} (f:list limb->T),
        compact_cols_loop2 carries out p n f
        = f (compact_cols_loop2 carries out p n id).
      Proof.
        induction n;
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In] 
                 | _ => progress simpl compact_cols_loop2
                 | _ => rewrite fold_right_no_starter_cps_correct
                 | _ => (rewrite @find_remove_first_cps_correct in *
                          by apply has_same_wt_correct )
                 | _ => smart_rewrite1 compact_no_carry_id
                 | _ => break_match
                 | _ => reflexivity
                 | _ => solve [auto] 
                 end.
      Qed.

      Lemma eval_compact_cols_loop2_id n:
        forall out p carries,
        eval (compact_cols_loop2 carries out p n id)
        = eval p + eval carries + eval out.
      Proof.
        induction n; 
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In runtime_fst runtime_snd] 
                 | _ => progress simpl compact_cols_loop2
                 | _ => progress subst 
                 | _ => progress (autorewrite with push_id
                        push_eval cancel_pair distr_length in * )
                 | _ => rewrite fold_right_no_starter_cps_correct
                 | _ => (rewrite @find_remove_first_cps_correct in *
                               by apply has_same_wt_correct )
                 | _ => smart_rewrite1 compact_no_carry_id
                 | _ => break_match
                 | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                   unique assert (length p > 0)%nat
                     by (destruct p; (discriminate || (simpl; omega)))
                 | _ => rewrite IHn by (distr_length; break_match; distr_length; discriminate)
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   rewrite <-find_remove_first_cps_correct in H
                     by apply has_same_wt_correct;
                     destruct (find_remove_first_cps_same_wt _ _ _ H);
                     clear H
                 | |- context[add ?x ?y] =>
                     specialize (add_correct x y)
                 | _ => discriminate
                 | _ => reflexivity
                 | _ => nsatz 
                 | _ => solve [auto] 
                 end.
        (* TODO : logic here is kinda ugly-- basic idea is "if you found a minimum weight in (p++carries), an element with that weight must be in either carries or p *)
        exfalso.
        repeat match goal with
                 | H : fold_right_no_starter Z.min _ = Some _ |- _ =>
                   apply fold_right_no_starter_min in H
                 | H : fst (find_remove_first _ _) = None |- _ =>
                   apply find_remove_first_None in H
                 | H : List.In _ (List.map _ _) |- _ =>
                   apply List.in_map_iff in H;
                     destruct H as [? [? ?]]; subst
                 | H : List.In _ (_ ++ _) |- _ => apply List.in_app_or in H; destruct H
                 | H1 : fst (find_remove_first _ ?p) = None,
                        H2 : List.In ?x ?p
                   |- _ =>
                   apply (find_remove_first_None _ _ H1) in H2;
                     cbv [has_same_wt id] in H2; simpl fst in H2;
                       break_if; congruence
                 | H : _ \/ _ |- _ => destruct H
               end.
      Qed. Hint Rewrite eval_compact_cols_loop2_id : push_eval.

      Definition compact_cols (p:list limb) {T} (f:list limb->T) :=
        compact_cols_loop1
          nil nil p (length p)
          (fun r => compact_cols_loop2
                      (fst r) nil (snd r) (length (fst r ++ snd r)) f).

      Lemma compact_cols_id (p:list limb) {T} (f:list limb->T):
        compact_cols p f = f (compact_cols p id).
      Proof.
        cbv [compact_cols];
          do 2 smart_rewrite4 compact_cols_loop1_id;
          smart_rewrite4 compact_cols_loop2_id; reflexivity.
      Qed.
      Lemma eval_compact_cols_id (p:list limb):
        eval (compact_cols p id) = eval p.
      Proof.
        cbv [compact_cols];
          repeat match goal with
                 | |- _ => progress intros
                 | |- _ => progress autorewrite with push_eval cancel_pair
                 | |- _ => progress distr_length
                 | |- _ => smart_rewrite4 compact_cols_loop1_id
                 | |- _ => smart_rewrite4 eval_compact_cols_loop2_id
                 | |- _ => reflexivity
                 end.
      Qed.
           
    End Saturated.
  End Associational.

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
      
      Definition eval {n} x := @to_associational n x _ Associational.eval.
      Lemma to_associational_id {n} x {T} f:
        @to_associational n x T f = f (to_associational x id).
      Proof.
        cbv [to_associational eval].
        rewrite !map_cps_correct, !to_list_cps_correct,
        !combine_cps_correct. reflexivity.
      Qed.
      Lemma eval_to_associational_id {n} x :
        Associational.eval (@to_associational n x _ id) = eval x.
      Proof.
        cbv [to_associational eval].
        rewrite !map_cps_correct, !to_list_cps_correct,
        !combine_cps_correct. reflexivity.
      Qed.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof. cbv [eval Associational.eval to_associational zeros].
             rewrite map_cps_correct, to_list_cps_correct, combine_cps_correct.
             rewrite Tuple.to_list_from_list.
             generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz. Qed.


      Definition add_to_nth {n} i x t {T} (f:tuple Z n->T) :=
        @on_tuple_cps _ _ 0 (update_nth_cps i (runtime_add x)) n n t _ f.
      Lemma eval_add_to_nth_id {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n):
        eval (@add_to_nth n i x xs _ id) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational add_to_nth runtime_add id].
        rewrite !map_cps_correct, !to_list_cps_correct, !combine_cps_correct.
        erewrite on_tuple_cps_correct by (intros; rewrite update_nth_cps_correct;
                                          apply f_equal; reflexivity).
        cbv [Tuple.on_tuple].
        rewrite !Tuple.to_list_from_list.
        rewrite ListUtil.combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)); cbv [ListUtil.splice_nth id];
          repeat match goal with
                 | _ => progress (apply Zminus_eq; ring_simplify)
                 | _ => progress autorewrite with push_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia.
        Unshelve.
        intros; subst. apply length_update_nth.
      Qed. Hint Rewrite @eval_add_to_nth_id : push_eval.
      Lemma add_to_nth_id {n} i x xs {T} f:
        @add_to_nth n i x xs T f = f (add_to_nth i x xs id).
      Proof.
        cbv [add_to_nth].
        erewrite !on_tuple_cps_correct by (intros; rewrite update_nth_cps_correct;
                                          apply f_equal; reflexivity).
        reflexivity.
        Unshelve.
        intros; subst. apply length_update_nth.
      Qed.
      (* TODO : since this form of the eval lemmas is better expressed as the two lemmas above, rewrite previous stuff. *)
      Lemma eval_add_to_nth {n} (i:nat) (x:Z) (H:(i<n)%nat) (xs:tuple Z n)
            {T} f g (Hfg:forall x, f x = g (eval x)):
        @add_to_nth n i x xs T f = g (weight i * x + eval xs).
      Proof.
        rewrite add_to_nth_id.
        rewrite Hfg. apply f_equal.
        auto using eval_add_to_nth_id.
      Qed. Hint Rewrite @eval_add_to_nth eval_zeros : push_eval.

      Fixpoint place (t:limb) (i:nat) {T} (f:nat * Z->T) :=
        if dec (fst t mod weight i = 0)
        then f (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place t i' f | O => f (O, fst t * snd t)%RT end.
      Lemma place_in_range (t:limb) (n:nat) : (fst (place t n id) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place t i : weight (fst (place t i id)) * snd (place t i id) = fst t * snd t.
      Proof. induction i; cbv [id]; simpl place; break_match; autorewrite with cancel_pair;
               try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto. Qed.
      Lemma place_id t i {T} f :
        @place t i T f = f (place t i id).
      Proof. cbv [id]; induction i; simpl; break_if; auto. Qed.

      Definition from_associational n (p:list limb) {T} (f:tuple Z n->T):=
        fold_right_cps (fun t st => place t (pred n) (fun p=> add_to_nth (fst p) (snd p) st id)) (zeros n) p f.
      Lemma eval_from_associational_id {n} p (n_nonzero:n<>O):
        eval (@from_associational n p _ id) = Associational.eval p.
      Proof.
        induction p; intros; simpl; autorewrite with push_eval;
          try reflexivity; cbv [from_associational] in *.
        pose proof (place_in_range a (pred n)).
        rewrite fold_right_cps_correct in IHp |- *; simpl.
        rewrite place_id, <-add_to_nth_id, eval_add_to_nth_id by omega.
        cbv [id] in *; rewrite IHp by omega.
        rewrite weight_place; nsatz.
      Qed. Hint Rewrite @eval_from_associational_id : push_eval.
      Lemma from_associational_id {n} p (n_nonzero:n<>O) {T} f:
        @from_associational n p T f = f (@from_associational n p _ id).
      Proof. cbv [from_associational]; rewrite !@fold_right_cps_correct; simpl; reflexivity. Qed.
      Hint Rewrite @eval_from_associational_id : push_eval.

      Section Carries.
        Context {modulo div : Z->Z->Z}.
        Context {div_mod : forall a b:Z, b <> 0 ->
                                       a = b * (div a b) + modulo a b}.
      Definition carry (index:nat) (p:list limb) {T} (f:list limb->T) :=
        @Associational.carry modulo div (weight index) (weight (S index) / weight index) p T f.
      Lemma carry_id i p {T} f:
        @carry i p T f = f (@carry i p _ id).
      Proof. cbv [carry]; apply Associational.carry_id; auto. Qed.
      Lemma eval_carry_id i p: weight (S i) / weight i <> 0 ->
        Associational.eval (carry i p id) = Associational.eval p.
      Proof. cbv [carry]; intros; eapply @eval_carry_id; eauto. Qed.
      Hint Rewrite @eval_carry_id : push_eval.
      End Carries.
    End Positional.
  End Positional.
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

Axiom add_get_carry : Z -> Z -> Z * Z.
Axiom mul : Z -> Z -> Z * Z.
Axiom modulo : Z -> Z -> Z.
Axiom div : Z -> Z -> Z.
Axiom div_mod :
 forall a b : Z,
 b <> 0 ->
 a = b * div a b + modulo a b.

Lemma lift_tuple2 {R S T n} f (g:R->S) : (forall a b, {prod | g prod = f a b}) ->
                              { op : tuple T n -> tuple T n -> R & forall a b, g (op a b) = f a b }.
Proof.
  intros X.
  exists (fun a b => proj1_sig (X a b)).
  intros a b. apply (proj2_sig (X a b)).
Qed.

Local Infix "^" := tuple : type_scope.
Goal { mul : (Z^4 -> Z^4 -> Z^7)%type &
             forall a b : Z^4,
               let eval {n} := Positional.eval (n := n) (fun i => 10^i) in
               eval (mul a b) = eval a  * eval b }.
Proof.
  apply lift_tuple2; intros.
  cbv [Tuple.tuple Tuple.tuple'] in *.
  repeat match goal with p : _ * Z |- _ => destruct p end.
  eexists; cbv zeta beta; intros.
  match goal with |- Positional.eval ?wt _ = Positional.eval ?wt ?a * Positional.eval ?wt ?b =>
                  transitivity (Positional.eval wt
                                  (Positional.to_associational (n := 4) wt a
                                  (fun r => Positional.to_associational (n := 4) wt b
                                  (fun r0 => Associational.mul r r0
                                  (fun r1 => Positional.from_associational wt 7 r1
                                  (fun r2 => Positional.to_associational wt r2
                                  (fun r3 => @Positional.carry wt modulo div 0 r3 _
                                  (fun r4 => @Positional.carry wt modulo div 1 r4 _
                                  (fun r5 => @Positional.carry wt modulo div 2 r5 _
                                  (fun r6 => @Positional.carry wt modulo div 3 r6 _
                                  (fun r7 => @Positional.carry wt modulo div 4 r7 _
                                  (fun r8 => @Positional.carry wt modulo div 5 r8 _
                                  (fun r9 => @Positional.carry wt modulo div 6 r9 _
                                  (fun r10 => @Positional.carry wt modulo div 7 r10 _
                                  (fun r11 => Positional.from_associational wt 7 r11 id
                               )))))))))))))))
  end.
  {
  apply f_equal.
  cbv - [runtime_add runtime_mul Let_In].
  cbv [runtime_add runtime_mul].
  repeat progress rewrite ?Z.mul_1_l, ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_0_r.
  reflexivity.
  }
  { repeat progress (try rewrite Positional.to_associational_id;
                     try rewrite Associational.mul_id;
                     try rewrite Positional.from_associational_id by congruence;
                     try rewrite Positional.carry_id;
                     cbv [id]; fold @id).
    rewrite Positional.eval_from_associational_id
      by (try (intro i; apply Z.pow_nonzero; try congruence; destruct i; omega);
          cbv; congruence).
    repeat rewrite Positional.eval_carry_id
      by (auto using div_mod; rewrite <-Z.pow_sub_r; cbv; try split; congruence).
    rewrite Positional.eval_to_associational_id.
    rewrite Positional.eval_from_associational_id
      by (try (intro i; apply Z.pow_nonzero; try congruence; destruct i; omega);
          cbv; congruence).
    rewrite Associational.eval_mul_id.
    rewrite Positional.eval_to_associational_id.
    rewrite Positional.eval_to_associational_id.
    reflexivity. }
Defined.