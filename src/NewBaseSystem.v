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
    Create HintDb uncps discriminated. Hint Rewrite @map_cps_correct : uncps.

    Fixpoint flat_map_cps {A B} (g:A->forall {T}, (list B->T)->T) (ls : list A) {T} (f:list B->T)  :=
      match ls with
      | nil => f nil
      | (x::tl)%list => g x (fun r => flat_map_cps g tl (fun rr => f (r ++ rr))%list)
      end.
    Lemma flat_map_cps_correct {A B} (g:A->forall {T}, (list B->T)->T) ls :
      forall {T} (f:list B->T),
        (forall x T h, @g x T h = h (g x id)) ->
        @flat_map_cps A B g ls T f = f (List.flat_map (fun x => g x id) ls).
    Proof.
      induction ls; intros; [reflexivity|].
      simpl flat_map_cps. simpl flat_map.
      rewrite H; erewrite IHls by eassumption.
      reflexivity.
    Qed.
    Hint Rewrite @flat_map_cps_correct using (intros; autorewrite with uncps; auto): uncps.

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
      Hint Rewrite @find_remove_first_cps_correct : uncps.

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
    Hint Rewrite @from_list_default_cps_correct : uncps.
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
    Hint Rewrite @to_list_cps_correct : uncps.
    
    Definition on_tuple_cps {A B} (d:B) (g:list A ->forall {T},(list B->T)->T) {n m}
               (xs : Tuple.tuple A n) {T} (f:tuple B m ->T) :=
      to_list_cps n xs (fun r => g r (fun rr => from_list_default_cps d m rr f)).
    Lemma on_tuple_cps_correct {A B} d (g:list A -> forall {T}, (list B->T)->T)
          {n m} xs {T} f
          (Hg : forall x {T} h, @g x T h = h (g x id)) : forall H,
      @on_tuple_cps A B d g n m xs T f = f (@Tuple.on_tuple A B (fun x => g x id) n m H xs).
    Proof.
      cbv [on_tuple_cps Tuple.on_tuple]; intros.
      rewrite to_list_cps_correct, Hg, from_list_default_cps_correct.
      rewrite (Tuple.from_list_default_eq _ _ _ (H _ (Tuple.length_to_list _))).
      reflexivity.
    Qed.  Hint Rewrite @on_tuple_cps_correct using (intros; autorewrite with uncps; auto): uncps.

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
    Hint Rewrite @update_nth_cps_correct : uncps.

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
    Hint Rewrite @combine_cps_correct: uncps.
    
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
      destruct (fold_right_min ls z);
      simpl List.In; tauto.
    Qed.
    Fixpoint fold_right_cps {A B} (g:B->A->A) (a0:A) (l:list B) {T} (f:A->T) :=
      match l with
      | nil => f a0
      | cons a tl => fold_right_cps g a0 tl (fun r => f (g a r))
      end.
    Lemma fold_right_cps_correct {A B} g a0 l: forall {T} f,
        @fold_right_cps A B g a0 l T f = f (List.fold_right g a0 l).
    Proof. induction l; intros; simpl; rewrite ?IHl; auto. Qed.
    Hint Rewrite @fold_right_cps_correct : uncps.

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
    Hint Rewrite @fold_right_no_starter_cps_correct : uncps.

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

      Definition has_same_wt (cx a:limb) {T} (f:bool->T) :=
        if dec (fst cx = fst a) then f true else f false.
      Definition has_same_wt_noncps cx a := has_same_wt cx a id.
      Hint Opaque has_same_wt_noncps : uncps.
      Lemma has_same_wt_id cx a {T} f:
        @has_same_wt cx a T f = f (has_same_wt_noncps cx a).
      Proof. cbv [has_same_wt has_same_wt_noncps]; prove_id. Qed.
      Hint Rewrite has_same_wt_id : uncps.

      Lemma find_remove_first'_same_wt cx cx' p: forall acc,
        fst (find_remove_first' (has_same_wt_noncps cx) acc p) = Some cx' ->
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + (eval (snd (find_remove_first' (has_same_wt_noncps cx) acc p))) = fst cx * snd cx + eval acc + eval p.
      Proof.
        cbv [has_same_wt has_same_wt_noncps];
          induction p; simpl find_remove_first' in *;
            repeat match goal with
                   | H : _ |- _ => erewrite (proj2 (IHp _ H))
                   | H : _ |- _ => erewrite (proj1 (IHp _ H))
                   | |- _ => progress prove_eval
                   end.
      Qed.
      Lemma find_remove_first_same_wt cx cx' p
        (H : fst (find_remove_first (has_same_wt_noncps cx) p) = Some cx') :
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + eval (snd (find_remove_first (has_same_wt_noncps cx) p)) = fst cx * snd cx + eval p.
      Proof.
        cbv [find_remove_first]; intros.
        erewrite (proj1 (find_remove_first'_same_wt _ _ _ _ H)) by eauto.
        erewrite (proj2 (find_remove_first'_same_wt _ _ _ _ H)) by eauto.
        prove_eval.
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
      Definition compact_no_carry'_noncps acc p := compact_no_carry' acc p id.
      Hint Opaque compact_no_carry'_noncps : uncps.
      Definition compact_no_carry p {T} f := @compact_no_carry' nil p T f.
      Definition compact_no_carry_noncps p := compact_no_carry p id.
      Hint Opaque compact_no_carry_noncps : uncps.
      Lemma compact_no_carry'_id p: forall acc {T} (f:list limb -> T),
        @compact_no_carry' acc p T f = f (compact_no_carry'_noncps acc p).
      Proof.
        cbv [compact_no_carry'_noncps]; induction p; prove_id;
          repeat match goal with
                 | _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 end; prove_id.
      Qed. Hint Rewrite compact_no_carry'_id : uncps.
      Lemma eval_compact_no_carry'_noncps p: forall acc,
        eval (compact_no_carry'_noncps acc p) = eval acc + eval p.
      Proof.
        induction p;
          repeat match goal with
                 | |- _ => progress (cbv [compact_no_carry'_noncps]; prove_eval)
                 | |- _ => rewrite IHp
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   apply find_remove_first_same_wt in H
                 end.
      Qed. Hint Rewrite eval_compact_no_carry'_noncps : uncps.
      Lemma length_compact_no_carry' p: forall acc,
        (length (compact_no_carry'_noncps acc p) <= length p + length acc)%nat.
      Proof.
        induction p;
          repeat match goal with
                 | _ => progress intros
                 | _ => progress distr_length
                 | _ => progress (autorewrite with uncps push_id)
                 | _ => rewrite IHp
                 | _ => break_match
                 | _ => reflexivity
                 | _ => progress (cbv [compact_no_carry'_noncps]; simpl)
                 end.
      Qed.
      Lemma compact_no_carry_id p {T} f:
         @compact_no_carry p T f = f (compact_no_carry_noncps p).
      Proof. cbv [compact_no_carry]; prove_id. Qed.
      Hint Rewrite compact_no_carry_id : uncps.
      Lemma eval_compact_no_carry_noncps p:
         eval (compact_no_carry_noncps p) = eval p.
      Proof.
        cbv [compact_no_carry_noncps compact_no_carry].
        rewrite compact_no_carry'_id; prove_eval.
      Qed. Hint Rewrite eval_compact_no_carry_noncps : push_eval.
      Lemma length_compact_no_carry p:
        (length (compact_no_carry_noncps p) <= length p)%nat.
      Proof.
        cbv [compact_no_carry_noncps compact_no_carry].
        rewrite compact_no_carry'_id, push_id, length_compact_no_carry'.
        distr_length.
      Qed. Hint Rewrite length_compact_no_carry : distr_length.

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
      Definition compact_cols_loop1_noncps c o i n := compact_cols_loop1 c o i n id.
      Hint Opaque compact_cols_loop1_noncps : uncps.
      Lemma compact_cols_loop1_id n:
        forall p out carries {T} (f:list limb * list limb ->T),
          compact_cols_loop1 carries out p n f
          = f (compact_cols_loop1_noncps carries out p n).
      Proof. cbv [compact_cols_loop1_noncps]; induction n; prove_id. Qed.
      Hint Rewrite compact_cols_loop1_id : uncps.
      Lemma eval_compact_cols_loop1_noncps n :
        forall p (H0:length p = n) out carries,
          eval (snd (compact_cols_loop1_noncps carries out p n))
          + eval (fst (compact_cols_loop1_noncps carries out p n))
          = eval p + eval out + eval carries.
      Proof.
        induction n; destruct p;
          repeat match goal with
                 | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                   unique assert (length p > 0)%nat
                     by (destruct p; (discriminate || (simpl; omega)))
                 | _ => rewrite IHn by
                       (distr_length; break_match; distr_length; discriminate)
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   apply find_remove_first_same_wt in H
                 | |- context[add ?x ?y] =>
                   specialize (add_correct x y)
                 | _ => progress prove_eval
                 | _ => progress (cbv [compact_cols_loop1_noncps]; simpl)
                 end.
      Qed. Hint Rewrite eval_compact_cols_loop1_noncps : push_eval.

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
      Definition compact_cols_loop2_noncps c o i n := compact_cols_loop2 c o i n id.
      Hint Opaque compact_cols_loop2_noncps : uncps.
      Lemma compact_cols_loop2_id n:
        forall out p carries  {T} (f:list limb->T),
        compact_cols_loop2 carries out p n f
        = f (compact_cols_loop2_noncps carries out p n).
      Proof. cbv [compact_cols_loop2_noncps]; induction n; prove_id. Qed.
      Hint Rewrite compact_cols_loop2_id : uncps.
      Lemma eval_compact_cols_loop2_noncps n:
        forall out p carries,
        eval (compact_cols_loop2_noncps carries out p n)
        = eval p + eval carries + eval out.
      Proof.
        cbv [compact_cols_loop2_noncps]; induction n;
          repeat match goal with
                 | _ => rewrite fold_right_no_starter_cps_correct
                 | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                   unique assert (length p > 0)%nat
                     by (destruct p; (discriminate || (simpl; omega)))
                 | _ => rewrite IHn
                     by (distr_length; break_match; distr_length; discriminate)
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   apply find_remove_first_same_wt in H
                 | |- context[add ?x ?y] =>
                   specialize (add_correct x y)
                 | _ => progress prove_eval
                 | _ => progress (cbv [compact_cols_loop2_noncps]; simpl) 
                 end.
        (* TODO : logic here is kinda ugly-- basic idea is "if you found a minimum weight in (p++carries), an element with that weight must be in either carries or p" *)
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
      Qed. Hint Rewrite eval_compact_cols_loop2_noncps : push_eval.

      Definition compact_cols (p:list limb) {T} (f:list limb->T) :=
        compact_cols_loop1
          nil nil p (length p)
          (fun r => compact_cols_loop2
                      (fst r) nil (snd r) (length (fst r ++ snd r)) f).
      Definition compact_cols_noncps p := compact_cols p id.
      Hint Opaque compact_cols_noncps : uncps.
      Lemma compact_cols_id (p:list limb) {T} (f:list limb->T):
        compact_cols p f = f (compact_cols_noncps p).
      Proof. cbv [compact_cols compact_cols_noncps]; prove_id. Qed.
      Hint Rewrite compact_cols_id : uncps.
      Lemma eval_compact_cols_noncps (p:list limb):
        eval (compact_cols_noncps p) = eval p.
      Proof. cbv [compact_cols_noncps compact_cols]; prove_eval. Qed.
      Hint Rewrite eval_compact_cols_noncps : push_eval.
           
    End Saturated.

    (* 
       it makes sense if we have m = 2^255-19 to have
       k = 2^255, c = [(1,19)]
       but then how do we get the digits for k-c?
       well, we can take the opposite of c, adding modulus, and add it to k
       is that actually a good idea? k + ((k-c)-c) = 2k - 2c, or 2*modulus
       we'd have to shift down

       alternative: store k-1
       then we can just subtract c+1

       to get -modulus, we want -k+c
       we currently have k-1, c+1
       
    *)
    Record Modulus :=
      {
        modulus:Z;
        k:Z;
        c:list limb;
        nonzero:modulus <> 0;
        k_nonzero: k <> 0;
        eval_modulus: k - eval c = modulus;
      }.

    Record SubCoeff {m:Modulus} :=
      {
        coeff:list limb;
        coeff_0 : (eval coeff) mod m.(modulus) = 0;
      }.

    Section Sub.
      Context {m:Modulus} {sc: @SubCoeff m}.

      Definition sub (p q : list limb) {T} (f:list limb->T) :=
        mul q [(1,-1)]
            (fun r => f (sc.(coeff) ++ p ++ r)).
      Definition sub_noncps p q := sub p q id.
      Hint Opaque sub_noncps : uncps.
      Lemma sub_id p q {T} f : @sub p q T f = f (sub_noncps p q).
      Proof. cbv [sub_noncps sub]; prove_id. Qed.
      Hint Rewrite sub_id : uncps.
      Lemma eval_sub_noncps p q :
        (eval (sub_noncps p q)) mod m.(modulus)
        = (eval p - eval q) mod m.(modulus).
      Proof.
        cbv [sub_noncps sub]; prove_eval.
        rewrite Z.add_mod, coeff_0, Z.add_0_l, Z.mod_mod by apply nonzero.
        f_equal; ring.
      Qed. Hint Rewrite eval_sub_noncps : push_eval.

     Definition opp (p : list limb) {T} (f:list limb->T) :=
       sub [] p f.
     Definition opp_noncps p := opp p id.
     Hint Opaque opp_noncps : uncps.
     Lemma opp_id p {T} f : @opp p T f = f (opp_noncps p).
     Proof. cbv [opp_noncps opp]; prove_id. Qed.
     Hint Rewrite opp_id : uncps.
     Lemma eval_opp_noncps p :
       (eval (opp_noncps p)) mod m.(modulus) = (- eval p) mod m.(modulus).
     Proof.
       cbv [opp_noncps opp]; fold (sub_noncps [] p); prove_eval.
     Qed. Hint Rewrite eval_opp_noncps : push_eval.
    End Sub.
    Hint Rewrite @sub_id @opp_id : uncps.
    Hint Rewrite @eval_sub_noncps @eval_opp_noncps : push_eval.

    Section Freeze.
      Context {m:Modulus} {sc: @SubCoeff m}
              {sat_add : list limb -> list limb -> forall {T}, (list limb*bool->T)->T}
              {cond_add : bool->list limb -> list limb -> forall {T}, (list limb->T)->T}
      .
      
      Definition sat_add_noncps p q := sat_add p q _ id.
      Hint Opaque sat_add_noncps : uncps.
      Lemma sat_add_id p q {T} f :
        @sat_add p q T f = f (sat_add_noncps p q).
      Admitted. Hint Rewrite sat_add_id : uncps.
      Lemma eval_sat_add_noncps p q :
        eval (fst (sat_add_noncps p q)) = eval p + eval q.
      Admitted. Hint Rewrite eval_sat_add_noncps : push_eval.
      Definition cond_add_noncps b p q := cond_add b p q _ id.
      Hint Opaque cond_add_noncps : uncps.
      Lemma cond_add_id b p q {T} f :
        @cond_add b p q T f = f (cond_add_noncps b p q).
      Admitted. Hint Rewrite cond_add_id : uncps.
      Lemma eval_cond_add_noncps b p q :
        eval (cond_add_noncps b p q)
        = if b then eval p + eval q else eval p.
      Admitted. Hint Rewrite eval_cond_add_noncps : push_eval.


      (* based on https://sourceforge.net/p/ed448goldilocks/code/ci/master/tree/src/p448/arch_x86_64/p448.c#l309 *)
      Definition freeze (x : list limb) {T} (f:list limb->T) :=
        reduce (m.(k)) (m.(c)) x
               (fun r =>
                  @sat_add r ((m.(k), -1)::(m.(c))) _ 
                           (fun rr =>
                              @opp m sc (m.(c)) _
                                   (fun rrr =>
                                      cond_add (snd rr) (fst rr) ((m.(k),1)::rrr) _ f
                                   )
                           )
               ).
      Definition freeze_noncps x := freeze x id.

      (* TODO : move to ZUtil *)
      Lemma Z_add_mod_0 a b c (H:c mod b = 0):
        (a+c) mod b = a mod b.
      Proof.
        intros; rewrite Z.add_mod_r, H, Z.add_0_r; reflexivity.
      Qed.

      Lemma eval_freeze_noncps x :
        eval (freeze_noncps x) mod m.(modulus) = eval x mod m.(modulus).
      Proof.
        cbv [freeze_noncps freeze].
        prove_eval;
          repeat match goal with
                 | |- (_ + (k _ * _ + _)) mod _ = _ =>
                   rewrite Z_add_mod_0
                 | |- (k m * ?x + _) mod ?m = 0 =>
                   transitivity ((x * m) mod m);
                     [|solve[auto using Z.mod_mul, nonzero]]
                 | _ => rewrite Z.add_mod_r; rewrite eval_opp_noncps; 
                          rewrite <-Z.add_mod_r
                 | _ => rewrite <-eval_modulus; autorewrite with push_eval;
                          rewrite ?eval_modulus;
                          solve [auto using nonzero, k_nonzero]
                 | _ => rewrite <-eval_modulus; f_equal; ring
                 end.
      Qed.

    End Freeze.
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
      Lemma from_associational_id {n} p (n_nonzero:n<>O) {T} f:
        @from_associational n p T f = f (from_associational_noncps n p).
      Proof. cbv [from_associational from_associational_noncps]; prove_id. Qed.
      Hint Rewrite @from_associational_id using omega : uncps.
      Lemma eval_from_associational_noncps {n} p (n_nonzero:n<>O):
        eval (from_associational_noncps n p) = Associational.eval p.
      Proof.
        cbv [from_associational from_associational_noncps]; induction p;
          [|pose proof (place_in_range a (pred n))]; prove_eval.
        cbv [place_noncps]; rewrite weight_place. nsatz.
      Qed. Hint Rewrite @eval_from_associational_noncps : push_eval.

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
  {
    repeat progress (try rewrite Positional.to_associational_id;
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