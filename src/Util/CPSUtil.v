Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.omega.Omega.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ListUtil.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.
Local Open Scope Z_scope.

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

Fixpoint map_cps {A B} (g : A->B) ls
         {T} (f:list B->T):=
  match ls with
  | nil => f nil
  | a :: t => map_cps g t (fun r => f (g a :: r))
  end.
Lemma map_cps_correct {A B} g ls: forall {T} f,
    @map_cps A B g ls T f = f (map g ls).
Proof. induction ls as [|?? IHls]; simpl; intros; rewrite ?IHls; reflexivity. Qed.
Create HintDb uncps discriminated. Hint Rewrite @map_cps_correct : uncps.

Fixpoint firstn_cps {A} (n:nat) (l:list A) {T} (f:list A->T) :=
  match n with
  | O => f nil
  | S n' => match l with
            | nil => f nil
            | a :: l' => f (a :: firstn n' l')
            end
  end.
Lemma firstn_cps_correct {A} n l T f :
  @firstn_cps A n l T f = f (firstn n l).
Proof. induction n; destruct l; reflexivity. Qed.
Hint Rewrite @firstn_cps_correct : uncps.

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
  induction ls as [|?? IHls]; intros T f H; [reflexivity|].
  simpl flat_map_cps. simpl flat_map.
  rewrite H; erewrite IHls by eassumption.
  reflexivity.
Qed.
Hint Rewrite @flat_map_cps_correct using (intros; autorewrite with uncps; auto): uncps.

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
  induction n as [|? IHn]; intros; simpl; [reflexivity|].
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
  cbv [on_tuple_cps Tuple.on_tuple]; intros H.
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

(* differs from fold_right_cps in that the functional argument `g` is also a CPS function *)
Fixpoint fold_right_cps2 {A B} (g : B -> A -> forall {T}, (A->T)->T) (a0 : A) (l : list B) {T} (f : A -> T) :=
  match l with
  | nil => f a0
  | b :: tl => fold_right_cps2 g a0 tl (fun r => g b r f)
  end.
Lemma fold_right_cps2_correct {A B} g a0 l : forall {T} f,
  (forall b a T h, @g b a T h = h (@g b a A id)) ->
  @fold_right_cps2 A B g a0 l T f = f (List.fold_right (fun b a => @g b a A id) a0 l).
Proof.
  induction l as [|?? IHl]; intros T f H; [reflexivity|].
  simpl fold_right_cps2. simpl fold_right.
  rewrite H; erewrite IHl by eassumption.
  rewrite H; reflexivity.
Qed.
Hint Rewrite @fold_right_cps2_correct using (intros; autorewrite with uncps; auto): uncps.

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
Proof. induction l as [|? l IHl]; intros; simpl; rewrite ?IHl; auto. Qed.
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

Import Tuple.

Module Tuple.
  Fixpoint map_cps {A B n} (g : A->B) :
  tuple A n -> forall {T}, (tuple B n->T) -> T:=
  match n with
  | O => fun _ _ f => f tt
  | S n' => fun t T f => map_cps g (tl t) (fun r => f (append (g (hd t)) r))
  end.
  Lemma map_cps_correct {A B n} g t: forall {T} f,
      @map_cps A B n g t T f = f (map g t).
  Proof.
    induction n; simpl map_cps; intros; try destruct t;
    [|rewrite IHn, <-map_append,<-subst_append]; reflexivity.
  Qed. Hint Rewrite @map_cps_correct : uncps.

  Fixpoint map2_cps {n A B C} (g:A->B->C) :
    tuple A n -> tuple B n -> forall {T}, (tuple C n->T) -> T :=
    match n with
    | O => fun _ _ _ f => f tt
    | S n' => fun xs ys T f =>
                map2_cps g (tl xs) (tl ys) (fun zs => f (append (g (hd xs) (hd ys)) zs))
    end.
  Lemma map2_cps_correct {n A B C} g xs ys : forall {T} f,
      @map2_cps n A B C g xs ys T f = f (map2 g xs ys).
  Proof.
    induction n; simpl map2_cps; intros; try destruct xs, ys;
    [|rewrite IHn, <-map2_append,<-!subst_append]; reflexivity.
  Qed. Hint Rewrite @map2_cps_correct : uncps.

  Fixpoint mapi_with'_cps {T A B n} i
          (f: nat->T->A->forall {R}, (T*B->R)->R) (start:T)
  : Tuple.tuple' A n -> forall {R}, (T * tuple' B n -> R) -> R :=
  match n as n0 return (tuple' A n0 -> forall {R}, (T * tuple' B n0->R)->R) with
  | O => fun ys {T} ret => f i start ys ret
  | S n' => fun ys {T} ret =>
              f i start (hd ys) (fun sb =>
              mapi_with'_cps (S i) f (fst sb) (tl ys)
                  (fun r => ret (fst r, (snd r, snd sb))))
  end.

  Fixpoint mapi_with_cps {S A B n}
          (f: nat->S->A->forall {T}, (S*B->T)->T) (start:S)
  : tuple A n -> forall {T}, (S * tuple B n->T)->T :=
  match n as n0 return (tuple A n0 -> forall {T}, (S * tuple B n0->T)->T) with
  | O => fun ys {T} ret => ret (start, tt)
  | S n' => fun ys {T} ret => mapi_with'_cps 0%nat f start ys ret
  end.

  Lemma mapi_with'_cps_correct {S A B n} : forall i f start xs T ret,
  (forall i s a R (ret:_->R), f i s a R ret = ret (f i s a _ id)) ->
  @mapi_with'_cps S A B n i f start xs T ret = ret (mapi_with' i (fun i s a => f i s a _ id) start xs).
  Proof. induction n as [|n IHn]; intros i f start xs T ret H; simpl; rewrite H, ?IHn by assumption; reflexivity. Qed.
  Lemma mapi_with_cps_correct {S A B n} f start xs T ret
  (H:forall i s a R (ret:_->R), f i s a R ret = ret (f i s a _ id))
  : @mapi_with_cps S A B n f start xs T ret = ret (mapi_with (fun i s a => f i s a _ id) start xs).
  Proof. destruct n; simpl; rewrite ?mapi_with'_cps_correct by assumption; reflexivity. Qed.
  Hint Rewrite @mapi_with_cps_correct @mapi_with'_cps_correct
       using (intros; autorewrite with uncps; auto): uncps.

  Fixpoint left_append_cps {A n} (x:A) :
    tuple A n -> forall {R}, (tuple A (S n) -> R) -> R :=
  match
    n as n0 return (tuple A n0 -> forall R, (tuple A (S n0) -> R) -> R)
  with
  | 0%nat => fun _ _ f => f x
  | S n' =>
      fun xs _ f =>
      left_append_cps x (tl xs) (fun r => f (append (hd xs) r))
  end.
  Lemma left_append_cps_correct A n x xs R f :
    @left_append_cps A n x xs R f = f (left_append x xs).
  Proof.
    induction n; [reflexivity|].
    simpl left_append. simpl left_append_cps.
    rewrite IHn. reflexivity.
  Qed.

  Definition tl_cps {A n} :
    tuple A (S n) -> forall {R}, (tuple A n -> R) -> R :=
  match
    n as n0 return (tuple A (S n0) -> forall R, (tuple A n0 -> R) -> R)
  with
  | 0%nat => fun _ _ f => f tt
  | S n' => fun xs _ f => f (fst xs)
  end.
  Lemma tl_cps_correct A n xs R f :
    @tl_cps A n xs R f = f (tl xs).
  Proof. destruct n; reflexivity. Qed.

  Definition hd_cps {A n} :
    tuple A (S n) -> forall {R}, (A -> R) -> R :=
  match
    n as n0 return (tuple A (S n0) -> forall R, (A -> R) -> R)
  with
  | 0%nat => fun x _ f => f x
  | S n' => fun xs _ f => f (snd xs)
  end.
  Lemma hd_cps_correct A n xs R f :
    @hd_cps A n xs R f = f (hd xs).
  Proof. destruct n; reflexivity. Qed.

  Fixpoint left_tl_cps {A n} :
    tuple A (S n) -> forall {R}, (tuple A n -> R) -> R :=
  match
    n as n0 return (tuple A (S n0) -> forall R, (tuple A n0 -> R) -> R)
  with
  | 0%nat => fun _ _ f => f tt
  | S n' =>
      fun xs _ f =>
        tl_cps xs (fun xtl => hd_cps xs (fun xhd =>
          left_tl_cps xtl (fun r => f (append xhd r))))
  end.
  Lemma left_tl_cps_correct A n xs R f :
    @left_tl_cps A n xs R f = f (left_tl xs).
  Proof.
    induction n; [reflexivity|].
    simpl left_tl. simpl left_tl_cps.
    rewrite IHn. reflexivity.
  Qed.

  Fixpoint left_hd_cps {A n} :
    tuple A (S n) -> forall {R}, (A -> R) -> R :=
  match
    n as n0 return (tuple A (S n0) -> forall R, (A -> R) -> R)
  with
  | 0%nat => fun x _ f => f x
  | S n' =>
      fun xs _ f => tl_cps xs (fun xtl => left_hd_cps xtl f)
  end.
  Lemma left_hd_cps_correct A n xs R f :
    @left_hd_cps A n xs R f = f (left_hd xs).
  Proof.
    induction n; [reflexivity|].
    simpl left_hd. simpl left_hd_cps.
    rewrite IHn. reflexivity.
  Qed.

  Lemma In_left_hd {A} n (p : tuple A (S n))
    : In (left_hd p) (to_list _ p).
  Proof.
    simpl in *.
    induction n as [|n IHn].
    { left; reflexivity. }
    { destruct p; simpl in *; right; auto. }
  Qed.

  Lemma In_to_list_left_tl {A} n (p : tuple A (S n)) x
    : In x (to_list n (left_tl p)) -> In x (to_list (S n) p).
  Proof.
    simpl in *.
    remember (to_list n (left_tl p)) as ls eqn:H.
    intro Hin; revert Hin H.
    revert n p.
    induction ls as [|l ls IHls], n.
    { simpl; intros ? []. }
    { simpl; intros ? []. }
    { simpl; congruence. }
    { simpl; intros [? p] [H0|H1] H; simpl in *;
        setoid_rewrite to_list_append in H;
        inversion H; clear H; subst; auto. }
  Qed.

  Lemma to_list_left_append {A} {n} (p:tuple A n) x
    : (to_list _ (left_append x p)) = to_list n p ++ x :: nil.
  Proof.
    destruct n as [|n]; simpl in *; [ reflexivity | ].
    induction n as [|n IHn]; simpl in *; [ reflexivity | ].
    destruct p; simpl in *; rewrite IHn; simpl; reflexivity.
  Qed.
End Tuple.
Hint Rewrite @Tuple.map_cps_correct @Tuple.left_append_cps_correct @Tuple.left_tl_cps_correct @Tuple.left_hd_cps_correct @Tuple.tl_cps_correct @Tuple.hd_cps_correct : uncps.
Hint Rewrite @Tuple.mapi_with_cps_correct @Tuple.mapi_with'_cps_correct
     using (intros; autorewrite with uncps; auto): uncps.
