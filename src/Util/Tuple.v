Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Export Crypto.Util.FixCoqMistakes.

Fixpoint tuple' T n : Type :=
  match n with
  | O => T
  | S n' => (tuple' T n' * T)%type
  end.

Definition tuple T n : Type :=
  match n with
  | O => unit
  | S n' => tuple' T n'
  end.

(** right-associated tuples *)
Fixpoint rtuple' T n : Type :=
  match n with
  | O => T
  | S n' => (T * rtuple' T n')%type
  end.

Definition rtuple T n : Type :=
  match n with
  | O => unit
  | S n' => rtuple' T n'
  end.

Fixpoint rsnoc' T n {struct n} : forall (x : rtuple' T n) (y : T), rtuple' T (S n)
  := match n return forall (x : rtuple' T n) (y : T), rtuple' T (S n) with
     | O => fun x y => (x, y)
     | S n' => fun x y => (fst x, @rsnoc' T n' (snd x) y)
     end.
Global Arguments rsnoc' {T n} _ _.

Fixpoint cons' T n {struct n} : forall (y : T) (x : tuple' T n), tuple' T (S n)
  := match n return forall (y : T) (x : tuple' T n), tuple' T (S n) with
     | O => fun y x => (y, x)
     | S n' => fun y x => (@cons' T n' y (fst x), snd x)
     end.
Global Arguments cons' {T n} _ _.

Fixpoint assoc_right' {n T} {struct n}
  : tuple' T n -> rtuple' T n
  := match n return tuple' T n -> rtuple' T n with
     | 0 => fun x => x
     | S n' => fun ts => let xs := @assoc_right' n' T (fst ts) in
                         let x := snd ts in
                         rsnoc' xs x
     end.

Definition assoc_right {n T}
  : tuple T n -> rtuple T n
  := match n with
     | 0 => fun x => x
     | S n' => @assoc_right' n' T
     end.

Fixpoint assoc_left' {n T} {struct n}
  : rtuple' T n -> tuple' T n
  := match n return rtuple' T n -> tuple' T n with
     | 0 => fun x => x
     | S n' => fun ts => let xs := @assoc_left' n' T (snd ts) in
                         let x := fst ts in
                         cons' x xs
     end.

Definition assoc_left {n T}
  : rtuple T n -> tuple T n
  := match n with
     | 0 => fun x => x
     | S n' => @assoc_left' n' T
     end.

Definition tl' {T n} : tuple' T (S n) -> tuple' T n := @fst _ _.
Definition tl {T n} : tuple T (S n) -> tuple T n :=
  match n with
  | O => fun _ => tt
  | S n' => @tl' T n'
  end.
Definition hd' {T n} : tuple' T n -> T :=
  match n with
  | O => fun x => x
  | S n' => @snd _ _
  end.
Definition hd {T n} : tuple T (S n) -> T := @hd' _ _.

Fixpoint to_list' {T} (n:nat) {struct n} : tuple' T n -> list T :=
  match n with
  | 0 => fun x => (x::nil)%list
  | S n' => fun xs : tuple' T (S n') => let (xs', x) := xs in (x :: to_list' n' xs')%list
  end.

Definition to_list {T} (n:nat) : tuple T n -> list T :=
  match n with
  | 0 => fun _ => nil
  | S n' => fun xs : tuple T (S n') => to_list' n' xs
  end.

Program Fixpoint from_list' {T} (y:T) (n:nat) (xs:list T) : length xs = n -> tuple' T n :=
  match n return _ with
  | 0 =>
    match xs return (length xs = 0 -> tuple' T 0) with
    | nil => fun _ => y
    | _ => _ (* impossible *)
    end
  | S n' =>
    match xs return (length xs = S n' -> tuple' T (S n')) with
    | cons x xs' => fun _ => (from_list' x n' xs' _, y)
    | _ => _ (* impossible *)
    end
  end.

Program Definition from_list {T} (n:nat) (xs:list T) : length xs = n -> tuple T n :=
match n return _ with
| 0 =>
    match xs return (length xs = 0 -> tuple T 0) with
    | nil => fun _ : 0 = 0 => tt
    | _ => _ (* impossible *)
    end
| S n' =>
    match xs return (length xs = S n' -> tuple T (S n')) with
    | cons x xs' => fun _ => from_list' x n' xs' _
    | _ => _ (* impossible *)
    end
end.

Lemma to_list_from_list : forall {T} (n:nat) (xs:list T) pf, to_list n (from_list n xs pf) = xs.
Proof.
  destruct xs; simpl; intros; subst; auto.
  generalize dependent t. simpl in *.
  induction xs; simpl in *; intros; congruence.
Qed.

Lemma length_to_list' T n t : length (@to_list' T n t) = S n.
Proof. induction n; simpl in *; trivial; destruct t; simpl; congruence. Qed.

Lemma length_to_list : forall {T} {n} (xs:tuple T n), length (to_list n xs) = n.
Proof.
  destruct n; [ reflexivity | apply length_to_list' ].
Qed.

Lemma from_list'_to_list' : forall T n (xs:tuple' T n),
    forall x xs' pf, to_list' n xs = cons x xs' ->
      from_list' x n xs' pf = xs.
Proof.
  induction n; intros.
  { simpl in *. injection H; clear H; intros; subst. congruence. }
  { destruct xs eqn:Hxs;
    destruct xs' eqn:Hxs';
    injection H; clear H; intros; subst; try discriminate.
    simpl. f_equal. eapply IHn. assumption. }
Qed.

Lemma from_list_to_list : forall {T n} (xs:tuple T n) pf, from_list n (to_list n xs) pf = xs.
Proof.
  destruct n; auto; intros; simpl in *.
  { destruct xs; auto. }
  { destruct (to_list' n xs) eqn:H; try discriminate.
    eapply from_list'_to_list'; assumption. }
Qed.

Fixpoint curry'T (R T : Type) (n : nat) : Type
  := match n with
     | 0 => T -> R
     | S n' => curry'T (T -> R) T n'
     end.
Definition curryT (R T : Type) (n : nat) : Type
  := match n with
     | 0 => R
     | S n' => curry'T R T n'
     end.

Fixpoint uncurry' {R T n} : (tuple' T n -> R) -> curry'T R T n
  := match n return (tuple' T n -> R) -> curry'T R T n with
     | 0 => fun f x => f x
     | S n' => fun f => @uncurry' (T -> R) T n' (fun xs x => f (xs, x))
     end.

Fixpoint uncurry {R T n} : (tuple T n -> R) -> curryT R T n
  := match n return (tuple T n -> R) -> curryT R T n with
     | 0 => fun f => f tt
     | S n' => @uncurry' R T n'
     end.

Fixpoint curry' {R T n} : curry'T R T n -> (tuple' T n -> R)
  := match n return curry'T R T n -> (tuple' T n -> R) with
     | 0 => fun f x => f x
     | S n' => fun f xs_x => @curry' (T -> R) T n' f (fst xs_x) (snd xs_x)
     end.

Fixpoint curry {R T n} : curryT R T n -> (tuple T n -> R)
  := match n return curryT R T n -> (tuple T n -> R) with
     | 0 => fun r _ => r
     | S n' => @curry' R T n'
     end.

Definition on_tuple {A B} (f:list A -> list B)
           {n m:nat} (H:forall xs, length xs = n -> length (f xs) = m)
           (xs:tuple A n) : tuple B m :=
  from_list m (f (to_list n xs))
            (H (to_list n xs) (length_to_list xs)).

Definition map {n A B} (f:A -> B) (xs:tuple A n) : tuple B n
  := on_tuple (List.map f) (fun _ => eq_trans (map_length _ _)) xs.

Definition on_tuple2 {A B C} (f : list A -> list B -> list C) {a b c : nat}
           (Hlength : forall la lb, length la = a -> length lb = b -> length (f la lb) = c)
           (ta:tuple A a) (tb:tuple B b) : tuple C c
  := from_list c (f (to_list a ta) (to_list b tb))
               (Hlength (to_list a ta) (to_list b tb) (length_to_list ta) (length_to_list tb)).

Definition map2 {n A B C} (f:A -> B -> C) (xs:tuple A n) (ys:tuple B n) : tuple C n
  := on_tuple2 (map2 f) (fun la lb pfa pfb => eq_trans (@map2_length _ _ _ _ la lb) (eq_trans (f_equal2 _ pfa pfb) (Min.min_idempotent _))) xs ys.

Lemma to_list'_ext {n A} (xs ys:tuple' A n) : to_list' n xs = to_list' n ys -> xs = ys.
Proof.
  induction n; simpl in *; [cbv; congruence|]; destruct_head' prod.
  intro Hp; injection Hp; clear Hp; intros; subst; eauto using f_equal2.
Qed.

Lemma to_list_ext {n A} (xs ys:tuple A n) : to_list n xs = to_list n ys -> xs = ys.
Proof.
  destruct n; simpl in *; destruct_head unit; eauto using to_list'_ext.
Qed.

Lemma from_list'_complete {A n} (xs:tuple' A n) : exists x ls pf, xs = from_list' x n ls pf.
Proof.
  destruct n; simpl in xs.
  {  exists xs. exists nil. exists eq_refl. reflexivity. }
  { destruct xs as [xs' x]. exists x. exists (to_list' _ xs'). eexists (length_to_list' _ _ _).
    symmetry; eapply from_list'_to_list'. reflexivity. }
Qed.

Lemma from_list_complete {A n} (xs:tuple A n) : exists ls pf, xs = from_list n ls pf.
Proof.
  exists (to_list n xs). exists (length_to_list _). symmetry; eapply from_list_to_list.
Qed.

Ltac tuples_from_lists :=
  repeat match goal with
         | [xs:tuple ?A _ |- _] =>
           let ls := fresh "l" xs in
           destruct (from_list_complete xs) as [ls [? ?]]; subst
         | [xs:tuple' ?A _ |- _] =>
           let a := fresh A in
           let ls := fresh "l" xs in
           destruct (from_list'_complete xs) as [a [ls [? ?]]]; subst
         end.

Lemma map_to_list {A B n ts} (f : A -> B)
  : List.map f (@to_list A n ts) = @to_list B n (map f ts).
Proof.
  tuples_from_lists; unfold map, on_tuple.
  repeat (rewrite to_list_from_list || rewrite from_list_to_list).
  reflexivity.
Qed.

Lemma to_list_map2 {A B C n xs ys} (f : A -> B -> C)
  : ListUtil.map2 f (@to_list A n xs) (@to_list B n ys) = @to_list C n (map2 f xs ys).
Proof.
  tuples_from_lists; unfold map2, on_tuple2.
  repeat (rewrite to_list_from_list || rewrite from_list_to_list).
  reflexivity.
Qed.

Ltac tuple_maps_to_list_maps :=
  try eapply to_list_ext;
  tuples_from_lists;
  repeat (rewrite <-@map_to_list || rewrite <-@to_list_map2 ||
          rewrite @to_list_from_list || rewrite @from_list_to_list).

Lemma map_map2 {n A B C D} (f:A -> B -> C) (g:C -> D) (xs:tuple A n) (ys:tuple B n)
  : map g (map2 f xs ys) = map2 (fun a b => g (f a b)) xs ys.
Proof.
  tuple_maps_to_list_maps; eauto using ListUtil.map_map2.
Qed.

Lemma map2_fst {n A B C} (f:A -> C) (xs:tuple A n) (ys:tuple B n)
  : map2 (fun a b => f a) xs ys = map f xs.
Proof.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_fst.
Qed.

Lemma map2_snd {n A B C} (f:B -> C) (xs:tuple A n) (ys:tuple B n)
  : map2 (fun a b => f b) xs ys = map f ys.
Proof.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_snd.
Qed.

Lemma map_id_ext {n A} (f : A -> A) (xs:tuple A n)
  : (forall x, f x = x) -> map f xs = xs.
Proof.
  intros; tuple_maps_to_list_maps.
  transitivity (List.map (fun x => x) lxs).
  { eapply ListUtil.pointwise_map; cbv [pointwise_relation]; eauto. }
  { eapply List.map_id. }
Qed.

Lemma map_id {n A} (xs:tuple A n)
  : map (fun x => x) xs = xs.
Proof. eapply map_id_ext; intros; reflexivity. Qed.

Lemma map2_map {n A B C A' B'} (f:A -> B -> C) (g:A' -> A) (h:B' -> B) (xs:tuple A' n) (ys:tuple B' n)
  : map2 f (map g xs) (map h ys) = map2 (fun a b => f (g a) (h b)) xs ys.
Proof.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_map.
Qed.

Lemma map_S' {n A B} (f:A -> B) (xs:tuple A (S n)) (x:A)
  : map (n:=S (S n)) f (xs, x) = (map (n:=S n) f xs, f x).
Proof.
  tuple_maps_to_list_maps.
  destruct lxs as [|x' lxs']; [simpl in *; discriminate|].
  change ( f x :: List.map f (to_list (S n) (from_list (S n) (x' :: lxs') x0)) = f x :: to_list (S n) (map f (from_list (S n) (x' :: lxs') x0)) ).
  tuple_maps_to_list_maps.
  reflexivity.
Qed.

Definition map_S {n A B} (f:A -> B) (xs:tuple' A n) (x:A)
  : map (n:=S (S n)) f (xs, x) = (map (n:=S n) f xs, f x) := map_S' _ _ _.

Lemma map2_S' {n A B C} (f:A -> B -> C) (xs:tuple A (S n)) (ys:tuple B (S n)) (x:A) (y:B)
  : map2 (n:=S (S n)) f (xs, x) (ys, y) = (map2 (n:=S n) f xs ys, f x y).
Proof.
  tuple_maps_to_list_maps.
  destruct lxs as [|x' lxs']; [simpl in *; discriminate|].
  destruct lys as [|y' lys']; [simpl in *; discriminate|].
  change ( f x y ::  ListUtil.map2 f (to_list (S n) (from_list (S n) (x' :: lxs') x1))
    (to_list (S n) (from_list (S n) (y' :: lys') x0)) = f x y :: to_list (S n) (map2 f (from_list (S n) (x' :: lxs') x1) (from_list (S n) (y' :: lys') x0)) ).
  tuple_maps_to_list_maps.
  reflexivity.
Qed.

Definition map2_S {n A B C} (f:A -> B -> C) (xs:tuple' A n) (ys:tuple' B n) (x:A) (y:B)
  : map2 (n:=S (S n)) f (xs, x) (ys, y) = (map2 (n:=S n) f xs ys, f x y) := map2_S' _ _ _ _ _.

Lemma map2_map_fst {n A B C A'} (f:A -> B -> C) (g:A' -> A) (xs:tuple A' n) (ys:tuple B n)
  : map2 f (map g xs) ys = map2 (fun a b => f (g a) b) xs ys.
Proof.
  rewrite <- (map2_map f g (fun x => x)), map_id; reflexivity.
Qed.

Lemma map2_map_snd {n A B C B'} (f:A -> B -> C) (g:B' -> B) (xs:tuple A n) (ys:tuple B' n)
  : map2 f xs (map g ys) = map2 (fun a b => f a (g b)) xs ys.
Proof.
  rewrite <- (map2_map f (fun x => x) g), map_id; reflexivity.
Qed.

Lemma map_map {n A B C} (g : B -> C) (f : A -> B) (xs:tuple A n)
  : map g (map f xs) = map (fun x => g (f x)) xs.
Proof. tuple_maps_to_list_maps; eapply List.map_map. Qed.

Section monad.
  Context (M : Type -> Type) (bind : forall X Y, M X -> (X -> M Y) -> M Y) (ret : forall X, X -> M X).
  Fixpoint lift_monad' {n A} {struct n}
    : tuple' (M A) n -> M (tuple' A n)
    := match n return tuple' (M A) n -> M (tuple' A n) with
       | 0 => fun t => t
       | S n' => fun xy => bind _ _ (@lift_monad' n' _ (fst xy)) (fun x' => bind _ _ (snd xy) (fun y' => ret _ (x', y')))
       end.
  Fixpoint push_monad' {n A} {struct n}
    : M (tuple' A n) -> tuple' (M A) n
    := match n return M (tuple' A n) -> tuple' (M A) n with
       | 0 => fun t => t
       | S n' => fun xy => (@push_monad' n' _ (bind _ _ xy (fun xy' => ret _ (fst xy'))),
                            bind _ _ xy (fun xy' => ret _ (snd xy')))
       end.
  Definition lift_monad {n A}
    : tuple (M A) n -> M (tuple A n)
    := match n return tuple (M A) n -> M (tuple A n) with
       | 0 => ret _
       | S n' => @lift_monad' n' A
       end.
  Definition push_monad {n A}
    : M (tuple A n) -> tuple (M A) n
    := match n return M (tuple A n) -> tuple (M A) n with
       | 0 => fun _ => tt
       | S n' => @push_monad' n' A
       end.
End monad.
Local Notation option_bind
  := (fun A B (x : option A) f => match x with
                                  | Some x' => f x'
                                  | None => None
                                  end).
Definition lift_option {n A} (xs : tuple (option A) n) : option (tuple A n)
  := lift_monad option option_bind (@Some) xs.
Definition push_option {n A} (xs : option (tuple A n)) : tuple (option A) n
  := push_monad option option_bind (@Some) xs.

Lemma lift_push_option {n A} (xs : option (tuple A (S n))) : lift_option (push_option xs) = xs.
Proof.
  simpl in *.
  induction n; [ reflexivity | ].
  simpl in *; rewrite IHn; clear IHn.
  destruct xs as [ [? ?] | ]; reflexivity.
Qed.

Lemma push_lift_option {n A} {xs : tuple (option A) (S n)} {v}
  : lift_option xs = Some v <-> xs = push_option (Some v).
Proof.
  simpl in *.
  induction n; [ reflexivity | ].
  specialize (IHn (fst xs) (fst v)).
  repeat first [ progress destruct_head_hnf' prod
               | progress destruct_head_hnf' and
               | progress destruct_head_hnf' iff
               | progress destruct_head_hnf' option
               | progress inversion_option
               | progress inversion_prod
               | progress subst
               | progress break_match
               | progress simpl in *
               | progress specialize_by exact eq_refl
               | reflexivity
               | split
               | intro ].
Qed.

Fixpoint fieldwise' {A B} (n:nat) (R:A->B->Prop) (a:tuple' A n) (b:tuple' B n) {struct n} : Prop.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) /\ fieldwise' _ _ n R (fst a) (fst b)). }
Defined.

Definition fieldwise {A B} (n:nat) (R:A->B->Prop) (a:tuple A n) (b:tuple B n) : Prop.
  destruct n; simpl @tuple in *.
  { exact True. }
  { exact (fieldwise' _ R a b). }
Defined.

Local Ltac Equivalence_fieldwise'_t :=
  let n := match goal with |- ?R (fieldwise' ?n _) => n end in
  let IHn := fresh in
  (* could use [dintuition] in 8.5 only, and remove the [destruct] *)
  repeat match goal with
         | [ H : Equivalence _ |- _ ] => destruct H
         | [ |- Equivalence _ ] => constructor
         end;
  induction n as [|? IHn]; [solve [auto]|];
  simpl; constructor; repeat intro; repeat intuition eauto.

Section Equivalence.
  Context {A} {R:relation A}.
  Global Instance Reflexive_fieldwise' {R_Reflexive:Reflexive R} {n:nat} : Reflexive (fieldwise' n R) | 5.
  Proof. Equivalence_fieldwise'_t. Qed.
  Global Instance Symmetric_fieldwise' {R_Symmetric:Symmetric R} {n:nat} : Symmetric (fieldwise' n R) | 5.
  Proof. Equivalence_fieldwise'_t. Qed.
  Global Instance Transitive_fieldwise' {R_Transitive:Transitive R} {n:nat} : Transitive (fieldwise' n R) | 5.
  Proof. Equivalence_fieldwise'_t. Qed.
  Global Instance Equivalence_fieldwise' {R_equiv:Equivalence R} {n:nat} : Equivalence (fieldwise' n R).
  Proof. constructor; exact _. Qed.

  Global Instance Reflexive_fieldwise {R_Reflexive:Reflexive R} {n:nat} : Reflexive (fieldwise n R) | 5.
  Proof. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Symmetric_fieldwise {R_Symmetric:Symmetric R} {n:nat} : Symmetric (fieldwise n R) | 5.
  Proof. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Transitive_fieldwise {R_Transitive:Transitive R} {n:nat} : Transitive (fieldwise n R) | 5.
  Proof. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Equivalence_fieldwise {R_equiv:Equivalence R} {n:nat} : Equivalence (fieldwise n R).
  Proof. constructor; exact _. Qed.
End Equivalence.

Arguments fieldwise' {A B n} _ _ _.
Arguments fieldwise {A B n} _ _ _.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Global Instance dec_fieldwise' {A RA} {HA : DecidableRel RA} {n} : DecidableRel (@fieldwise' A A n RA) | 10.
Proof.
  induction n; simpl @fieldwise'.
  { exact _. }
  { intros ??.
    exact _. }
Defined.

Global Instance dec_fieldwise {A RA} {HA : DecidableRel RA} {n} : DecidableRel (@fieldwise A A n RA) | 10.
Proof.
  destruct n; unfold fieldwise; exact _.
Defined.

Section fieldwise_map.
  Local Arguments map : simpl never.
  Lemma fieldwise'_map_eq {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple' A n) (t2:tuple' B n)
    : fieldwise' R (map (n:=S n) f t1) (map (n:=S n) g t2)
      = fieldwise' (fun x y => R (f x) (g y)) t1 t2.
  Proof.
    induction n; [ reflexivity | ].
    destruct t1, t2.
    rewrite !map_S.
    simpl @fieldwise'; rewrite IHn; reflexivity.
  Qed.

  Lemma fieldwise_map_eq {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple A n) (t2:tuple B n)
    : fieldwise R (map f t1) (map g t2)
      = fieldwise (fun x y => R (f x) (g y)) t1 t2.
  Proof.
    destruct n; [ reflexivity | apply fieldwise'_map_eq ].
  Qed.

  Lemma fieldwise'_map_iff {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple' A n) (t2:tuple' B n)
    : fieldwise' R (map (n:=S n) f t1) (map (n:=S n) g t2)
      <-> fieldwise' (fun x y => R (f x) (g y)) t1 t2.
  Proof. rewrite fieldwise'_map_eq; reflexivity. Qed.

  Lemma fieldwise_map_iff {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple A n) (t2:tuple B n)
    : fieldwise R (map f t1) (map g t2)
      <-> fieldwise (fun x y => R (f x) (g y)) t1 t2.
  Proof. rewrite fieldwise_map_eq; reflexivity. Qed.
End fieldwise_map.

Fixpoint fieldwiseb' {A B} (n:nat) (R:A->B->bool) (a:tuple' A n) (b:tuple' B n) {struct n} : bool.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) && fieldwiseb' _ _ n R (fst a) (fst b))%bool. }
Defined.

Definition fieldwiseb {A B} (n:nat) (R:A->B->bool) (a:tuple A n) (b:tuple B n) : bool.
  destruct n; simpl @tuple in *.
  { exact true. }
  { exact (fieldwiseb' _ R a b). }
Defined.

Arguments fieldwiseb' {A B n} _ _ _.
Arguments fieldwiseb {A B n} _ _ _.

Lemma fieldwiseb'_fieldwise' :forall {A B} n R Rb
                                   (a:tuple' A n) (b:tuple' B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb' Rb a b = true <-> fieldwise' R a b).
Proof.
  intros.
  revert n a b;
  induction n; intros; simpl @tuple' in *;
    simpl fieldwiseb'; simpl fieldwise'; auto.
  cbv beta.
  rewrite Bool.andb_true_iff.
  f_equiv; auto.
Qed.

Lemma fieldwiseb_fieldwise :forall {A B} n R Rb
                                   (a:tuple A n) (b:tuple B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb Rb a b = true <-> fieldwise R a b).
Proof.
  intros; destruct n; simpl @tuple in *;
    simpl @fieldwiseb; simpl @fieldwise; try tauto.
  auto using fieldwiseb'_fieldwise'.
Qed.


Fixpoint from_list_default' {T} (d y:T) (n:nat) (xs:list T) : tuple' T n :=
  match n return tuple' T n with
  | 0 => y (* ignore high digits *)
  | S n' =>
         match xs return _ with
         | cons x xs' => (from_list_default' d x n' xs', y)
         | nil => (from_list_default' d d n' nil, y)
         end
  end.

Definition from_list_default {T} d (n:nat) (xs:list T) : tuple T n :=
match n return tuple T n with
| 0 => tt
| S n' =>
    match xs return _ with
    | cons x xs' => (from_list_default' d x n' xs')
    | nil => (from_list_default' d d n' nil)
    end
end.

Lemma from_list_default'_eq : forall {T} (d : T) xs n y pf,
  from_list_default' d y n xs = from_list' y n xs pf.
Proof.
  induction xs; destruct n; intros; simpl in *;
    solve [ congruence (* 8.5 *)
          | erewrite IHxs; reflexivity ]. (* 8.4 *)
Qed.

Lemma from_list_default_eq : forall {T} (d : T) xs n pf,
  from_list_default d n xs = from_list n xs pf.
Proof.
  induction xs; destruct n; intros; try solve [simpl in *; congruence].
  apply from_list_default'_eq.
Qed.

Fixpoint function R T n : Type :=
  match n with
  | O => R
  | S n' => T -> function R T n'
  end.

Fixpoint apply' {R T} (n:nat) : (T -> function R T n) -> tuple' T n -> R :=
  match n with
  | 0 => id
  | S n' => fun f x => apply' n' (f (snd x)) (fst x)
  end.

Definition apply {R T} (n:nat) : function R T n -> tuple T n -> R :=
  match n with
  | O => fun r _ => r
  | S n' => fun f x =>  apply' n' f x
  end.

Require Import Coq.Lists.SetoidList.

Lemma fieldwise_to_list_iff : forall {T n} R (s t : tuple T n),
    (fieldwise R s t <-> Forall2 R (to_list _ s) (to_list _ t)).
Proof.
  induction n; split; intros.
  + constructor.
  + cbv [fieldwise]. auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [to_list']; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      constructor; intuition auto.
      apply IHn; auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [fieldwise']; auto.
      cbv [to_list'] in *; inversion H; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      inversion H; subst.
      split; try assumption.
      apply IHn; auto.
Qed.


Require Import Crypto.Util.ListUtil. (* To initialize [distr_length] database *)
Hint Rewrite length_to_list' @length_to_list : distr_length.
