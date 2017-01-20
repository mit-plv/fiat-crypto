Require Import Coq.Lists.List.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

Inductive LetInM : Type -> Type :=
| ret {T} (v : T) : LetInM T
| let_in {A B} (v : A) (f : A -> LetInM B) : LetInM B.

Bind Scope letinm_scope with LetInM.
Delimit Scope letinm_scope with letinm.
Notation "'mlet' x := y 'in' f" := (let_in y (fun x => f%letinm)) : letinm_scope.

Fixpoint denote {A} (x : LetInM A) : A :=
  match x with
  | ret _ v => v
  | let_in T A v f => dlet x := v in @denote A (f x)
  end.

Fixpoint bind {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B
  := match v in LetInM A return (A -> _) -> _ with
     | ret T v => fun f => f v
     | let_in A B v g => fun f => let_in v (fun x => bind (g x) f)
     end.
Notation "x <- y ; z" := (bind y%letinm (fun x => z%letinm)) : letinm_scope.

Fixpoint under_lets {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B
  := match v in LetInM A return (A -> _) -> _ with
     | ret T v => fun f => f v
     | let_in A B v g => fun f => let_in v (fun x => bind (g x) f)
     end.

Definition lift {A B} (f : A -> B) : LetInM A -> LetInM B
  := fun x => under_lets x (fun y => ret (f y)).
Definition lift2 {A B C} (f : A -> B -> C) : LetInM A -> LetInM B -> LetInM C
  := fun x y => under_lets x (fun x' => under_lets y (fun y' => ret (f x' y'))).

Create HintDb push_denote discriminated.
Hint Extern 1 => progress autorewrite with push_denote in * : push_denote.

Ltac push_denote_step :=
  first [ progress simpl @denote in *
        | progress autorewrite with push_denote in *
        | progress autounfold with push_denote in * ].
Ltac push_denote := repeat push_denote_step.

Local Ltac t_step :=
  first [ push_denote_step
        | reflexivity
        | progress simpl in *
        | progress unfold Let_In in *
        | solve [ auto ]
        | congruence ].
Local Ltac t := repeat t_step.

Lemma denote_bind A B v f : denote (@bind A B v f) = denote (f (denote v)).
Proof. induction v; t. Qed.
Hint Rewrite denote_bind : push_denote.

Lemma denote_under_lets A B v f : denote (@under_lets A B v f) = denote (f (denote v)).
Proof. induction v; t. Qed.
Hint Rewrite denote_under_lets : push_denote.

Lemma denote_lift A B (f : A -> B) v : denote (lift f v) = f (denote v).
Proof. unfold lift; t. Qed.
Hint Rewrite denote_lift : push_denote.

Lemma denote_lift2 A B C (f : A -> B -> C) x y : denote (lift2 f x y) = f (denote x) (denote y).
Proof. unfold lift2; t. Qed.
Hint Rewrite denote_lift2 : push_denote.

Module Import List.
  Definition app {A} := lift2 (@List.app A).
  Definition nil {A} := ret (@nil A).
  Definition cons {A} x := lift (@cons A x).
  Hint Unfold app nil cons : push_denote.

  Definition flat_map {A B} (f : A -> LetInM (list B)) (ls : LetInM (list A))
    := under_lets
         ls
         (fix flat_map (l : list A) : LetInM (list B)
          := match l with
             | Lists.List.nil => nil
             | x :: t => app (f x) (flat_map t)
             end).

  Lemma denote_flat_map A B f ls : denote (@flat_map A B f ls) = Lists.List.flat_map (fun x => denote (f x)) (denote ls).
  Proof. unfold flat_map; t; induction (denote ls); t. Qed.
  Hint Rewrite denote_flat_map : push_denote.
End List.

Infix "++" := List.app : letinm_scope.
Infix "::" := List.cons : letinm_scope.
