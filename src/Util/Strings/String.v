Require Import Coq.omega.Omega.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.Strings.Ascii.

Local Open Scope list_scope.
Local Open Scope string_scope.

(** *** String concatenation *)
(** [concat sep sl] concatenates the list of strings [sl], inserting
    the separator string [sep] between each. *)

Definition concat (sep : string) : list string -> string
  := fix concat (sl : list string) : string
       := match sl with
          | nil => EmptyString
          | cons x nil => x
          | cons x xs => x ++ sep ++ concat xs
          end.

(** *** Conversion to and from lists *)
Fixpoint to_list (s : string) : list ascii
  := match s with
     | EmptyString => nil
     | String x xs => cons x (to_list xs)
     end.
Fixpoint of_list (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons x xs => String x (of_list xs)
     end.

Lemma to_of_list s : to_list (of_list s) = s.
Proof. induction s as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.
Lemma of_to_list s : of_list (to_list s) = s.
Proof. induction s as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.

Lemma of_list_app s1 s2 : of_list (s1 ++ s2) = of_list s1 ++ of_list s2.
Proof. induction s1 as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.
Lemma to_list_app s1 s2 : to_list (s1 ++ s2) = (to_list s1 ++ to_list s2)%list.
Proof. induction s1 as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.

Definition lift_list_function (f : list ascii -> list ascii) (s : string) : string
  := of_list (f (to_list s)).

(** *** Mapping over a string *)
(** [map f s] applies function [f] in turn to all the characters of
    [s], creating a new string to return *)
Definition map (f : ascii -> ascii) : string -> string
  := lift_list_function (List.map f).
Lemma map_step f s
  : map f s = match s with
              | EmptyString => EmptyString
              | String x xs => String (f x) (map f xs)
              end.
Proof. destruct s; reflexivity. Qed.

(** *** string reversal *)
(** [rev s] reverses the string [s] *)
Definition rev : string -> string
  := lift_list_function (@List.rev _).

Lemma rev_step s
  : rev s
    = match s with
      | EmptyString => EmptyString
      | String x xs => rev xs ++ String x EmptyString
      end.
Proof. destruct s; cbn; rewrite ?of_list_app; reflexivity. Qed.

(** *** trimming a string *)
(** [trim s] returns a copy of the argument, without leading and trailing
    whitespace. The characters regarded as whitespace are: ' ',
    '\012', '\n', '\r', and '\t'. *)
Fixpoint ltrim (s : string) : string
  := match s with
     | EmptyString => EmptyString
     | String x xs
       => if ((x =? " ") || (x =? NewPage) || (x =? LF) || (x =? CR) || (x =? Tab))%char%bool
          then ltrim xs
          else s
     end.
Definition rtrim (s : string) : string
  := rev (ltrim (rev s)).

Definition trim (s : string) : string
  := rtrim (ltrim s).

(** Finds last occurence of [s1] in [s2], where the first character
    after [s1] is at position less than or equal to [n + 1].  Returns
    the location of the first character of [s1] in that occurence in
    [s2], if it exists. *)

Definition rindex (n : nat) (s1 s2 : string) : option nat :=
  option_map
    (fun n => length s2 - n - length s1)
    (index (length s2 - n - 1) (rev s1) (rev s2)).


Lemma append_alt s1 s2 : s1 ++ s2 = of_list (to_list s1 ++ to_list s2).
Proof. rewrite of_list_app, !of_to_list; reflexivity. Qed.
Lemma append_empty_r s : s ++ "" = s.
Proof.
  rewrite append_alt; cbn; rewrite List.app_nil_r, of_to_list. reflexivity.
Qed.
Lemma append_assoc s1 s2 s3 : s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
Proof.
  rewrite !append_alt, ?to_of_list; cbn; rewrite List.app_assoc; reflexivity.
Qed.

Lemma length_substring n1 n2 s
  : length (substring n1 n2 s) = Nat.min n2 (length s - n1).
Proof.
  revert n1 n2; induction s as [|a s IHs]; intros; cbn.
  { destruct n1, n2; cbn; reflexivity. }
  { destruct n1; [ destruct n2 | ]; cbn; rewrite ?IHs, <- ?Minus.minus_n_O; reflexivity. }
Qed.

Lemma length_append s1 s2 : length (s1 ++ s2) = length s1 + length s2.
Proof.
  revert s1; induction s1 as [|a s1 IHs1]; cbn; congruence.
Qed.

(** *** membership *)
(** [contains n s1 s2] returns [true] if [s1] occurs in [s2] starting
    at position [n], and false otherwise *)
Definition contains (n : nat) (s1 s2 : string) : bool :=
  match index n s1 s2 with
  | Some _ => true
  | None => false
  end.

Section strip_prefix_cps.
  Context {R} (found : string -> R)
          (remaining : string -> string -> R).

  Fixpoint strip_prefix_cps (sepch : ascii) (sep : string) (s2 : string) {struct s2} : R
    := match s2 with
       | EmptyString => remaining (String sepch sep) s2
       | String x xs
         => if ascii_beq sepch x
            then match sep with
                 | EmptyString => found xs
                 | String sepch sep
                   => strip_prefix_cps sepch sep xs
                 end
            else remaining (String sepch sep) s2
       end.
End strip_prefix_cps.

(** *** splitting a string *)
(** [split sep s] returns the list of all (possibly empty) substrings
    of [s] that are delimited by the [sep] character.

    The function's output is specified by the following invariants:

    - The list is not empty.

    - Concatenating its elements using sep as a separator returns a
      string equal to the input

        [concat sep (split sep s) = s]

    - No string in the result contains [sep] as a substring, unless
      [sep] is the empty string, in which case this function returns
      [map (fun ch => String ch "") (to_list s)] if [s] is non-empty,
      and [""::nil] if [s] is also empty. *)

Fixpoint split_helper (sepch : ascii) (sep : string) (s : string) (rev_acc : string) {struct s}
  : list string
  := strip_prefix_cps
       (fun s => rev rev_acc :: split_helper sepch sep s "")
       (fun _ _
        => match s with
           | EmptyString => rev rev_acc :: nil
           | String x xs
             => split_helper sepch sep xs (String x rev_acc)
           end)
       sepch sep s.

Definition split (sep : string) (s : string) : list string
  := match sep with
     | EmptyString
       => if string_beq s EmptyString
          then "" :: nil
          else List.map (fun ch => String ch "") (to_list s)
     | String sepch sep
       => split_helper sepch sep s ""
     end.

Fixpoint split_helper_non_empty sepch sep s rev_acc {struct s}
  : split_helper sepch sep s rev_acc <> nil.
Proof.
  destruct s as [|x xs]; cbn [split_helper];
    [ cbn; clear split_helper_non_empty; congruence | ].
  generalize (split_helper_non_empty sepch sep xs (String x rev_acc)).
  generalize (split_helper sepch sep xs (String x rev_acc)).
  intros ls H.
  generalize (String x xs).
  generalize sep at 2.
  generalize sepch at 2.
  fix H' 3.
  intros sepch' sep' s'.
  destruct s' as [|a s']; cbn; [ assumption | ].
  destruct (sepch' =? a)%char, sep'; try (clear H' split_helper_non_empty; congruence).
  apply H'.
Qed.

Lemma split_non_empty sep s : split sep s <> nil.
Proof.
  unfold split; destruct sep, s; try apply split_helper_non_empty; cbn;
    congruence.
Qed.

Lemma split_empty_empty : split EmptyString EmptyString = "" :: nil.
Proof. reflexivity. Qed.
Lemma split_empty_non_empty s
  : s <> EmptyString
    -> split EmptyString s = List.map (fun ch => String ch "") (to_list s).
Proof.
  intro H; destruct s; cbn; congruence.
Qed.

Fixpoint split_helper_no_substring sepch sep s rev_acc
  : List.Forall (fun s' => contains 0 (rev rev_acc ++ String sepch sep) s' = false)
                (split_helper sepch sep s rev_acc).
Proof.
  destruct s as [|x xs]; cbn [split_helper];
    [ cbn; clear split_helper_no_substring;
      repeat constructor
    | ].
  { unfold contains.
    edestruct index eqn:H; [ | reflexivity ].
    apply index_correct1 in H.
    apply (f_equal length) in H.
    rewrite length_substring, !length_append in H.
    revert H; apply PeanoNat.Nat.min_case_strong; cbn; intros; omega. }
  { generalize (split_helper_no_substring sepch sep xs (String x rev_acc)).
    generalize (split_helper sepch sep xs (String x rev_acc)).
    intros ls.
Abort.
Lemma split_no_substring sep s (Hsep : sep <> EmptyString)
  : List.Forall (fun s' => contains 0 sep s' = false)
                (split sep s).
Proof.
  destruct sep as [|sepch sep]; [ congruence | ].
  unfold split.
Abort.

Fixpoint concat_split_helper sepch sep s rev_acc
  : concat (String sepch sep) (split_helper sepch sep s rev_acc)
    = rev rev_acc ++ s.
Proof.
  destruct s as [|x xs]; cbn [split_helper];
    [ cbn; rewrite append_empty_r; reflexivity | ].
  generalize (concat_split_helper sepch sep xs (String x rev_acc)).
  generalize (split_helper sepch sep xs (String x rev_acc)).
  intros ls H.
  rewrite rev_step, <- append_assoc in H; cbn in H; revert H.
  generalize (String x xs); clear x xs.
  revert sep.
  revert sepch.
  fix H' 3.
  intros sepch' sep' s'; intros.
  destruct s' as [|a s']; cbn; [ assumption | ].
  destruct (sepch' =? a)%char eqn:Hsep, sep'; try (clear H' concat_split_helper; congruence).
  { cbn [concat].
    rewrite (concat_split_helper sepch' "" s').
    destruct (split_helper sepch' "" s' "") eqn:H''.
    { apply split_helper_non_empty in H''; exfalso; assumption. }
    { cbn.
      apply internal_ascii_dec_bl in Hsep; subst; reflexivity. } }
  { apply internal_ascii_dec_bl in Hsep; subst.
Abort.

Lemma concat_split sep s : concat sep (split sep s) = s.
Proof.
  destruct sep; cbn.
  { destruct s as [|x xs]; [ reflexivity | cbn ].
    revert x; induction xs as [|x' xs' IHxs]; intro x; cbn; trivial.
    apply f_equal; auto. }
  {
Abort.
