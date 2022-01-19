Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Crypto.Util.Strings.Ascii.

Local Open Scope list_scope.
Local Open Scope string_scope.


(** TODO: Remove this once we drop support for Coq 8.9 (it's in the stdlib in Coq 8.10 *)
(** *** Conversion to/from [list ascii] *)

Fixpoint string_of_list_ascii (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons ch s => String ch (string_of_list_ascii s)
     end.

Fixpoint list_ascii_of_string (s : string) : list ascii
  := match s with
     | EmptyString => nil
     | String ch s => cons ch (list_ascii_of_string s)
     end.

Lemma string_of_list_ascii_of_string s : string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s as [|? ? IHs]; [ reflexivity | cbn; apply f_equal, IHs ].
Defined.

Lemma list_ascii_of_string_of_list_ascii s : list_ascii_of_string (string_of_list_ascii s) = s.
Proof.
  induction s as [|? ? IHs]; [ reflexivity | cbn; apply f_equal, IHs ].
Defined.

(** *** String concatenation *)

Lemma string_of_list_ascii_app s1 s2 : string_of_list_ascii (s1 ++ s2) = string_of_list_ascii s1 ++ string_of_list_ascii s2.
Proof. induction s1 as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.
Lemma list_ascii_of_string_app s1 s2 : list_ascii_of_string (s1 ++ s2) = (list_ascii_of_string s1 ++ list_ascii_of_string s2)%list.
Proof. induction s1 as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.

Definition lift_list_function (f : list ascii -> list ascii) (s : string) : string
  := string_of_list_ascii (f (list_ascii_of_string s)).

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


(** *** Lower and upper case *)
Definition to_lower (s : string) : string := map Ascii.to_lower s.
Definition to_upper (s : string) : string := map Ascii.to_upper s.

(** *** string reversal *)
(** [rev s] reverses the string [s] *)
(** Note that we use [rev_append . []] for non-quadratic behavior *)
Definition rev : string -> string
  := lift_list_function (fun s => List.rev_append s nil).

Lemma rev_step s
  : rev s
    = match s with
      | EmptyString => EmptyString
      | String x xs => rev xs ++ String x EmptyString
      end.
Proof. destruct s; cbn; rewrite ?List.rev_append_rev, ?List.app_nil_r, ?string_of_list_ascii_app; reflexivity. Qed.

Fixpoint take_while_drop_while (f : ascii -> bool) (s : string) : string * string
  := match s with
     | EmptyString => (EmptyString, EmptyString)
     | String ch s
       => if f ch
          then let '(s1, s2) := take_while_drop_while f s in
               (String ch s1, s2)
          else (EmptyString, String ch s)
     end.

(** *** trimming a string *)
(** [trim s] returns a copy of the argument, without leading and trailing
    whitespace. The characters regarded as whitespace are: ' ',
    '\012', '\n', '\r', and '\t'. *)
Definition ltrim (s : string) : string
  := snd (take_while_drop_while Ascii.is_whitespace s).

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


Lemma append_alt s1 s2 : s1 ++ s2 = string_of_list_ascii (list_ascii_of_string s1 ++ list_ascii_of_string s2).
Proof. rewrite string_of_list_ascii_app, !string_of_list_ascii_of_string; reflexivity. Qed.
Lemma append_empty_r s : s ++ "" = s.
Proof.
  rewrite append_alt; cbn; rewrite List.app_nil_r, string_of_list_ascii_of_string. reflexivity.
Qed.
Lemma append_assoc s1 s2 s3 : s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
Proof.
  rewrite !append_alt, !list_ascii_of_string_of_list_ascii; cbn; rewrite List.app_assoc; reflexivity.
Qed.

Lemma substring_alt n m s
  : substring n m s = string_of_list_ascii (List.firstn m (List.skipn n (list_ascii_of_string s))).
Proof.
  revert n m; induction s as [|ch s IHs]; intros [|n] [|m]; try reflexivity; cbn;
    rewrite IHs; cbn; try reflexivity.
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

(** [startswith prefix s] returns [true] iff [s] starts with [prefix] *)
Definition startswith (prefix s : string) : bool
  := (prefix =? (substring 0 (length prefix) s))%string.

Lemma startswith_correct prefix s
  : startswith prefix s = true <-> substring 0 (length prefix) s = prefix.
Proof.
  pose proof (String.eqb_spec prefix (substring 0 (length prefix) s)) as H'.
  cbv [startswith].
  split; intro H; destruct H'; congruence.
Qed.

(** [endswith postfix s] returns [true] iff [s] ends with [postfix] *)
Definition endswith (postfix s : string) : bool
  := (postfix =? (substring (length s - length postfix) (length postfix) s))%string.

Lemma endswith_correct postfix s
  : endswith postfix s = true <-> substring (length s - length postfix) (length postfix) s = postfix.
Proof.
  pose proof (String.eqb_spec postfix (substring (length s - length postfix) (length postfix) s)) as H'.
  cbv [endswith].
  split; intro H; destruct H'; congruence.
Qed.

Section strip_prefix_cps.
  Context {R} (found : string -> R)
          (remaining : string -> string -> R).

  Fixpoint strip_prefix_cps (sepch : ascii) (sep : string) (s2 : string) {struct s2} : R
    := match s2 with
       | EmptyString => remaining (String sepch sep) s2
       | String x xs
         => if (sepch =? x)%char
            then match sep with
                 | EmptyString => found xs
                 | String sepch sep
                   => strip_prefix_cps sepch sep xs
                 end
            else remaining (String sepch sep) s2
       end.

  Lemma strip_prefix_cps_found sepch sep s2 s2'
        (Hfound : String sepch sep ++ s2' = s2)
    : strip_prefix_cps sepch sep s2 = found s2'.
  Proof using Type.
    revert sepch sep Hfound; induction s2 as [|ch s2 IHs2]; intros; cbn in Hfound; inversion Hfound; clear Hfound; subst.
    destruct sep; cbn [strip_prefix_cps]; now rewrite Ascii.eqb_refl; auto.
  Qed.
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
      [map (fun ch => String ch "") (list_ascii_of_string s)] if [s] is non-empty,
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
       => if (s =? "")%string
          then "" :: nil
          else List.map (fun ch => String ch "") (list_ascii_of_string s)
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
    -> split EmptyString s = List.map (fun ch => String ch "") (list_ascii_of_string s).
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
    revert H; apply PeanoNat.Nat.min_case_strong; cbn; intros; lia. }
  { generalize (split_helper_no_substring sepch sep xs (String x rev_acc)).
    generalize (split_helper sepch sep xs (String x rev_acc)).
    intros ls.
    clear split_helper_no_substring; intro split_helper_no_substring.
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
  destruct (Ascii.eqb_spec sepch' a), sep'; try (clear H' concat_split_helper; congruence).
  { cbn [concat].
    rewrite (concat_split_helper sepch' "" s').
    destruct (split_helper sepch' "" s' "") eqn:H''.
    { apply split_helper_non_empty in H''; exfalso; assumption. }
    { cbn; subst; reflexivity. } }
  { subst.
Abort.

Lemma concat_split sep s : concat sep (split sep s) = s.
Proof.
  destruct sep; cbn.
  { destruct s as [|x xs]; [ reflexivity | cbn ].
    revert x; induction xs as [|x' xs' IHxs]; intro x; cbn; trivial.
    apply f_equal; auto. }
  {
Abort.

Definition replace (from to s : string) : string
  := concat to (split from s).

Notation NewLine := (String Ascii.NewLine "").
Notation CR := (String Ascii.CR "").
Notation LF := (String Ascii.LF "").
Notation CRLF := (String Ascii.CR (String Ascii.LF "")).
Notation Tab := (String Ascii.Tab "").

(** Given a list of strings, breaks all strings within the list at
    CFLF, CF, and LF.  Useful for normalizing a newline-separated list
    of strings, where some substrings might contain newlines *)
Definition split_newlines (s : list string) : list string
  := List.flat_map (split CR) (List.flat_map (split LF) (List.flat_map (split CRLF) s)).

(** Title case makes all words after a space begin with a capital letter *)
Definition capitalize_first_letter (s : string) : string
  := match s with
     | "" => ""
     | String ch s => String (Ascii.to_upper ch) s
     end.
Definition uncapitalize_first_letter (s : string) : string
  := match s with
     | "" => ""
     | String ch s => String (Ascii.to_lower ch) s
     end.
Definition to_title_case_sep (sep : string) (s : string) : string
  := concat sep (List.map capitalize_first_letter (split sep s)).
Definition to_title_case (s : string) : string
  := to_title_case_sep " " s.

Lemma substring_0_0 :
  forall s, substring 0 0 s = "".
Proof. destruct s; reflexivity. Qed.

Lemma append_eq_r_iff s1 s2 s3 :
  s1 ++ s2 = s1 ++ s3 <-> s2 = s3.
Proof.
  induction s1; cbn [append]; split;
    try inversion 1; intros; auto; [ ].
  apply IHs1. auto.
Qed.

Lemma append_eq_prefix :
  forall s1 s2 s3 s4,
    s1 ++ s2 = s3 ++ s4 ->
    prefix s1 s3 = true \/ prefix s3 s1 = true.
Proof.
  induction s1; destruct s3; cbn [append prefix] in *;
    intros; try tauto; [ ].
  match goal with H : String _ _ = String _ _ |- _ =>
                  inversion H; clear H; subst end.
  match goal with |- context [ascii_dec ?x ?y] =>
                  destruct (ascii_dec x y) end;
  subst; try tauto; [ ].
  eapply IHs1; eauto.
Qed.

Definition repeat (ch : ascii) (n : nat) : string
  := string_of_list_ascii (List.repeat ch n).

(** TODO: Better name for this? *)
Definition rfill (ch : ascii) (ls : list string) : list string
  := let len := List.fold_right Nat.max 0 (List.map String.length ls) in
     let fill s := s ++ repeat ch (len - String.length s) in
     List.map fill ls.

Definition strip_trailing_spaces (s : string) : string
  := concat NewLine (List.map rtrim (split NewLine s)).

Fixpoint strip_leading_newlines (s : list string) : list string
  := match s with
     | nil => nil
     | s :: ls => if (rtrim s =? "")%string
                  then strip_leading_newlines ls
                  else s :: ls
     end.

Definition strip_trailing_newlines (s : list string) : list string
  := List.rev_append (strip_leading_newlines (List.rev_append s nil)) nil.
