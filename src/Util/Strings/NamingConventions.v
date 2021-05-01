Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Listable.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive name_case_kind := lower | upper.
Record word_case_data := { first_letter_case : name_case_kind ; rest_letters_case : name_case_kind }.
Record capitalization_data := { separator : string ; first_word_case : word_case_data ; rest_words_case : word_case_data }.
Record capitalization_convention := { capitalization_convention_data :> capitalization_data ; only_lower_first_letters : bool }.

Derive name_case_kind_Listable SuchThat (@FinitelyListable name_case_kind name_case_kind_Listable) As name_case_kind_FinitelyListable.
Proof. prove_ListableDerive. Qed.
Global Existing Instances name_case_kind_Listable name_case_kind_FinitelyListable.

(* M-x query-replace-regex RET \([^ ]+\) => _ RET \1 => "\1" *)
Global Instance show_name_case_kind : Show name_case_kind
  := fun v
     => match v with
        | lower => "lower"
        | upper => "upper"
        end.
Global Instance show_lvl_name_case_kind : ShowLevel name_case_kind := show_name_case_kind.

Definition parse_name_case_kind_list : list (string * name_case_kind)
  := Eval vm_compute in
      List.map
        (fun v => (show v, v))
        (list_all name_case_kind).

Global Instance show_word_case_data : Show word_case_data
  := fun v
     => ("{| first_letter_case := " ++ show v.(first_letter_case))
          ++ " ; rest_letters_case := " ++ show v.(rest_letters_case) ++ " |}".
Global Instance show_lvl_word_case_data : ShowLevel word_case_data := show_word_case_data.

Global Instance show_capitalization_data : Show capitalization_data
  := fun v
     => ("{| separator := " ++ show v.(separator))
          ++ (" ; first_word_case := " ++ show v.(first_word_case))
          ++ " ; rest_words_case := " ++ show v.(rest_words_case) ++ " |}".
Global Instance show_lvl_capitalization_data : ShowLevel capitalization_data := show_capitalization_data.

Global Instance show_capitalization_convention : Show capitalization_convention
  := fun v
     => ("{| capitalization_convention_data := " ++ show v.(capitalization_convention_data))
          ++ " ; only_lower_first_letters := " ++ show v.(only_lower_first_letters) ++ " |}".
Global Instance show_lvl_capitalization_convention : ShowLevel capitalization_convention := show_capitalization_convention.

Definition case_adjust_ascii (data : name_case_kind) : Ascii.ascii -> Ascii.ascii
  := match data with
     | lower => Ascii.to_lower
     | upper => Ascii.to_upper
     end.
Definition case_adjust_string (data : name_case_kind) : string -> string
  := match data with
     | lower => String.to_lower
     | upper => String.to_upper
     end.
Definition case_adjust_word (only_lower_first_char : bool) (data : word_case_data) (s : string) : string
  := match s with
     | EmptyString => EmptyString
     | String ch rest => String (case_adjust_ascii data.(first_letter_case) ch)
                                (let adjusted := case_adjust_string data.(rest_letters_case) rest in
                                 match only_lower_first_char, data.(rest_letters_case) with
                                 | _, upper => adjusted
                                 | true, lower => rest
                                 | false, lower => adjusted
                                 end)
     end.
Definition case_adjust_word_list (only_lower_first_char : bool) (data : capitalization_data) (words : list string) : list string
  := match words with
     | [] => []
     | firstword :: restwords
       => (case_adjust_word only_lower_first_char data.(first_word_case) firstword)
            :: List.map (case_adjust_word only_lower_first_char data.(rest_words_case)) restwords
     end.
Definition case_adjust_words (only_lower_first_char : bool) (data : capitalization_data) (words : list string) : string
  := String.concat data.(separator) (case_adjust_word_list only_lower_first_char data words).

Fixpoint split_before_gen (f : Ascii.ascii -> bool) (s : string) : list string
  := match s with
     | EmptyString => []
     | String ch rest
       => match split_before_gen f rest with
          | [] => [String ch EmptyString]
          | EmptyString :: xs
            => String ch EmptyString :: xs
          | String ch' _ as x :: xs
            => if f ch'
               then String ch EmptyString :: x :: xs
               else String ch x :: xs
          end
     end.

Definition split_before_uppercase (s : string) : list string := split_before_gen Ascii.is_upper s.
Definition split_before_lowercase (s : string) : list string := split_before_gen Ascii.is_lower s.

Lemma concat_split_before_gen f s : concat "" (split_before_gen f s) = s.
Proof.
  induction s; cbn; [ reflexivity | ]; edestruct split_before_gen; cbn in *; subst; [ reflexivity | ].
  break_innermost_match; reflexivity.
Qed.

Lemma concat_split_before_uppercase s : concat "" (split_before_uppercase s) = s.
Proof. apply concat_split_before_gen. Qed.
Lemma concat_split_before_lowercase s : concat "" (split_before_lowercase s) = s.
Proof. apply concat_split_before_gen. Qed.

Definition before_word_splittable (data : word_case_data) : bool
  := match data.(first_letter_case), data.(rest_letters_case) with
     | upper, lower
     | lower, upper
       => true
     | upper, upper
     | lower, lower
       => false
     end.
Definition splitter_function (data : capitalization_data) : option (string -> list string)
  := if (data.(separator) =? "")%string
     then match data.(first_word_case).(first_letter_case), data.(first_word_case).(rest_letters_case),
                data.(rest_words_case).(first_letter_case), data.(rest_words_case).(rest_letters_case)
          with
          | _, lower, upper, lower => Some split_before_uppercase
          | _, upper, lower, upper => Some split_before_lowercase
          | _, _, _, _ => None
          end
     else Some (String.split data.(separator)).

Definition split_case_to_words (data : capitalization_data) (s : string) : if splitter_function data then list string else unit
  := match splitter_function data as f return if f then _ else _ with
     | Some f => f s
     | None => tt
     end.

Definition convert_case (from : capitalization_data) (to : capitalization_convention) (s : string) : if splitter_function from then string else unit
  := match splitter_function from as f return if f then _ else _ with
     | Some f => case_adjust_words to.(only_lower_first_letters) to (f s)
     | None => tt
     end.

Module Word.
  Notation lowercase := {| first_letter_case := lower ; rest_letters_case := lower |}.
  Notation uppercase := {| first_letter_case := upper ; rest_letters_case := upper |}.
  Notation titlecase := {| first_letter_case := upper ; rest_letters_case := lower |}.
End Word.

Notation flatcase := {| separator := "" ; first_word_case := Word.lowercase ; rest_words_case := Word.lowercase |}.
Notation UPPERFLATCASE := {| separator := "" ; first_word_case := Word.uppercase ; rest_words_case := Word.uppercase |}.
Notation camelCase := {| separator := "" ; first_word_case := Word.lowercase ; rest_words_case := Word.titlecase |}.
Notation UpperCamelCase := {| separator := "" ; first_word_case := Word.titlecase ; rest_words_case := Word.titlecase |}.
Notation snake_case := {| separator := "_" ; first_word_case := Word.lowercase ; rest_words_case := Word.lowercase |}.
Notation SCREAMING_SNAKE_CASE := {| separator := "_" ; first_word_case := Word.uppercase ; rest_words_case := Word.uppercase |}.
Notation camel_Snake_Case := {| separator := "_" ; first_word_case := Word.lowercase ; rest_words_case := Word.titlecase |}.
Notation Pascal_Snake_Case := {| separator := "_" ; first_word_case := Word.titlecase ; rest_words_case := Word.titlecase |}.
Notation dash_case := {| separator := "-" ; first_word_case := Word.lowercase ; rest_words_case := Word.lowercase |}.
Notation doner_case := {| separator := "|" ; first_word_case := Word.lowercase ; rest_words_case := Word.lowercase |}.
Notation TRAIN_CASE := {| separator := "-" ; first_word_case := Word.uppercase ; rest_words_case := Word.uppercase |}.
Notation Train_Case := {| separator := "-" ; first_word_case := Word.titlecase ; rest_words_case := Word.titlecase |}.

Definition parse_capitalization_data_pre_list : list (capitalization_data * list string)
  := [
      (flatcase, ["flat case"; "flatcase"])
      ; (UPPERFLATCASE, ["upper flat case"; "UPPER FLAT CASE"; "UPPERFLATCASE"])
      ; (camelCase, ["camelCase"; "lower camelCase"; "lowerCamelCase"; "dromedaryCase"])
      ; (UpperCamelCase, ["PascalCase"; "UpperCamelCase"; "Upper Camel Case"; "StudlyCase"])
      ; (snake_case, ["snake_case"; "pothole_case"])
      ; (SCREAMING_SNAKE_CASE, ["SCREAMING_SNAKE_CASE"; "MACRO_CASE"; "CONSTANT_CASE"])
      ; (camel_Snake_Case, ["camel_Snake_Case"])
      ; (Pascal_Snake_Case, ["Pascal_Snake_Case"])
      ; (dash_case, ["kebab-case"; "dash-case"; "lisp-case"])
      ; (doner_case, ["doner|case"])
      ; (TRAIN_CASE, ["TRAIN-CASE"; "COBOL-CASE"; "SCREAMING-KEBAB-CASE"])
      ; (Train_Case, ["Train-Case"; "HTTP-Header-Case"])
    ].

Definition parse_capitalization_data_list : list (string * capitalization_data)
  := Eval compute in
      List.flat_map
        (fun '(v, ls) => List.map (fun s => (s, v)) ls)
        parse_capitalization_data_pre_list.
Definition parse_capitalization_data : ParserAction capitalization_data
  := parse_strs parse_capitalization_data_list.

Definition parse_capitalization_data_strict : string -> option capitalization_data
  := finalize parse_capitalization_data.
