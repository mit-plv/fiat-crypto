Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.Notations.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope option_scope.
Local Open Scope char_scope.
Local Open Scope string_scope.

Definition ParserAction T := string -> list (T * string).
Delimit Scope parse_scope with parse.
Bind Scope parse_scope with ParserAction.
Definition parse_impossible {T} : ParserAction T
  := fun s => [].
Definition parse_empty : ParserAction unit
  := fun s
     => if s =? ""
        then [(tt, "")]
        else [].
Definition parse_seq_gen {A B C} (f : A -> B -> C) (p1 : ParserAction A) (p2 : ParserAction B) : ParserAction C
  := fun s
     => flat_map
          (fun '(a, s) => List.map (fun '(b, s) => (f a b, s)) (p2 s))
          (p1 s).
Definition parse_alt_gen {A B C} (f : A + B -> C) (p1 : ParserAction A) (p2 : ParserAction B) : ParserAction C
  := fun s
     => ((List.map (fun '(v, s) => (f (inl v), s)) (p1 s))
           ++ List.map (fun '(v, s) => (f (inr v), s)) (p2 s))%list.
Definition parse_alt {A} (p1 p2 : ParserAction A) : ParserAction A
  := parse_alt_gen (fun aa => match aa with inl a => a | inr a => a end) p1 p2.

Notation ε := parse_empty.
Infix "||" := parse_alt : parse_scope.
Infix "||->{ f }" := (parse_alt_gen f) : parse_scope.
Infix ";;->{ f }" := (parse_seq_gen f) : parse_scope.
Infix ";;" := (parse_seq_gen (@pair _ _)) : parse_scope.

Definition parse_ascii (prefix : ascii) : ParserAction ascii
  := fun s
     => match s with
        | EmptyString => []
        | String ch s' => if ascii_beq ch prefix
                          then [(ch, s')]
                          else []
        end.

Coercion parse_ascii : ascii >-> ParserAction.

Definition parse_str (prefix : string) : ParserAction string
  := fun s
     => if startswith prefix s
        then [(prefix, substring (String.length prefix) (String.length s) s)]
        else [].

Coercion parse_str : string >-> ParserAction.

Definition parse_map {A B} (f : A -> B) : ParserAction A -> ParserAction B
  := fun p s
     => List.map (fun '(v, s) => (f v, s)) (p s).

Definition parse_maybe {A} (p : ParserAction A) : ParserAction (option A)
  := (p ||->{ fun v => match v with inl v => Some v | inr _ => None end } "")%parse.

Notation "f ?" := (parse_maybe f) : parse_scope.

Definition option_to_list {A} (v : option A) : list A
  := match v with
     | Some v => [v]
     | None => []
     end.

Definition option_list_to_list {A} (v : option (list A)) : list A
  := match v with
     | Some v => v
     | None => []
     end.

Definition fuel {A} (p : nat -> ParserAction A) : ParserAction A
  := fun s => p (S (String.length s)) s.

Fixpoint parse_plus_fueled {A} (p : ParserAction A) (fuel : nat) : ParserAction (list A)
  := (p ;;->{ @cons _ } (match fuel with
                         | O => fun s => []
                         | S fuel => parse_map option_list_to_list ((parse_plus_fueled p fuel)?)
                         end)).

Definition parse_plus {A} (p : ParserAction A) : ParserAction (list A)
  := fuel (parse_plus_fueled p).

Definition parse_star {A} (p : ParserAction A) : ParserAction (list A)
  := parse_map option_list_to_list ((parse_plus p)?).

Notation "p +" := (parse_plus p) : parse_scope.
Notation "p *" := (parse_star p) : parse_scope.

Definition whitespace : list ascii
  := [" "; "009" (* \t *); "010" (* \n *); "013" (* \r *); "012" (* \f *); "011" (* \v *)]%char.
Definition whitespace_strs : list string
  := Eval compute in List.map (fun ch => String ch "") whitespace.

Definition parse_strs {T} (ls : list (string * T)) : ParserAction T
  := List.fold_left ((fun p2 '(s1, v1) => (s1:string) ||->{ fun v => match v with inl _ => v1 | inr v => v end } p2)%parse)
                    ls
                    parse_impossible.



Definition parse_any_whitespace : ParserAction (list string)
  := Eval cbv [List.fold_right List.fold_left whitespace whitespace_strs List.tl List.hd parse_strs List.combine] in
      (List.fold_left (B:=string) parse_alt (tl whitespace_strs) (hd " " whitespace_strs))*.

Definition strip_whitespace_around {A} (p : ParserAction A) : ParserAction A
  := parse_any_whitespace ;;->{ fun _ v => v }
                          p ;;->{ fun v _ => v }
                          parse_any_whitespace.

Definition parse_list_gen {A} (leftbr sep rightbr : string) (parse : ParserAction A) : ParserAction (list A)
  := (strip_whitespace_around leftbr)
       ;;->{ fun _ v => v }
       ((parse ;;->{ @cons _ }
               (strip_whitespace_around sep ;;->{ fun _ tl => tl } parse)* ))?
       ;;->{ fun v _ => match v with None => [] | Some ls => ls end }
       strip_whitespace_around rightbr.

Definition parse_list {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list_gen "[" ";" "]" parse.

Definition parse_list_Python_style {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list_gen "[" "," "]" parse.

Definition parse_list_Mathematica_style {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list_gen "{" "," "}" parse.

Definition parse_comma_list {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list_gen "" "," "" parse.

Definition parse_semicolon_list {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list_gen "" ";" "" parse.

Definition parse_any_list {A} (parse : ParserAction A) : ParserAction (list A)
  := parse_list parse || parse_list_Python_style parse || parse_list_Mathematica_style parse || parse_comma_list parse || parse_semicolon_list parse.

Fixpoint split_before_first (f : ascii -> bool) (s : string) : string * string
  := match s with
     | EmptyString => (EmptyString, EmptyString)
     | String ch rest
       => if f ch
          then (EmptyString, s)
          else let '(s1, s2) := split_before_first f rest in
               (String ch s1, s2)
     end.

Fixpoint split_before_first_skip (f : ascii -> bool) (s : string) (skip : nat) : string * string
  := match skip, s with
     | 0, _ => split_before_first f s
     | _, EmptyString => (EmptyString, EmptyString)
     | S skip', String ch rest
       => let '(s1, s2) := split_before_first_skip f rest skip' in
          (String ch s1, s2)
     end.

Definition finalize {A} (p : ParserAction A) : string -> option A
  := fun s => match (p ;;->{fun v _ => v} ε)%parse s with
              | [(v, _)] => Some v
              | _ => None
              end.

(*
Definition parse_ch {T} (ls : list (ascii * T)) (s : string) : option (T * string)
  := match s with
     | EmptyString => None
     | String ch s
       => List.fold_right
            (fun '(ch', t) default
             => if ascii_beq ch ch' then Some (t, s) else default)
            None
            ls
     end.
*)
