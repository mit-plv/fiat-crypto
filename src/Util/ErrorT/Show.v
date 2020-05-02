Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ErrorT.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.

Global Instance show_ErrorT {ErrT T} {show_ErrT : Show ErrT} {show_T : Show T}
  : Show (@ErrorT ErrT T)
  := fun with_parens v
     => maybe_wrap_parens
          with_parens
          match v with
          | Success v => "Success " ++ show true v
          | Error msg => "Error " ++ show true msg
          end.

Global Instance show_lines_ErrorT {ErrT T} {show_lines_ErrT : ShowLines ErrT} {show_lines_T : ShowLines T}
  : ShowLines (@ErrorT ErrT T)
  := fun with_parens v
     => maybe_wrap_parens_lines
          with_parens
          (let '(prefix, lines)
               := match v with
                  | Success v => ("Success", show_lines true v)
                  | Error msg => ("Error", show_lines true msg)
                  end in
           match lines with
           | [] => [prefix ++ " ()"]
           | [line] => [prefix ++ " " ++ line]
           | lines => (([prefix ++ " ("]%string)
                         ++ (List.map (fun s => "  " ++ s)%string lines)
                         ++ [")"])%list
           end).
