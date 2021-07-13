Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ErrorT.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.

Global Instance show_lvl_ErrorT {ErrT T} {show_ErrT : ShowLevel ErrT} {show_T : ShowLevel T}
  : ShowLevel (@ErrorT ErrT T)
  := fun v
     => match v with
        | Success v => show_lvl_app (fun 'tt => "Success") v
        | Error msg => show_lvl_app (fun 'tt => "Error") msg
        end.
Global Instance show_ErrorT {ErrT T} {show_ErrT : Show ErrT} {show_T : Show T} : Show (@ErrorT ErrT T)
  := let _ := @ShowLevel_of_Show ErrT in
     let _ := @ShowLevel_of_Show T in
     _.

Global Instance show_lines_ErrorT {ErrT T} {show_lines_ErrT : ShowLines ErrT} {show_lines_T : ShowLines T}
  : ShowLines (@ErrorT ErrT T)
  := fun v
     => let '(prefix, lines)
            := match v with
               | Success v => ("Success", show_lines v)
               | Error msg => ("Error", show_lines msg)
               end in
        match lines with
        | [] => [prefix ++ " ()"]
        | [line] => [prefix ++ " " ++ line]
        | lines => (([prefix ++ " ("]%string)
                      ++ (List.map (fun s => "  " ++ s)%string lines)
                      ++ [")"])%list
        end.
