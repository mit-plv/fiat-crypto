Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.FSets.FMapString.
Require Import Crypto.Util.MSets.MSetString.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Variant debug_status := enabled | disabled.
Variant full_debug_status := explicit (_ : debug_status) | elided.
Global Coercion explicit : debug_status >-> full_debug_status.
Coercion bool_of_debug_status (d : debug_status) : bool
  := match d with
     | enabled => true
     | disabled => false
     end.
Definition bool_of_full_debug_status (d : full_debug_status) (default : bool) : bool
  := match d with
     | elided => default
     | explicit d => bool_of_debug_status d
     end.
Global Instance show_debug_status : Show debug_status
  := fun s => match s with
              | enabled => "enabled"
              | disabled => "disabled"
              end.
Global Instance show_full_debug_status : Show full_debug_status
  := fun s => match s with
              | explicit s => show s
              | elided => "elided"
              end.
Variant debug_option_kind := all | alias (_ : list string).
Coercion simple (s : string) : debug_option_kind := alias [s].

Definition preparse_debug_opts (spec : list (string * debug_option_kind)) (args : list string) : list (debug_option_kind * debug_status)
  := let spec := List.fold_left (fun acc '(s, k) => StringMap.add s k acc) spec (@StringMap.empty _) in
     let args := List.filter (fun s => negb (s =? "")) (List.map String.trim (List.flat_map (String.split ",") args)) in
     List.map
       (fun arg
        => let '(prefix, shortened_arg) := (substring 0 1 arg, substring 1 (String.length arg) arg) in
           let '(status, arg) := if (prefix =? "-")%string
                                 then (disabled, shortened_arg)
                                 else if (prefix =? "+")%string
                                      then (enabled, shortened_arg)
                                      else (enabled, arg) in
           (Option.value (StringMap.find arg spec) (simple arg), status))
       args.

Definition aggregate_debug_opts (args : list (debug_option_kind * debug_status)) : full_debug_status (* all status *) * StringMap.t debug_status
  := List.fold_left
       (fun '(all_status, acc) '(k, s)
        => match k with
           | all => (explicit s, StringMap.map (fun _ => s) acc)
           | alias ls
             => (all_status,
                  List.fold_left
                    (fun acc arg => StringMap.add arg s acc)
                    ls
                    acc)
           end)
       args
       (elided, @StringMap.empty _).

Fixpoint format_debug_opts (known_options : list string) (status : StringMap.t debug_status) : Tuple.tuple full_debug_status (List.length known_options)
  := match known_options return Tuple.tuple full_debug_status (List.length known_options) with
     | [] => tt
     | opt :: opts
       => Tuple.cons
            match StringMap.find opt status with
            | Some s => explicit s
            | None => elided
            end
            (format_debug_opts opts status)
     end.

Definition post_parse_debug_opts (known_options : list string) (status : full_debug_status (* all status *) * StringMap.t debug_status)
  : full_debug_status (* all status *) * list (string * debug_status) (* unknown options *) * Tuple.tuple full_debug_status (List.length known_options)
  := let '(all_status, status) := status in
     let known_options_set := List.fold_right StringSet.add StringSet.empty known_options in
     let unknown_options := List.filter (fun '(opt, _) => negb (StringSet.mem opt known_options_set)) (StringMap.elements status) in
     (all_status, unknown_options, format_debug_opts known_options status).

Definition parse_debug_opts (spec : list (string * debug_option_kind)) (known_options : list string) (args : list string)
  : full_debug_status (* all status *) * list (string * debug_status) (* unknown options *) * Tuple.tuple full_debug_status (List.length known_options)
  := let res := preparse_debug_opts spec args in
     let res := aggregate_debug_opts res in
     let res := post_parse_debug_opts known_options res in
     res.
