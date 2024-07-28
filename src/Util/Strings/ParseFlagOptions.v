From Coq Require Import String.
From Coq Require Import List.
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

Variant flag_status := enabled | disabled.
Variant full_flag_status := explicit (_ : flag_status) | elided.
Global Coercion explicit : flag_status >-> full_flag_status.
Coercion bool_of_flag_status (d : flag_status) : bool
  := match d with
     | enabled => true
     | disabled => false
     end.
Definition bool_of_full_flag_status (d : full_flag_status) (default : bool) : bool
  := match d with
     | elided => default
     | explicit d => bool_of_flag_status d
     end.
Global Instance show_flag_status : Show flag_status
  := fun s => match s with
              | enabled => "enabled"
              | disabled => "disabled"
              end.
Global Instance show_full_flag_status : Show full_flag_status
  := fun s => match s with
              | explicit s => show s
              | elided => "elided"
              end.
Variant flag_option_kind := all | alias (_ : list string).
Coercion simple (s : string) : flag_option_kind := alias [s].

Definition preparse_flag_opts (spec : list (string * flag_option_kind)) (args : list string) : list (flag_option_kind * flag_status)
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

Definition aggregate_flag_opts (args : list (flag_option_kind * flag_status)) : full_flag_status (* all status *) * StringMap.t flag_status
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

Fixpoint format_flag_opts (known_options : list string) (status : StringMap.t flag_status) : Tuple.tuple full_flag_status (List.length known_options)
  := match known_options return Tuple.tuple full_flag_status (List.length known_options) with
     | [] => tt
     | opt :: opts
       => Tuple.cons
            match StringMap.find opt status with
            | Some s => explicit s
            | None => elided
            end
            (format_flag_opts opts status)
     end.

Definition post_parse_flag_opts (known_options : list string) (status : full_flag_status (* all status *) * StringMap.t flag_status)
  : full_flag_status (* all status *) * list (string * flag_status) (* unknown options *) * Tuple.tuple full_flag_status (List.length known_options)
  := let '(all_status, status) := status in
     let known_options_set := List.fold_right StringSet.add StringSet.empty known_options in
     let unknown_options := List.filter (fun '(opt, _) => negb (StringSet.mem opt known_options_set)) (StringMap.elements status) in
     (all_status, unknown_options, format_flag_opts known_options status).

Definition post_parse_flag_opts_to_filter (known_options : list string) (status : full_flag_status (* all status *) * StringMap.t flag_status)
  : full_flag_status (* all status *) * list (string * flag_status) (* unknown options *) * (string -> full_flag_status)
  := let '(all_status, status) := status in
     let known_options_set := List.fold_right StringSet.add StringSet.empty known_options in
     let unknown_options := List.filter (fun '(opt, _) => negb (StringSet.mem opt known_options_set)) (StringMap.elements status) in
     (all_status, unknown_options, fun s => match StringMap.find s status with
                                            | Some s => explicit s
                                            | None => elided
                                            end).

Definition parse_flag_opts (spec : list (string * flag_option_kind)) (known_options : list string) (args : list string)
  : full_flag_status (* all status *) * list (string * flag_status) (* unknown options *) * Tuple.tuple full_flag_status (List.length known_options)
  := let res := preparse_flag_opts spec args in
     let res := aggregate_flag_opts res in
     let res := post_parse_flag_opts known_options res in
     res.

Definition parse_flag_opts_to_filter (spec : list (string * flag_option_kind)) (known_options : list string) (args : list string)
  : full_flag_status (* all status *) * list (string * flag_status) (* unknown options *) * (string -> full_flag_status)
  := let res := preparse_flag_opts spec args in
     let res := aggregate_flag_opts res in
     let res := post_parse_flag_opts_to_filter known_options res in
     res.

Definition parse_flag_opts_to_bool_filter (default : bool) (spec : list (string * flag_option_kind)) (known_options : list string) (args : list string)
  : list (string * flag_status) (* unknown options *) * (string -> bool)
  := let '(all_status, unknown, filter) := parse_flag_opts_to_filter spec known_options args in
     (unknown, fun s => bool_of_full_flag_status (filter s) default).
