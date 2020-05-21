(** Coq version of OCaml's Arg module *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.OctalString.
Require Import Coq.Strings.HexString.
Require Import Coq.Strings.BinaryString.
Require Import Crypto.Util.Strings.Ascii.
Require Import Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** Adapted from https://caml.inria.fr/pub/docs/manual-ocaml/libref/Arg.html *)

Inductive base_system := bin | hex | oct | dec.

Inductive spec :=
| Unit
| Bool
| String
| Int (b : list base_system)
| Nat (b : list base_system)
| Tuple (ls : list spec)
| Symbol (syms : list string)
| CustomSymbol {dataT : Type} (syms : list (string * dataT))
| Custom {dataT : Type} (parse : string -> option dataT) (expected_descr : string)
.

Inductive key := long_key (_ : string) | short_key (_ : string).
Definition doc := list string.
Definition usage_msg := list string.

Local Notation type_of_list l ls := (List.fold_left (fun a b : Type => prod a b) ls l).
Local Notation type_of_list' ls
  := match ls return Type with
     | [] => unit
     | l :: ls' => type_of_list l ls'
     end.

Fixpoint spec_data (s : spec) : Type
  := match s with
     | Unit => unit
     | Bool => bool
     | String => string
     | Int b => base_system * Z
     | Nat b => base_system * nat
     | Tuple nil => unit
     | Tuple (l :: ls) => type_of_list (spec_data l) (List.map spec_data ls)
     | Symbol syms => string
     | CustomSymbol dataT syms => dataT
     | Custom dataT parse err_msg => dataT
     end.


Definition spec_data_with_key (s : spec) : Type
  := list (string * spec_data s).

Definition opt_spec_data (opt : bool) (s : spec) : Type
  := if opt then option (spec_data s) else spec_data s.

Definition keyed_spec_list_data (s : list (list key * spec * doc)) : Type
  := type_of_list' (List.map (fun '(_, s, _) => spec_data_with_key s) s).

Definition spec_list_data (opt : bool) (s : list (string * spec * doc)) : Type
  := type_of_list' (List.map (fun '(_, s, _) => opt_spec_data opt s) s).


Fixpoint update_type_of_list (T1 T2 : Type) Ts (f : T1 -> T2) {struct Ts}
  : type_of_list T1 Ts -> type_of_list T2 Ts
  := match Ts return type_of_list T1 Ts -> type_of_list T2 Ts with
     | nil => f
     | cons T Ts
       => @update_type_of_list _ _ Ts (fun '(t1, t) => (f t1, t))
     end.

Fixpoint update_type_of_list2 (T1 T2 T : Type) Ts {struct Ts}
  : (type_of_list T1 Ts -> type_of_list T2 Ts) -> type_of_list (T * T1)%type Ts -> type_of_list (T * T2)%type Ts
  := match Ts return (type_of_list T1 Ts -> type_of_list T2 Ts) -> type_of_list (T * T1)%type Ts -> type_of_list (T * T2)%type Ts with
     | nil => fun f '(t, t1) => (t, f t1)
     | cons T' Ts
       => fun f v
          => let v := @update_type_of_list
                        _ _ Ts (fun '(a, b, c) => (a, (b, c)))
                        v in
             @update_type_of_list
               _ _ Ts (fun '(a, (b, c)) => (a, b, c))
               (@update_type_of_list2 _ _ _ Ts f v)
     end.

Definition cons_type_of_list {x x' xs} (v : x)
  : type_of_list x' xs -> type_of_list x (x' :: xs)
  := update_type_of_list _ _ _ (@pair _ _ v).

Definition cons_type_of_list' {x xs} (v : x)
  : type_of_list' xs -> type_of_list x xs
  := match xs with
     | [] => fun _ => v
     | _ :: _ => @cons_type_of_list _ _ _ v
     end.

Fixpoint uncons_type_of_list {l ls}
  : type_of_list l ls -> l * type_of_list' ls
  := match ls return type_of_list l ls -> l * type_of_list' ls with
     | [] => fun v => (v, tt)
     | l' :: ls
       => fun v
          => let '(v, v', vs) := @uncons_type_of_list (l * l')%type ls v in
             (v, cons_type_of_list' v' vs)
     end.

Fixpoint split_type_of_list_' {l1 ls1 ls2} {struct ls1}
  : type_of_list l1 (ls1 ++ ls2) -> type_of_list l1 ls1 * type_of_list' ls2
  := match ls1 with
     | [] => uncons_type_of_list
     | l1' :: ls1 => @split_type_of_list_' (l1 * l1')%type ls1 ls2
     end.

Definition split_type_of_list' {ls1 ls2}
  : type_of_list' (ls1 ++ ls2) -> type_of_list' ls1 * type_of_list' ls2
  := match ls1 with
     | [] => @pair _ _ tt
     | _ :: _ => split_type_of_list_'
     end.

Local Definition make_symlist prefix sep suffix l
  := match l with
     | nil => "<none>"
     | h :: t => List.fold_left (fun x y => x ++ sep ++ y) t (prefix ++ h) ++ suffix
     end%string.

Local Definition doc_length (d : doc) : nat := List.fold_right Nat.add 0 (List.map String.length d).

Definition print_key (k : key) : string
  := match k with
     | long_key k => "--" ++ k
     | short_key k => "-" ++ k
     end.
Local Definition print_key_list (k : list key) : string
  := match k with
     | nil => "<none>"
     | k => String.concat ", " (List.map print_key k)
     end.

Local Definition print_spec_parts : (list key + string) * spec * doc -> string * list string
  := fun '(k, s, d)
     => if Nat.ltb 0 (doc_length d)
        then (("  "
                 ++ (match k with
                     | inl k => print_key_list k
                     | inr k => k
                     end) ++ " "
                 ++ (match s with
                     | Symbol syms => make_symlist "{" "|" "}" syms
                     | CustomSymbol _ syms => make_symlist "{" "|" "}" (List.map (@fst _ _) syms)
                     | _ => ""
                     end))%string,
              ([hd "" d])
                ++ tl d
                ++ (if Nat.eqb (List.length (tl d)) 0 then nil else [""]))
        else ("", nil).

Definition print_spec_short (k : string) (s : spec) : string
  := match s with
     | Symbol syms => make_symlist "{" "|" "}" syms
     | CustomSymbol _ syms => make_symlist "{" "|" "}" (List.map (@fst _ _) syms)
     | _ => k
     end.

Local Definition help_specs : list (list key * spec * doc)
  := [([short_key "h"; long_key "help"],
       Unit,
       ["Display this list of options"])].

Definition arg_matches_key (arg : string) (k : key) : bool
  := (arg =? print_key k)%string.

Definition arg_matches_key_list (arg : string) (k : list key) : bool
  := List.fold_right orb false (List.map (arg_matches_key arg) k).

Definition parse_bool_opt (s : string) : option bool
  := if (s =? "true")%string
     then Some true
     else if (s =? "false")%string
          then Some false
          else None.

Definition print_base_system (b : base_system) : string
  := match b with
     | bin => "binary"
     | hex => "hexadecimal"
     | oct => "octal"
     | dec => "decimal"
     end.

Definition print_base_systems (b : list base_system) : string
  := match List.rev b with
     | nil => "<magical>"
     | b::nil => print_base_system b
     | b2::b1::nil => print_base_system b1 ++ " or " ++ print_base_system b2
     | b :: bs => String.concat ", " ((List.map print_base_system (List.rev bs)) ++ ["or " ++ print_base_system b]%string)
     end.

Definition parse_int_as_opt (b : base_system) (s : string) : option Z
  := let '(to_Z, of_Z) := match b with
                          | bin => (BinaryString.to_Z, BinaryString.of_Z)
                          | hex => (HexString.to_Z, HexString.of_Z)
                          | oct => (OctalString.to_Z, OctalString.of_Z)
                          | dec => (fun s => Option.sequence_return (Decimal.Z.of_string s) 0%Z, Decimal.Z.to_string)
                          end in
     let v := to_Z s in
     let s' := of_Z v in
     if (s =? s')%string
     then Some v
     else None.

Definition parse_int_opt (b : list base_system) (s : string) : option (base_system * Z)
  := List.fold_right
       (fun b default => match parse_int_as_opt b s with
                         | Some v => Some (b, v)
                         | None => default
                         end)
       None
       b.

Definition parse_nat_opt (b : list base_system) (s : string) : option (base_system * nat)
  := option_map (fun '(b, z) => (b, Z.to_nat z)) (parse_int_opt b s).

Inductive parse_error :=
| help (prog_name : string)
| missing (prog_name : string) (opt_name : string)
| wrong (prog_name : string) (opt_name : string) (got : string) (expected : string)
| no_keyed_arg (prog_name : string) (bad_args : list string)
| missing_prog_name
| too_many_args (prog_name : string) (remaining : list string)
| out_of_fuel (prog_name : string)
| internal_error (prog_name : string) (msg : string).

Definition parse_result T := ErrorT parse_error T.

Fixpoint parse_args_via_spec (s : spec) (argv : list string)
         (missing : parse_error)
         (wrong : string (* got *) -> string (* expected *) -> parse_error)
         {struct s}
  : parse_result (spec_data s * list string)
  := match s, argv return parse_result (spec_data s * list string) with
     | Unit, argv => Success (tt, argv)
     | Bool, arg::argv
       => v <- match parse_bool_opt arg with
               | Some b => Success b
               | None => Error (wrong arg "a boolean")
               end;
            Success (v, argv)
     | String, arg::argv => Success (arg, argv)
     | Int b, arg::argv
       => v <- match parse_int_opt b arg with
               | Some v => Success v
               | None => Error (wrong arg ("a " ++ print_base_systems b ++ " integer")%string)
               end;
            Success (v, argv)
     | Nat b, arg::argv
       => v <- match parse_nat_opt b arg with
               | Some v => Success v
               | None => Error (wrong arg ("a " ++ print_base_systems b ++ " integer")%string)
               end;
            Success (v, argv)
     | Custom dataT parse expected_descr, arg::argv
       => v <- match parse arg with
               | Some v => Success v
               | None => Error (wrong arg expected_descr)
               end;
            Success (v, argv)
     | Tuple nil, argv
       => Success (tt, argv)
     | Tuple (l :: ls), argv
       => lv <- parse_args_via_spec l argv missing wrong;
            let '(lv, argv) := lv in
            list_rect
              (fun ls => forall T : Type,
                   T -> list string -> parse_result (fold_left (fun a b : Type => (a * b)%type) (List.map spec_data ls) T * list string))
              (fun T lv argv => Success (lv, argv))
              (fun x xs rec T lv argv
               => xv <- parse_args_via_spec x argv missing wrong;
                    let '(xv, argv) := xv in
                    rec _ (lv, xv) argv)
              ls
              _
              lv
              argv
     | Symbol syms, arg::argv
       => if List.existsb (fun s => arg =? s)%string syms
          then Success (arg, argv)
          else Error (wrong arg ("one of: " ++ (make_symlist "" " " "" syms))%string)
     | CustomSymbol dataT syms, arg::argv
       => match List.find (fun '(s, v) => arg =? s)%string syms with
          | Some (s, v) => Success (v, argv)
          | None => Error (wrong arg ("one of: " ++ (make_symlist "" " " "" (List.map (@fst _ _) syms)))%string)
          end
     | Bool, nil
     | String, nil
     | Int _, nil
     | Nat _, nil
     | Symbol _, nil
     | CustomSymbol _ _, nil
     | Custom _ _ _, nil
       => Error missing
     end%error.

Record arg_spec :=
  { named_args : list (list key * spec * doc);
    anon_args : list (string * spec * doc);
    anon_opt_args : list (string * spec * doc);
    anon_opt_repeated_arg : option (string * spec * doc) }.

Inductive ShouldBlockIndent := NoIndent | ArbitraryIndent | IndentUpTo (n : nat).
Existing Class ShouldBlockIndent.

Local Definition spaces (n : nat) : string
  := String.string_of_list_ascii (List.repeat " "%char n).

Local Definition maybe_block_indent {should_block_indent : ShouldBlockIndent} (indent : nat) (lhs : string) (rhs : list string)
  := let lhs := (lhs ++ "  ")%string in
     let indent := match should_block_indent with
                   | NoIndent => spaces (String.length lhs)
                   | ArbitraryIndent => spaces indent
                   | IndentUpTo n => spaces (Nat.min indent n)
                   end in
     ((lhs ++ String.substring 0 (String.length indent - String.length lhs) indent ++ hd "" rhs)%string)
       :: List.map (fun s => indent ++ s)%string (tl rhs).

Definition usage_string {should_block_indent : ShouldBlockIndent} : arg_spec -> usage_msg -> list string
  := fun specs err
     => err
          ++ [String.NewLine]
          ++ (let spec_parts
                  := ((List.map (fun '(k, s, d) => print_spec_parts (inl k, s, d)) (specs.(named_args) ++ help_specs))
                        ++ (List.map (fun '(k, s, d) => print_spec_parts (inr k, s, d)) (specs.(anon_args) ++ specs.(anon_opt_args) ++ match specs.(anon_opt_repeated_arg) with Some v => [v] | None => nil end))) in
              let max_length := List.fold_right Nat.max O (List.map String.length (List.map (@fst _ _) spec_parts)) in
              List.flat_map
                (fun '(lhs, rhs) => maybe_block_indent (2 + max_length) lhs rhs)
                spec_parts).

Definition arg_spec_results (s : arg_spec)
  := (keyed_spec_list_data s.(named_args) * spec_list_data false s.(anon_args) * spec_list_data true s.(anon_opt_args) * (match s.(anon_opt_repeated_arg) with None => unit | Some (k, s, d) => list (spec_data s) end))%type.

Definition consume_one_named_arg
         (arg : string)
         (argv : list string)
         (named_arg : list key * spec * doc)
         (missing : parse_error)
         (wrong : string (* got *) -> string (* expected *) -> parse_error)
  : parse_result (option ((spec_data_with_key (snd (fst named_arg)) -> spec_data_with_key (snd (fst named_arg)))
                          * list string (* remaining *)))
  := (if arg_matches_key_list arg (fst (fst named_arg))
      then (res <- parse_args_via_spec (snd (fst named_arg)) argv missing wrong;
           Success (Some ((fun data_so_far => data_so_far ++ [(arg, fst res)]), snd res)))
      else Success None)%error.


Fixpoint consume_named_arg
         (arg : string)
         (argv : list string)
         (named_args : list (list key * spec * doc))
         (missing : string (* key *) -> parse_error)
         (wrong : string (* key *) -> string (* got *) -> string (* expected *) -> parse_error)
         {struct named_args}
  : parse_result ((keyed_spec_list_data named_args -> keyed_spec_list_data named_args) * list string (* remaining *))
  := (match named_args return parse_result ((keyed_spec_list_data named_args -> keyed_spec_list_data named_args) * list string (* remaining *))
      with
      | nil => Success (fun data_so_far => data_so_far, arg::argv)
      | (k, s, d) :: named_args
        => (lv <- consume_one_named_arg arg argv (k, s, d) (missing arg) (wrong arg);
              match lv with
              | Some (upd, argv)
                => Success (update_type_of_list _ _ _ upd, argv)
              | None
                => (rec <- @consume_named_arg arg argv named_args missing wrong;
                      let '(upd, argv) := rec in
                      Success (match named_args
                                     return (keyed_spec_list_data named_args -> keyed_spec_list_data named_args) ->
                                            type_of_list (spec_data_with_key s) (List.map (fun '(_, s0, _) => spec_data_with_key s0) named_args) ->
                                            type_of_list (spec_data_with_key s) (List.map (fun '(_, s0, _) => spec_data_with_key s0) named_args)
                               with
                               | nil => fun _ x => x
                               | cons (k', s', d') xs => update_type_of_list2 _ _ _ _
                               end upd,
                               argv))
              end)
      end%error).

Definition consume_help_or_named_arg
           (arg : string)
           (argv : list string)
           (named_args : list (list key * spec * doc))
           (missing : string (* key *) -> parse_error)
           (wrong : string (* key *) -> string (* got *) -> string (* expected *) -> parse_error)
           (help : parse_error)
  : parse_result ((keyed_spec_list_data named_args -> keyed_spec_list_data named_args) * list string (* remaining *))
  := if arg_matches_key_list arg [short_key "h"; long_key "help"]
     then Error help
     else consume_named_arg arg argv named_args missing wrong.

Definition consume_one_anon_arg (opt : bool) (argv : list string) (s : spec)
           (missing : parse_error)
           (wrong : string (* got *) -> string (* expected *) -> parse_error)
  : parse_result (opt_spec_data opt s * list string (* remaining *))
  := match parse_args_via_spec s argv missing wrong with
     | Success (v, argv)
       => Success (match opt return opt_spec_data opt s with
                   | true => Some v
                   | false => v
                   end,
                   argv)
     | Error err
       => match opt return parse_result (opt_spec_data opt s * list string (* remaining *)) with
          | true => Success (None, argv)
          | false => Error err
          end
     end.

Fixpoint Build_type_of_list_map {A}
         {f l ls}
         (v : l)
         (vf : forall x, f x)
         {struct ls}
  : type_of_list l (@List.map A _ f ls)
  := match ls with
     | [] => v
     | l' :: ls => @Build_type_of_list_map A f _ ls (v, vf _) vf
     end.

Definition cons_spec_list_data {opt s1 s2 s3 ss}
  : opt_spec_data opt s2 -> spec_list_data opt ss -> spec_list_data opt ((s1, s2, s3) :: ss)
  := match ss with
     | [] => fun v _ => v
     | (_, _, _) :: _ => fun v vs => cons_type_of_list v vs
     end.

Definition empty_spec_list_data_opt
           {anon_opt_args : list (string * spec * doc)}
  : spec_list_data true anon_opt_args
  := match anon_opt_args return spec_list_data true anon_opt_args with
     | [] => tt
     | (_, _, _) :: _ => Build_type_of_list_map (f:=fun '(_, _, _) => _) None (fun '(_, _, _) => None)
     end.

Definition empty_opt_repeated_arg {A B} {v : option (A * _ * B)}
  : match v with
    | Some (_, s0, _) => list (spec_data s0)
    | None => unit
    end
  := match v with
     | Some (_, _, _) => []
     | None => tt
     end.

Fixpoint consume_args
         (fuel : nat)
         (argv : list string)
         (s : arg_spec)
         (missing : string (* key *) -> parse_error)
         (wrong : string (* key *) -> string (* got *) -> string (* expected *) -> parse_error)
         (too_many : list string (* remaining *) -> parse_error)
         (internal_error : string (* msg *) -> parse_error)
         (no_keyed_arg : list string (* unrecognized arguments *) -> parse_error)
         (help : parse_error)
         (out_of_fuel : parse_error)
         {struct fuel}
  : parse_result ((keyed_spec_list_data s.(named_args) -> keyed_spec_list_data s.(named_args)) * spec_list_data false s.(anon_args) * spec_list_data true s.(anon_opt_args) * (match s.(anon_opt_repeated_arg) with None => unit | Some (k, s, d) => list (spec_data s) end))%type
  := let initial_len := List.length argv in
     let do_recr s fuel' argv'
         := if list_beq _ String.eqb argv argv'
            then (* no progress *)
              match argv' with
              | [] => Error (internal_error "Encountered empty argument list when doing recursion in consume_args")
              | arg :: _
                => if String.startswith "-" arg
                   then Error (no_keyed_arg [arg])
                   else Error (too_many argv')
              end
            else
              @consume_args fuel' argv' s missing wrong too_many internal_error no_keyed_arg help out_of_fuel in
     let spec := s in
     match argv, fuel with
     | nil, _
       => match s.(anon_args) as saa
                return parse_result (_ * spec_list_data false saa * _ * _)%type
          with
          | [] => Success (fun data => data, tt, empty_spec_list_data_opt, empty_opt_repeated_arg)
          | (k, s, d) :: _ => Error (missing k)
          end
     | cons _ _, O => Error out_of_fuel
     | cons arg argv, S fuel'
       => if String.startswith "-" arg
          then (* named *)
            (res <- consume_help_or_named_arg arg argv s.(named_args) missing wrong help;
            let '(upd0, argv) := res in
            res <- do_recr s fuel' argv;
            let '(upd1, anon_data, anon_opt_data, anon_opt_repeated_data) := res in
            Success (fun data => upd1 (upd0 data), anon_data, anon_opt_data, anon_opt_repeated_data))
          else (* anonymous *)
            let sna := s.(named_args) in
            match s.(anon_args) as saa, s.(anon_opt_args) as saoa, s.(anon_opt_repeated_arg) as saora
                  return parse_result ((keyed_spec_list_data s.(named_args) -> keyed_spec_list_data s.(named_args)) * spec_list_data false saa * spec_list_data true saoa * (match saora with None => unit | Some (k, s, d) => list (spec_data s) end))%type
            with
            | [], [], None => Error (too_many (arg :: argv))
            | [], [], Some (k, s, d)
              => (res <- consume_one_anon_arg false (arg :: argv) s (missing k) (wrong k);
                 let '(v, argv) := res in
                 res <- do_recr {| named_args := sna ; anon_args := [] ; anon_opt_args := [] ; anon_opt_repeated_arg := Some (k, s, d) |} fuel' argv;
                 let '(upd, tt, tt, vs) := res in
                 Success (upd, tt, tt, v :: vs))
            | [], (k, s, d) :: saoa, saora
              => (res <- consume_one_anon_arg true (arg :: argv) s (missing k) (wrong k);
                 let '(v, argv) := res in
                 res <- do_recr {| named_args := sna ; anon_args := [] ; anon_opt_args := saoa ; anon_opt_repeated_arg := saora |} fuel' argv;
                 let '(upd, tt, vs, rest) := res in
                 Success (upd, tt, cons_spec_list_data (opt:=true) v vs, rest))
            | (k, s, d) :: saa, saoa, saora
              => (res <- consume_one_anon_arg false (arg :: argv) s (missing k) (wrong k);
                 let '(v, argv) := res in
                 res <- do_recr {| named_args := sna ; anon_args := saa ; anon_opt_args := saoa ; anon_opt_repeated_arg := saora |} fuel' argv;
                 let '(upd, vs, rest_opt, rest) := res in
                 Success (upd, cons_spec_list_data (opt:=false) v vs, rest_opt, rest))
            end
     end%error.

Definition default_named_result {s} : spec_data_with_key s := nil.

Fixpoint default_named_results' {T : Type} {ss : list (list key * spec * doc)} (t : T) {struct ss}
  : type_of_list T (List.map (fun '(_, s0, _) => spec_data_with_key s0) ss)
  := match ss return type_of_list T (List.map (fun '(_, s0, _) => spec_data_with_key s0) ss) with
     | nil => t
     | cons (_, s, _) ss => @default_named_results' _ ss (t, default_named_result)
     end.

Definition default_named_results {ls}
  : keyed_spec_list_data ls
  := match ls with
     | nil => tt
     | (_, s, _) :: ss => @default_named_results' _ ss default_named_result
     end.

Definition parse_argv (argv : list string) (arg_spec : arg_spec)
  : parse_result (arg_spec_results arg_spec)
  := match argv with
     | nil => Error missing_prog_name
     | prog_name :: argv
       => (res <- consume_args (10 + (List.length argv)) argv arg_spec (missing prog_name) (wrong prog_name) (too_many_args prog_name) (internal_error prog_name) (no_keyed_arg prog_name) (help prog_name) (out_of_fuel prog_name);
          let '(upd, anon_data, anon_opt_data, anon_opt_repeated_data) := res in
          Success (upd default_named_results, anon_data, anon_opt_data, anon_opt_repeated_data))
     end%error.

Definition is_real_error (e : parse_error) : bool := match e with help _ => false | _ => true end.

Definition make_usage (prog_name : string) (spec : arg_spec) : string
  := "USAGE: "
       ++ prog_name ++ " [OPTS...] "
       ++ (String.concat
             " "
             ((List.map (fun '(k, s, d) => print_spec_short k s) spec.(anon_args))
                ++ (List.map (fun '(k, s, d) => "[" ++ print_spec_short k s ++ "]")%string spec.(anon_opt_args))
                ++ match spec.(anon_opt_repeated_arg) with
                   | Some (k, s, d) => ["[" ++ print_spec_short k s ++ "...]"]%string
                   | None => nil
                   end)).

Definition show_list_parse_error {should_block_indent : ShouldBlockIndent} (spec : arg_spec) (err : parse_error) : list string
  := let mk_usage prog_name err := (usage_string spec (err ++ [String.NewLine; make_usage prog_name spec]) ++ [String.NewLine])%list in
     match err with
     | help prog_name
       => mk_usage prog_name []
     | missing prog_name opt_name
       => mk_usage prog_name [prog_name ++ ": option '" ++ opt_name ++ "' needs an argument."]%string
     | wrong prog_name opt_name got expected
       => mk_usage prog_name [prog_name ++ ": wrong argument '" ++ got ++ "'; option '" ++ opt_name ++ "' expects " ++ expected ++ "."]%string
     | missing_prog_name => ["Empty argv" ++ String.NewLine]%string
     | too_many_args prog_name remaining
       => mk_usage prog_name [prog_name ++ ": unrecognized arguments: " ++ String.concat " " remaining]%string
     | no_keyed_arg prog_name invalid_args
       => mk_usage prog_name [prog_name ++ ": unrecognized keyed arguments: " ++ String.concat " " invalid_args]%string
     | internal_error prog_name msg
       => mk_usage prog_name [prog_name ++ ": Internal error (please report as a bug): " ++ msg]%string
     | out_of_fuel prog_name
       => mk_usage prog_name [prog_name ++ ": Internal fatal error while parsing command line arguments: Out of fuel (probably a bugged command line argument specification)"]%string
     end.

Instance default_should_block_indent : ShouldBlockIndent := ArbitraryIndent.
