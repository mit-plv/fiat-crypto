Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.QArith.QArith_base.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Strings.Decimal.
Import ListNotations. Local Open Scope list_scope. Local Open Scope string_scope.

Class Show T := show : bool (* parens *) -> T -> string.
Class ShowLines T := show_lines : bool -> T -> list string.

Definition maybe_wrap_parens (parens : bool) (s : string)
  := if parens then "(" ++ s ++ ")" else s.

Definition maybe_wrap_parens_lines (parens : bool) (s : list string)
  := match s, parens with
     | s, false => s
     | nil, _ => nil
     | [s], _ => [maybe_wrap_parens parens s]
     | s, true => "(" :: List.map (String " ") s ++ [")"]
     end%list.

Global Instance show_lines_of_show {T} `{Show T} : ShowLines T | 1000
  := fun parens v => [show parens v].

Global Instance show_unit : Show unit := fun _ _ => "tt".
Global Instance show_True : Show True := fun _ _ => "I".
Global Instance show_False : Show False := fun _ pf => match pf with end.
Global Instance show_Empty_set : Show Empty_set := fun _ pf => match pf with end.
Global Instance show_bool : Show bool := fun _ b => if b then "true" else "false".
Global Instance show_option {T} `{Show T} : Show (option T)
  := fun p v
     => match v with
       | Some v
         => maybe_wrap_parens
             p
             ("Some " ++ show true v)
       | None => "None"
       end.
Global Instance show_list {T} `{Show T} : Show (list T)
  := fun _ ls => "[" ++ String.concat ", " (List.map (show false) ls) ++ "]".
Global Instance show_prod {A B} `{Show A, Show B} : Show (A * B)
  := fun _ '(a, b) => "(" ++ show false a ++ ", " ++ show true b ++ ")".
Global Instance show_string : Show string := fun _ s => """" ++ s ++ """".
Global Instance show_ascii : Show ascii := fun _ ch => String "'" (String ch "'").

Global Instance show_lines_option {T} `{ShowLines T} : ShowLines (option T)
  := fun p v
     => match v with
        | Some v
          => maybe_wrap_parens_lines
               p
               match show_lines true v with
               | [s] => ["Show " ++ s]
               | s => "Show"::List.map (String " ") s
               end
        | None => ["None"]
        end.
Global Instance show_lines_list {T} `{ShowLines T} : ShowLines (list T)
  := fun _ ls
     => let ls := List.map (show_lines false) ls in
        (if List.forallb
              (fun lines => Nat.eqb (List.length lines) 1)
              ls
         then ["[" ++ String.concat ", " (List.map (String.concat String.NewLine) ls) ++ "]"]%string
         else ["["] ++ match ls with
                       | nil => ["]"]
                       | x :: xs
                         => (List.map (String " ") x)
                              ++ (List.flat_map
                                    (fun x' => "," :: List.map (String " ") x')
                                    xs)
                              ++ ["]"]
                       end)%list.
Global Instance show_lines_prod {A B} `{ShowLines A, ShowLines B} : ShowLines (A * B)
  := fun _ '(a, b)
     => match show_lines false a, show_lines true b with
        | [a], [b] => ["(" ++ a ++ ", " ++ b ++ ")"]%string
        | a, b => ["("] ++ a ++ [", "] ++ b ++ [")"]
        end%list.

Module Export Decimal.
  Global Instance show_positive : Show positive
    := fun _ p
       => decimal_string_of_pos p.
  Global Instance show_N : Show N
    := fun _ n
       => match n with
         | N0 => "0"
         | Npos p => show false p
         end.
  Global Instance show_nat : Show nat
    := fun _ n => show false (N.of_nat n).
  Global Instance show_Z : Show Z
    := fun _ z
       => match z with
         | Zneg p => "-" ++ show false p
         | Z0 => "0"
         | Zpos p => show false p
         end.
  Definition show_Q_frac : Show Q
    := fun parens q
       => if (Qden q =? 1)%positive
          then show parens (Qnum q)
          else maybe_wrap_parens
                 parens
                 (show true (Qnum q) ++ " / " ++ show true (Qden q)).
  Global Instance show_Q : Show Q
    := fun parens q
       => if (Qden q =? 1)%positive
          then show parens (Qnum q)
          else let lg10 := Z.log10 (Z.pos (Qden q)) in
               if (10^lg10 =? Z.pos (Qden q))%Z
               then let lg10 := Z.to_nat lg10 in
                    let int_part := show_Z false (Qnum q / Z.pos (Qden q))%Z in
                    let dec_part := show_Z false (Z.abs (Qnum q) mod (Z.pos (Qden q)))%Z in
                    int_part
                      ++ "."
                      ++ String.of_list (List.repeat "0"%char (lg10 - length dec_part)) ++ dec_part
               else
                 show_Q_frac parens q.
End Decimal.

Module Hex.
  Definition show_positive : Show positive
    := fun _ p => HexString.of_pos p.
  Definition show_Z : Show Z
    := fun _ z => HexString.of_Z z.
  Definition show_N : Show N
    := fun _ n
       => match n with
         | N0 => "0"
         | Npos p => show_positive false p
         end.
  Definition show_nat : Show nat
    := fun _ n => show_N false (N.of_nat n).
  Definition show_Q : Show Q
    := fun parens q
       => if (Qden q =? 1)%positive
         then show_Z parens (Qnum q)
         else maybe_wrap_parens
                parens
                (show_Z true (Qnum q) ++ " / " ++ show_positive true (Qden q)).
End Hex.

Module PowersOfTwo.
  Fixpoint show_Z_up_to' (max : nat) (max_dec : Z) (neg : bool) : Show Z
    := match max with
       | O => Hex.show_Z
       | S n'
         => fun with_parens z
            => if z <? max_dec
               then Decimal.show_Z with_parens z
               else if Z.abs (2^Z.log2_up z - z) <=? Z.abs (z - 2^Z.log2 z)
                    then let log2z := Z.log2_up z in
                         let z := 2^log2z - z in
                         if z =? 0
                         then "2^" ++ Decimal.show_Z false log2z
                         else maybe_wrap_parens
                                with_parens
                                ("2^" ++ Decimal.show_Z false log2z
                                      ++ (if neg then "+" else "-")
                                      ++ show_Z_up_to' n' max_dec (negb neg) false z)
                    else let log2z := Z.log2 z in
                         let z := z - 2^log2z in
                         if z =? 0
                         then "2^" ++ Decimal.show_Z false log2z
                         else maybe_wrap_parens
                                with_parens
                                ("2^" ++ Decimal.show_Z false log2z
                                      ++ (if neg then "-" else "+")
                                      ++ show_Z_up_to' n' max_dec neg false z)
       end%Z%string.

  Definition show_Z_up_to (max : nat) (max_dec : Z) : Show Z
    := fun with_parens z
       => (if z <? 0
           then "-" ++ (show_Z_up_to' max max_dec false true (-z))
           else if z =? 0
                then "0"
                else show_Z_up_to' max max_dec false with_parens z)%Z.

  Definition show_Z : Show Z
    := fun with_parens z => show_Z_up_to (S (Z.to_nat (Z.log2_up (Z.abs z)))) 32 with_parens z.
End PowersOfTwo.
