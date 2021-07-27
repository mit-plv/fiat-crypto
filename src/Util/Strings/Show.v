Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.QArith.QArith_base.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Coq.Strings.HexString.
Require Import Crypto.Util.Strings.Decimal.
Require Export Crypto.Util.Level.
Import ListNotations. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope string_scope.
Local Open Scope level_scope.

Class ShowLevel T := show_lvl : T -> Level -> string.
Class ShowLevel2 A B := show_lvl2 : A -> B -> Level -> string.
Class ShowLevel3 A B C := show_lvl3 : A -> B -> C -> Level -> string.
Class Show T := show : T -> string.
Class ShowLines T := show_lines : T -> list string.
Definition show_lvl2_explicit (F : ShowLevel unit -> ShowLevel unit -> ShowLevel2 unit unit)
  : (Level -> string) -> (Level -> string) -> (Level -> string)
  := fun show_f show_x => F (fun 'tt => show_f) (fun 'tt => show_x) tt tt.
Notation app_lvl := (Level.level 10) (only parsing).
Notation term_lvl := (Level.level 200) (only parsing).
Notation pair_lvl := (Level.prev term_lvl) (only parsing).
Notation pair_assoc := LeftAssoc (only parsing).
Notation opp_lvl := (Level.level 35) (only parsing).
Notation impl_lvl := (Level.level 99) (only parsing).
Notation impl_assoc := RightAssoc (only parsing).
Notation iff_lvl := (Level.level 95) (only parsing).
Notation iff_assoc := RightAssoc (only parsing).
Notation lneg_lvl := (Level.level 75) (only parsing).
Notation rel_lvl := (Level.level 70) (only parsing).
Notation rel_assoc := RightAssoc (only parsing).
Notation add_lvl := (Level.level 50) (only parsing).
Notation add_assoc := FullyAssoc (only parsing).
Notation sub_lvl := (Level.level 50) (only parsing).
Notation sub_assoc := LeftAssoc (only parsing).
Notation mul_lvl := (Level.level 40) (only parsing).
Notation mul_assoc := FullyAssoc (only parsing).
Notation div_lvl := (Level.level 40) (only parsing).
Notation div_assoc := NoAssoc (only parsing).
Notation mod_lvl := (Level.level 40) (only parsing).
Notation mod_assoc := NoAssoc (only parsing).
Notation andb_lvl := (Level.level 40) (only parsing).
Notation andb_assoc := FullyAssoc (only parsing).
Notation orb_lvl := (Level.level 40) (only parsing).
Notation orb_assoc := FullyAssoc (only parsing).
Notation pow_lvl := (Level.level 30) (only parsing).
Notation pow_assoc := RightAssoc (only parsing).

Global Instance Show_of_ShowLevel {T} `{ShowLevel T} : Show T | 1000 := fun t => show_lvl t term_lvl.
Definition ShowLevel_of_Show {T} `{Show T} : ShowLevel T := fun t _ => show t.
Definition ShowLines_of_Show {T} `{Show T} : ShowLines T := fun t => [show t].
Global Instance Show_of_ShowLines {T} `{ShowLines T} : Show T | 1000 := fun t => String.concat String.NewLine (show_lines t).
Global Coercion Show_of_ShowLevel : ShowLevel >-> Show.
Global Coercion ShowLevel_of_Show : Show >-> ShowLevel.

Global Instance show_lvl_const : ShowLevel (unit -> string) := fun f _ => f tt.
Global Instance show_lvl_id : ShowLevel (Level -> string) := fun f lvl => f lvl.

Definition maybe_wrap_parens (parens : bool) (s : string)
  := if parens then "(" ++ s ++ ")" else s.
Definition show_wrap_parens (plvl : Level) {A} `{ShowLevel A} : ShowLevel A
  := fun a lvl => if lvl <? plvl then "(" ++ show_lvl a term_lvl ++ ")" else show_lvl a lvl.
Definition lvl_wrap_parens (plvl : Level) (s : string) : Level -> string
  := show_wrap_parens plvl (fun 'tt => s).
(** wrap with parentheses if the level is negative *)
Definition neg_wrap_parens_with_lvl (f : Level -> string) : Level -> string
  := show_wrap_parens 0 f.
Definition neg_wrap_parens (f : string) : Level -> string
  := neg_wrap_parens_with_lvl (fun _ => f).
Definition ShowLevel2_binop_assoc (assoc : Associativity) (binop_lvl : Level) (binop : string) {A B}
           `{ShowLevel A, ShowLevel B}
  : ShowLevel2 A B
  := fun a b
     => lvl_wrap_parens
          binop_lvl
          (let lvl := binop_lvl in
           match assoc with
           | LeftAssoc => show_lvl a lvl ++ binop ++ show_lvl b (Level.next lvl)
           | RightAssoc => show_lvl a (Level.next lvl) ++ binop ++ show_lvl b lvl
           | NoAssoc => show_lvl a (Level.next lvl) ++ binop ++ show_lvl b (Level.next lvl)
           | FullyAssoc => show_lvl a lvl ++ binop ++ show_lvl b lvl
           | ExplicitAssoc lvl_l lvl_r => show_lvl a lvl_l ++ binop ++ show_lvl b lvl_r
           end).
Definition show_lvl_binop (assoc : Associativity) (binop_lvl : Level) {A B} `{SA : ShowLevel A, SB : ShowLevel B}
  : A -> string -> B -> Level -> string
  := fun a binop b => ShowLevel2_binop_assoc assoc binop_lvl binop a b.
Definition show_lvl_app {A B} `{ShowLevel A, ShowLevel B} : ShowLevel2 A B
  := ShowLevel2_binop_assoc LeftAssoc app_lvl " ".
Definition show_lvl_app2 {A B C} `{ShowLevel A, ShowLevel B, ShowLevel C} : ShowLevel3 A B C
  := fun a b c => show_lvl_app (show_lvl_app a b) c.
Definition show_lvl_preop_assoc (assoc : Associativity) (op_lvl : Level) {A}
           `{ShowLevel A}
  : string -> A -> Level -> string
  := fun preop a => show_lvl_binop assoc op_lvl (fun 'tt => "") preop a.
Definition show_lvl_postop_assoc (assoc : Associativity) (op_lvl : Level) {A}
           `{ShowLevel A}
  : A -> string -> Level -> string
  := fun a postop => show_lvl_binop assoc op_lvl a postop (fun 'tt => "").
Definition show_lvl_unop (unop_lvl : Level) (unop : string) {A}
           `{ShowLevel A}
  : ShowLevel A
  := fun a => show_lvl_preop_assoc RightAssoc unop_lvl unop a.
Definition show_lvl_postop (postop_lvl : Level) {A}
           `{ShowLevel A}
  : A -> string -> Level -> string
  := fun a postop => show_lvl_postop_assoc LeftAssoc postop_lvl a postop.

Definition maybe_wrap_parens_lines (parens : bool) (s : list string)
  := match s, parens with
     | s, false => s
     | nil, _ => nil
     | [s], _ => [maybe_wrap_parens parens s]
     | s, true => "(" :: List.map (String " ") s ++ [")"]
     end%list.

Global Instance show_lvl_unit : ShowLevel unit := fun 'tt => neg_wrap_parens "tt".
Global Instance show_lvl_True : ShowLevel True := fun 'I => neg_wrap_parens "I".
Global Instance show_lvl_False : ShowLevel False := fun pf => match pf with end.
Global Instance show_lvl_Empty_set : ShowLevel Empty_set := fun pf => match pf with end.
Global Instance show_lvl_bool : ShowLevel bool := fun b => neg_wrap_parens (if b then "true" else "false").
Global Instance show_lvl_option {T} `{ShowLevel T} : ShowLevel (option T)
  := fun v
     => match v with
        | Some v
          => show_lvl_app (fun 'tt => "Some") (show_lvl v)
        | None => neg_wrap_parens "None"
        end.
Global Instance show_option {T} `{Show T} : Show (option T) | 2000 := let _ := @ShowLevel_of_Show T in _.
Global Instance show_lvl_list {T} `{ShowLevel T} : ShowLevel (list T)
  := fun ls => neg_wrap_parens
                 ("[" ++ String.concat ", " (List.map (fun v => show_lvl v term_lvl) ls) ++ "]").
Global Instance show_list {T} `{Show T} : Show (list T) | 2000 := let _ := @ShowLevel_of_Show T in _.
Global Instance show_lvl_prod {A B} `{ShowLevel A, ShowLevel B} : ShowLevel (A * B)
  := fun '(a, b) => show_lvl_binop pair_assoc pair_lvl a ", " b.
Global Instance show_prod {A B} `{Show A, Show B} : Show (A * B) | 2000 :=
  let _ := @ShowLevel_of_Show A in
  let _ := @ShowLevel_of_Show B in
  _.
Global Instance show_lvl_sum {A B} `{ShowLevel A, ShowLevel B} : ShowLevel (A + B)
  := fun ab => match ab with
               | inl v => show_lvl_app (fun 'tt => "inl") (show_lvl v)
               | inr v => show_lvl_app (fun 'tt => "inr") (show_lvl v)
               end.
Global Instance show_sum {A B} `{Show A, Show B} : Show (A + B) | 2000
  := let _ := @ShowLevel_of_Show A in
     let _ := @ShowLevel_of_Show B in
     _.
Global Instance show_lvl_sigT {A B} `{ShowLevel A, forall a, ShowLevel (B a)} : ShowLevel (@sigT A B)
  := fun '(existT a b) => show_lvl_binop pair_assoc pair_lvl a "; " b.
Global Instance show_sigT {A B} `{Show A, forall a, Show (B a)} : Show (@sigT A B) | 2000 :=
  let _ := @ShowLevel_of_Show A in
  let _ := fun a => @ShowLevel_of_Show (B a) in
  _.
Global Instance show_lvl_sig {A} {B : A -> Prop} `{ShowLevel A, forall a, ShowLevel (B a)} : ShowLevel (@sig A B)
  := fun '(exist a b) => show_lvl_binop pair_assoc pair_lvl a "; " b.
Global Instance show_sig {A} {B : A -> Prop} `{Show A, forall a, Show (B a)} : Show (@sig A B) | 2000 :=
  let _ := @ShowLevel_of_Show A in
  let _ := fun a => @ShowLevel_of_Show (B a) in
  _.
Global Instance show_lvl_string : ShowLevel string := fun s => neg_wrap_parens ("""" ++ (String.replace """" """""" s) ++ """").
Global Instance show_lvl_ascii : ShowLevel ascii := fun ch => neg_wrap_parens (String "'" (String ch "'")).

Global Instance show_lines_option {T} `{ShowLines T} : ShowLines (option T)
  := fun v
     => match v with
        | Some v
          => match show_lines v with
             | [s] => ["Show " ++ s]
             | s => "Show"::List.map (String " ") s
               end
        | None => ["None"]
        end.
Global Instance show_lines_list {T} `{ShowLines T} : ShowLines (list T)
  := fun ls
     => let ls := List.map show_lines ls in
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
  := fun '(a, b)
     => match show_lines a, show_lines b with
        | [a], [b] => ["(" ++ a ++ ", " ++ b ++ ")"]%string
        | a, b => ["("] ++ a ++ [", "] ++ b ++ [")"]
        end%list.

Module Export Decimal.
  Global Instance show_lvl_positive : ShowLevel positive
    := fun p => neg_wrap_parens (Decimal.Pos.to_string p).
  Global Instance show_positive : Show positive := show_lvl_positive.
  Global Instance show_lvl_N : ShowLevel N
    := fun n => neg_wrap_parens
                  match n with
                  | N0 => "0"
                  | Npos p => show p
                  end.
  Global Instance show_N : Show N := show_lvl_N.
  Global Instance show_lvl_nat : ShowLevel nat
    := fun n => show_lvl (N.of_nat n).
  Global Instance show_nat : Show nat := show_lvl_nat.
  Global Instance show_lvl_Z : ShowLevel Z
    := fun z
       => match z with
          | Zneg p => show_lvl_unop opp_lvl "-" p
          | Z0 => neg_wrap_parens "0"
          | Zpos p => show_lvl p
          end.
  Global Instance show_Z : Show Z := show_lvl_Z.
  Definition show_lvl_Q_frac : ShowLevel Q
    := fun q
       => if (Qden q =? 1)%positive
          then show_lvl (Qnum q)
          else show_lvl_binop
                 div_assoc div_lvl
                 (Qnum q) " / " (Qden q).
  Definition show_Q_frac : Show Q := show_lvl_Q_frac.
  Global Instance show_lvl_Q : ShowLevel Q
    := fun q
       => if (Qden q =? 1)%positive
          then show_lvl (Qnum q)
          else let lg10 := Z.log10 (Z.pos (Qden q)) in
               if (10^lg10 =? Z.pos (Qden q))%Z
               then let lg10 := Z.to_nat lg10 in
                    let int_part := show_Z (Z.abs (Qnum q) / Z.pos (Qden q))%Z in
                    let dec_part := show_Z (Z.abs (Qnum q) mod (Z.pos (Qden q)))%Z in
                    let abs_part
                        := int_part
                             ++ "."
                             ++ String.string_of_list_ascii (List.repeat "0"%char (lg10 - length dec_part)) ++ dec_part in
                    if (Qnum q <? 0)%Z
                    then show_lvl_unop opp_lvl "-" (fun 'tt => abs_part)
                    else neg_wrap_parens abs_part
               else
                 show_lvl_Q_frac q.
  Global Instance show_Q : Show Q := show_lvl_Q.
End Decimal.

Module Hex.
  Definition show_lvl_positive : ShowLevel positive
    := fun p => neg_wrap_parens (HexString.of_pos p).
  Definition show_positive : Show positive := show_lvl_positive.
  Definition show_lvl_Z : ShowLevel Z
    := fun z => let s := HexString.of_Z (Z.abs z) in
                if z <? 0
                then show_lvl_unop opp_lvl "-" (fun 'tt => s)
                else neg_wrap_parens s.
  Definition show_Z : Show Z := show_lvl_Z.
  Definition show_lvl_N : ShowLevel N
    := fun n
       => match n with
         | N0 => neg_wrap_parens "0"
         | Npos p => show_lvl_positive p
          end.
  Definition show_N : Show N := show_lvl_N.
  Definition show_lvl_nat : ShowLevel nat
    := fun n => show_lvl_N (N.of_nat n).
  Definition show_nat : Show nat := show_lvl_nat.
  Definition show_lvl_Q : ShowLevel Q
    := fun q
       => if (Qden q =? 1)%positive
          then show_lvl_Z (Qnum q)
          else show_lvl_binop
                 div_assoc div_lvl
                 (show_lvl_Z (Qnum q)) " / " (show_lvl_positive (Qden q)).
  Definition show_Q : Show Q := show_lvl_Q.
End Hex.

Module PowersOfTwo.
  Fixpoint show_lvl_Z_up_to' (max : nat) (max_dec : Z) (neg : bool) : ShowLevel Z
    := match max with
       | O => Hex.show_lvl_Z
       | S n'
         => fun z
            => if z <? max_dec
               then Decimal.show_lvl_Z z
               else if Z.abs (2^Z.log2_up z - z) <=? Z.abs (z - 2^Z.log2 z)
                    then let log2z := Z.log2_up z in
                         let z := 2^log2z - z in
                         if z =? 0
                         then show_lvl_binop
                                pow_assoc pow_lvl
                                2 "^" (Decimal.show_lvl_Z log2z)
                         else show_lvl_binop
                                FullyAssoc add_lvl
                                (show_lvl_binop
                                   pow_assoc pow_lvl
                                   2 "^" (Decimal.show_lvl_Z log2z))
                                (if neg then "+" else "-")
                                (show_lvl_Z_up_to' n' max_dec (negb neg) z)
                    else let log2z := Z.log2 z in
                         let z := z - 2^log2z in
                         if z =? 0
                         then show_lvl_binop
                                pow_assoc pow_lvl
                                2 "^" (Decimal.show_lvl_Z log2z)
                         else show_lvl_binop
                                FullyAssoc add_lvl
                                (show_lvl_binop
                                   pow_assoc pow_lvl
                                   2 "^" (Decimal.show_lvl_Z log2z))
                                (if neg then "-" else "+")
                                (show_lvl_Z_up_to' n' max_dec neg z)
       end%Z%string.

  Definition show_lvl_Z_up_to (max : nat) (max_dec : Z) : ShowLevel Z
    := fun z
       => (if z <? 0
           then lvl_wrap_parens
                  add_lvl
                  ("-" ++ show_lvl_Z_up_to' max max_dec false (-z) add_lvl)
           else if z =? 0
                then neg_wrap_parens "0"
                else show_lvl_Z_up_to' max max_dec false z)%Z.
  Definition show_Z_up_to (max : nat) (max_dec : Z) : Show Z
    := show_lvl_Z_up_to max max_dec.
  Definition show_lvl_Z : ShowLevel Z
    := fun z => show_lvl_Z_up_to (S (Z.to_nat (Z.log2_up (Z.abs z)))) 32 z.
  Definition show_Z : Show Z
    := show_lvl_Z.
End PowersOfTwo.
