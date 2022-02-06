Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Option.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.ParseArithmeticToTaps.
Require Import Crypto.Util.OptionList.
Import ListNotations.
Import Coq.Lists.List.
Local Open Scope option_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope core_scope.

Definition single_tap_primes : list string :=
  [
    (* single-tap: *)

    "2^127 - 1"; (* "kummer strikes back" *)
  "2^129 - 25";
  "2^130 - 5"; (* poly1305 *)
  "2^137 - 13";
  "2^140 - 27";
  "2^141 - 9";
  "2^150 - 5";
  "2^150 - 3";
  "2^152 - 17";
  "2^158 - 15";
  "2^165 - 25";
  "2^166 - 5";
  "2^171 - 19";
  "2^174 - 17";
  "2^174 - 3";
  "2^189 - 25";
  "2^190 - 11";
  "2^191 - 19";
  "2^194 - 33";
  "2^196 - 15";
  "2^198 - 17";
  "2^206 - 5";
  "2^212 - 29";
  "2^213 - 3";
  "2^221 - 3";
  "2^222 - 117";
  "2^226 - 5";
  "2^230 - 27";
  "2^235 - 15";
  "2^243 - 9";
  "2^251 - 9";
  "2^255 - 765";
  "2^255 - 19"; (* curve25519 *)
  "2^256 - 189";
  "2^266 - 3";
  "2^285 - 9";
  "2^291 - 19";
  "2^321 - 9";
  "2^336 - 17";
  "2^336 - 3";
  "2^338 - 15";
  "2^369 - 25";
  "2^379 - 19";
  "2^382 - 105";
  "2^383 - 421";
  "2^383 - 187";
  "2^383 - 31";
  "2^384 - 317";
  "2^389 - 21";
  "2^401 - 31";
  "2^413 - 21";
  "2^414 - 17";
  "2^444 - 17";
  "2^452 - 3";
  "2^468 - 17";
  "2^488 - 17";
  "2^489 - 21";
  "2^495 - 31";
  "2^511 - 481";
  "2^511 - 187";
  "2^512 - 569";
  "2^521 - 1" (* p512 *)
  ].

Definition two_tap_golden_ratio_primes : list string :=
  [

    (* two taps, golden ratio: *)

    "2^192 - 2^64 - 1";
  "2^216 - 2^108 - 1";
  "2^322 - 2^161 - 1";
  "2^416 - 2^208 - 1";
  "2^448 - 2^224 - 1"; (* goldilocks *)
  "2^450 - 2^225 - 1";
  "2^480 - 2^240 - 1" (* ridinghood *)
  ].

Definition two_or_more_tap_primes : list string :=
  [
    (* two or more taps *)

    "2^205 - 45*2^198 - 1";
  "2^224 - 2^96 + 1"; (* p224 *)
  "2^256 - 2^224 + 2^192 + 2^96 - 1"; (* p256 *)
  "2^256 - 2^32 - 977"; (* bitcoin *)
  "2^256 - 4294968273"; (* bitcoin, for 64-bit impl *)
  "2^384 - 2^128 - 2^96 + 2^32 - 1" (* p384 *)
  ].

Definition montgomery_friendly_primes : list string :=
  [
    (* Montgomery-Friendly *)

    "2^256 - 88*2^240 - 1";
  "2^254 - 127*2^240 - 1";
  "2^384 - 79*2^376 - 1";
  "2^384 - 5*2^368 - 1";
  "2^512 - 491*2^496 - 1";
  "2^510 - 290*2^496 - 1"
  ].

Definition multitap_primes : list string :=
  two_tap_golden_ratio_primes
    ++ two_or_more_tap_primes
    ++ montgomery_friendly_primes.

Definition primes : list string :=
  single_tap_primes ++ multitap_primes.

Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.

(* 15.5 s for primes up to 2^301 *)
(* 25.674 s for primes up to 2^351 *)
(* 76.298 s for primes 2^300 up to 2^401 *)
Local Open Scope nat_scope.
Local Open Scope core_scope.
Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.
Time Definition possible_limbs :=
  Eval native_compute in
    Option.List.lift
      (Option.List.map
         (fun p => match parseZ_arith_to_taps p with
                   | Some (s, c)
                     => if (s <=? 2^350)%Z
                        then Some (Some (p, [(64, get_possible_limbs s c 64); (32, get_possible_limbs s c 32)]))
                        else None
                   | None => Some None
                   end)
         primes).

Import ListUtil.
Time Definition balances
  := Eval native_compute in
      option_map
       (fun ps
        => Option.List.lift
             (List.map
                (fun '(p, ls)
                 => option_map
                      (fun '(s, c)
                       => (p,
                           List.map
                             (fun '(bw, ns)
                              => List.map
                                   (fun n
                                    => let bal := @balance default_tight_upperbound_fraction n s c in
                                       let tub := @tight_upperbounds default_tight_upperbound_fraction n s c in
                                       let dif := map2 Z.sub bal tub in
                                       ((bw, n),
                                        ("balance:                                        ",
                                         (let show_lvl_Z := PowersOfTwo.show_lvl_Z in show bal),
                                         (let show_lvl_Z := Hex.show_lvl_Z in show bal)),
                                        ("tight_upperbounds:                              ",
                                         (let show_lvl_Z := PowersOfTwo.show_lvl_Z in show tub),
                                         (let show_lvl_Z := Hex.show_lvl_Z in show tub)),
                                        ("balance - tight_upperbounds:                    ",
                                         (let show_lvl_Z := PowersOfTwo.show_lvl_Z in show dif),
                                         (let show_lvl_Z := Hex.show_lvl_Z in show dif))))
                                   ns)
                             ls))
                      (parseZ_arith_to_taps p))
                ps))
       possible_limbs.
Local Notation "[ ]" := nil (format "[ ]") : core_scope.
Local Notation "[ x ]" := (cons x nil) : core_scope.
Local Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) (format "'[hv ' [ x ;  '/' y ;  '/' .. ;  '/' z ] ']'") : core_scope.
Local Close Scope list_scope.
Local Open Scope core_scope.
Set Printing Width 250.
Redirect "Crypto.UnsaturatedSolinasHeuristics.Tests.get_possible_limbs"
         Print possible_limbs.
Redirect "Crypto.UnsaturatedSolinasHeuristics.Tests.get_balances"
         Print balances.
