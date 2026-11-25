Set Loose Hint Behavior "Strict".

Require Export Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import bbv.BinNotation(forceOption,ParseError,parseError).


Local Open Scope N_scope.

Local Open Scope char_scope.

Definition octDigitToN (c : ascii) : option N :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | _   => None
  end.

Local Close Scope char_scope.

Local Open Scope string_scope.

Fixpoint readOctNAux (s : string) (acc : N) : option N :=
  match s with
    | "" => Some acc
    | String c s' =>
      match octDigitToN c with
        | Some n => readOctNAux s' (8 * acc + n)
        | None => None
      end
  end.

Definition readOctN (s : string) : option N := readOctNAux s 0.

Goal readOctN "777" = Some 511.
Proof. reflexivity. Qed.

Definition oct (s : string) := forceOption N parseError (readOctN s) ParseError.

Goal oct"777" = 511.
Proof. reflexivity. Qed.

Goal oct"01234567" = 342391.
Proof. reflexivity. Qed.

Goal oct"512000001" = 86507521.
Proof. reflexivity. Qed.

Goal oct"8" = ParseError.
Proof. reflexivity. Qed.

Local Close Scope string_scope.

Local Close Scope N_scope.
