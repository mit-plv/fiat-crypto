Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Numbers.DecimalString.
Require Coq.Numbers.DecimalN.
Require Coq.Numbers.DecimalZ.
Import BinPosDef.
Import BinIntDef.
Import BinNatDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Module N.
  Definition of_string (s : string) : option N
    := option_map N.of_uint (NilEmpty.uint_of_string s).

  Definition to_string (v : N) : string
    := NilEmpty.string_of_uint (N.to_uint v).

  Lemma of_to v
    : of_string (to_string v) = Some v.
  Proof.
    cbv [of_string to_string option_map].
    now rewrite NilEmpty.usu, DecimalN.Unsigned.of_to.
  Qed.

  (** Going the other ways strips leading zeros; we don't prove anything about it *)
End N.

Module Pos.
  Definition of_string (s : string) : option positive
    := match N.of_string s with
       | Some N0 | None => None
       | Some (Npos p) => Some p
       end.

  Definition to_string (v : positive) : string
    := N.to_string (Npos v).

  Lemma of_to v
    : of_string (to_string v) = Some v.
  Proof.
    cbv [of_string to_string option_map].
    now rewrite N.of_to.
  Qed.

  (** Going the other ways strips leading zeros; we don't prove anything about it *)
End Pos.

Module Z.
  Definition of_string (s : string) : option Z
    := option_map Z.of_int (NilEmpty.int_of_string s).

  Definition to_string (v : Z) : string
    := NilEmpty.string_of_int (Z.to_int v).

  Lemma of_to v
    : of_string (to_string v) = Some v.
  Proof.
    cbv [of_string to_string option_map].
    now rewrite NilEmpty.isi, DecimalZ.of_to.
  Qed.

  (** Going the other ways strips leading zeros; we don't prove anything about it *)
End Z.
