Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Util.Strings.Equality.
Import BinPosDef.

Module Import DecimalHelpers. (* mostly from the decimal plugin, see https://github.com/coq/coq/pull/6599/files *)
  Inductive uint :=
  | Nil
  | D0 (_:uint)
  | D1 (_:uint)
  | D2 (_:uint)
  | D3 (_:uint)
  | D4 (_:uint)
  | D5 (_:uint)
  | D6 (_:uint)
  | D7 (_:uint)
  | D8 (_:uint)
  | D9 (_:uint).

  Notation zero := (D0 Nil).

  (** For conversions with binary numbers, it is easier to operate
    on little-endian numbers. *)

  Fixpoint revapp (d d' : uint) :=
    match d with
    | Nil => d'
    | D0 d => revapp d (D0 d')
    | D1 d => revapp d (D1 d')
    | D2 d => revapp d (D2 d')
    | D3 d => revapp d (D3 d')
    | D4 d => revapp d (D4 d')
    | D5 d => revapp d (D5 d')
    | D6 d => revapp d (D6 d')
    | D7 d => revapp d (D7 d')
    | D8 d => revapp d (D8 d')
    | D9 d => revapp d (D9 d')
    end.

  Definition rev d := revapp d Nil.

  Module Little.
    (** Successor of little-endian numbers *)
    Fixpoint succ d :=
      match d with
      | Nil => D1 Nil
      | D0 d => D1 d
      | D1 d => D2 d
      | D2 d => D3 d
      | D3 d => D4 d
      | D4 d => D5 d
      | D5 d => D6 d
      | D6 d => D7 d
      | D7 d => D8 d
      | D8 d => D9 d
      | D9 d => D0 (succ d)
      end.

    Fixpoint double d :=
      match d with
      | Nil => Nil
      | D0 d => D0 (double d)
      | D1 d => D2 (double d)
      | D2 d => D4 (double d)
      | D3 d => D6 (double d)
      | D4 d => D8 (double d)
      | D5 d => D0 (succ_double d)
      | D6 d => D2 (succ_double d)
      | D7 d => D4 (succ_double d)
      | D8 d => D6 (succ_double d)
      | D9 d => D8 (succ_double d)
      end

    with succ_double d :=
           match d with
           | Nil => D1 Nil
           | D0 d => D1 (double d)
           | D1 d => D3 (double d)
           | D2 d => D5 (double d)
           | D3 d => D7 (double d)
           | D4 d => D9 (double d)
           | D5 d => D1 (succ_double d)
           | D6 d => D3 (succ_double d)
           | D7 d => D5 (succ_double d)
           | D8 d => D7 (succ_double d)
           | D9 d => D9 (succ_double d)
           end.
  End Little.


  Module Pos.
    Local Open Scope positive_scope.
    Fixpoint to_little_uint p :=
      match p with
      | 1 => D1 Nil
      | p~1 => Little.succ_double (to_little_uint p)
      | p~0 => Little.double (to_little_uint p)
      end.

    Definition to_uint p := rev (to_little_uint p).

    Local Notation ten := 1~0~1~0.

    Fixpoint of_uint_acc (d:uint)(acc:positive) :=
      match d with
      | Nil => acc
      | D0 l => of_uint_acc l (Pos.mul ten acc)
      | D1 l => of_uint_acc l (Pos.add 1 (Pos.mul ten acc))
      | D2 l => of_uint_acc l (Pos.add 1~0 (Pos.mul ten acc))
      | D3 l => of_uint_acc l (Pos.add 1~1 (Pos.mul ten acc))
      | D4 l => of_uint_acc l (Pos.add 1~0~0 (Pos.mul ten acc))
      | D5 l => of_uint_acc l (Pos.add 1~0~1 (Pos.mul ten acc))
      | D6 l => of_uint_acc l (Pos.add 1~1~0 (Pos.mul ten acc))
      | D7 l => of_uint_acc l (Pos.add 1~1~1 (Pos.mul ten acc))
      | D8 l => of_uint_acc l (Pos.add 1~0~0~0 (Pos.mul ten acc))
      | D9 l => of_uint_acc l (Pos.add 1~0~0~1 (Pos.mul ten acc))
      end.
  End Pos.

  Module N.
    Fixpoint of_uint (d:uint) : N :=
      match d with
      | Nil => N0
      | D0 l => of_uint l
      | D1 l => Npos (Pos.of_uint_acc l 1)
      | D2 l => Npos (Pos.of_uint_acc l 1~0)
      | D3 l => Npos (Pos.of_uint_acc l 1~1)
      | D4 l => Npos (Pos.of_uint_acc l 1~0~0)
      | D5 l => Npos (Pos.of_uint_acc l 1~0~1)
      | D6 l => Npos (Pos.of_uint_acc l 1~1~0)
      | D7 l => Npos (Pos.of_uint_acc l 1~1~1)
      | D8 l => Npos (Pos.of_uint_acc l 1~0~0~0)
      | D9 l => Npos (Pos.of_uint_acc l 1~0~0~1)
      end.
  End N.

  Module String.
    Local Open Scope string_scope.
    Fixpoint of_uint (v : uint) : string
      := match v with
         | Nil => ""
         | D0 x => String "0" (of_uint x)
         | D1 x => String "1" (of_uint x)
         | D2 x => String "2" (of_uint x)
         | D3 x => String "3" (of_uint x)
         | D4 x => String "4" (of_uint x)
         | D5 x => String "5" (of_uint x)
         | D6 x => String "6" (of_uint x)
         | D7 x => String "7" (of_uint x)
         | D8 x => String "8" (of_uint x)
         | D9 x => String "9" (of_uint x)
         end.

    Fixpoint to_uint (v : string) : uint
      := match v with
         | EmptyString => Nil
         | String ch v
           => let rest := to_uint v in
              (if ascii_beq ch "0"
               then D0 rest
               else if ascii_beq ch "1"
               then D1 rest
               else if ascii_beq ch "2"
               then D2 rest
               else if ascii_beq ch "3"
               then D3 rest
               else if ascii_beq ch "4"
               then D4 rest
               else if ascii_beq ch "5"
               then D5 rest
               else if ascii_beq ch "6"
               then D6 rest
               else if ascii_beq ch "7"
               then D7 rest
               else if ascii_beq ch "8"
               then D8 rest
               else if ascii_beq ch "9"
               then D9 rest
               else Nil)
         end.

    Lemma to_of v : String.to_uint (String.of_uint v) = v.
    Proof. induction v; cbn; f_equal; trivial. Qed.
  End String.
End DecimalHelpers.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Definition decimal_string_of_pos (p : positive) : string
  := String.of_uint (Pos.to_uint p).

Definition pos_of_decimal_string (s : string) : positive
  := match N.of_uint (String.to_uint s) with
     | N0 => 1
     | Npos p => p
     end.

(*Lemma pos_of_decimal_string_of_pos (p : positive)
  : pos_of_decimal_string (decimal_string_of_pos p) = p.
Proof.
  cbv [pos_of_decimal_string decimal_string_of_pos].
  rewrite String.to_of.
 ...
Qed.*)

Example decimal_string_of_pos_1 : decimal_string_of_pos 1 = "1" := eq_refl.
Example decimal_string_of_pos_2 : decimal_string_of_pos 2 = "2" := eq_refl.
Example decimal_string_of_pos_3 : decimal_string_of_pos 3 = "3" := eq_refl.
Example decimal_string_of_pos_7 : decimal_string_of_pos 7 = "7" := eq_refl.
Example decimal_string_of_pos_8 : decimal_string_of_pos 8 = "8" := eq_refl.
Example decimal_string_of_pos_9 : decimal_string_of_pos 9 = "9" := eq_refl.
Example decimal_string_of_pos_10 : decimal_string_of_pos 10 = "10" := eq_refl.
Example decimal_string_of_pos_11 : decimal_string_of_pos 11 = "11" := eq_refl.
Example decimal_string_of_pos_12 : decimal_string_of_pos 12 = "12" := eq_refl.
Example decimal_string_of_pos_13 : decimal_string_of_pos 13 = "13" := eq_refl.
Example decimal_string_of_pos_14 : decimal_string_of_pos 14 = "14" := eq_refl.
Example decimal_string_of_pos_15 : decimal_string_of_pos 15 = "15" := eq_refl.
Example decimal_string_of_pos_16 : decimal_string_of_pos 16 = "16" := eq_refl.
