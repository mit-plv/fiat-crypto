Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Util.Strings.Equality.
Require Crypto.Util.Pos.
Import BinPosDef.

Local Open Scope bool_scope.
Local Open Scope positive_scope.
Local Open Scope string_scope.

Fixpoint hex_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | 2 => String "2" rest
     | 3 => String "3" rest
     | 4 => String "4" rest
     | 5 => String "5" rest
     | 6 => String "6" rest
     | 7 => String "7" rest
     | 8 => String "8" rest
     | 9 => String "9" rest
     | 10 => String "a" rest
     | 11 => String "b" rest
     | 12 => String "c" rest
     | 13 => String "d" rest
     | 14 => String "e" rest
     | 15 => String "f" rest
     | p'~0~0~0~0 => hex_string_of_pos' p' (String "0" rest)
     | p'~0~0~0~1 => hex_string_of_pos' p' (String "1" rest)
     | p'~0~0~1~0 => hex_string_of_pos' p' (String "2" rest)
     | p'~0~0~1~1 => hex_string_of_pos' p' (String "3" rest)
     | p'~0~1~0~0 => hex_string_of_pos' p' (String "4" rest)
     | p'~0~1~0~1 => hex_string_of_pos' p' (String "5" rest)
     | p'~0~1~1~0 => hex_string_of_pos' p' (String "6" rest)
     | p'~0~1~1~1 => hex_string_of_pos' p' (String "7" rest)
     | p'~1~0~0~0 => hex_string_of_pos' p' (String "8" rest)
     | p'~1~0~0~1 => hex_string_of_pos' p' (String "9" rest)
     | p'~1~0~1~0 => hex_string_of_pos' p' (String "a" rest)
     | p'~1~0~1~1 => hex_string_of_pos' p' (String "b" rest)
     | p'~1~1~0~0 => hex_string_of_pos' p' (String "c" rest)
     | p'~1~1~0~1 => hex_string_of_pos' p' (String "d" rest)
     | p'~1~1~1~0 => hex_string_of_pos' p' (String "e" rest)
     | p'~1~1~1~1 => hex_string_of_pos' p' (String "f" rest)
     end.
Definition hex_string_of_pos (p : positive) : string
  := String "0" (String "x" (hex_string_of_pos' p "")).

Local Notation default := 1.

Fixpoint pos_of_hex_string' (s : string) (rest : option positive)
  : option positive
  := match s with
     | "" => rest
     | String ch s'
       => pos_of_hex_string'
            s'
            (if ascii_beq ch "0"
             then match rest with
                  | Some p => Some (p~0~0~0~0)
                  | None => None
                  end
             else if ascii_beq ch "1"
             then match rest with
                  | Some p => Some (p~0~0~0~1)
                  | None => Some 1
                  end
             else if ascii_beq ch "2"
             then match rest with
                  | Some p => Some (p~0~0~1~0)
                  | None => Some 2
                  end
             else if ascii_beq ch "3"
             then match rest with
                  | Some p => Some (p~0~0~1~1)
                  | None => Some 3
                  end
             else if ascii_beq ch "4"
             then match rest with
                  | Some p => Some (p~0~1~0~0)
                  | None => Some 4
                  end
             else if ascii_beq ch "5"
             then match rest with
                  | Some p => Some (p~0~1~0~1)
                  | None => Some 5
                  end
             else if ascii_beq ch "6"
             then match rest with
                  | Some p => Some (p~0~1~1~0)
                  | None => Some 6
                  end
             else if ascii_beq ch "7"
             then match rest with
                  | Some p => Some (p~0~1~1~1)
                  | None => Some 7
                  end
             else if ascii_beq ch "8"
             then match rest with
                  | Some p => Some (p~1~0~0~0)
                  | None => Some 8
                  end
             else if ascii_beq ch "9"
             then match rest with
                  | Some p => Some (p~1~0~0~1)
                  | None => Some 9
                  end
             else if ascii_beq ch "a" || ascii_beq ch "A"
             then match rest with
                  | Some p => Some (p~1~0~1~0)
                  | None => Some 10
                  end
             else if ascii_beq ch "b" || ascii_beq ch "B"
             then match rest with
                  | Some p => Some (p~1~0~1~1)
                  | None => Some 11
                  end
             else if ascii_beq ch "c" || ascii_beq ch "C"
             then match rest with
                  | Some p => Some (p~1~1~0~0)
                  | None => Some 12
                  end
             else if ascii_beq ch "d" || ascii_beq ch "D"
             then match rest with
                  | Some p => Some (p~1~1~0~1)
                  | None => Some 13
                  end
             else if ascii_beq ch "e" || ascii_beq ch "E"
             then match rest with
                  | Some p => Some (p~1~1~1~0)
                  | None => Some 14
                  end
             else if ascii_beq ch "f" || ascii_beq ch "F"
             then match rest with
                  | Some p => Some (p~1~1~1~1)
                  | None => Some 15
                  end
             else None)
     end.
Definition pos_of_hex_string (s : string) : positive
  := match s with
     | String s0 (String sb s)
       => if ascii_beq s0 "0"
          then if ascii_beq sb "x"
               then match pos_of_hex_string' s None with
                    | Some p => p
                    | None => default
                    end
               else default
          else default
     | _ => default
     end.

Fixpoint pos_hex_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~0~1
  | 2 => p~0~0~1~0
  | 3 => p~0~0~1~1
  | 4 => p~0~1~0~0
  | 5 => p~0~1~0~1
  | 6 => p~0~1~1~0
  | 7 => p~0~1~1~1
  | 8 => p~1~0~0~0
  | 9 => p~1~0~0~1
  | 10 => p~1~0~1~0
  | 11 => p~1~0~1~1
  | 12 => p~1~1~0~0
  | 13 => p~1~1~0~1
  | 14 => p~1~1~1~0
  | 15 => p~1~1~1~1
  | q~0~0~0~0 => (pos_hex_app p q)~0~0~0~0
  | q~0~0~0~1 => (pos_hex_app p q)~0~0~0~1
  | q~0~0~1~0 => (pos_hex_app p q)~0~0~1~0
  | q~0~0~1~1 => (pos_hex_app p q)~0~0~1~1
  | q~0~1~0~0 => (pos_hex_app p q)~0~1~0~0
  | q~0~1~0~1 => (pos_hex_app p q)~0~1~0~1
  | q~0~1~1~0 => (pos_hex_app p q)~0~1~1~0
  | q~0~1~1~1 => (pos_hex_app p q)~0~1~1~1
  | q~1~0~0~0 => (pos_hex_app p q)~1~0~0~0
  | q~1~0~0~1 => (pos_hex_app p q)~1~0~0~1
  | q~1~0~1~0 => (pos_hex_app p q)~1~0~1~0
  | q~1~0~1~1 => (pos_hex_app p q)~1~0~1~1
  | q~1~1~0~0 => (pos_hex_app p q)~1~1~0~0
  | q~1~1~0~1 => (pos_hex_app p q)~1~1~0~1
  | q~1~1~1~0 => (pos_hex_app p q)~1~1~1~0
  | q~1~1~1~1 => (pos_hex_app p q)~1~1~1~1
  end.

Fixpoint pos_of_hex_string_of_pos' (p : positive)
      (base : option positive)
      (rest : string)
  : pos_of_hex_string' (hex_string_of_pos' p rest) base
    = pos_of_hex_string' rest (match base with
                               | None => Some p
                               | Some v => Some (pos_hex_app v p)
                               end).
Proof.
  do 4 try destruct p as [p|p|]; destruct base; try reflexivity;
    cbn; rewrite pos_of_hex_string_of_pos'; reflexivity.
Qed.

Lemma pos_of_hex_string_of_pos (p : positive)
  : pos_of_hex_string (hex_string_of_pos p) = p.
Proof.
  cbn; rewrite pos_of_hex_string_of_pos'; reflexivity.
Qed.

Example hex_string_of_pos_1 : hex_string_of_pos 1 = "0x1" := eq_refl.
Example hex_string_of_pos_2 : hex_string_of_pos 2 = "0x2" := eq_refl.
Example hex_string_of_pos_3 : hex_string_of_pos 3 = "0x3" := eq_refl.
Example hex_string_of_pos_7 : hex_string_of_pos 7 = "0x7" := eq_refl.
Example hex_string_of_pos_8 : hex_string_of_pos 8 = "0x8" := eq_refl.
Example hex_string_of_pos_9 : hex_string_of_pos 9 = "0x9" := eq_refl.
Example hex_string_of_pos_10 : hex_string_of_pos 10 = "0xa" := eq_refl.
Example hex_string_of_pos_11 : hex_string_of_pos 11 = "0xb" := eq_refl.
Example hex_string_of_pos_12 : hex_string_of_pos 12 = "0xc" := eq_refl.
Example hex_string_of_pos_13 : hex_string_of_pos 13 = "0xd" := eq_refl.
Example hex_string_of_pos_14 : hex_string_of_pos 14 = "0xe" := eq_refl.
Example hex_string_of_pos_15 : hex_string_of_pos 15 = "0xf" := eq_refl.
Example hex_string_of_pos_16 : hex_string_of_pos 16 = "0x10" := eq_refl.
