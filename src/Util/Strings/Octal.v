Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Util.Strings.Equality.
Require Crypto.Util.Pos.
Import BinPosDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Fixpoint oct_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | 2 => String "2" rest
     | 3 => String "3" rest
     | 4 => String "4" rest
     | 5 => String "5" rest
     | 6 => String "6" rest
     | 7 => String "7" rest
     | p'~0~0~0 => oct_string_of_pos' p' (String "0" rest)
     | p'~0~0~1 => oct_string_of_pos' p' (String "1" rest)
     | p'~0~1~0 => oct_string_of_pos' p' (String "2" rest)
     | p'~0~1~1 => oct_string_of_pos' p' (String "3" rest)
     | p'~1~0~0 => oct_string_of_pos' p' (String "4" rest)
     | p'~1~0~1 => oct_string_of_pos' p' (String "5" rest)
     | p'~1~1~0 => oct_string_of_pos' p' (String "6" rest)
     | p'~1~1~1 => oct_string_of_pos' p' (String "7" rest)
     end.
Definition oct_string_of_pos (p : positive) : string
  := String "0" (String "o" (oct_string_of_pos' p "")).

Local Notation default := 1.

Fixpoint pos_of_oct_string' (s : string) (rest : option positive)
  : option positive
  := match s with
     | "" => rest
     | String ch s'
       => pos_of_oct_string'
            s'
            (if ascii_beq ch "0"
             then match rest with
                  | Some p => Some (p~0~0~0)
                  | None => None
                  end
             else if ascii_beq ch "1"
             then match rest with
                  | Some p => Some (p~0~0~1)
                  | None => Some 1
                  end
             else if ascii_beq ch "2"
             then match rest with
                  | Some p => Some (p~0~1~0)
                  | None => Some 2
                  end
             else if ascii_beq ch "3"
             then match rest with
                  | Some p => Some (p~0~1~1)
                  | None => Some 3
                  end
             else if ascii_beq ch "4"
             then match rest with
                  | Some p => Some (p~1~0~0)
                  | None => Some 4
                  end
             else if ascii_beq ch "5"
             then match rest with
                  | Some p => Some (p~1~0~1)
                  | None => Some 5
                  end
             else if ascii_beq ch "6"
             then match rest with
                  | Some p => Some (p~1~1~0)
                  | None => Some 6
                  end
             else if ascii_beq ch "7"
             then match rest with
                  | Some p => Some (p~1~1~1)
                  | None => Some 7
                  end
             else None)
     end.
Definition pos_of_oct_string (s : string) : positive
  := match s with
     | String s0 (String sb s)
       => if ascii_beq s0 "0"
          then if ascii_beq sb "o"
               then match pos_of_oct_string' s None with
                    | Some p => p
                    | None => default
                    end
               else default
          else default
     | _ => default
     end.

Fixpoint pos_oct_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~1
  | 2 => p~0~1~0
  | 3 => p~0~1~1
  | 4 => p~1~0~0
  | 5 => p~1~0~1
  | 6 => p~1~1~0
  | 7 => p~1~1~1
  | q~0~0~0 => (pos_oct_app p q)~0~0~0
  | q~0~0~1 => (pos_oct_app p q)~0~0~1
  | q~0~1~0 => (pos_oct_app p q)~0~1~0
  | q~0~1~1 => (pos_oct_app p q)~0~1~1
  | q~1~0~0 => (pos_oct_app p q)~1~0~0
  | q~1~0~1 => (pos_oct_app p q)~1~0~1
  | q~1~1~0 => (pos_oct_app p q)~1~1~0
  | q~1~1~1 => (pos_oct_app p q)~1~1~1
  end.

Fixpoint pos_of_oct_string_of_pos' (p : positive)
      (base : option positive)
      (rest : string)
  : pos_of_oct_string' (oct_string_of_pos' p rest) base
    = pos_of_oct_string' rest (match base with
                               | None => Some p
                               | Some v => Some (pos_oct_app v p)
                               end).
Proof.
  do 3 try destruct p as [p|p|]; destruct base; try reflexivity;
    cbn; rewrite pos_of_oct_string_of_pos'; reflexivity.
Qed.

Lemma pos_of_oct_string_of_pos (p : positive)
  : pos_of_oct_string (oct_string_of_pos p) = p.
Proof.
  cbn; rewrite pos_of_oct_string_of_pos'; reflexivity.
Qed.

Example oct_string_of_pos_1 : oct_string_of_pos 1 = "0o1" := eq_refl.
Example oct_string_of_pos_2 : oct_string_of_pos 2 = "0o2" := eq_refl.
Example oct_string_of_pos_3 : oct_string_of_pos 3 = "0o3" := eq_refl.
Example oct_string_of_pos_7 : oct_string_of_pos 7 = "0o7" := eq_refl.
Example oct_string_of_pos_8 : oct_string_of_pos 8 = "0o10" := eq_refl.
