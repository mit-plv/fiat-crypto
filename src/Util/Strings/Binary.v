Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Numbers.BinNums.
Require Import Crypto.Util.Strings.Equality.
Require Crypto.Util.Pos.
Import BinPosDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Fixpoint bin_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | p'~0 => bin_string_of_pos' p' (String "0" rest)
     | p'~1 => bin_string_of_pos' p' (String "1" rest)
     end.
Definition bin_string_of_pos (p : positive) : string
  := String "0" (String "b" (bin_string_of_pos' p "")).

Local Notation default := 1.

Fixpoint pos_of_bin_string' (s : string) (rest : option positive)
  : option positive
  := match s with
     | "" => rest
     | String ch s'
       => pos_of_bin_string'
            s'
            (if ascii_beq ch "0"
             then option_map xO rest
             else if ascii_beq ch "1"
                  then match rest with
                       | Some p => Some (xI p)
                       | None => Some xH
                       end
                  else None)
     end.
Definition pos_of_bin_string (s : string) : positive
  := match s with
     | String s0 (String sb s)
       => if ascii_beq s0 "0"
          then if ascii_beq sb "b"
               then match pos_of_bin_string' s None with
                    | Some p => p
                    | None => default
                    end
               else default
          else default
     | _ => default
     end.

Lemma pos_of_bin_string_of_pos' (p : positive)
      (base : option positive)
      (rest : string)
  : pos_of_bin_string' (bin_string_of_pos' p rest) base
    = pos_of_bin_string' rest (match base with
                               | None => Some p
                               | Some v => Some (Pos.app v p)
                               end).
Proof.
  revert base rest; induction p, base; intros; try reflexivity;
    cbn; rewrite IHp; reflexivity.
Qed.

Lemma pos_of_bin_string_of_pos (p : positive)
  : pos_of_bin_string (bin_string_of_pos p) = p.
Proof.
  cbn; rewrite pos_of_bin_string_of_pos'; reflexivity.
Qed.

Example bin_string_of_pos_1 : bin_string_of_pos 1 = "0b1" := eq_refl.
Example bin_string_of_pos_2 : bin_string_of_pos 2 = "0b10" := eq_refl.
Example bin_string_of_pos_3 : bin_string_of_pos 3 = "0b11" := eq_refl.
