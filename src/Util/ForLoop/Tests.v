Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Util.ForLoop.
Require Import Crypto.Util.ForLoop.InvariantFramework.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.

Check (for i (:= 0; += 1; < 10) updating (v := 5) {{ v + i }}).
Check (for (int i = 0; i < 5; i++) updating ( '(v1, v2) = (0, 0) ) {{ (v1 + i, v2 + i) }}).

Compute for (int i = 0; i < 5; i++) updating (v = 0) {{ v + i }}.
Compute for (int i = 0; i <= 5; i++) updating (v = 0) {{ v + i }}.
Compute for (int i = 5; i > -1; i--) updating (v = 0) {{ v + i }}.
Compute for (int i = 5; i >= 0; i--) updating (v = 0) {{ v + i }}.
Compute for (int i = 0; i < 5; i += 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 0; i <= 5; i += 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 5; i > -1; i -= 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 5; i >= 0; i -= 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 0; i < 6; i += 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 0; i <= 6; i += 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 6; i > -1; i -= 2) updating (v = 0) {{ v + i }}.
Compute for (int i = 6; i >= 0; i -= 2) updating (v = 0) {{ v + i }}.
Check eq_refl : for (int i = 0; i <= 5; i++) updating (v = 0) {{ v + i }} = 15.
Check eq_refl : for (int i = 0; i < 5; i++) updating (v = 0) {{ v + i }} = 10.
Check eq_refl : for (int i = 5; i >= 0; i--) updating (v = 0) {{ v + i }} = 15.
Check eq_refl : for (int i = 5; i > -1; i--) updating (v = 0) {{ v + i }} = 15.
Check eq_refl : for (int i = 0; i <= 5; i += 2) updating (v = 0) {{ v + i }} = 6.
Check eq_refl : for (int i = 0; i < 5; i += 2) updating (v = 0) {{ v + i }} = 6.
Check eq_refl : for (int i = 5; i > -1; i -= 2) updating (v = 0) {{ v + i }} = 9.
Check eq_refl : for (int i = 5; i >= 0; i -= 2) updating (v = 0) {{ v + i }} = 9.
Check eq_refl : for (int i = 0; i <= 6; i += 2) updating (v = 0) {{ v + i }} = 12.
Check eq_refl : for (int i = 0; i < 6; i += 2) updating (v = 0) {{ v + i }} = 6.
Check eq_refl : for (int i = 6; i > -1; i -= 2) updating (v = 0) {{ v + i }} = 12.
Check eq_refl : for (int i = 6; i >= 0; i -= 2) updating (v = 0) {{ v + i }} = 12.

Local Notation for_sumT n'
  := (let n := Z.pos n' in
      (2 *
       for (int i = 0; i <= n; i++) updating (v = 0) {{
         v + i
       }})%Z
      = n * (n + 1))
       (only parsing).

Check eq_refl : for_sumT 5.

(** Here we show that if we add the numbers from 0 to n, we get [n * (n + 1) / 2] *)
Example for_sum n' : for_sumT n'.
Proof.
  intro n.
  apply for_loop_ind_le1.
  { compute; reflexivity. }
  { intros; nia. }
Qed.
