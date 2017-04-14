Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.ForLoop.

Local Open Scope Z_scope.

Check (for i (:= 0; += 1; < 10) updating (v := 5) {{ v + i }}).
Check (for (int i = 0; i < 5; i++) updating ( '(v1, v2) = (0, 0) ) {{ (v1 + i, v2 + i) }}).
