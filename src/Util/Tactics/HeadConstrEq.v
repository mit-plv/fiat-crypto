Require Import Crypto.Util.Tactics.Head.

Ltac head_constr_eq T1 T2 :=
  let h1 := head T1 in
  let h2 := head T2 in
  constr_eq h1 h2.

Ltac head_constr_eq_nounivs T1 T2 :=
  let h1 := head T1 in
  let h2 := head T2 in
  constr_eq_nounivs h1 h2.

Ltac head_constr_eq_strict T1 T2 :=
  let h1 := head T1 in
  let h2 := head T2 in
  constr_eq_strict h1 h2.
