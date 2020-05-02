Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Crypto.Util.Strings.Show.

Module ShowWSetsOn (E : Equalities.DecidableType) (W : WSetsOn E).
  Global Instance show_t {show_elt : Show E.t} : Show W.t
    := fun with_parens v => show with_parens (W.elements v).
  Global Instance show_lines_t {show_elt : ShowLines E.t} : ShowLines W.t
    := fun with_parens v => show_lines with_parens (W.elements v).
End ShowWSetsOn.

Module ShowWSets (W : WSets) := ShowWSetsOn W.E W.
