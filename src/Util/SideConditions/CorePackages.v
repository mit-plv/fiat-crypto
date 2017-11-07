Import EqNotations.

Record evar_package {T} (v : T) :=
  { val : T;
    evar_package_pf : val = v }.
Arguments val {T v} _.
Arguments evar_package_pf {T v} _.
Record evard_package {s d} (v : s) :=
  { vald : d;
    evard_package_pfT : s = d;
    evard_package_pf : vald = rew evard_package_pfT in v }.
Arguments vald {s d v} _.
Arguments evard_package_pfT {s d v} _.
Arguments evard_package_pf {s d v} _.

Ltac autosolve else_tac := else_tac ().
