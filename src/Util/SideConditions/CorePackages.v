Import EqNotations.

Record evar_package {T} (v : T) :=
  { val : T;
    evar_package_pf : val = v }.
Arguments val {T v} _.
Arguments evar_package_pf {T v} _.

Record evar_function_package {A B} (f : forall x : A, B x) :=
  { valf : forall x : A, B x;
    evarf_package_pf : forall x, valf x = f x }.
Arguments valf {A B f} _.
Arguments evarf_package_pf {A B f} _ _.

Record evard_package {s d} (v : s) :=
  { vald : d;
    evard_package_pfT : s = d;
    evard_package_pf : vald = rew evard_package_pfT in v }.
Arguments vald {s d v} _.
Arguments evard_package_pfT {s d v} _.
Arguments evard_package_pf {s d v} _.

Local Notation "'rew' 'dependent' H 'in' H'"
  := (match H with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").

Record evard_function_package {sA sB dA dB} (f : forall x : sA, sB x) :=
  { valdf : forall x : dA, dB x;
    evardf_package_pfTA : dA = sA;
    evardf_package_pfTB : forall x, sB (rew evardf_package_pfTA in x) = dB x;
    evardf_package_pf : forall x, valdf x = rew dependent evardf_package_pfTB x in (f (rew evardf_package_pfTA in x)) }.
Arguments valdf {sA sB dA dB f} _ _.
Arguments evardf_package_pfTA {sA sB dA dB f} _.
Arguments evardf_package_pfTB {sA sB dA dB f} _.
Arguments evardf_package_pf {sA sB dA dB f} _ _.

Ltac autosolve else_tac := else_tac ().
