Require Import Coq.Numbers.BinNums.
Require Export Crypto.Util.FixCoqMistakes.

Local Generalizable All Variables.

Class pointed (T : Type) := point : T.

Module Export Hints1.
  Global Hint Extern 5 (pointed _) => solve [ constructor ] : typeclass_instances.
End Hints1.

Ltac step_pointed _ :=
  (constructor + (unshelve (econstructor; revgoals); revgoals));
  match goal with |- ?T => change (pointed T) end.

Ltac solve_pointed _ :=
  step_pointed ();
  exact _.

Local Hint Extern 6 (pointed _) => step_pointed () : typeclass_instances.
Local Hint Extern 7 (pointed _) => solve_pointed () : typeclass_instances.


Global Instance pointed_True : pointed True := _.
Global Instance pointed_unit : pointed unit := _.
Global Instance pointed_bool : pointed bool := _.
Global Instance pointed_list {A} : pointed (list A) := _.
Global Instance pointed_nat : pointed nat := _.
Global Instance pointed_N : pointed N := _.
Global Instance pointed_positive : pointed positive := _.
Global Instance pointed_Z : pointed Z := _.
Global Instance pointed_inhabited `{pointed A} : pointed (inhabited A) := _.
Global Instance pointed_sum_l {A B} {_ : pointed A} : pointed (A + B) | 2 := _.
Global Instance pointed_sum_r {A B} {_ : pointed B} : pointed (A + B) | 2 := _.
Global Instance pointed_or_l {A B : Prop} {_ : pointed A} : pointed (A \/ B) | 2 := _.
Global Instance pointed_or_r {A B : Prop} {_ : pointed B} : pointed (A \/ B) | 2 := _.
Global Instance pointed_prod `{pointed A, pointed B} : pointed (A * B) := _.
Global Instance pointed_and {A B : Prop} `{pointed A, pointed B} : pointed (A /\ B) := _.
Global Instance pointed_sig {A} {B : A -> Prop} {a : pointed A} {b : pointed (B a)} : pointed (sig B) := _.
Global Instance pointed_sigT {A B} {a : pointed A} {b : pointed (B a)} : pointed (sigT B) := _.
Global Instance pointed_sig2 {A} {B C : A -> Prop} {a : pointed A} {b : pointed (B a)} {c : pointed (C a)} : pointed (sig2 B C) := _.
Global Instance pointed_sigT2 {A B C} {a : pointed A} {b : pointed (B a)} {c : pointed (C a)} : pointed (sigT2 B C) := _.
Global Instance pointed_ex {A} {B : A -> Prop} {a : pointed A} {b : pointed (B a)} : pointed (ex B) := _.
Global Instance pointed_ex2 {A} {B C : A -> Prop} {a : pointed A} {b : pointed (B a)} {c : pointed (C a)} : pointed (ex2 B C) := _.
Global Instance pointed_ex_inhab {A} {B : A -> Prop} {a : pointed (inhabited A)} {b : forall a, pointed (B a)} : pointed (ex B)
  := match a return ex B with
     | inhabits a => ex_intro _ a (b a)
     end.
Global Instance pointed_ex2_inhab {A} {B C : A -> Prop} {a : pointed (inhabited A)} {b : forall a, pointed (B a)} {c : forall a, pointed (C a)} : pointed (ex2 B C)
  := match a return ex2 B C with
     | inhabits a => ex_intro2 _ _ a (b a) (c a)
     end.
Global Instance pointed_eq_refl {A x} : pointed (x = x :> A) := _.
Global Instance pointed_impl {A} {B : A -> Type} {f : forall a : pointed A, pointed (B a)} : pointed (forall a, B a) | 3 := f.
Global Instance pointed_Prop : pointed Prop := True.
Global Instance pointed_Set : pointed Set := True.
Global Instance pointed_Type : pointed Type := True.

Module Export Hints.
  Export Crypto.Util.FixCoqMistakes.
  Export Hints1.
  Global Existing Instances
         pointed_True
         pointed_unit
         pointed_bool
         pointed_list
         pointed_nat
         pointed_N
         pointed_positive
         pointed_Z
         pointed_inhabited
         pointed_prod
         pointed_and
         pointed_sig
         pointed_sigT
         pointed_sig2
         pointed_sigT2
         pointed_ex
         pointed_ex2
         pointed_ex_inhab
         pointed_ex2_inhab
         pointed_eq_refl
         pointed_Prop
         pointed_Set
         pointed_Type
  .
  Global Existing Instances
         pointed_sum_l
         pointed_sum_r
         pointed_or_l
         pointed_or_r
  | 2.
  Global Existing Instance pointed_impl | 3.
End Hints.
