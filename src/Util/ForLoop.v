(** * Definition and Notations for [for (int i = i₀; i < i∞; i += Δi)] *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Notations.

Section with_body.
  Context {stateT : Type}
          (body : nat -> stateT -> stateT).

  Fixpoint repeat_function (count : nat) (st : stateT) : stateT
    := match count with
       | O => st
       | S count' => repeat_function count' (body count st)
       end.
End with_body.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Definition for_loop {stateT} (i0 finish : Z) (step : Z) (initial : stateT) (body : Z -> stateT -> stateT)
  : stateT
  := let count := Z.to_nat (Z.quot (finish - i0 + step - Z.sgn step) step) in
     repeat_function (fun c => body (i0 + step * Z.of_nat (count - c))) count initial.


Notation "'for' i (:= i0 ; += step ; < finish ) 'updating' ( state := initial ) {{ body }}"
  := (for_loop i0 finish step initial (fun i state => body))
     : core_scope.

Module Import ForNotationConstants.
  Definition eq := @eq Z.
  Module Z.
    Definition ltb := Z.ltb.
    Definition ltb' := Z.ltb.
    Definition gtb := Z.gtb.
    Definition gtb' := Z.gtb.
  End Z.
End ForNotationConstants.

Delimit Scope for_notation_scope with for_notation.
Notation "x += y" := (eq x (Z.pos y)) : for_notation_scope.
Notation "x -= y" := (eq x (Z.neg y)) : for_notation_scope.
Notation "++ x" := (x += 1)%for_notation : for_notation_scope.
Notation "-- x" := (x -= 1)%for_notation : for_notation_scope.
Notation "x ++" := (x += 1)%for_notation : for_notation_scope.
Notation "x --" := (x -= 1)%for_notation : for_notation_scope.
Infix "<" := Z.ltb : for_notation_scope.
Infix ">" := Z.gtb : for_notation_scope.
Notation "x <= y" := (Z.ltb' x (y + 1)) : for_notation_scope.
Notation "x >= y" := (Z.gtb' x (y - 1)) : for_notation_scope.

Class class_eq {A} (x y : A) := make_class_eq : x = y.
Global Instance class_eq_refl {A x} : @class_eq A x x := eq_refl.

Class for_loop_is_good (i0 : Z) (step : Z) (finish : Z) (cmp : Z -> Z -> bool)
  := make_good :
       ((Z.sgn step =? Z.sgn (finish - i0))
          && (cmp i0 finish))
       = true.
Hint Extern 0 (for_loop_is_good _ _ _ _) => vm_compute; reflexivity : typeclass_instances.

Definition for_loop_notation {i0 : Z} {step : Z} {finish : Z} {stateT} {initial : stateT}
           {cmp : Z -> Z -> bool}
           step_expr finish_expr (body : Z -> stateT -> stateT)
           {Hstep : class_eq (fun i => i = step) step_expr}
           {Hfinish : class_eq (fun i => cmp i finish) finish_expr}
           {Hgood : for_loop_is_good i0 step finish cmp}
  : stateT
  := for_loop i0 finish step initial body.

Notation "'for' ( 'int' i = i0 ; finish_expr ; step_expr ) 'updating' ( state1 .. staten = initial ) {{ body }}"
  := (@for_loop_notation
        i0%Z _ _ _ initial%Z _
        (fun i : Z => step_expr%for_notation)
        (fun i : Z => finish_expr%for_notation)
        (fun (i : Z) => (fun state1 => .. (fun staten => body) .. ))
        _ _ _).
Notation "'for' ( 'int' i = i0 ; finish_expr ; step_expr ) 'updating' ( state1 .. staten = initial ) {{ body }}"
  := (@for_loop_notation
        i0%Z _ _ _ initial%Z _
        (fun i : Z => step_expr%for_notation)
        (fun i : Z => finish_expr%for_notation)
        (fun (i : Z) => (fun state1 => .. (fun staten => body) .. ))
        eq_refl eq_refl _).
