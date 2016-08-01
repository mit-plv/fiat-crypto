Class IsHProp T := allpath_hprop : forall x y : T, x = y.

Notation IsHPropRel R := (forall x y, IsHProp (R x y)).

Ltac hprop_destruct_trivial_step :=
  match goal with
  | [ H : unit |- _ ] => destruct H
  | [ H : True |- _ ] => destruct H
  | [ H : False |- _ ] => destruct H
  | [ H : Empty_set |- _ ] => destruct H
  | [ H : prod _ _ |- _ ] => destruct H
  | [ H : and _ _ |- _ ] => destruct H
  | [ H : sigT _ |- _ ] => destruct H
  | [ H : sig _ |- _ ] => destruct H
  | [ H : ex _ |- _ ] => destruct H
  | [ H : forall x y : ?A, x = y, x0 : ?A, x1 : ?A |- _ ]
    => destruct (H x0 x1)
  | [ H : forall a0 (x y : _), x = y, x0 : ?A, x1 : ?A |- _ ]
    => destruct (H _ x0 x1)
  end.
Ltac hprop_destruct_trivial := repeat hprop_destruct_trivial_step.

Ltac pre_hprop :=
  repeat (intros
          || subst
          || hprop_destruct_trivial
          || split
          || unfold IsHProp in *
          || hnf ).

Ltac solve_hprop_transparent_with tac :=
  pre_hprop;
  try solve [ reflexivity
            | decide equality; eauto with nocore
            | tac ].

Ltac solve_hprop_transparent := solve_hprop_transparent_with fail.

Local Hint Extern 0 => solve [ solve_hprop_transparent ] : typeclass_instances.

Global Instance ishprop_unit : IsHProp unit. exact _. Defined.
Global Instance ishprop_True : IsHProp True. exact _. Defined.
Global Instance ishprop_Empty_set : IsHProp Empty_set. exact _. Defined.
Global Instance ishprop_False : IsHProp False. exact _. Defined.
Global Instance ishprop_prod {A B} `{IsHProp A, IsHProp B} : IsHProp (A * B). exact _. Defined.
Global Instance ishprop_and {A B : Prop} `{IsHProp A, IsHProp B} : IsHProp (A /\ B). exact _. Defined.
Global Instance ishprop_sigT {A P} `{IsHProp A, forall a : A, IsHProp (P a)} : IsHProp (@sigT A P). exact _. Defined.
Global Instance ishprop_sig {A} {P : A -> Prop} `{IsHProp A, forall a : A, IsHProp (P a)} : IsHProp (@sig A P). exact _. Defined.
