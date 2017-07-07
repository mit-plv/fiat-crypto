Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Util.Notations.

Create HintDb wf discriminated.

Ltac solve_wf_side_condition := solve [ eassumption | eauto 250 with wf ].

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Local Notation eP2 := (fun t1t2 => var1 (fst t1t2) * var2 (snd t1t2))%type (only parsing).
    Local Notation eP := (fun t => var1 t * var2 t)%type (only parsing).
    Local Notation "x == y" := (existT eP _ (x, y)%core).
    Fixpoint flatten_binding_list2 {t1 t2} (x : interp_flat_type var1 t1) (y : interp_flat_type var2 t2) : list (sigT eP2)
      := (match t1, t2 return interp_flat_type var1 t1 -> interp_flat_type var2 t2 -> list _ with
          | Tbase t1, Tbase t2 => fun x y => existT eP2 (t1, t2)%core (x, y)%core :: nil
          | Unit, Unit => fun x y => nil
          | Prod t0 t1, Prod t0' t1'
            => fun x y => @flatten_binding_list2 _ _ (snd x) (snd y) ++ @flatten_binding_list2 _ _ (fst x) (fst y)
          | Tbase _, _
          | Unit, _
          | Prod _ _, _
            => fun _ _ => nil
          end x y)%list.
    Fixpoint flatten_binding_list {t} (x : interp_flat_type var1 t) (y : interp_flat_type var2 t) : list (sigT eP)
      := (match t return interp_flat_type var1 t -> interp_flat_type var2 t -> list _ with
          | Tbase _ => fun x y => (x == y) :: nil
          | Unit => fun x y => nil
          | Prod t0 t1 => fun x y => @flatten_binding_list _ (snd x) (snd y) ++ @flatten_binding_list _ (fst x) (fst y)
          end x y)%list.

    Inductive wff : list (sigT eP) -> forall {t}, @exprf var1 t -> @exprf var2 t -> Prop :=
    | WfTT : forall G, @wff G _ TT TT
    | WfVar : forall G (t : base_type_code) x x', List.In (x == x') G -> @wff G (Tbase t) (Var x) (Var x')
    | WfOp : forall G {t} {tR} (e : @exprf var1 t) (e' : @exprf var2 t) op,
        wff G e e'
        -> wff G (Op (tR := tR) op e) (Op (tR := tR) op e')
    | WfLetIn : forall G t1 t2 e1 e1' (e2 : interp_flat_type var1 t1 -> @exprf var1 t2) e2',
        wff G e1 e1'
        -> (forall x1 x2, wff (flatten_binding_list x1 x2 ++ G) (e2 x1) (e2' x2))
        -> wff G (LetIn e1 e2) (LetIn e1' e2')
    | WfPair : forall G {t1} {t2} (e1: @exprf var1 t1) (e2: @exprf var1 t2)
                      (e1': @exprf var2 t1) (e2': @exprf var2 t2),
        wff G e1 e1'
        -> wff G e2 e2'
        -> wff G (Pair e1 e2) (Pair e1' e2').
    Inductive wf : forall {t}, @expr var1 t -> @expr var2 t -> Prop :=
    | WfAbs : forall A B e e',
        (forall x x', @wff (flatten_binding_list x x') B (e x) (e' x'))
        -> @wf (Arrow A B) (Abs e) (Abs e').
  End with_var.

  Definition Wf {t} (E : @Expr t) := forall var1 var2, wf (E var1) (E var2).
End language.

Global Arguments wff {_ _ _ _} G {t} _ _.
Global Arguments wf {_ _ _ _ t} _ _.
Global Arguments Wf {_ _ t} _.

Hint Constructors wf wff : wf.
