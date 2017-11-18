Require Import Crypto.Compilers.Syntax.

Section language.
  Context {base_type_code}
          {var : base_type_code -> Type}.

  Section cps.
    Context {rT : Type}
            (Forall : forall T (R : var T -> rT), rT).

    Fixpoint intros_interp_flat_type_cps
             {t : flat_type base_type_code}
      : forall (R : interp_flat_type var t -> rT),
        rT
      := match t return (interp_flat_type var t -> rT) -> rT with
         | Tbase T => fun R => Forall _ (fun v : var T => R v)
         | Unit => fun R => R tt
         | Prod A B
           => fun R : interp_flat_type _ A * interp_flat_type _ B -> _
              => @intros_interp_flat_type_cps
                   A
                   (fun a
                    => @intros_interp_flat_type_cps
                         B
                         (fun b
                          => R (a, b)))
         end.
  End cps.
  Definition intros_interp_flat_type_Prop {t}
    := @intros_interp_flat_type_cps Prop (fun T R => forall v : var T, R v) t.
  Definition intros_interp_flat_type_Type {t}
    := @intros_interp_flat_type_cps Type (fun T R => forall v : var T, R v) t.

  Fixpoint intros_interp_flat_type
           {t : flat_type base_type_code}
    : forall {R : interp_flat_type var t -> Type},
      @intros_interp_flat_type_Type t R
      -> (forall v : interp_flat_type var t, R v)
    := match t return forall R : interp_flat_type var t -> Type,
           @intros_interp_flat_type_Type t R -> (forall v : interp_flat_type _ t, R v)
       with
       | Tbase T => fun R f => f
       | Unit => fun R p 'tt => p
       | Prod A B
         => fun (R : interp_flat_type _ A * interp_flat_type _ B -> _)
                (f : intros_interp_flat_type_Type
                       (fun a => intros_interp_flat_type_Type (fun b => R (a, b))))
                '((a, b) : interp_flat_type _ A * interp_flat_type _ B)
            => @intros_interp_flat_type
                 B _ (@intros_interp_flat_type A _ f a) b
       end.

  Fixpoint introsP_interp_flat_type
           {t : flat_type base_type_code}
    : forall {R : interp_flat_type var t -> Prop},
      @intros_interp_flat_type_Prop t R
      -> (forall v : interp_flat_type var t, R v)
    := match t return forall R : interp_flat_type var t -> Prop,
           @intros_interp_flat_type_Prop t R -> (forall v : interp_flat_type _ t, R v)
       with
       | Tbase T => fun R f => f
       | Unit => fun R p 'tt => p
       | Prod A B
         => fun (R : interp_flat_type _ A * interp_flat_type _ B -> _)
                (f : intros_interp_flat_type_Prop
                       (fun a => intros_interp_flat_type_Prop (fun b => R (a, b))))
                '((a, b) : interp_flat_type _ A * interp_flat_type _ B)
            => @introsP_interp_flat_type
                 B _ (@introsP_interp_flat_type A _ f a) b
       end.
End language.

Ltac post_intro_interp_flat_type_intros :=
  let do_cbv _ :=
      (cbv [intros_interp_flat_type_Type intros_interp_flat_type_Prop intros_interp_flat_type_cps]) in
  lazymatch goal with
  | [ |- @intros_interp_flat_type_Type _ ?var ?t ?R ]
    => let t' := (eval cbv in t) in
       change (@intros_interp_flat_type_Type _ var t' (fun v => id (R v)));
       do_cbv (); post_intro_interp_flat_type_intros
  | [ |- @intros_interp_flat_type_Prop _ ?var ?t ?R ]
    => let t' := (eval cbv in t) in
       change (@intros_interp_flat_type_Prop _ var t' (fun v => id (R v)));
       do_cbv (); post_intro_interp_flat_type_intros
  | [ |- forall x, _ ] => intro; post_intro_interp_flat_type_intros
  | [ |- id ?P ] => change P
  end.
Ltac intro_interp_flat_type :=
  lazymatch goal with
  | [ |- forall v : interp_flat_type ?var ?t, @?R v ]
    => let t' := (eval compute in t) in
       refine (@intros_interp_flat_type _ var t' (fun v => id (R v)) _);
       post_intro_interp_flat_type_intros
  end.
