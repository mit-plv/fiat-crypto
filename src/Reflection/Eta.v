Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).
  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).

    Section gen_flat_type.
      Context (eta : forall {A B}, A * B -> A * B).
      Fixpoint interp_flat_type_eta_gen {t T} : (interp_flat_type var t -> T) -> interp_flat_type var t -> T
        := match t return (interp_flat_type var t -> T) -> interp_flat_type var t -> T with
           | Tbase T => fun f => f
           | Unit => fun f => f
           | Prod A B
             => fun f x
                => let '(a, b) := eta _ _ x in
                   @interp_flat_type_eta_gen
                     A _
                     (fun a' => @interp_flat_type_eta_gen B _ (fun b' => f (a', b')) b)
                     a
           end.

      Section gen_type.
        Context (exprf_eta : forall {t} (e : exprf t), exprf t).
        Definition expr_eta_gen {t} (e : expr t) : expr (Arrow (domain t) (codomain t))
          := Abs (interp_flat_type_eta_gen (fun x => exprf_eta _ (invert_Abs e x))).
      End gen_type.

      Fixpoint exprf_eta_gen {t} (e : exprf t) : exprf t
        := match e in Syntax.exprf _ _ t return exprf t with
           | TT => TT
           | Var t v => Var v
           | Op t1 tR opc args => Op opc (@exprf_eta_gen _ args)
           | LetIn tx ex tC eC
             => LetIn (@exprf_eta_gen _ ex)
                      (interp_flat_type_eta_gen eC)
           | Pair tx ex ty ey => Pair (@exprf_eta_gen _ ex) (@exprf_eta_gen _ ey)
           end.
    End gen_flat_type.

    Definition interp_flat_type_eta {t T}
      := @interp_flat_type_eta_gen (fun _ _ x => x) t T.
    Definition interp_flat_type_eta' {t T}
      := @interp_flat_type_eta_gen (fun _ _ x => (fst x, snd x)) t T.
    Definition exprf_eta {t}
      := @exprf_eta_gen (fun _ _ x => x) t.
    Definition exprf_eta' {t}
      := @exprf_eta_gen (fun _ _ x => (fst x, snd x)) t.
    Definition expr_eta {t}
      := @expr_eta_gen (fun _ _ x => x) (@exprf_eta) t.
    Definition expr_eta' {t}
      := @expr_eta_gen (fun _ _ x => (fst x, snd x)) (@exprf_eta') t.
  End with_var.
  Definition ExprEtaGen eta {t} (e : Expr t) : Expr (Arrow (domain t) (codomain t))
    := fun var => expr_eta_gen eta (@exprf_eta_gen var eta) (e var).
  Definition ExprEta {t} (e : Expr t) : Expr (Arrow (domain t) (codomain t))
    := fun var => expr_eta (e var).
  Definition ExprEta' {t} (e : Expr t) : Expr (Arrow (domain t) (codomain t))
    := fun var => expr_eta' (e var).
End language.
