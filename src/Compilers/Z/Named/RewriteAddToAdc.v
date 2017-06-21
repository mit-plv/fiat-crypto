Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Named.GetNames.
Require Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.

Section named.
  Context {Name : Type}
          (name_beq : Name -> Name -> bool).
  Import Named.Syntax.
  Local Notation flat_type := (flat_type base_type).
  Local Notation type := (type base_type).
  Local Notation exprf := (@exprf base_type op Name).
  Local Notation expr := (@expr base_type op Name).

  Local Notation tZ := (Tbase TZ).
  Local Notation ADC bw c x y := (Op (@AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                     (Pair (Pair (t1:=tZ) c (t2:=tZ) x) (t2:=tZ) y)).
  Local Notation ADD bw x y := (ADC bw (Op (OpConst 0) TT) x y).
  Local Notation ADX x y := (Op (@Add TZ TZ TZ) (Pair (t1:=tZ) x (t2:=tZ) y)).
  Local Infix "=Z?" := Z.eqb.
  Local Infix "=n?" := name_beq.

  Definition is_const_or_var {t} (v : exprf t)
    := match v with
       | Var _ _ => true
       | Op _ _ (OpConst _ _) TT => true
       | _ => false
       end.

  Fixpoint name_list_has_duplicate (ls : list Name) : bool
    := match ls with
       | nil => false
       | cons n ns
         => orb (name_list_has_duplicate ns)
                (List.fold_left orb (List.map (name_beq n) ns) false)
       end.

  Definition invertT t
    := option ((Name * Name * Z * exprf tZ * exprf tZ)
               * (Name * Name * Z * exprf tZ * Name)
               * (((Name * Name * Name) * exprf t)
                  + exprf t)).

  Definition invert_for_do_rewrite_step1 {t} (e : exprf t)
    : option ((Name * Name * Z * exprf tZ * exprf tZ) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Z * exprf tZ * exprf tZ) * exprf t) with
       | (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0)
         => Some ((a2, c1, bw1, a, b), P0)
       | _ => None
       end%core%nexpr%bool.
  Definition invert_for_do_rewrite_step2 {t} (e : exprf t)
    : option ((Name * Name * Z * exprf tZ * Name) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Z * exprf tZ * Name) * exprf t) with
       | (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var TZ a2') as ex1) in P1)
         => Some ((s, c2, bw2, c0, a2'), P1)
       | _ => None
       end%core%nexpr%bool.
  Definition invert_for_do_rewrite_step3 {t} (e : exprf t)
    : option ((Name * Name * Name) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Name) * exprf t) with
       | (nlet c        : tZ      := (ADX (Var TZ c1') (Var TZ c2') as ex2) in P)
         => Some ((c, c1', c2'), P)
       | _ => None
       end%core%nexpr%bool.

  Definition invert_for_do_rewrite {t} (e : exprf t)
    : invertT t
    := match invert_for_do_rewrite_step1 e with
       | Some ((a2, c1, bw1, a, b), P0)          (* (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0) *)
         => match invert_for_do_rewrite_step2 P0 with
            | Some ((s, c2, bw2, c0, a2'), P1)   (* (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var TZ a2') as ex1) in P1) *)
              => match match invert_for_do_rewrite_step3 P1 with
                       | Some ((c, c1', c2'), P) (* (nlet c        : tZ      := (ADX (Var TZ c1') (Var TZ c2') as ex2) in P) as P1' *)
                         => if (((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                                  && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                                  && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                            then Some ((a2, c1, bw1, a, b),
                                       (s, c2, bw2, c0, a2'),
                                       inl ((c, c1', c2'), P))
                            else None
                       | None => None
                       end with
                 | Some v => Some v
                 | None => if (((bw1 =Z? bw2) && (a2 =n? a2'))
                                 && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                                 && negb (name_list_has_duplicate (a2::c1::s::c2::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                           then Some ((a2, c1, bw1, a, b),
                                      (s, c2, bw2, c0, a2'),
                                      inr P1)
                           else None
                 end
            | None => None
            end
       | None => None
       end%core%nexpr%bool.

  Definition do_rewrite {t} (e : exprf t)
    : exprf t
    := match invert_for_do_rewrite e with
       | Some ((a2, c1, bw1, a, b),
               (s, c2, bw2, c0, a2'),
               inl ((c, c1', c2'), P))
         => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
             nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
             nlet c        : tZ      := ADX (Var c1') (Var c2') in
             nlet (s, c)   : tZ * tZ := ADC bw1 c0 a b in
             P)
       | Some ((a2, c1, bw1, a, b),
               (s, c2, bw2, c0, a2'),
               inr P)
         => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
             nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
             nlet s        : tZ      := (nlet (s, c1) : tZ * tZ := ADC bw1 c0 a b in Var s) in
             P)
       | None
         => e
       end%core%nexpr.

  Definition rewrite_exprf_prestep
             (rewrite_exprf : forall {t} (e : exprf t), exprf t)
             {t} (e : exprf t)
    : exprf t
    := match e in Named.exprf _ _ _ t return exprf t with
       | TT => TT
       | Var _ n => Var n
       | Op _ _ opc args
         => Op opc (@rewrite_exprf _ args)
       | (nlet nx := ex in eC)
         => (nlet nx := @rewrite_exprf _ ex in @rewrite_exprf _ eC)
       | Pair tx ex ty ey
         => Pair (@rewrite_exprf tx ex) (@rewrite_exprf ty ey)
       end%nexpr.

  Fixpoint rewrite_exprf {t} (e : exprf t) : exprf t
    := do_rewrite (@rewrite_exprf_prestep (@rewrite_exprf) t e).

  Definition rewrite_expr {t} (e : expr t) : expr t
    := match e in Named.expr _ _ _ t return expr t with
       | Abs _ _ n f => Abs n (rewrite_exprf f)
       end.
End named.
