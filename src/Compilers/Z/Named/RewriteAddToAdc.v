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

  Definition do_rewrite
             {t} (e : exprf t)
    : option (exprf t)
    := match e in Named.exprf _ _ _ t return option (exprf t) with
       |           (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0)
         => match P0 in Named.exprf _ _ _ t return option (exprf t) with
            |      (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var _ a2') as ex1) in P1)
              => match P1 in Named.exprf _ _ _ t return option (exprf t) with
                 | (nlet c        : tZ      := (ADX (Var _ c1') (Var _ c2') as ex2) in P)
                   => if (((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                            && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                            && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                      then Some (nlet (a2, c1) : tZ * tZ := ex0 in
                                 nlet (s , c2) : tZ * tZ := ex1 in
                                 nlet c        : tZ      := ex2 in
                                 nlet (s, c)   : tZ * tZ := ADC bw1 c0 a b in
                                 P)
                      else None
                 | P1' => None
                 end
            | P0' => None
            end
       | _ => None
       end%core%nexpr%bool.

  Definition do_rewriteo {t} (e : exprf t) : exprf t
    := match do_rewrite e with
       | Some e' => e'
       | None => e
       end.

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
    := do_rewriteo (@rewrite_exprf_prestep (@rewrite_exprf) t e).

  Definition rewrite_expr {t} (e : expr t) : expr t
    := match e in Named.expr _ _ _ t return expr t with
       | Abs _ _ n f => Abs n (rewrite_exprf f)
       end.
End named.
