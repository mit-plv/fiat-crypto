Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Rewriter.Language.Language.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Import invert_expr.

  Module Subst01.
    Section with_counter.
      Context {t : Type}
              (one : t)
              (incr : t -> t).

      Local Notation PositiveMap_incr idx m
        := (PositiveMap.add idx (match PositiveMap.find idx m with
                                 | Some n => incr n
                                 | None => one
                                 end) m).

      Section with_ident.
        Context {base_type : Type}.
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}.
        Local Notation expr := (@expr.expr base_type ident).
        (** N.B. This does not work well when let-binders are not at top-level *)
        Fixpoint compute_live_counts' {t} (e : @expr (fun _ => positive) t) (cur_idx : positive) (live : PositiveMap.t _)
          : positive * PositiveMap.t _
          := match e with
             | expr.Var t v => (cur_idx, PositiveMap_incr v live)
             | expr.Ident t idc => (cur_idx, live)
             | expr.App s d f x
               => let '(idx, live) := @compute_live_counts' _ f cur_idx live in
                  let '(idx, live) := @compute_live_counts' _ x idx live in
                  (idx, live)
             | expr.Abs s d f
               => let '(idx, live) := @compute_live_counts' _ (f cur_idx) (Pos.succ cur_idx) live in
                  (cur_idx, live)
             | expr.LetIn tx tC ex eC
               => let '(idx, live) := @compute_live_counts' tC (eC cur_idx) (Pos.succ cur_idx) live in
                  if PositiveMap.mem cur_idx live
                  then @compute_live_counts' tx ex idx live
                  else (idx, live)
             end.
        Definition compute_live_counts {t} e : PositiveMap.t _ := snd (@compute_live_counts' t e 1 (PositiveMap.empty _)).
        Definition ComputeLiveCounts {t} (e : expr.Expr t) := compute_live_counts (e _).

        Section with_var.
          Context (doing_subst : forall T1 T2, T1 -> T2 -> T1)
                  {var : type -> Type}
                  (should_subst : t -> bool)
                  (live : PositiveMap.t t).
          Fixpoint subst0n' {t} (e : @expr (@expr var) t) (cur_idx : positive)
            : positive * @expr var t
            := match e with
               | expr.Var t v => (cur_idx, v)
               | expr.Ident t idc => (cur_idx, expr.Ident idc)
               | expr.App s d f x
                 => let '(idx, f') := @subst0n' _ f cur_idx in
                    let '(idx, x') := @subst0n' _ x idx in
                    (idx, expr.App f' x')
               | expr.Abs s d f
                 => (cur_idx, expr.Abs (fun v => snd (@subst0n' _ (f (expr.Var v)) (Pos.succ cur_idx))))
               | expr.LetIn tx tC ex eC
                 => let '(idx, ex') := @subst0n' tx ex cur_idx in
                    let eC' := fun v => snd (@subst0n' tC (eC v) (Pos.succ cur_idx)) in
                    if match PositiveMap.find cur_idx live with
                       | Some n => should_subst n
                       | None => true
                       end
                    then (Pos.succ cur_idx, eC' (doing_subst _ _ ex' (Pos.succ cur_idx, PositiveMap.elements live)))
                    else (Pos.succ cur_idx, expr.LetIn ex' (fun v => eC' (expr.Var v)))
               end.

          Definition subst0n {t} e : expr t
            := snd (@subst0n' t e 1).
        End with_var.

        Definition Subst0n (doing_subst : forall T1 T2, T1 -> T2 -> T1) (should_subst : t -> bool) {t} (e : expr.Expr t) : expr.Expr t
          := fun var => subst0n doing_subst should_subst (ComputeLiveCounts e) (e _).
      End with_ident.
    End with_counter.

    Section for_01.
      Inductive one_or_more := one | more.
      Local Notation t := one_or_more.
      Let incr : t -> t := fun _ => more.
      Let should_subst : t -> bool
        := fun v => match v with
                    | one => true
                    | more => false
                    end.

      Definition Subst01 {base_type ident} {t} (e : expr.Expr t) : expr.Expr t
        := @Subst0n _ one incr base_type ident (fun _ _ x _ => x) should_subst t e.
    End for_01.
  End Subst01.

  Module DeadCodeElimination.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Definition OUGHT_TO_BE_UNUSED {T1 T2} (v : T1) (v' : T2) := v.
      Global Opaque OUGHT_TO_BE_UNUSED.

      Definition EliminateDead {t} (e : expr.Expr t) : expr.Expr t
        := @Subst01.Subst0n unit tt (fun _ => tt) base_type ident (@OUGHT_TO_BE_UNUSED) (fun _ => false) t e.
    End with_ident.
  End DeadCodeElimination.
End Compilers.
