Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Import invert_expr.
  Import defaults.

  Module DeadCodeElimination.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Fixpoint compute_live' {t} (e : @expr (fun _ => PositiveSet.t) t) (cur_idx : positive)
        : positive * PositiveSet.t
        := match e with
           | expr.Var t v => (cur_idx, v)
           | expr.App s d f x
             => let '(idx, live1) := @compute_live' _ f cur_idx in
                let '(idx, live2) := @compute_live' _ x idx in
                (idx, PositiveSet.union live1 live2)
           | expr.Abs s d f
             => let '(_, live) := @compute_live' _ (f PositiveSet.empty) cur_idx in
                (cur_idx, live)
           | expr.LetIn tx tC ex eC
             => let '(idx, live) := @compute_live' tx ex cur_idx in
                let '(_, live) := @compute_live' tC (eC (PositiveSet.add idx live)) (Pos.succ idx) in
                (Pos.succ idx, live)
           | expr.Ident t idc => (cur_idx, PositiveSet.empty)
           end.
      Definition compute_live {t} e : PositiveSet.t := snd (@compute_live' t e 1).
      Definition ComputeLive {t} (e : expr.Expr t) := compute_live (e _).

      Section with_var.
        Context {var : type -> Type}
                (live : PositiveSet.t).
        Definition OUGHT_TO_BE_UNUSED {T1 T2} (v : T1) (v' : T2) := v.
        Global Opaque OUGHT_TO_BE_UNUSED.
        Fixpoint eliminate_dead' {t} (e : @expr (@expr var) t) (cur_idx : positive)
          : positive * @expr var t
          := match e with
             | expr.Var t v => (cur_idx, v)
             | expr.Ident t idc => (cur_idx, expr.Ident idc)
             | expr.App s d f x
               => let '(idx, f') := @eliminate_dead' _ f cur_idx in
                  let '(idx, x') := @eliminate_dead' _ x idx in
                  (idx, expr.App f' x')
             | expr.Abs s d f
               => (cur_idx, expr.Abs (fun v => snd (@eliminate_dead' _ (f (expr.Var v)) cur_idx)))
             | expr.LetIn tx tC ex eC
               => let '(idx, ex') := @eliminate_dead' tx ex cur_idx in
                  let eC' := fun v => snd (@eliminate_dead' _ (eC v) (Pos.succ idx)) in
                  if PositiveSet.mem idx live
                  then (Pos.succ idx, expr.LetIn ex' (fun v => eC' (expr.Var v)))
                  else (Pos.succ idx, eC' (OUGHT_TO_BE_UNUSED ex' (Pos.succ idx, PositiveSet.elements live)))
             end.

        Definition eliminate_dead {t} e : expr t
          := snd (@eliminate_dead' t e 1).
      End with_var.

      Definition EliminateDead {t} (e : expr.Expr t) : expr.Expr t
        := fun var => eliminate_dead (ComputeLive e) (e _).
    End with_ident.
  End DeadCodeElimination.

  Module Subst01.
    Local Notation PositiveMap_incr idx m
      := (PositiveMap.add idx (match PositiveMap.find idx m with
                               | Some n => S n
                               | None => S O
                               end) m).
    Local Notation PositiveMap_union m1 m2
      := (PositiveMap.map2
            (fun c1 c2
             => match c1, c2 with
                | Some n1, Some n2 => Some (n1 + n2)%nat
                | Some n, None
                | None, Some n
                  => Some n
                | None, None => None
                end) m1 m2).
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Fixpoint compute_live_counts' {t} (e : @expr (fun _ => positive) t) (cur_idx : positive)
        : positive * PositiveMap.t nat
        := match e with
           | expr.Var t v => (cur_idx, PositiveMap_incr v (PositiveMap.empty _))
           | expr.Ident t idc => (cur_idx, PositiveMap.empty _)
           | expr.App s d f x
             => let '(idx, live1) := @compute_live_counts' _ f cur_idx in
                let '(idx, live2) := @compute_live_counts' _ x idx in
                (idx, PositiveMap_union live1 live2)
           | expr.Abs s d f
             => let '(idx, live) := @compute_live_counts' _ (f cur_idx) (Pos.succ cur_idx) in
                (cur_idx, live)
           | expr.LetIn tx tC ex eC
             => let '(idx, live1) := @compute_live_counts' tx ex cur_idx in
                let '(idx, live2) := @compute_live_counts' tC (eC idx) (Pos.succ idx) in
                (idx, PositiveMap_union live1 live2)
           end.
      Definition compute_live_counts {t} e : PositiveMap.t _ := snd (@compute_live_counts' t e 1).
      Definition ComputeLiveCounts {t} (e : expr.Expr t) := compute_live_counts (e _).

      Section with_var.
        Context {var : type -> Type}
                (live : PositiveMap.t nat).
        Fixpoint subst01' {t} (e : @expr (@expr var) t) (cur_idx : positive)
          : positive * @expr var t
          := match e with
             | expr.Var t v => (cur_idx, v)
             | expr.Ident t idc => (cur_idx, expr.Ident idc)
             | expr.App s d f x
               => let '(idx, f') := @subst01' _ f cur_idx in
                  let '(idx, x') := @subst01' _ x idx in
                  (idx, expr.App f' x')
             | expr.Abs s d f
               => (cur_idx, expr.Abs (fun v => snd (@subst01' _ (f (expr.Var v)) (Pos.succ cur_idx))))
             | expr.LetIn tx tC ex eC
               => let '(idx, ex') := @subst01' tx ex cur_idx in
                  let eC' := fun v => snd (@subst01' tC (eC v) (Pos.succ idx)) in
                  if match PositiveMap.find idx live with
                     | Some n => (n <=? 1)%nat
                     | None => true
                     end
                  then (Pos.succ idx, eC' ex')
                  else (Pos.succ idx, expr.LetIn ex' (fun v => eC' (expr.Var v)))
             end.

        Definition subst01 {t} e : expr t
          := snd (@subst01' t e 1).
      End with_var.

      Definition Subst01 {t} (e : expr.Expr t) : expr.Expr t
        := fun var => subst01 (ComputeLiveCounts e) (e _).
    End with_ident.
  End Subst01.
End Compilers.
