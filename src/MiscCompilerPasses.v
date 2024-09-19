From Coq Require Import ZArith.
From Coq Require Import MSetPositive.
From Coq Require Import FMapPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Rewriter.Language.Language.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Language.TreeCaching.
Import ListNotations. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export Language.TreeCaching.Compilers.
  Import invert_expr.

  Module Subst01.
    Section with_counter.
      Context {t : Type}
              (one : t)
              (incr : t -> t)
              (incr_always_live : option t -> t).

      Local Notation PositiveMap_incr idx m
        := (PositiveMap.add idx (match PositiveMap.find idx m with
                                 | Some n => incr n
                                 | None => one
                                 end) m).

      Local Notation PositiveMap_incr_always_live idx m
        := (PositiveMap.add idx (incr_always_live (PositiveMap.find idx m)) m).

      Section with_ident.
        Context {base_type : Type}.
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}
                (** some identifiers, like [comment], might always be live *)
                (is_ident_always_live : forall t, ident t -> bool).
        Local Notation expr := (@expr.expr base_type ident).
        (* [option t] is "is the let-in here live?", meaningless elsewhere; the thunk is for debugging *)
        Local Notation tree := (@tree_nd.tree (option t * (unit -> positive * list (positive * t)))).
        (** N.B. This does not work well when let-binders are not at top-level *)
        Fixpoint contains_always_live_ident {var} (dummy : forall t, var t) {t} (e : @expr var t)
          : bool
          := match e with
             | expr.Var _ _ => false
             | expr.Ident t idc => is_ident_always_live _ idc
             | expr.App s d f x
               => contains_always_live_ident dummy f || contains_always_live_ident dummy x
             | expr.Abs s d f
               => contains_always_live_ident dummy (f (dummy _))
             | expr.LetIn tx tC ex eC
               => contains_always_live_ident dummy ex || contains_always_live_ident dummy (eC (dummy _))
             end%bool.
        Definition meaningless : option t * (unit -> positive * list (positive * t)) := (None, (fun 'tt => (1%positive, []%list))).
        Global Opaque meaningless.
        Fixpoint compute_live_counts' {t} (e : @expr (fun _ => positive) t) (cur_idx : positive) (live : PositiveMap.t _)
          : positive * PositiveMap.t _ * option tree
          := match e with
             | expr.Var t v
               => let '(idx, live) := (cur_idx, PositiveMap_incr v live) in
                  (idx, live, Some (tree_nd.Var meaningless))
             | expr.Ident t idc
               => let '(idx, live) := (cur_idx, live) in
                  (idx, live, Some (tree_nd.Ident meaningless))
             | expr.App s d f x
               => let '(idx, live, f_tree) := @compute_live_counts' _ f cur_idx live in
                  let '(idx, live, x_tree) := @compute_live_counts' _ x idx live in
                  (idx, live, Some (tree_nd.App meaningless f_tree x_tree))
             | expr.Abs s d f
               => let '(idx, live, f_tree) := @compute_live_counts' _ (f cur_idx) (Pos.succ cur_idx) live in
                  (idx, live, Some (tree_nd.Abs meaningless f_tree))
             | expr.LetIn tx tC ex eC
               => let '(idx, live, C_tree) := @compute_live_counts' tC (eC cur_idx) (Pos.succ cur_idx) live in
                  let live := if contains_always_live_ident (fun _ => cur_idx (* dummy *)) ex
                              then PositiveMap_incr_always_live cur_idx live
                              else live in
                  let debug_info := fun 'tt => (Pos.succ cur_idx, PositiveMap.elements live) in
                  match PositiveMap.find cur_idx live with
                  | Some x_count
                    => let '(x_idx, x_live, x_tree) := @compute_live_counts' tx ex idx live in
                       (x_idx, x_live, Some (tree_nd.LetIn (Some x_count, debug_info) x_tree C_tree))
                  | None
                    => (idx, live, Some (tree_nd.LetIn (None, debug_info) None C_tree))
                  end
             end%bool.
        Definition compute_live_counts {t} e : option tree := snd (@compute_live_counts' t e 1 (PositiveMap.empty _)).
        Definition ComputeLiveCounts {t} (e : expr.Expr t) := compute_live_counts (e _).

        Section with_var.
          (* [doing_subst_debug] is a hook for something like
             reduction-effects debug print, or for catching bad
             substitutions as in [OUGHT_TO_BE_UNUSED] below, so we can
             debug subst01; we forcibly stuff its second argument into
             a thunk so that it does not impact performance in cbv nor
             in extraction *)
          Context (doing_subst_debug : forall T1 T2, T1 -> (unit -> T2) -> T1)
                  {var : type -> Type}
                  (should_subst : t -> bool).
          (** When [live] is [None], we don't inline anything, just
              dropping [var].  This is required for preventing blowup
              in inlining lets in unused [LetIn]-bound expressions.
              *)
          Fixpoint subst0n (live : option tree) {t} (e : @expr (@expr var) t)
            : @expr var t
            := match e with
               | expr.Var t v => v
               | expr.Ident t idc => expr.Ident idc
               | expr.App s d f x
                 => let '(f_live, x_live)
                      := match live with
                         | Some (tree_nd.App _ f_live x_live) => (f_live, x_live)
                         | _ => (None, None)
                         end%core in
                    let f' := @subst0n f_live _ f in
                    let x' := @subst0n x_live _ x in
                    expr.App f' x'
               | expr.Abs s d f
                 => let f_tree
                      := match live with
                         | Some (tree_nd.Abs _ f_tree) => f_tree
                         | _ => None
                         end in
                    expr.Abs (fun v => @subst0n f_tree _ (f (expr.Var v)))
               | expr.LetIn tx tC ex eC
                 => match live with
                    | Some (tree_nd.LetIn (x_count, debug_info) x_tree C_tree)
                      => let ex' := @subst0n x_tree tx ex in
                         let eC' := fun v => @subst0n C_tree tC (eC v) in
                         if match x_count with
                            | Some n => should_subst n
                            | None => true
                            end
                         then eC' (doing_subst_debug _ _ ex' debug_info)
                         else expr.LetIn ex' (fun v => eC' (expr.Var v))
                    | _
                      => let ex' := @subst0n None tx ex in
                         let eC' := fun v => @subst0n None tC (eC v) in
                         expr.LetIn ex'  (fun v => eC' (expr.Var v))
                    end
               end.
        End with_var.

        Section with_transport.
          Context {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
            {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr var)}.
          (** We pass through [Flat] to ensure that the passed in
              [Expr] only gets invoked at a single [var] type *)
          Definition Subst0n (doing_subst_debug : forall T1 T2, T1 -> (unit -> T2) -> T1) (should_subst : t -> bool) {t} (E : expr.Expr t) : expr.Expr t
            := dlet_nd e := GeneralizeVar.ToFlat E in
                let E := GeneralizeVar.FromFlat e in
                fun var => subst0n doing_subst_debug should_subst (ComputeLiveCounts E) (E _).
        End with_transport.
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

      Definition Subst01
        {base_type ident}
        {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
        {exprDefault : forall var, @DefaultValue.type.base.DefaultT _ _}
        (is_ident_always_live : forall t, ident t -> bool)
        {t} (e : expr.Expr t) : expr.Expr t
        := @Subst0n _ one incr (fun _ => more) base_type ident is_ident_always_live try_make_transport_base_type_cps exprDefault (fun _ _ x _ => x) should_subst t e.
    End for_01.
  End Subst01.

  Module DeadCodeElimination.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Definition OUGHT_TO_BE_UNUSED {T1 T2} (v : T1) (v' : T2) := v.
      Global Opaque OUGHT_TO_BE_UNUSED.
      Definition EliminateDead
        {ident : type -> Type}
        {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
        {exprDefault : forall var, @DefaultValue.type.base.DefaultT _ _}
        (is_ident_always_live : forall t, ident t -> bool)
        {t} (e : expr.Expr t)
        : expr.Expr t
        := @Subst01.Subst0n unit tt (fun _ => tt) (fun _ => tt) base_type ident is_ident_always_live try_make_transport_base_type_cps exprDefault (fun T1 T2 => OUGHT_TO_BE_UNUSED) (fun _ => false) t e.
    End with_ident.
  End DeadCodeElimination.
End Compilers.
