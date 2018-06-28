Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.CPSNotations.
Require Crypto.Util.PrimitiveProd.
Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.UnderLets.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export GENERATEDIdentifiersWithoutTypes.Compilers.
  Import invert_expr.

  Module pattern.
    Export GENERATEDIdentifiersWithoutTypes.Compilers.pattern.

    Module base.
      Local Notation einterp := type.interp.
      Module type.
        Inductive type := any | type_base (t : Compilers.base.type.base) | prod (A B : type) | list (A : type).
      End type.
      Notation type := type.type.

      Module Notations.
        Global Coercion type.type_base : Compilers.base.type.base >-> type.type.
        Bind Scope pbtype_scope with type.type.
        (*Bind Scope ptype_scope with Compilers.type.type type.type.*) (* COQBUG(https://github.com/coq/coq/issues/7699) *)
        Delimit Scope ptype_scope with ptype.
        Delimit Scope pbtype_scope with pbtype.
        Notation "A * B" := (type.prod A%ptype B%ptype) : ptype_scope.
        Notation "A * B" := (type.prod A%pbtype B%pbtype) : pbtype_scope.
        Notation "()" := (type.type_base base.type.unit) : pbtype_scope.
        Notation "()" := (type.base (type.type_base base.type.unit)) : ptype_scope.
        Notation "A -> B" := (type.arrow A%ptype B%ptype) : ptype_scope.
        Notation "??" := type.any : pbtype_scope.
        Notation "??" := (type.base type.any) : ptype_scope.
      End Notations.
    End base.
    Notation type := (type.type base.type).
    Export base.Notations.

    Inductive pattern {ident : Type} :=
    | Wildcard (t : type)
    | Ident (idc : ident)
    | App (f x : pattern).

    Global Arguments Wildcard {ident%type} t%ptype.

    Notation ident := ident.ident.

    Module Export Notations.
      Export base.Notations.
      Delimit Scope pattern_scope with pattern.
      Bind Scope pattern_scope with pattern.
      Local Open Scope pattern_scope.
      Notation "#?()" := (Ident ident.LiteralUnit) : pattern_scope.
      Notation "#?N" := (Ident ident.LiteralNat) : pattern_scope.
      Notation "#?ℕ" := (Ident ident.LiteralNat) : pattern_scope.
      Notation "#?Z" := (Ident ident.LiteralZ) : pattern_scope.
      Notation "#?ℤ" := (Ident ident.LiteralZ) : pattern_scope.
      Notation "#?B" := (Ident ident.LiteralBool) : pattern_scope.
      Notation "#?𝔹" := (Ident ident.LiteralBool) : pattern_scope.
      Notation "??{ t }" := (Wildcard t) (format "??{ t }") : pattern_scope.
      Notation "??" := (??{??})%pattern : pattern_scope.
      Notation "# idc" := (Ident idc) : pattern_scope.
      Infix "@" := App : pattern_scope.
      Notation "( x , y , .. , z )" := (#ident.pair @ .. (#ident.pair @ x @ y) .. @ z) : pattern_scope.
      Notation "x :: xs" := (#ident.cons @ x @ xs) : pattern_scope.
      Notation "xs ++ ys" := (#ident.List_app @ xs @ ys) : pattern_scope.
      Notation "[ ]" := (#ident.nil) : pattern_scope.
      Notation "[ x ]" := (x :: []) : pattern_scope.
      Notation "[ x ; y ; .. ; z ]" :=  (x :: (y :: .. (z :: []) ..)) : pattern_scope.
      Notation "x - y" := (#ident.Z_sub @ x @ y) : pattern_scope.
      Notation "x + y" := (#ident.Z_add @ x @ y) : pattern_scope.
      Notation "x / y" := (#ident.Z_div @ x @ y) : pattern_scope.
      Notation "x * y" := (#ident.Z_mul @ x @ y) : pattern_scope.
      Notation "x 'mod' y" := (#ident.Z_modulo @ x @ y)%pattern : pattern_scope.
      Notation "- x" := (#ident.Z_opp @ x) : pattern_scope.
    End Notations.
  End pattern.
  Export pattern.Notations.
  Notation pattern := (@pattern.pattern pattern.ident).

  Module RewriteRules.
    Module Import AnyExpr.
      Record anyexpr {base_type} {ident var : type.type base_type -> Type}
        := wrap { anyexpr_ty : base_type ; unwrap :> @expr.expr base_type ident var (type.base anyexpr_ty) }.
      Global Arguments wrap {base_type ident var _} _.
    End AnyExpr.

    Module Compile.
      Section with_var0.
        Context {base_type} {ident var : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.

        Fixpoint value' (with_lets : bool) (t : type)
          := match t with
             | type.base t
               => if with_lets then UnderLets (expr t) else expr t
             | type.arrow s d
               => value' false s -> value' true d
             end.
        Definition value := value' false.
        Definition value_with_lets := value' true.

        Definition Base_value {t} : value t -> value_with_lets t
          := match t with
             | type.base t => fun v => UnderLets.Base v
             | type.arrow _ _ => fun v => v
             end.

        Fixpoint splice_under_lets_with_value {T t} (x : UnderLets T) : (T -> value_with_lets t) -> value_with_lets t
          := match t return (T -> value_with_lets t) -> value_with_lets t with
             | type.arrow s d
               => fun k v => @splice_under_lets_with_value T d x (fun x' => k x' v)
             | type.base _ => fun k => x <-- x; k x
             end%under_lets.
        Local Notation "x <--- v ; f" := (splice_under_lets_with_value x (fun v => f%under_lets)) : under_lets_scope.
        Definition splice_value_with_lets {t t'} : value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t'
          := match t return value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t' with
             | type.arrow _ _
               => fun e k => k e
             | type.base _ => fun e k => e <--- e; k e
             end%under_lets.
      End with_var0.
      Section with_var.
        Context {ident var : type.type base.type -> Type}
                {pident : Type}
                (*(invert_Literal_cps : forall t, ident t ~> option (type.interp base.interp t))*)
                (*(beq_typed : forall t (X : pident) (Y : ident t), bool)*)
                (full_types : pident -> Type)
                (invert_bind_args : forall t (idc : ident t) (pidc : pident), option (full_types pidc))
                (type_of_pident : forall (pidc : pident), full_types pidc -> type.type base.type)
                (pident_to_typed : forall (pidc : pident) (args : full_types pidc), ident (type_of_pident pidc args))
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                (of_typed_ident : forall {t}, ident t -> pident)
                (arg_types : pident -> option Type)
                (bind_args : forall {t} (idc : ident t), match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end)
                (pident_beq : pident -> pident -> bool)
                (try_make_transport_ident_cps : forall (P : pident -> Type) (idc1 idc2 : pident), ~> option (P idc1 -> P idc2)).
        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation anyexpr := (@anyexpr ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation value_with_lets := (@value_with_lets base.type ident var).
        Local Notation Base_value := (@Base_value base.type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident var).
        Let type_base (t : base.type) : type := type.base t.
        Coercion type_base : base.type >-> type.

        Context (reify_and_let_binds_base_cps : forall (t : base.type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T).

        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

        Fixpoint reify {with_lets} {t} : value' with_lets t -> expr t
          := match t, with_lets return value' with_lets t -> expr t with
             | type.base _, false => fun v => v
             | type.base _, true => fun v => UnderLets.to_expr v
             | type.arrow s d, _
               => fun f
                  => λ x , @reify _ d (f (@reflect _ s ($x)))
             end%expr%under_lets%cps
        with reflect {with_lets} {t} : expr t -> value' with_lets t
             := match t, with_lets return expr t -> value' with_lets t with
                | type.base _, false => fun v => v
                | type.base _, true => fun v => UnderLets.Base v
                | type.arrow s d, _
                  => fun f (x : value' _ _) => @reflect _ d (f @ (@reify _ s x))
                end%expr%under_lets.

        Definition reify_and_let_binds_cps {with_lets} {t} : value' with_lets t -> forall T, (expr t -> UnderLets T) -> UnderLets T
          := match t, with_lets return value' with_lets t -> forall T, (expr t -> UnderLets T) -> UnderLets T with
             | type.base _, false => reify_and_let_binds_base_cps _
             | type.base _, true => fun v => fun T k => v' <-- v; reify_and_let_binds_base_cps _ v' T k
             | type.arrow s d, _
               => fun f T k => k (reify f)
             end%expr%under_lets%cps.

        Inductive rawexpr : Type :=
        | rIdent {t} (idc : ident t) {t'} (alt : expr t')
        | rApp (f x : rawexpr) {t} (alt : expr t)
        | rExpr {t} (e : expr t)
        | rValue {t} (e : value t).

        Definition type_of_rawexpr (e : rawexpr) : type
          := match e with
             | rIdent t idc t' alt => t'
             | rApp f x t alt => t
             | rExpr t e => t
             | rValue t e => t
             end.
        Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
          := match e with
             | rIdent t idc t' alt => alt
             | rApp f x t alt => alt
             | rExpr t e => e
             | rValue t e => reify e
             end.
        Definition value_of_rawexpr (e : rawexpr) : value (type_of_rawexpr e)
          := Eval cbv [expr_of_rawexpr] in
              match e with
              | rValue t e => e
              | e => reflect (expr_of_rawexpr e)
              end.
        Definition rValueOrExpr {t} : value t -> rawexpr
          := match t with
             | type.base _ => @rExpr _
             | type.arrow _ _ => @rValue _
             end.
        Definition rValueOrExpr2 {t} : value t -> expr t -> rawexpr
          := match t with
             | type.base _ => fun v e => @rExpr _ e
             | type.arrow _ _ => fun v e => @rValue _ v
             end.

        Definition try_rExpr_cps {T t} (k : option rawexpr -> T) : expr t -> T
          := match t with
             | type.base _ => fun e => k (Some (rExpr e))
             | type.arrow _ _ => fun _ => k None
             end.

        Definition reveal_rawexpr_cps (e : rawexpr) : ~> rawexpr
          := fun T k
             => match e with
               | rExpr _ e as r
               | rValue (type.base _) e as r
                 => match e with
                   | expr.Ident t idc => k (rIdent idc e)
                   | expr.App s d f x => k (rApp (rExpr f) (rExpr x) e)
                   | _ => k r
                   end
               | e' => k e'
               end.

        Inductive quant_type := qforall | qexists.

        (* p for pattern *)
        Fixpoint pbase_type_interp_cps (quant : quant_type) (t : pattern.base.type) (K : base.type -> Type) : Type
          := match t with
             | pattern.base.type.any
               => match quant with
                 | qforall => forall t : base.type, K t
                 | qexists => { t : base.type & K t }
                 end
             | pattern.base.type.type_base t => K t
             | pattern.base.type.prod A B
               => @pbase_type_interp_cps
                   quant A
                   (fun A'
                    => @pbase_type_interp_cps
                        quant B (fun B' => K (A' * B')%etype))
             | pattern.base.type.list A
               => @pbase_type_interp_cps
                   quant A (fun A' => K (base.type.list A'))
             end.

        Fixpoint ptype_interp_cps (quant : quant_type) (t : ptype) (K : type -> Type) {struct t} : Type
          := match t with
             | type.base t
               => pbase_type_interp_cps quant t (fun t => K (type.base t))
             | type.arrow s d
               => @ptype_interp_cps
                   quant s
                   (fun s => @ptype_interp_cps
                            quant d (fun d => K (type.arrow s d)))
             end.

        Definition ptype_interp (quant : quant_type) (t : ptype) (K : Type -> Type) : Type
          := ptype_interp_cps quant t (fun t => K (value t)).

        Fixpoint binding_dataT (p : pattern) : Type
          := match p return Type with
             | pattern.Wildcard t => ptype_interp qexists t id
             | pattern.Ident idc => match arg_types idc return Type with
                                   | Some t => t
                                   | None => unit
                                   end
             | pattern.App f x => binding_dataT f * binding_dataT x
             end%type.

        Fixpoint bind_base_cps {t1 t2}
                 (K : base.type -> Type)
                 (v : K t2)
                 {struct t1}
          : ~> option (pbase_type_interp_cps qexists t1 K)
          := match t1 return ~> option (pbase_type_interp_cps qexists t1 K) with
             | pattern.base.type.any
               => (return (Some (existT K t2 v)))
             | pattern.base.type.type_base t
               => (tr <-- base.try_make_transport_cps _ _ _;
                  return (Some (tr v)))
             | pattern.base.type.prod A B
               => fun T k
                 => match t2 return K t2 -> T with
                   | base.type.prod A' B'
                     => fun v
                       => (v' <-- @bind_base_cps B B' (fun B' => K (A' * B')%etype) v;
                            v'' <-- @bind_base_cps A A' (fun A' => pbase_type_interp_cps qexists B (fun B' => K (A' * B')%etype)) v';
                          return (Some v''))
                           T k
                   | _ => fun _ => k None
                   end v
             | pattern.base.type.list A
               => fun T k
                 => match t2 return K t2 -> T with
                   | base.type.list A'
                     => fun v => @bind_base_cps A A' (fun A' => K (base.type.list A')) v T k
                   | _ => fun _ => k None
                   end v
             end%cps.

        Fixpoint bind_value_cps {t1 t2}
                 (K : type -> Type)
                 (v : K t2)
                 {struct t1}
          : ~> option (ptype_interp_cps qexists t1 K)
          := match t1 return ~> option (ptype_interp_cps qexists t1 K) with
             | type.base t1
               => fun T k
                 => match t2 return K t2 -> T with
                   | type.base t2
                     => fun v => bind_base_cps (fun t => K (type.base t)) v T k
                   | _ => fun _ => k None
                   end v
             | type.arrow A B
               => fun T k
                 => match t2 return K t2 -> T with
                   | type.arrow A' B'
                     => fun v
                       => (v' <-- @bind_value_cps B B' (fun B' => K (A' -> B')%etype) v;
                            v'' <-- @bind_value_cps A A' (fun A' => ptype_interp_cps qexists B (fun B' => K (A' -> B')%etype)) v';
                          return (Some v''))
                           T k
                   | _ => fun _ => k None
                   end v
             end%cps.

        Fixpoint bind_data_cps (e : rawexpr) (p : pattern)
          : ~> option (binding_dataT p)
          := match p, e return ~> option (binding_dataT p) with
             | pattern.Wildcard t, _
               => bind_value_cps value (value_of_rawexpr e)
             | pattern.Ident pidc, rIdent _ idc _ _
               => (tr <-- (try_make_transport_ident_cps
                             (fun idc => match arg_types idc with
                                         | Some t1 => t1
                                         | None => unit
                                         end) _ _);
                     return (Some (tr (bind_args _ idc))))
             | pattern.App pf px, rApp f x _ _
               => (f' <-- bind_data_cps f pf;
                     x' <-- bind_data_cps x px;
                   return (Some (f', x')))
             | pattern.Ident _, _
             | pattern.App _ _, _
               => (return None)
             end%cps.

        (** We follow
            http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf,
            "Compiling Pattern Matching to Good Decision Trees" by Luc
            Maranget.  A [decision_tree] describes how to match a
            vector (or list) of patterns against a vector of
            expressions. The cases of a [decision_tree] are:

            - [TryLeaf k onfailure]: Try the kth rewrite rule; if it
              fails, keep going with [onfailure]

            - [Failure]: Abort; nothing left to try

            - [Switch icases app_case default]: With the first element
              of the vector, match on its kind; if it is an identifier
              matching something in [icases], remove the first element
              of the vector run that decision tree; if it is an
              application and [app_case] is not [None], try the
              [app_case] decision_tree, replacing the first element of
              each vector with the two elements of the function and
              the argument its applied to; otherwise, don't modify the
              vectors, and use the [default] decision tree.

            - [Swap i cont]: Swap the first element of the vector with
              the ith element, and keep going with [cont] *)
        Inductive decision_tree :=
        | TryLeaf (k : nat) (onfailure : decision_tree)
        | Failure
        | Switch (icases : list (pident * decision_tree))
                 (app_case : option decision_tree)
                 (default : decision_tree)
        | Swap (i : nat) (cont : decision_tree).

        Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
          := match nth_error ls i, nth_error ls j with
             | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
             | _, _ => None
             end.

        Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : option nat -> list rawexpr -> option (unit -> T) -> T) {struct d} : T
          := match d with
             | TryLeaf k onfailure
               => cont (Some k) ctx
                      (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
             | Failure => cont None ctx None
             | Switch icases app_case default_case
               => match ctx with
                  | nil => cont None ctx None
                  | ctx0 :: ctx'
                    => let default _ := @eval_decision_tree T ctx default_case cont in
                       reveal_rawexpr_cps
                         ctx0 _
                         (fun ctx0'
                          => match ctx0' with
                             | rIdent t idc t' alt
                               => fold_right
                                    (fun '(pidc, icase) default 'tt
                                     => match invert_bind_args _ idc pidc with
                                        | Some args
                                          => @eval_decision_tree
                                               T ctx' icase
                                               (fun k ctx''
                                                => cont k (rIdent (pident_to_typed pidc args) alt :: ctx''))
                                        | None => default tt
                                        end)
                                    default
                                    icases
                                    tt
                             | rApp f x t alt
                               => match app_case with
                                  | Some app_case
                                    => @eval_decision_tree
                                         T (f :: x :: ctx') app_case
                                         (fun k ctx''
                                          => match ctx'' with
                                             | f' :: x' :: ctx'''
                                               => cont k (rApp f' x' alt :: ctx''')
                                             | _ => cont None ctx
                                             end)
                                  | None => default tt
                                  end
                             | rExpr t e
                             | rValue t e
                               => default tt
                             end)
                  end
             | Swap i d'
               => match swap_list 0 i ctx with
                 | Some ctx'
                   => @eval_decision_tree
                       T ctx' d'
                       (fun k ctx''
                        => match swap_list 0 i ctx'' with
                          | Some ctx''' => cont k ctx'''
                          | None => cont None ctx
                          end)
                 | None => cont None ctx None
                 end
             end.

        Local Notation opt_anyexprP ivar
          := (fun should_do_again : bool => UnderLets (@AnyExpr.anyexpr base.type ident (if should_do_again then ivar else var)))
               (only parsing).
        Local Notation opt_anyexpr ivar
          := (option (sigT (opt_anyexprP ivar))) (only parsing).

        Definition rewrite_ruleTP
          := (fun p : pattern => binding_dataT p -> forall T, (opt_anyexpr value -> T) -> T).
        Definition rewrite_ruleT := sigT rewrite_ruleTP.
        Definition rewrite_rulesT
          := (list rewrite_ruleT).

        Definition eval_rewrite_rules
                   (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
                   (maybe_do_again
                    := fun (should_do_again : bool) (t : base.type)
                       => if should_do_again return ((@expr.expr base.type ident (if should_do_again then value else var) t) -> UnderLets (expr t))
                         then do_again t
                         else UnderLets.Base)
                   (d : decision_tree)
                   (rew : rewrite_rulesT)
                   (e : rawexpr)
          : UnderLets (expr (type_of_rawexpr e))
          := eval_decision_tree
               (e::nil) d
               (fun k ctx default_on_rewrite_failure
                => match k, ctx return UnderLets (expr (type_of_rawexpr e)) with
                  | Some k', e'::nil
                    => match nth_error rew k' return UnderLets (expr (type_of_rawexpr e)) with
                      | Some (existT p f)
                        => bind_data_cps
                            e' p _
                            (fun v
                             => match v with
                               | Some v
                                 => f v _
                                     (fun fv
                                      => match fv return UnderLets (expr (type_of_rawexpr e)) with
                                        | Some (existT should_do_again fv)
                                          => (fv <-- fv;
                                               fv <-- maybe_do_again should_do_again _ fv;
                                               type.try_transport_cps
                                                 base.try_make_transport_cps _ _ _ fv _
                                                 (fun fv'
                                                  => match fv', default_on_rewrite_failure with
                                                    | Some fv'', _ => UnderLets.Base fv''
                                                    | None, Some default => default tt
                                                    | None, None => UnderLets.Base (expr_of_rawexpr e)
                                                    end))%under_lets
                                        | None => match default_on_rewrite_failure with
                                                 | Some default => default tt
                                                 | None => UnderLets.Base (expr_of_rawexpr e)
                                                 end
                                        end)
                               | None => UnderLets.Base (expr_of_rawexpr e)
                               end)
                      | None => UnderLets.Base (expr_of_rawexpr e)
                      end
                  | _, _ => UnderLets.Base (expr_of_rawexpr e)
                   end).

        Local Notation enumerate ls
          := (List.combine (List.seq 0 (List.length ls)) ls).

        Fixpoint first_satisfying_helper {A B} (f : A -> option B) (ls : list A) : option B
          := match ls with
             | nil => None
             | cons x xs
               => match f x with
                 | Some v => Some v
                 | None => first_satisfying_helper f xs
                 end
             end.

        Definition get_index_of_first_non_wildcard (p : list pattern) : option nat
          := first_satisfying_helper
               (fun '(n, x) => match x with
                            | pattern.Wildcard _ => None
                            | _ => Some n
                            end)
               (enumerate p).

        Definition filter_pattern_wildcard (p : list (nat * list pattern)) : list (nat * list pattern)
          := filter (fun '(_, p) => match p with
                                 | pattern.Wildcard _::_ => true
                                 | _ => false
                                 end)
                    p.

        Fixpoint get_unique_pattern_ident' (p : list (nat * list pattern)) (so_far : list pident) : list pident
          := match p with
             | nil => List.rev so_far
             | (_, pattern.Ident pidc :: _) :: ps
               => let so_far' := if existsb (pident_beq pidc) so_far
                                 then so_far
                                 else pidc :: so_far in
                  get_unique_pattern_ident' ps so_far'
             | _ :: ps => get_unique_pattern_ident' ps so_far
             end.

        Definition get_unique_pattern_ident p : list pident := get_unique_pattern_ident' p nil.

        Definition contains_pattern_pident (pidc : pident) (p : list (nat * list pattern)) : bool
          := existsb (fun '(n, p) => match p with
                                  | pattern.Ident pidc'::_ => pident_beq pidc pidc'
                                  | _ => false
                                  end)
                     p.

        Definition contains_pattern_app (p : list (nat * list pattern)) : bool
          := existsb (fun '(n, p) => match p with
                                  | pattern.App _ _::_ => true
                                  | _ => false
                                  end)
                     p.

        Definition refine_pattern_app (p : nat * list pattern) : option (nat * list pattern)
          := match p with
             | (n, pattern.Wildcard d::ps)
               => Some (n, (??{?? -> d} :: ?? :: ps)%list%pattern)
             | (n, pattern.App f x :: ps)
               => Some (n, f :: x :: ps)
             | (_, pattern.Ident _::_)
             | (_, nil)
               => None
             end.

        Definition refine_pattern_pident (pidc : pident) (p : nat * list pattern) : option (nat * list pattern)
          := match p with
             | (n, pattern.Wildcard _::ps)
               => Some (n, ps)
             | (n, pattern.Ident pidc'::ps)
               => if pident_beq pidc pidc'
                 then Some (n, ps)
                 else None
             | (_, pattern.App _ _::_)
             | (_, nil)
               => None
             end.

        Definition compile_rewrites_step
                   (compile_rewrites : list (nat * list pattern) -> option decision_tree)
                   (pattern_matrix : list (nat * list pattern))
          : option decision_tree
          := match pattern_matrix with
             | nil => Some Failure
             | (n1, p1) :: ps
               => match get_index_of_first_non_wildcard p1 with
                 | None (* p1 is all wildcards *)
                   => (onfailure <- compile_rewrites ps;
                        Some (TryLeaf n1 onfailure))
                 | Some Datatypes.O
                   => default_case <- compile_rewrites (filter_pattern_wildcard pattern_matrix);
                        app_case <- (if contains_pattern_app pattern_matrix
                                     then option_map Some (compile_rewrites (Option.List.map refine_pattern_app pattern_matrix))
                                     else Some None);
                        let pidcs := get_unique_pattern_ident pattern_matrix in
                        let icases := Option.List.map
                                        (fun pidc => option_map (pair pidc) (compile_rewrites (Option.List.map (refine_pattern_pident pidc) pattern_matrix)))
                                        pidcs in
                        Some (Switch icases app_case default_case)
                 | Some i
                   => let pattern_matrix'
                         := List.map
                              (fun '(n, ps)
                               => (n,
                                  match swap_list 0 i ps with
                                  | Some ps' => ps'
                                  | None => nil (* should be impossible *)
                                  end))
                              pattern_matrix in
                     d <- compile_rewrites pattern_matrix';
                       Some (Swap i d)
                 end
             end%option.

        Fixpoint compile_rewrites' (fuel : nat) (pattern_matrix : list (nat * list pattern))
          : option decision_tree
          := match fuel with
             | Datatypes.O => None
             | Datatypes.S fuel' => compile_rewrites_step (@compile_rewrites' fuel') pattern_matrix
             end.

        Definition compile_rewrites (fuel : nat) (ps : rewrite_rulesT)
          := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).


        Fixpoint with_bindingsT (p : pattern) (T : Type)
          := match p return Type with
             | pattern.Wildcard t => ptype_interp qforall t (fun eT => eT -> T)
             | pattern.Ident idc
               => match arg_types idc with
                 | Some t => t -> T
                 | None => T
                 end
             | pattern.App f x => with_bindingsT f (with_bindingsT x T)
             end.

        Fixpoint lift_pbase_type_interp_cps {K1 K2} {quant} (F : forall t : base.type, K1 t -> K2 t) {t}
          : pbase_type_interp_cps quant t K1
            -> pbase_type_interp_cps quant t K2
          := match t, quant return pbase_type_interp_cps quant t K1
                                   -> pbase_type_interp_cps quant t K2 with
             | pattern.base.type.any, qforall
               => fun f t => F t (f t)
             | pattern.base.type.any, qexists
               => fun tf => existT _ _ (F _ (projT2 tf))
             | pattern.base.type.type_base t, _
               => F _
             | pattern.base.type.prod A B, _
               => @lift_pbase_type_interp_cps
                   _ _ quant
                   (fun A'
                    => @lift_pbase_type_interp_cps
                        _ _ quant (fun _ => F _) B)
                   A
             | pattern.base.type.list A, _
               => @lift_pbase_type_interp_cps
                   _ _ quant (fun _ => F _) A
             end.

        Fixpoint lift_ptype_interp_cps {K1 K2} {quant} (F : forall t : type.type base.type, K1 t -> K2 t) {t}
          : ptype_interp_cps quant t K1
            -> ptype_interp_cps quant t K2
          := match t return ptype_interp_cps quant t K1
                                   -> ptype_interp_cps quant t K2 with
             | type.base t
               => lift_pbase_type_interp_cps F
             | type.arrow A B
               => @lift_ptype_interp_cps
                   _ _ quant
                   (fun A'
                    => @lift_ptype_interp_cps
                        _ _ quant (fun _ => F _) B)
                   A
             end.

        Fixpoint lift_with_bindings {p} {A B : Type} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
          := match p return with_bindingsT p A -> with_bindingsT p B with
             | pattern.Wildcard t
               => lift_ptype_interp_cps
                   (K1:=fun t => value t -> A)
                   (K2:=fun t => value t -> B)
                   (fun _ f v => F (f v))
             | pattern.Ident idc
               => match arg_types idc as ty
                       return match ty with
                              | Some t => t -> A
                              | None => A
                              end -> match ty with
                                    | Some t => t -> B
                                    | None => B
                                    end
                 with
                 | Some _ => fun f v => F (f v)
                 | None => F
                 end
             | pattern.App f x
               => @lift_with_bindings
                   f _ _
                   (@lift_with_bindings x _ _ F)
             end.

        Fixpoint app_pbase_type_interp_cps {T : Type} {K1 K2 : base.type -> Type}
                 (F : forall t, K1 t -> K2 t -> T)
                 {t}
          : pbase_type_interp_cps qforall t K1
            -> pbase_type_interp_cps qexists t K2 -> T
          := match t return pbase_type_interp_cps qforall t K1
                            -> pbase_type_interp_cps qexists t K2 -> T with
             | pattern.base.type.any
               => fun f tv => F _ (f _) (projT2 tv)
             | pattern.base.type.type_base t
               => fun f v => F _ f v
             | pattern.base.type.prod A B
               => @app_pbase_type_interp_cps
                   _
                   (fun A' => pbase_type_interp_cps qforall B (fun B' => K1 (A' * B')%etype))
                   (fun A' => pbase_type_interp_cps qexists B (fun B' => K2 (A' * B')%etype))
                   (fun A'
                    => @app_pbase_type_interp_cps
                        _
                        (fun B' => K1 (A' * B')%etype)
                        (fun B' => K2 (A' * B')%etype)
                        (fun _ => F _)
                        B)
                   A
             | pattern.base.type.list A
               => @app_pbase_type_interp_cps T (fun A' => K1 (base.type.list A')) (fun A' => K2 (base.type.list A')) (fun _ => F _) A
             end.

        Fixpoint app_ptype_interp_cps {T : Type} {K1 K2 : type -> Type}
                 (F : forall t, K1 t -> K2 t -> T)
                 {t}
          : ptype_interp_cps qforall t K1
            -> ptype_interp_cps qexists t K2 -> T
          := match t return ptype_interp_cps qforall t K1
                            -> ptype_interp_cps qexists t K2 -> T with
             | type.base t => app_pbase_type_interp_cps F
             | type.arrow A B
               => @app_ptype_interp_cps
                   _
                   (fun A' => ptype_interp_cps qforall B (fun B' => K1 (A' -> B')%etype))
                   (fun A' => ptype_interp_cps qexists B (fun B' => K2 (A' -> B')%etype))
                   (fun A'
                    => @app_ptype_interp_cps
                        _
                        (fun B' => K1 (A' -> B')%etype)
                        (fun B' => K2 (A' -> B')%etype)
                        (fun _ => F _)
                        B)
                   A
             end.

        Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
          := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
             | pattern.Wildcard t
               => app_ptype_interp_cps
                   (K1:=fun t => value t -> T)
                   (K2:=fun t => value t)
                   (fun _ f v => f v)
             | pattern.Ident idc
               => match arg_types idc as ty
                       return match ty with
                              | Some t => t -> T
                              | None => T
                              end -> match ty return Type with
                                    | Some t => t
                                    | None => unit
                                    end -> T
                 with
                 | Some t => fun f x => f x
                 | None => fun v 'tt => v
                 end
             | pattern.App f x
               => fun F '(vf, vx)
                 => @app_binding_data _ x (@app_binding_data _ f F vf) vx
             end.

        (** XXX MOVEME? *)
        Definition mkcast {P : type -> Type} {t1 t2 : type} : ~> (option (P t1 -> P t2))
          := fun T k => type.try_make_transport_cps base.try_make_transport_cps P t1 t2 _ k.
        Definition cast {P : type -> Type} {t1 t2 : type} (v : P t1) : ~> (option (P t2))
          := fun T k => type.try_transport_cps base.try_make_transport_cps P t1 t2 v _ k.
        Definition castb {P : base.type -> Type} {t1 t2 : base.type} (v : P t1) : ~> (option (P t2))
          := fun T k => base.try_transport_cps P t1 t2 v _ k.
        Definition castbe {t1 t2 : base.type} (v : expr t1) : ~> (option (expr t2))
          := @castb expr t1 t2 v.
        Definition castv {t1 t2} (v : value t1) : ~> (option (value t2))
          := fun T k => type.try_transport_cps base.try_make_transport_cps value t1 t2 v _ k.

        Section with_do_again.
          Context (dtree : decision_tree)
                  (rewrite_rules : rewrite_rulesT)
                  (default_fuel : nat)
                  (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t)).

          Let dorewrite1 (e : rawexpr) : UnderLets (expr (type_of_rawexpr e))
            := eval_rewrite_rules do_again dtree rewrite_rules e.

          Fixpoint assemble_identifier_rewriters' (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t
            := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t with
               | type.base _
                 => fun e k => k (fun t => UnderLets (expr t)) (dorewrite1 e)
               | type.arrow s d
                 => fun f k (x : value' _ _)
                    => let x' := reify x in
                       @assemble_identifier_rewriters' d (rApp f (rValueOrExpr2 x x') (k _ (expr_of_rawexpr f) @ x'))%expr (fun _ => id)
               end%under_lets.

          Definition assemble_identifier_rewriters {t} (idc : ident t) : value_with_lets t
            := eta_ident_cps _ _ idc (fun t' idc' => assemble_identifier_rewriters' t' (rIdent idc' #idc') (fun _ => id)).
        End with_do_again.
      End with_var.

      Section full.
        Context {var : type.type base.type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation value := (@Compile.value base.type ident var).
        Local Notation value_with_lets := (@Compile.value_with_lets base.type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident var).
        Local Notation reify_and_let_binds_cps := (@Compile.reify_and_let_binds_cps ident var (@UnderLets.reify_and_let_binds_base_cps var)).
        Local Notation reflect := (@Compile.reflect ident var).
        Section with_rewrite_head.
          Context (rewrite_head : forall t (idc : ident t), value_with_lets t).

          Local Notation "e <---- e' ; f" := (Compile.splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
          Local Notation "e <----- e' ; f" := (Compile.splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

          Fixpoint rewrite_bottomup {t} (e : @expr value t) : value_with_lets t
            := match e in expr.expr t return value_with_lets t with
               | expr.Ident t idc
                 => rewrite_head _ idc
               | expr.App s d f x => let f : value s -> value_with_lets d := @rewrite_bottomup _ f in x <---- @rewrite_bottomup _ x; f x
               | expr.LetIn A B x f => x <---- @rewrite_bottomup A x;
                                         xv <----- reify_and_let_binds_cps x _ UnderLets.Base;
                                         @rewrite_bottomup B (f (reflect xv))
               | expr.Var t v => Compile.Base_value v
               | expr.Abs s d f => fun x : value s => @rewrite_bottomup d (f x)
               end%under_lets.
        End with_rewrite_head.

        Notation nbe := (@rewrite_bottomup (fun t idc => reflect (expr.Ident idc))).

        Fixpoint repeat_rewrite
                 (rewrite_head : forall (do_again : forall t : base.type, @expr value (type.base t) -> UnderLets (@expr var (type.base t)))
                                            t (idc : ident t), value_with_lets t)
                 (fuel : nat) {t} e : value_with_lets t
          := @rewrite_bottomup
               (rewrite_head
                  (fun t' e'
                   => match fuel with
                      | Datatypes.O => nbe e'
                      | Datatypes.S fuel' => @repeat_rewrite rewrite_head fuel' (type.base t') e'
                      end%under_lets))
               t e.

        Definition rewrite rewrite_head fuel {t} e : expr t
          := reify (@repeat_rewrite rewrite_head fuel t e).
      End full.

      Definition Rewrite rewrite_head fuel {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
        := fun var => @rewrite var (rewrite_head var) fuel t (e _).
    End Compile.

    Module pident := pattern.ident.

    Module Make.
      Section make_rewrite_rules.
        Import Compile.
        Context {var : type.type base.type -> Type}.
        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation anyexpr := (@anyexpr ident var).
        Local Notation pattern := (@pattern.pattern pattern.ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Let type_base (t : base.type) : type := type.base t.
        Let ptype_base (t : pattern.base.type) : ptype := type.base t.
        Let ptype_base' (t : base.type.base) : ptype := @type.base pattern.base.type t.
        Coercion ptype_base' : base.type.base >-> ptype.
        Coercion type_base : base.type >-> type.
        Coercion ptype_base : pattern.base.type >-> ptype.
        Local Notation opt_anyexprP ivar
          := (fun should_do_again : bool => UnderLets (@AnyExpr.anyexpr base.type ident (if should_do_again then ivar else var))).
        Local Notation opt_anyexpr ivar
          := (option (sigT (opt_anyexprP ivar))).
        Local Notation binding_dataT := (@binding_dataT ident var pattern.ident pattern.ident.arg_types).
        Local Notation lift_with_bindings := (@lift_with_bindings ident var pattern.ident pattern.ident.arg_types).
        Local Notation app_binding_data := (@app_binding_data ident var pattern.ident pattern.ident.arg_types).
        Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pattern.ident pattern.ident.arg_types).
        Local Notation rewrite_ruleT := (@rewrite_ruleT ident var pattern.ident pattern.ident.arg_types).
        Local Notation castv := (@castv ident var).

        Definition make_base_Literal_pattern (t : base.type.base) : pattern
          := Eval cbv [pident.of_typed_ident] in
              pattern.Ident (pident.of_typed_ident (@ident.Literal t DefaultValue.type.base.default)).

        Definition bind_base_Literal_pattern (t : base.type.base) : binding_dataT (make_base_Literal_pattern t) ~> base.interp t
          := match t return binding_dataT (make_base_Literal_pattern t) ~> base.interp t with
             | base.type.unit
             | base.type.Z
             | base.type.bool
             | base.type.nat
               => fun v => (return v)
             end%cps.

        Fixpoint make_Literal_pattern (t : base.type) : option { p : pattern & binding_dataT p ~> base.interp t }
          := match t return option { p : pattern & binding_dataT p ~> base.interp t } with
             | base.type.type_base t => Some (existT _ (make_base_Literal_pattern t) (bind_base_Literal_pattern t))
             | base.type.prod A B
               => (a <- make_Literal_pattern A;
                    b <- make_Literal_pattern B;
                    Some (existT
                            (fun p : pattern => binding_dataT p ~> base.interp (A * B))
                            (#pident.pair @ (projT1 a) @ (projT1 b))%pattern
                            (fun '(args : unit * binding_dataT (projT1 a) * binding_dataT (projT1 b))
                             => (av <--- projT2 a (snd (fst args));
                                  bv <--- projT2 b (snd args);
                                return (av, bv)))))
             | base.type.list A => None
             end%option%cps.

        Fixpoint make_interp_rewrite' (t : type) (p : pattern) (rew : binding_dataT p ~> type.interp base.interp t) {struct t}
          : option rewrite_ruleT
          := match t return (_ ~> type.interp base.interp t) -> _ with
             | type.base t
               => fun rew
                 => Some (existT _ p (fun args => v <--- rew args;
                                     return (Some (existT _ false (UnderLets.Base (AnyExpr.wrap (ident.smart_Literal v)))))))
             | type.arrow (type.base s) d
               => fun rew
                 => (lit_s <- make_Literal_pattern s;
                      @make_interp_rewrite'
                        d
                        (pattern.App p (projT1 lit_s))
                        (fun (args : binding_dataT p * binding_dataT (projT1 lit_s))
                         => (rewp <--- rew (fst args);
                              sv <--- projT2 lit_s (snd args);
                            return (rewp sv))))
             | type.arrow _ _ => fun _ => None
             end%option%cps rew.

        Definition make_interp_rewrite'' {t} (idc : ident t) : option rewrite_ruleT
          := make_interp_rewrite'
               t
               (pattern.Ident (pident.of_typed_ident idc))
               (fun iargs => return (ident.interp (pident.retype_ident idc iargs)))%cps.
        (*
        Definition make_interp_rewrite {t} (idc : ident t)
          := invert_Some (make_interp_rewrite'' idc).
         *)

        Local Ltac get_all_valid_interp_rules_from body so_far :=
          let next := match body with
                      | context[@Some (sigT (fun x : pattern => binding_dataT x ~> opt_anyexpr value)) ?rew]
                        => lazymatch so_far with
                          | context[cons rew _] => constr:(I : I)
                          | _ => lazymatch rew with
                                | existT _ _ _ => constr:(Some rew)
                                | _ => constr:(I : I)
                                end
                          end
                      | _ => constr:(@None unit)
                      end in
          lazymatch next with
          | Some ?rew => get_all_valid_interp_rules_from body (cons rew so_far)
          | None => (eval cbv [List.rev List.app] in (List.rev so_far))
          end.
        Local Ltac make_valid_interp_rules :=
          let body := constr:(fun t idc => @pident.eta_ident_cps _ t idc (@make_interp_rewrite'')) in
          let body := (eval cbv [pident.eta_ident_cps make_interp_rewrite'' make_interp_rewrite' make_Literal_pattern pident.of_typed_ident Option.bind projT1 projT2 cpsbind cpsreturn cpscall ident.interp pident.retype_ident ident.gen_interp bind_base_Literal_pattern make_base_Literal_pattern] in body) in
          let body := (eval cbn [base.interp binding_dataT pattern.ident.arg_types base.base_interp ident.smart_Literal fold_right map] in body) in
          let retv := get_all_valid_interp_rules_from body (@nil rewrite_ruleT) in
          exact retv.
        Definition interp_rewrite_rules : rewrite_rulesT
          := ltac:(make_valid_interp_rules).
      End make_rewrite_rules.
    End Make.

    Section with_var.
      Import Compile.
      Context {var : type.type base.type -> Type}.
      Local Notation type := (type.type base.type).
      Local Notation expr := (@expr.expr base.type ident var).
      Local Notation value := (@value base.type ident var).
      Local Notation anyexpr := (@anyexpr ident var).
      Local Notation pattern := (@pattern.pattern pattern.ident).
      Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
      Local Notation ptype := (type.type pattern.base.type).
      Let type_base (t : base.type) : type := type.base t.
      Let ptype_base (t : pattern.base.type) : ptype := type.base t.
      Let ptype_base' (t : base.type.base) : ptype := @type.base pattern.base.type t.
      Coercion ptype_base' : base.type.base >-> ptype.
      Coercion type_base : base.type >-> type.
      Coercion ptype_base : pattern.base.type >-> ptype.
      Local Notation opt_anyexprP ivar
        := (fun should_do_again : bool => UnderLets (@AnyExpr.anyexpr base.type ident (if should_do_again then ivar else var))).
      Local Notation opt_anyexpr ivar
        := (option (sigT (opt_anyexprP ivar))).
      Local Notation binding_dataT := (@binding_dataT ident var pattern.ident pattern.ident.arg_types).
      Local Notation lift_with_bindings := (@lift_with_bindings ident var pattern.ident pattern.ident.arg_types).
      Local Notation app_binding_data := (@app_binding_data ident var pattern.ident pattern.ident.arg_types).
      Local Notation rewrite_ruleTP := (@rewrite_ruleTP ident var pattern.ident pattern.ident.arg_types).
      Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pattern.ident pattern.ident.arg_types).
      Local Notation castv := (@castv ident var).
      Local Notation assemble_identifier_rewriters := (@assemble_identifier_rewriters ident var pattern.ident pattern.ident.full_types (@pattern.ident.invert_bind_args) pattern.ident.type_of pattern.ident.to_typed (@pattern.ident.eta_ident_cps) (@pattern.ident.of_typed_ident) pattern.ident.arg_types (@pattern.ident.bind_args) pattern.ident.try_make_transport_ident_cps).

      Let UnderLetsExpr {btype bident ivar} t := @UnderLets.UnderLets base.type ident var (@expr.expr btype bident ivar t).
      Let UnderLetsAnyExpr {btype ident ivar} := @UnderLets.UnderLets btype ident ivar (@AnyExpr.anyexpr btype ident ivar).
      Let UnderLetsAnyExprCpsOpt {btype bident ivar} := ~> option (@UnderLets.UnderLets base.type ident var (@AnyExpr.anyexpr btype bident ivar)).
      (*Let UnderLetsAnyAnyExpr {btype ident ivar} := @UnderLets.UnderLets btype ident ivar (@AnyAnyExpr.anyexpr btype ident ivar).*)
      Let BaseWrapUnderLetsAnyExpr {btype bident ivar t} : @UnderLetsExpr btype bident ivar t -> @UnderLetsAnyExprCpsOpt btype bident ivar
        := fun e T k
           => k (match t return @UnderLets.UnderLets _ _ _ (@expr.expr _ _ _ t) -> _ with
                | type.base _ => fun e => Some (e <-- e; UnderLets.Base (AnyExpr.wrap e))%under_lets
                | type.arrow _ _ => fun _ => None
                end e)%cps.
      Let BaseExpr {btype ident ivar t} : @expr.expr btype ident ivar t -> @UnderLetsExpr btype ident ivar t := UnderLets.Base.
      (*Let BaseAnyAnyExpr {btype ident ivar t} : @expr.expr btype ident ivar t -> @UnderLets.UnderLets btype ident ivar (@expr.expr btype ident ivar t) := UnderLets.Base.*)
      Coercion BaseWrapUnderLetsAnyExpr : UnderLetsExpr >-> UnderLetsAnyExprCpsOpt.
      Coercion BaseExpr : expr >-> UnderLetsExpr.
      Notation ret v := ((v : UnderLetsExpr _) : UnderLetsAnyExprCpsOpt).
      Notation oret v := (fun T k => k (Some v)).
      (*Coercion BaseExpr : expr >-> UnderLets.*)
      Notation make_rewrite'_cps p f
        := (existT
              (fun p' : pattern => binding_dataT p' ~> (opt_anyexpr value))
              p%pattern
              (fun v T (k : opt_anyexpr value -> T)
               => @app_binding_data _ p%pattern f%expr v T k)).
      Notation make_rewrite' p f
        := (existT
              (fun p' : pattern => binding_dataT p' ~> (opt_anyexpr value))
              p%pattern
              (fun v T (k : opt_anyexpr value -> T)
               => k (@app_binding_data _ p%pattern f%expr v))).
      Notation make_rewrite p f
        := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsAnyExprCpsOpt base.type ident var => (x' <-- x; oret (existT (opt_anyexprP value) false x'))%cps) f%expr) in
            make_rewrite'_cps p f').
      Notation make_rewrite_step p f
        := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsAnyExprCpsOpt base.type ident value => (x' <-- x; oret (existT (opt_anyexprP value) true x'))%cps) f%expr) in
            make_rewrite'_cps p f').

      Local Notation "x' <- v ; C" := (fun T k => v%cps T (fun x' => match x' with Some x' => (C%cps : UnderLetsAnyExprCpsOpt) T k | None => k None end)) : cps_scope.
      Local Notation "x <-- y ; f" := (UnderLets.splice y (fun x => (f%cps : UnderLetsExpr _))) : cps_scope.
      Local Notation "x <--- y ; f" := (UnderLets.splice_list y (fun x => (f%cps : UnderLetsExpr _))) : cps_scope.
      Local Notation "x <---- y ; f" := (fun T k => match y with Some x => (f%cps : UnderLetsAnyExprCpsOpt) T k | None => k None end) : cps_scope.

      Definition rlist_rect {A P}
                 {ivar}
                 (Pnil : @UnderLetsExpr base.type ident ivar (type.base P))
                 (Pcons : expr (type.base A) -> list (expr (type.base A)) -> @expr.expr base.type ident ivar (type.base P) -> @UnderLetsExpr base.type ident ivar (type.base P))
                 (e : expr (type.base (base.type.list A)))
        : @UnderLetsAnyExprCpsOpt base.type ident ivar
        := (ls <- reflect_list_cps e;
              list_rect
                (fun _ => UnderLetsExpr (type.base P))
                Pnil
                (fun x xs rec => rec' <-- rec; Pcons x xs rec')
                ls)%cps.

      Definition rlist_rect_cast {A A' P}
                 {ivar}
                 (Pnil : @UnderLetsExpr base.type ident ivar (type.base P))
                 (Pcons : expr (type.base A) -> list (expr (type.base A)) -> @expr.expr base.type ident ivar (type.base P) -> @UnderLetsExpr base.type ident ivar (type.base P))
                 (e : expr (type.base A'))
        : @UnderLetsAnyExprCpsOpt base.type ident ivar
        := (e <- castbe e; rlist_rect Pnil Pcons e)%cps.

      Definition rwhen {ivar} (v : @UnderLetsAnyExprCpsOpt base.type ident ivar) (cond : bool)
        : @UnderLetsAnyExprCpsOpt base.type ident ivar
        := fun T k => if cond then v T k else k None.

      Local Notation "e 'when' cond" := (rwhen e%cps cond) (only parsing, at level 100).

      Local Notation ℤ := base.type.Z.
      Local Notation ℕ := base.type.nat.
      Local Notation bool := base.type.bool.
      Local Notation list := pattern.base.type.list.

      Local Arguments Make.interp_rewrite_rules / .

      (**
         The follow are rules for rewriting expressions. On the left is a pattern to match:
           ??: any expression whose type contains no arrows.
           ??{x}: any expression whose type is x.
           ??{pattern.base.type.list ??}: for example, a list with elements of a captured type. (The captured type does not match a type with arrows.)
           x @ y: x applied to y.
           #?x: a value, know at compile time, with type x. (Where x is one of {ℕ or N (nat), 𝔹 or B (bool), ℤ or Z (integers)}.)
           #x: the identifer x.

         A matched expression is replaced with the right-hand-side, which is a function that returns a syntax tree, or None to indicate that the match didn't really match. The syntax tree is under three monads: continuation, option, and custom UnderLets monad.

         The function takes the elements that where matched on the LHS as arguments. The arguments are given in the same order as on the LHS, but where wildcards in a type appear before the outer wildcard for that element. So ??{??} results in two arguments, the second wildcard comes first, and ??{?? -> ??} gives arguments in the order 2, 3, 1.

         Sometimes matching an identifer will also result in arguments. Depends on the identifer. Good luck!

In the RHS, the follow notation applies:
           ##x: the literal value x
           #x: the identifier x
           x @ y: x applied to y
           $x: PHOAS variable named x
           λ: PHOAS abstraction / functions

         On the RHS, since we're returning a value under three monads, there's some fun notion for dealing with different levels of the monad stack in a single expression:
           ret: return something of type [UnderLets expr]
           <-: bind, under the CPS+Option monad.
           <--: bind, under the UnderLets monad
           <---: bind, under the UnderLets+List monad
           <----: bind, under the Option monad.

         If you have an expression of type expr or UnderLetsExpr or UnderLetsAnyExprCpsOpt, coercions will handle it; if you have an expression of type [UnderLets expr], you will need [ret].

         If stuck, email Jason.
       *)
      Definition rewrite_rules : rewrite_rulesT
        := Eval cbn [Make.interp_rewrite_rules List.app] in
            Make.interp_rewrite_rules
              ++ [
                make_rewrite (#pident.fst @ (??, ??)) (fun _ x _ y => x)
                ; make_rewrite (#pident.snd @ (??, ??)) (fun _ x _ y => y)
                ; make_rewrite (#pident.List_repeat @ ?? @ #?ℕ) (fun _ x n => reify_list (repeat x n))
                ; make_rewrite
                    (#pident.bool_rect @ ??{() -> ??} @ ??{() -> ??} @ #?𝔹)
                    (fun _ t _ f b
                     => if b return UnderLetsExpr (type.base (if b then _ else _))
                        then t ##tt
                        else f ##tt)
                ; make_rewrite
                    (#pident.pair_rect @ ??{?? -> ?? -> ??} @ (??, ??))
                    (fun _ _ _ f _ x _ y
                     => x <- castbe x; y <- castbe y; ret (f x y))
                ; make_rewrite
                    (??{list ??} ++ ??{list ??})
                    (fun _ xs _ ys => rlist_rect_cast ys (fun x _ xs_ys => x :: xs_ys) xs)
                ; make_rewrite
                    (#pident.List_rev @ ??{list ??})
                    (fun _ xs
                     => xs <- reflect_list_cps xs;
                          reify_list (List.rev xs))
                ; make_rewrite_step
                    (#pident.List_flat_map @ ??{?? -> list ??} @ ??{list ??})
                    (fun _ B f _ xs
                     => rlist_rect_cast
                          []
                          (fun x _ flat_map_tl => fx <-- f x; UnderLets.Base ($fx ++ flat_map_tl))
                          xs)
                ; make_rewrite_step
                    (#pident.List_partition @ ??{?? -> base.type.bool} @ ??{list ??})
                    (fun _ f _ xs
                     => rlist_rect_cast
                          ([], [])
                          (fun x tl partition_tl
                           => fx <-- f x;
                                (#ident.pair_rect
                                  @ (λ g d, #ident.bool_rect
                                             @ (λ _, ($x :: $g, $d))
                                             @ (λ _, ($g, $x :: $d))
                                             @ $fx)
                                  @ partition_tl))
                          xs)
                ; make_rewrite
                    (#pident.List_fold_right @ ??{?? -> ?? -> ??} @ ?? @ ??{list ??})
                    (fun _ _ _ f B init A xs
                     => f <- @castv _ (A -> B -> B)%etype f;
                          rlist_rect
                            init
                            (fun x _ y => f x y)
                            xs)
                ; make_rewrite
                    (#pident.list_rect @ ??{() -> ??} @ ??{?? -> ?? -> ?? -> ??} @ ??{list ??})
                    (fun P Pnil _ _ _ _ Pcons A xs
                     => Pcons <- @castv _ (A -> base.type.list A -> P -> P) Pcons;
                          rlist_rect
                            (Pnil ##tt)
                            (fun x' xs' rec => Pcons x' (reify_list xs') rec)
                            xs)
                ; make_rewrite
                    (#pident.list_case @ ??{() -> ??} @ ??{?? -> ?? -> ??} @ []) (fun _ Pnil _ _ _ Pcons => ret (Pnil ##tt))
                ; make_rewrite
                    (#pident.list_case @ ??{() -> ??} @ ??{?? -> ?? -> ??} @ (?? :: ??))
                    (fun _ Pnil _ _ _ Pcons _ x _ xs
                     => x <- castbe x; xs <- castbe xs; ret (Pcons x xs))
                ; make_rewrite
                    (#pident.List_map @ ??{?? -> ??} @ ??{list ??})
                    (fun _ _ f _ xs
                     => rlist_rect_cast
                          []
                          (fun x _ fxs => fx <-- f x; fx :: fxs)
                          xs)
                ; make_rewrite
                    (#pident.List_nth_default @ ?? @ ??{list ??} @ #?ℕ)
                    (fun _ default _ ls n
                     => default <- castbe default;
                          ls <- reflect_list_cps ls;
                          nth_default default ls n)
                ; make_rewrite
                    (#pident.nat_rect @ ??{() -> ??} @ ??{base.type.nat -> ?? -> ??} @ #?ℕ)
                    (fun P O_case _ _ S_case n
                     => S_case <- @castv _ (@type.base base.type base.type.nat -> type.base P -> type.base P) S_case;
                          ret (nat_rect _ (O_case ##tt) (fun n' rec => rec <-- rec; S_case ##n' rec) n))
                ; make_rewrite
                    (#pident.List_length @ ??{list ??})
                    (fun _ xs => xs <- reflect_list_cps xs; ##(List.length xs))
                ; make_rewrite
                    (#pident.List_combine @ ??{list ??} @ ??{list ??})
                    (fun _ xs _ ys
                     => xs <- reflect_list_cps xs;
                          ys <- reflect_list_cps ys;
                          reify_list (List.map (fun '((x, y)%core) => (x, y)) (List.combine xs ys)))
                ; make_rewrite
                    (#pident.List_update_nth @ #?ℕ @ ??{?? -> ??} @ ??{list ??})
                    (fun n _ _ f A ls
                     => f <- @castv _ (A -> A) f;
                          ls <- reflect_list_cps ls;
                          ret
                            (retv <--- (update_nth
                                          n
                                          (fun x => x <-- x; f x)
                                          (List.map UnderLets.Base ls));
                               reify_list retv))
                ; make_rewrite (#?ℤ   + ??{ℤ}) (fun z v => v  when  Z.eqb z 0)
                ; make_rewrite (??{ℤ} + #?ℤ  ) (fun v z => v  when  Z.eqb z 0)
                ; make_rewrite (#?ℤ   + (-??{ℤ})) (fun z v => ##z - v  when  Z.gtb z 0)
                ; make_rewrite ((-??{ℤ}) + #?ℤ  ) (fun v z => ##z - v  when  Z.gtb z 0)
                ; make_rewrite (#?ℤ   + (-??{ℤ})) (fun z v => -(##((-z)%Z) + v)  when  Z.ltb z 0)
                ; make_rewrite ((-??{ℤ}) + #?ℤ  ) (fun v z => -(v + ##((-z)%Z))  when  Z.ltb z 0)
                ; make_rewrite ((-??{ℤ}) + (-??{ℤ})) (fun x y => -(x + y))
                ; make_rewrite ((-??{ℤ}) +   ??{ℤ} ) (fun x y => y - x)
                ; make_rewrite (  ??{ℤ}  + (-??{ℤ})) (fun x y => x - y)

                ; make_rewrite (#?ℤ   - (-??{ℤ})) (fun z v =>  v  when  Z.eqb z 0)
                ; make_rewrite (#?ℤ   -   ??{ℤ} ) (fun z v => -v  when  Z.eqb z 0)
                ; make_rewrite (??{ℤ} - #?ℤ     ) (fun v z =>  v  when  Z.eqb z 0)
                ; make_rewrite (#?ℤ   - (-??{ℤ})) (fun z v => ##z + v  when  Z.gtb z 0)
                ; make_rewrite (#?ℤ   - (-??{ℤ})) (fun z v => v - ##((-z)%Z)     when  Z.ltb z 0)
                ; make_rewrite (#?ℤ   -   ??{ℤ} ) (fun z v => -(##((-z)%Z) + v)  when  Z.ltb z 0)
                ; make_rewrite ((-??{ℤ}) - #?ℤ  ) (fun v z => -(v + ##((-z)%Z))  when  Z.gtb z 0)
                ; make_rewrite ((-??{ℤ}) - #?ℤ  ) (fun v z => ##((-z)%Z) - v     when  Z.ltb z 0)
                ; make_rewrite (  ??{ℤ}  - #?ℤ  ) (fun v z => v + ##((-z)%Z)     when  Z.ltb z 0)
                ; make_rewrite ((-??{ℤ}) - (-??{ℤ})) (fun x y => y - x)
                ; make_rewrite ((-??{ℤ}) -   ??{ℤ} ) (fun x y => -(x + y))
                ; make_rewrite (  ??{ℤ}  - (-??{ℤ})) (fun x y => x + y)

                ; make_rewrite (#?ℤ   * ??{ℤ}) (fun z v => ##0  when  Z.eqb z 0)
                ; make_rewrite (??{ℤ} * #?ℤ  ) (fun v z => ##0  when  Z.eqb z 0)
                ; make_rewrite (#?ℤ   * ??{ℤ}) (fun z v => v  when  Z.eqb z 1)
                ; make_rewrite (??{ℤ} * #?ℤ  ) (fun v z => v  when  Z.eqb z 1)
                ; make_rewrite (#?ℤ      * (-??{ℤ})) (fun z v =>  v  when  Z.eqb z (-1))
                ; make_rewrite ((-??{ℤ}) * #?ℤ     ) (fun v z =>  v  when  Z.eqb z (-1))
                ; make_rewrite (#?ℤ      *   ??{ℤ} ) (fun z v => -v  when  Z.eqb z (-1))
                ; make_rewrite (??{ℤ}    * #?ℤ     ) (fun v z => -v  when  Z.eqb z (-1))
                ; make_rewrite (#?ℤ      * ??{ℤ}   ) (fun z v => -(##((-z)%Z) * v)  when  Z.ltb z 0)
                ; make_rewrite (??{ℤ}    * #?ℤ     ) (fun v z => -(v * ##((-z)%Z))  when  Z.ltb z 0)
                ; make_rewrite ((-??{ℤ}) * (-??{ℤ})) (fun x y => x * y)
                ; make_rewrite ((-??{ℤ}) *   ??{ℤ} ) (fun x y => -(x * y))
                ; make_rewrite (  ??{ℤ}  * (-??{ℤ})) (fun x y => -(x * y))

                ; make_rewrite (??{ℤ} * #?ℤ) (fun x y => x << (Z.log2 y)  when  Z.eqb y (2^Z.log2 y))
                ; make_rewrite (#?ℤ * ??{ℤ}) (fun y x => x << (Z.log2 y)  when  Z.eqb y (2^Z.log2 y))
                ; make_rewrite (??{ℤ} / #?ℤ) (fun x y => x >> (Z.log2 y)  when  Z.eqb y (2^Z.log2 y))
                ; make_rewrite (??{ℤ} mod #?ℤ) (fun x y => #(ident.Z_land (y-1)) @ x  when  Z.eqb y (2^Z.log2 y))
                ; make_rewrite (-(-??{ℤ})) (fun v => v)

                (** TODO(jadep): These next two are only here for demonstration purposes; remove them once you no longer need it as a template *)
                (* if it's a concrete pair, we can opp the second value *)
                ; make_rewrite (#pident.Z_neg_snd @ (??{ℤ}, ??{ℤ})) (fun x y => (x, -y))
                (* if it's not a concrete pair, let-bind the pair and negate the second element *)
                ; make_rewrite
                    (#pident.Z_neg_snd @ ??{ℤ * ℤ})
                    (fun xy => ret (UnderLets.UnderLet xy (fun xyv => UnderLets.Base (#ident.fst @ $xyv, -(#ident.snd @ $xyv)))))

                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ #?ℤ @ ??{ℤ}) (fun s xx y => (##0, ##0)%Z  when  Z.eqb xx 0)
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ ??{ℤ} @ #?ℤ) (fun s y xx => (##0, ##0)%Z  when  Z.eqb xx 0)
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ #?ℤ @ ??{ℤ}) (fun s xx y => (y, ##0)%Z  when  Z.eqb xx 1)
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ ??{ℤ} @ #?ℤ) (fun s y xx => (y, ##0)%Z  when  Z.eqb xx 1)
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ #?ℤ @ ??{ℤ}) (fun s xx y => (-y, ##0%Z)  when  Z.eqb xx (-1))
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ ??{ℤ} @ #?ℤ) (fun s y xx => (-y, ##0%Z)  when  Z.eqb xx (-1))

                ; make_rewrite (#pident.Z_add_get_carry @ #?ℤ @ #?ℤ @ ??{ℤ}) (fun s xx y => (y, ##0%Z)  when  Z.eqb xx 0)
                ; make_rewrite (#pident.Z_add_get_carry @ #?ℤ @ ??{ℤ} @ #?ℤ) (fun s y xx => (y, ##0%Z)  when  Z.eqb xx 0)

                ; make_rewrite (#pident.Z_add_with_carry @ #?ℤ @ ??{ℤ} @ ??{ℤ}) (fun c x y => x + y  when  Z.eqb c 0)


                ; make_rewrite
                    (#pident.Z_add_with_get_carry @ #?ℤ @ #?ℤ @ #?ℤ @ ??{ℤ}) (fun s cc xx y => (y, ##0)  when   (cc =? 0) && (xx =? 0))
                ; make_rewrite
                    (#pident.Z_add_with_get_carry @ #?ℤ @ #?ℤ @ ??{ℤ} @ #?ℤ) (fun s cc y xx => (y, ##0)  when   (cc =? 0) && (xx =? 0))
                ; make_rewrite (* carry = 0: ADC x y -> ADD x y *)
                    (#pident.Z_add_with_get_carry @ #?ℤ @ #?ℤ @ ??{ℤ} @ ??{ℤ})
                    (fun s cc x y => #(ident.Z_add_get_carry_concrete s) @ x @ y  when  cc =? 0)
                ; make_rewrite (* ADC 0 0 -> (ADX 0 0, 0) *)
                    (#pident.Z_add_with_get_carry @ #?ℤ @ ??{ℤ} @ #?ℤ @ #?ℤ)
                    (fun s c xx yy => #ident.Z_add_with_carry @ ##s @ ##xx @ ##yy  when  (xx =? 0) && (yy =? 0))

                ; make_rewrite
                    (#pident.Z_add_get_carry @ #?ℤ @ (-??{ℤ}) @ ??{ℤ})
                    (fun s y x => ret (UnderLets.UnderLet
                                         (#(ident.Z_sub_get_borrow_concrete s) @ x @ y)
                                         (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_get_carry @ #?ℤ @ ??{ℤ} @ (-??{ℤ}))
                    (fun s x y => ret (UnderLets.UnderLet
                                         (#(ident.Z_sub_get_borrow_concrete s) @ x @ y)
                                         (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))


                ; make_rewrite
                    (#pident.Z_add_with_get_carry @ #?ℤ @ (-??{ℤ}) @ (-??{ℤ}) @ ??{ℤ})
                    (fun s c y x => ret (UnderLets.UnderLet
                                           (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ y)
                                           (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_with_get_carry @ #?ℤ @ (-??{ℤ}) @ ??{ℤ} @ (-??{ℤ}))
                    (fun s c x y => ret (UnderLets.UnderLet
                                           (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ y)
                                           (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))

                ; make_rewrite
                    (#pident.Z_add_get_carry_concrete @ (-??{ℤ}) @ ??{ℤ})
                    (fun s y x => ret (UnderLets.UnderLet
                                         (#(ident.Z_sub_get_borrow_concrete s) @ x @ y)
                                         (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ (-??{ℤ}))
                    (fun s x y => ret (UnderLets.UnderLet
                                         (#(ident.Z_sub_get_borrow_concrete s) @ x @ y)
                                         (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_get_carry_concrete @ #?ℤ @ ??{ℤ})
                    (fun s yy x => ret (UnderLets.UnderLet
                                         (#(ident.Z_sub_get_borrow_concrete s) @ x @ ##(-yy)%Z)
                                         (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc))))
                                       when  yy <=? 0)
                ; make_rewrite
                    (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ #?ℤ)
                    (fun s x yy => ret (UnderLets.UnderLet
                                          (#(ident.Z_sub_get_borrow_concrete s) @ x @ ##(-yy)%Z)
                                          (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc))))
                                       when  yy <=? 0)


                ; make_rewrite
                    (#pident.Z_add_with_get_carry_concrete @ (-??{ℤ}) @ (-??{ℤ}) @ ??{ℤ})
                    (fun s c y x => ret (UnderLets.UnderLet
                                           (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ y)
                                           (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_with_get_carry_concrete @ (-??{ℤ}) @ ??{ℤ} @ (-??{ℤ}))
                    (fun s c x y => ret (UnderLets.UnderLet
                                           (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ y)
                                           (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc)))))
                ; make_rewrite
                    (#pident.Z_add_with_get_carry_concrete @ (-??{ℤ}) @ #?ℤ @ ??{ℤ})
                    (fun s c yy x => ret (UnderLets.UnderLet
                                            (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ ##(-yy)%Z)
                                            (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc))))
                                         when  yy <=? 0)
                ; make_rewrite
                    (#pident.Z_add_with_get_carry_concrete @ (-??{ℤ}) @ ??{ℤ} @ #?ℤ)
                    (fun s c x yy => ret (UnderLets.UnderLet
                                            (#(ident.Z_sub_with_get_borrow_concrete s) @ c @ x @ ##(-yy)%Z)
                                            (fun vc => UnderLets.Base (#ident.fst @ $vc, -(#ident.snd @ $vc))))
                                         when  yy <=? 0)

                ; make_rewrite (#pident.Z_add_get_carry_concrete @ #?ℤ @ ??{ℤ}) (fun s xx y => (y, ##0)  when  xx =? 0)
                ; make_rewrite (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ #?ℤ) (fun s y xx => (y, ##0)  when  xx =? 0)

                (** XXX TODO: Do we still need the _concrete versions? *)
                ; make_rewrite (#pident.Z_mul_split @ #?ℤ @ ??{ℤ} @ ??{ℤ}) (fun s x y => #(ident.Z_mul_split_concrete s) @ x @ y)
                ; make_rewrite (#pident.Z_rshi @ #?ℤ @ ??{ℤ} @ ??{ℤ} @ #?ℤ) (fun x y z a => #(ident.Z_rshi_concrete x a) @ y @ z)
                ; make_rewrite (#pident.Z_cc_m @ #?ℤ @ ??{ℤ}) (fun x y => #(ident.Z_cc_m_concrete x) @ y)
                ; make_rewrite (#pident.Z_add_get_carry @ #?ℤ @ ??{ℤ} @ ??{ℤ}) (fun s x y => #(ident.Z_add_get_carry_concrete s) @ x @ y)
                ; make_rewrite (#pident.Z_add_with_get_carry @ #?ℤ @ ??{ℤ} @ ??{ℤ} @ ??{ℤ}) (fun s c x y => #(ident.Z_add_with_get_carry_concrete s) @ c @ x @ y)
                ; make_rewrite (#pident.Z_sub_get_borrow @ #?ℤ @ ??{ℤ} @ ??{ℤ}) (fun s x y => #(ident.Z_sub_get_borrow_concrete s) @ x @ y)
                ; make_rewrite (#pident.Z_sub_with_get_borrow @ #?ℤ @ ??{ℤ} @ ??{ℤ} @ ??{ℤ}) (fun s x y b => #(ident.Z_sub_with_get_borrow_concrete s) @ x @ y @ b)

                ; make_rewrite_step (* _step, so that if one of the arguments is concrete, we automatically get the rewrite rule for [Z_cast] applying to it *)
                    (#pident.Z_cast2 @ (??{ℤ}, ??{ℤ})) (fun r x y => (#(ident.Z_cast (fst r)) @ $x, #(ident.Z_cast (snd r)) @ $y))

                ; make_rewrite (-??{ℤ}) (fun e => ret (UnderLets.UnderLet e (fun v => UnderLets.Base (-$v)))  when  negb (SubstVarLike.is_var_fst_snd_pair_opp e)) (* inline negation when the rewriter wouldn't already inline it *)
              ]%list%pattern%cps%option%under_lets%Z%bool.

      Definition dtree'
        := Eval compute in @compile_rewrites ident var pattern.ident pattern.ident.arg_types pattern.ident.ident_beq 100 rewrite_rules.
      Definition dtree : decision_tree
        := Eval compute in invert_Some dtree'.
      Definition default_fuel := Eval compute in List.length rewrite_rules.

      Import PrimitiveHList.
      (* N.B. The [combine_hlist] call MUST eta-expand
         [pr2_rewrite_rules].  That is, it MUST NOT block reduction of
         the resulting list of cons cells on the pair-structure of
         [pr2_rewrite_rules].  This is required so that we can use
         [cbv -] to unfold the entire discrimination tree evaluation,
         including choosing which rewrite rule to apply and binding
         its arguments, without unfolding any of the identifiers used
         to define the replacement value.  (The symptom of messing
         this up is that the [cbv -] will run out of memory when
         trying to reduce things.)  We accomplish this by making
         [hlist] based on a primitive [prod] type with judgmental η,
         so that matching on its structure never blocks reduction. *)
      Definition split_rewrite_rules := Eval cbv [split_list projT1 projT2 rewrite_rules] in split_list rewrite_rules.
      Definition pr1_rewrite_rules := Eval hnf in projT1 split_rewrite_rules.
      Definition pr2_rewrite_rules := Eval hnf in projT2 split_rewrite_rules.
      Definition all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) pr1_rewrite_rules pr2_rewrite_rules.

      Definition rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
        := @assemble_identifier_rewriters dtree all_rewrite_rules do_again t idc.

      Section fancy.
        Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> option Z).
        Definition fancy_rewrite_rules : rewrite_rulesT
          := [
              (*
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y << 128) --> (add 128) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x << 128, ?y) --> (add 128) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y >> 128) --> (add (- 128)) @@ (x, y)
(Z.add_get_carry_concrete 2^256) @@ (?x >> 128, ?y) --> (add (- 128)) @@ (y, x)
(Z.add_get_carry_concrete 2^256) @@ (?x, ?y)        --> (add 0) @@ (y, x)
*)
              make_rewrite
                (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ (#pident.Z_shiftl @ ??{ℤ}))
                (fun s x offset y => #(ident.fancy_add (Z.log2 s) offset) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_get_carry_concrete @ (#pident.Z_shiftl @ ??{ℤ}) @ ??{ℤ})
                  (fun s offset y x => #(ident.fancy_add (Z.log2 s) offset) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ (#pident.Z_shiftr @ ??{ℤ}))
                  (fun s x offset y => #(ident.fancy_add (Z.log2 s) (-offset)) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_get_carry_concrete @ (#pident.Z_shiftr @ ??{ℤ}) @ ??{ℤ})
                  (fun s offset y x => #(ident.fancy_add (Z.log2 s) (-offset)) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_get_carry_concrete @ ??{ℤ} @ ??{ℤ})
                  (fun s x y => #(ident.fancy_add (Z.log2 s) 0) @ (x, y)  when  s =? 2^Z.log2 s)
(*
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (addc 128) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x << 128, ?y) --> (addc 128) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (addc (- 128)) @@ (c, x, y)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x >> 128, ?y) --> (addc (- 128)) @@ (c, y, x)
(Z.add_with_get_carry_concrete 2^256) @@ (?c, ?x, ?y)        --> (addc 0) @@ (c, y, x)
 *)
              ; make_rewrite
                  (#pident.Z_add_with_get_carry_concrete @ ??{ℤ} @ ??{ℤ} @ (#pident.Z_shiftl @ ??{ℤ}))
                  (fun s c x offset y => #(ident.fancy_addc (Z.log2 s) offset) @ (c, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_with_get_carry_concrete @ ??{ℤ} @ (#pident.Z_shiftl @ ??{ℤ}) @ ??{ℤ})
                  (fun s c offset y x => #(ident.fancy_addc (Z.log2 s) offset) @ (c, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_with_get_carry_concrete @ ??{ℤ} @ ??{ℤ} @ (#pident.Z_shiftr @ ??{ℤ}))
                  (fun s c x offset y => #(ident.fancy_addc (Z.log2 s) (-offset)) @ (c, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_with_get_carry_concrete @ ??{ℤ} @ (#pident.Z_shiftr @ ??{ℤ}) @ ??{ℤ})
                  (fun s c offset y x => #(ident.fancy_addc (Z.log2 s) (-offset)) @ (c, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_add_with_get_carry_concrete @ ??{ℤ} @ ??{ℤ} @ ??{ℤ})
                  (fun s c x y => #(ident.fancy_addc (Z.log2 s) 0) @ (c, x, y)  when  s =? 2^Z.log2 s)
(*
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y << 128) --> (sub 128) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y >> 128) --> (sub (- 128)) @@ (x, y)
(Z.sub_get_borrow_concrete 2^256) @@ (?x, ?y)        --> (sub 0) @@ (y, x)
 *)
              ; make_rewrite
                  (#pident.Z_sub_get_borrow_concrete @ ??{ℤ} @ (#pident.Z_shiftl @ ??{ℤ}))
                  (fun s x offset y => #(ident.fancy_sub (Z.log2 s) offset) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_sub_get_borrow_concrete @ ??{ℤ} @ (#pident.Z_shiftr @ ??{ℤ}))
                  (fun s x offset y => #(ident.fancy_sub (Z.log2 s) (-offset)) @ (x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_sub_get_borrow_concrete @ ??{ℤ} @ ??{ℤ})
                  (fun s x y => #(ident.fancy_sub (Z.log2 s) 0) @ (x, y)  when  s =? 2^Z.log2 s)
(*
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y << 128) --> (subb 128) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y >> 128) --> (subb (- 128)) @@ (c, x, y)
(Z.sub_with_get_borrow_concrete 2^256) @@ (?c, ?x, ?y)        --> (subb 0) @@ (c, y, x)
 *)
              ; make_rewrite
                  (#pident.Z_sub_with_get_borrow_concrete @ ??{ℤ} @ ??{ℤ} @ (#pident.Z_shiftl @ ??{ℤ}))
                  (fun s b x offset y => #(ident.fancy_subb (Z.log2 s) offset) @ (b, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_sub_with_get_borrow_concrete @ ??{ℤ} @ ??{ℤ} @ (#pident.Z_shiftr @ ??{ℤ}))
                  (fun s b x offset y => #(ident.fancy_subb (Z.log2 s) (-offset)) @ (b, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_sub_with_get_borrow_concrete @ ??{ℤ} @ ??{ℤ} @ ??{ℤ})
                  (fun s b x y => #(ident.fancy_subb (Z.log2 s) 0) @ (b, x, y)  when  s =? 2^Z.log2 s)
              (*(Z.rshi_concrete 2^256 ?n) @@ (?c, ?x, ?y) --> (rshi n) @@ (x, y)*)
              ; make_rewrite
                  (#pident.Z_rshi_concrete @ ??{ℤ} @ ??{ℤ})
                  (fun '((s, n)%core) x y => #(ident.fancy_rshi (Z.log2 s) n) @ (x, y)  when  s =? 2^Z.log2 s)
(*
Z.zselect @@ (Z.cc_m_concrete 2^256 ?c, ?x, ?y) --> selm @@ (c, x, y)
Z.zselect @@ (?c &' 1, ?x, ?y)                  --> sell @@ (c, x, y)
Z.zselect @@ (?c, ?x, ?y)                       --> selc @@ (c, x, y)
 *)
              ; make_rewrite
                  (#pident.Z_zselect @ (#pident.Z_cc_m_concrete @ ??{ℤ}) @ ??{ℤ} @ ??{ℤ})
                  (fun s c x y => #(ident.fancy_selm (Z.log2 s)) @ (c, x, y)  when  s =? 2^Z.log2 s)
              ; make_rewrite
                  (#pident.Z_zselect @ (#pident.Z_land @ ??{ℤ}) @ ??{ℤ} @ ??{ℤ})
                  (fun mask c x y => #ident.fancy_sell @ (c, x, y)  when  mask =? 1)
              ; make_rewrite
                  (#pident.Z_zselect @ ??{ℤ} @ ??{ℤ} @ ??{ℤ})
                  (fun c x y => #ident.fancy_selc @ (c, x, y))
(*Z.add_modulo @@ (?x, ?y, ?m) --> addm @@ (x, y, m)*)
              ; make_rewrite
                  (#pident.Z_add_modulo @ ??{ℤ} @ ??{ℤ} @ ??{ℤ})
                  (fun x y m => #ident.fancy_addm @ (x, y, m))
(*
Z.mul @@ (?x &' (2^128-1), ?y &' (2^128-1)) --> mulll @@ (x, y)
Z.mul @@ (?x &' (2^128-1), ?y >> 128)       --> mullh @@ (x, y)
Z.mul @@ (?x >> 128, ?y &' (2^128-1))       --> mulhl @@ (x, y)
Z.mul @@ (?x >> 128, ?y >> 128)             --> mulhh @@ (x, y)
 *)
              (* literal on left *)
              ; make_rewrite
                  (#?ℤ * (#pident.Z_land @ ??{ℤ}))
                  (fun x mask y => let s := (2*Z.log2_up mask)%Z in x <---- invert_low s x; #(ident.fancy_mulll s) @ (##x, y)  when  (mask =? 2^(s/2)-1))
              ; make_rewrite
                  (#?ℤ * (#pident.Z_shiftr @ ??{ℤ}))
                  (fun x offset y => let s := (2*offset)%Z in x <---- invert_low s x; #(ident.fancy_mullh s) @ (##x, y))
              ; make_rewrite
                  (#?ℤ * (#pident.Z_land @ ??{ℤ}))
                  (fun x mask y => let s := (2*Z.log2_up mask)%Z in x <---- invert_high s x; #(ident.fancy_mulhl s) @ (##x, y)  when  mask =? 2^(s/2)-1)
              ; make_rewrite
                  (#?ℤ * (#pident.Z_shiftr @ ??{ℤ}))
                  (fun x offset y => let s := (2*offset)%Z in x <---- invert_high s x; #(ident.fancy_mulhh s) @ (##x, y))

              (* literal on right *)
              ; make_rewrite
                  ((#pident.Z_land @ ??{ℤ}) * #?ℤ)
                  (fun mask x y => let s := (2*Z.log2_up mask)%Z in y <---- invert_low s y; #(ident.fancy_mulll s) @ (x, ##y)  when  (mask =? 2^(s/2)-1))
              ; make_rewrite
                  ((#pident.Z_land @ ??{ℤ}) * #?ℤ)
                  (fun mask x y => let s := (2*Z.log2_up mask)%Z in y <---- invert_high s y; #(ident.fancy_mullh s) @ (x, ##y)  when  mask =? 2^(s/2)-1)
              ; make_rewrite
                  ((#pident.Z_shiftr @ ??{ℤ}) * #?ℤ)
                  (fun offset x y => let s := (2*offset)%Z in y <---- invert_low s y; #(ident.fancy_mulhl s) @ (x, ##y))
              ; make_rewrite
                  ((#pident.Z_shiftr @ ??{ℤ}) * #?ℤ)
                  (fun offset x y => let s := (2*offset)%Z in y <---- invert_high s y; #(ident.fancy_mulhh s) @ (x, ##y))

              (* no literal *)
              ; make_rewrite
                  ((#pident.Z_land @ ??{ℤ}) * (#pident.Z_land @ ??{ℤ}))
                  (fun mask1 x mask2 y => let s := (2*Z.log2_up mask1)%Z in #(ident.fancy_mulll s) @ (x, y)  when  (mask1 =? 2^(s/2)-1) && (mask2 =? 2^(s/2)-1))
              ; make_rewrite
                  ((#pident.Z_land @ ??{ℤ}) * (#pident.Z_shiftr @ ??{ℤ}))
                  (fun mask x offset y => let s := (2*offset)%Z in #(ident.fancy_mullh s) @ (x, y)  when  mask =? 2^(s/2)-1)
              ; make_rewrite
                  ((#pident.Z_shiftr @ ??{ℤ}) * (#pident.Z_land @ ??{ℤ}))
                  (fun offset x mask y => let s := (2*offset)%Z in #(ident.fancy_mulhl s) @ (x, y)  when  mask =? 2^(s/2)-1)
              ; make_rewrite
                  ((#pident.Z_shiftr @ ??{ℤ}) * (#pident.Z_shiftr @ ??{ℤ}))
                  (fun offset1 x offset2 y => let s := (2*offset1)%Z in #(ident.fancy_mulhh s) @ (x, y)  when  offset1 =? offset2)

            ]%list%pattern%cps%option%under_lets%Z%bool.

        Definition fancy_dtree'
          := Eval compute in @compile_rewrites ident var pattern.ident pattern.ident.arg_types pattern.ident.ident_beq 100 fancy_rewrite_rules.
        Definition fancy_dtree : decision_tree
          := Eval compute in invert_Some fancy_dtree'.
        Definition fancy_default_fuel := Eval compute in List.length fancy_rewrite_rules.

        Import PrimitiveHList.
        Definition fancy_split_rewrite_rules := Eval cbv [split_list projT1 projT2 fancy_rewrite_rules] in split_list fancy_rewrite_rules.
        Definition fancy_pr1_rewrite_rules := Eval hnf in projT1 fancy_split_rewrite_rules.
        Definition fancy_pr2_rewrite_rules := Eval hnf in projT2 fancy_split_rewrite_rules.
        Definition fancy_all_rewrite_rules := combine_hlist (P:=rewrite_ruleTP) fancy_pr1_rewrite_rules fancy_pr2_rewrite_rules.

        Definition fancy_rewrite_head0 do_again {t} (idc : ident t) : value_with_lets t
          := @assemble_identifier_rewriters fancy_dtree fancy_all_rewrite_rules do_again t idc.
      End fancy.
    End with_var.

    Section red_fancy.
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> option Z)
              {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Let rewrite_head1
        := Eval cbv -[fancy_pr2_rewrite_rules
                        base.interp base.try_make_transport_cps
                        type.try_make_transport_cps type.try_transport_cps
                        UnderLets.splice UnderLets.to_expr
                        Compile.reflect Compile.reify Compile.reify_and_let_binds_cps UnderLets.reify_and_let_binds_base_cps
                        Compile.value' SubstVarLike.is_var_fst_snd_pair_opp
                     ] in @fancy_rewrite_head0 var invert_low invert_high do_again t idc.
      (* Finished transaction in 1.434 secs (1.432u,0.s) (successful) *)

      Time Local Definition fancy_rewrite_head2
        := Eval cbv [id
                       rewrite_head1 fancy_pr2_rewrite_rules
                       projT1 projT2
                       cpsbind cpscall cps_option_bind cpsreturn
                       pattern.ident.arg_types
                       Compile.app_binding_data
                       Compile.app_pbase_type_interp_cps
                       Compile.app_ptype_interp_cps
                       Compile.bind_base_cps
                       Compile.bind_data_cps
                       Compile.binding_dataT
                       Compile.bind_value_cps
                       Compile.eval_decision_tree
                       Compile.eval_rewrite_rules
                       Compile.expr_of_rawexpr
                       Compile.lift_pbase_type_interp_cps
                       Compile.lift_ptype_interp_cps
                       Compile.lift_with_bindings
                       Compile.pbase_type_interp_cps
                       Compile.ptype_interp
                       Compile.ptype_interp_cps
                       (*Compile.reflect*)
                       (*Compile.reify*)
                       Compile.reveal_rawexpr_cps
                       Compile.rValueOrExpr
                       Compile.swap_list
                       Compile.type_of_rawexpr
                       Compile.value
                       (*Compile.value'*)
                       Compile.value_of_rawexpr
                       Compile.value_with_lets
                       Compile.with_bindingsT
                       ident.smart_Literal
                       type.try_transport_cps
                       rlist_rect rlist_rect_cast rwhen
                    ] in rewrite_head1.
      (* Finished transaction in 1.347 secs (1.343u,0.s) (successful) *)

      Local Arguments base.try_make_base_transport_cps _ !_ !_.
      Local Arguments base.try_make_transport_cps _ !_ !_.
      Local Arguments type.try_make_transport_cps _ _ _ !_ !_.
      Local Arguments fancy_rewrite_head2 / .

      Time Definition fancy_rewrite_head
        := Eval cbn [id
                       fancy_rewrite_head2
                       cpsbind cpscall cps_option_bind cpsreturn
                       Compile.reify Compile.reify_and_let_binds_cps Compile.reflect Compile.value'
                       UnderLets.reify_and_let_binds_base_cps
                       UnderLets.splice UnderLets.splice_list UnderLets.to_expr
                       base.interp base.base_interp
                       type.try_make_transport_cps base.try_make_transport_cps base.try_make_base_transport_cps
                       PrimitiveProd.Primitive.fst PrimitiveProd.Primitive.snd Datatypes.fst Datatypes.snd
                    ] in fancy_rewrite_head2.
      (* Finished transaction in 13.298 secs (13.283u,0.s) (successful) *)

      Redirect "/tmp/fancy_rewrite_head" Print fancy_rewrite_head.
    End red_fancy.

    Section red.
      Context {var : type.type base.type -> Type}
              (do_again : forall t : base.type, @expr base.type ident (@Compile.value base.type ident var) (type.base t)
                                                -> UnderLets.UnderLets base.type ident var (@expr base.type ident var (type.base t)))
              {t} (idc : ident t).

      Time Let rewrite_head1
        := Eval cbv -[pr2_rewrite_rules
                        base.interp base.try_make_transport_cps
                        type.try_make_transport_cps type.try_transport_cps
                        UnderLets.splice UnderLets.to_expr
                        Compile.reflect UnderLets.reify_and_let_binds_base_cps Compile.reify Compile.reify_and_let_binds_cps
                        Compile.value'
                        SubstVarLike.is_var_fst_snd_pair_opp
                     ] in @rewrite_head0 var do_again t idc.
      (* Finished transaction in 16.593 secs (16.567u,0.s) (successful) *)

      Time Local Definition rewrite_head2
        := Eval cbv [id
                       rewrite_head1 pr2_rewrite_rules
                       projT1 projT2
                       cpsbind cpscall cps_option_bind cpsreturn
                       pattern.ident.arg_types
                       Compile.app_binding_data
                       Compile.app_pbase_type_interp_cps
                       Compile.app_ptype_interp_cps
                       Compile.bind_base_cps
                       Compile.bind_data_cps
                       Compile.binding_dataT
                       Compile.bind_value_cps
                       Compile.eval_decision_tree
                       Compile.eval_rewrite_rules
                       Compile.expr_of_rawexpr
                       Compile.lift_pbase_type_interp_cps
                       Compile.lift_ptype_interp_cps
                       Compile.lift_with_bindings
                       Compile.pbase_type_interp_cps
                       Compile.ptype_interp
                       Compile.ptype_interp_cps
                       (*Compile.reflect*)
                       (*Compile.reify*)
                       Compile.reveal_rawexpr_cps
                       Compile.rValueOrExpr
                       Compile.swap_list
                       Compile.type_of_rawexpr
                       Compile.value
                       (*Compile.value'*)
                       Compile.value_of_rawexpr
                       Compile.value_with_lets
                       Compile.with_bindingsT
                       ident.smart_Literal
                       type.try_transport_cps
                       rlist_rect rlist_rect_cast rwhen
                    ] in rewrite_head1.
      (* Finished transaction in 29.683 secs (29.592u,0.048s) (successful) *)

      Local Arguments base.try_make_base_transport_cps _ !_ !_.
      Local Arguments base.try_make_transport_cps _ !_ !_.
      Local Arguments type.try_make_transport_cps _ _ _ !_ !_.
      Local Arguments rewrite_head2 / .

      Time Definition rewrite_head
        := Eval cbn [id
                       rewrite_head2
                       cpsbind cpscall cps_option_bind cpsreturn
                       Compile.reify Compile.reify_and_let_binds_cps Compile.reflect Compile.value'
                       UnderLets.reify_and_let_binds_base_cps
                       UnderLets.splice UnderLets.splice_list UnderLets.to_expr
                       base.interp base.base_interp
                       type.try_make_transport_cps base.try_make_transport_cps base.try_make_base_transport_cps
                       PrimitiveProd.Primitive.fst PrimitiveProd.Primitive.snd Datatypes.fst Datatypes.snd
                    ] in rewrite_head2.
      (* Finished transaction in 16.561 secs (16.54u,0.s) (successful) *)

      Redirect "/tmp/rewrite_head" Print rewrite_head.
    End red.

    Definition Rewrite {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (@rewrite_head) default_fuel t e.
    Definition RewriteToFancy
               (invert_low invert_high : Z (*log2wordmax*) -> Z -> option Z)
               {t} (e : expr.Expr (ident:=ident) t) : expr.Expr (ident:=ident) t
      := @Compile.Rewrite (fun var _ => @fancy_rewrite_head invert_low invert_high var) fancy_default_fuel t e.
  End RewriteRules.

  Import defaults.

  Definition PartialEvaluate {t} (e : Expr t) : Expr t := RewriteRules.Rewrite e.
End Compilers.
