Require Import Crypto.Language.
Require Import Crypto.Util.Notations.

Module Compilers.
  Export Language.Compilers.
  Import invert_expr.

  Module SubstVarLike.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Section with_var.
        Context {var : type -> Type}.
        Section with_var_like.
          Context (is_var_like : forall t, @expr var t -> bool).
          Fixpoint subst_var_like {t} (e : @expr (@expr var) t) : @expr var t
            := match e with
               | expr.LetIn tx tC ex eC
                 => let ex' := @subst_var_like tx ex in
                    let eC' := fun v => @subst_var_like tC (eC v) in
                    if is_var_like _ ex'
                    then eC' ex'
                    else expr.LetIn ex' (fun v => eC' ($v))
               | expr.App s d f x
                 => let f' := @subst_var_like _ f in
                    let x' := @subst_var_like _ x in
                    expr.App f' x'
               | expr.Abs s d f
                 => expr.Abs (fun v => @subst_var_like _ (f ($v)))
               | expr.Var t v => v
               | expr.Ident t idc => expr.Ident idc
               end%expr.
        End with_var_like.
        Section with_ident_like.
          Context (ident_is_good : forall t, ident t -> bool).
          Fixpoint is_recursively_var_or_ident {t} (e : @expr var t) : bool
            := match e with
               | expr.Ident t idc => ident_is_good _ idc
               | expr.Var t v => true
               | expr.Abs s d f => false
               | expr.App s d f x
                 => andb (@is_recursively_var_or_ident _ f)
                         (@is_recursively_var_or_ident _ x)
               | expr.LetIn A B x f => false
               end.
        End with_ident_like.
      End with_var.

      Definition SubstVarLike (is_var_like : forall var t, @expr var t -> bool)
                 {t} (e : expr.Expr t) : expr.Expr t
        := fun var => subst_var_like (is_var_like _) (e _).

      Definition SubstVar {t} (e : expr.Expr t) : expr.Expr t
        := SubstVarLike (fun _ _ e => match invert_Var e with Some _ => true | None => false end) e.

      Definition SubstVarOrIdent (should_subst_ident : forall t, ident t -> bool)
                 {t} (e : expr.Expr t) : expr.Expr t
        := SubstVarLike (fun var t => is_recursively_var_or_ident should_subst_ident) e.
    End with_ident.

    Definition ident_is_var_like {t} (idc : ident t) : bool
      := match idc with
         | ident.Literal _ _
         | ident.nil _
         | ident.cons _
         | ident.pair _ _
         | ident.fst _ _
         | ident.snd _ _
         | ident.Z_opp
         | ident.Z_cast _
         | ident.Z_cast2 _
           => true
         | _ => false
         end.
    Definition is_var_fst_snd_pair_opp_cast {var} {t} (e : expr (var:=var) t) : bool
      := @is_recursively_var_or_ident base.type ident var (@ident_is_var_like) t e.
    Definition IsVarFstSndPairOppCast {t} (e : expr.Expr t) : bool
      := @is_var_fst_snd_pair_opp_cast (fun _ => unit) t (e _).

    Definition SubstVarFstSndPairOppCast {t} (e : expr.Expr t) : expr.Expr t
      := @SubstVarOrIdent base.type ident (@ident_is_var_like) t e.
  End SubstVarLike.

  Module UnderLets.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.
      Local Notation expr := (@expr base_type ident var).

      Inductive UnderLets {T : Type} :=
      | Base (v : T)
      | UnderLet {A} (x : expr A) (f : var A -> UnderLets).

      Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
        := match x with
           | Base v => e v
           | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
           end.

      Fixpoint splice_list {A B} (ls : list (@UnderLets A)) (e : list A -> @UnderLets B) : @UnderLets B
        := match ls with
           | nil => e nil
           | cons x xs
             => splice x (fun x => @splice_list A B xs (fun xs => e (cons x xs)))
           end.

      Definition splice_option {A B} (v : option (@UnderLets A)) (e : option A -> @UnderLets B) : @UnderLets B
        := match v with
           | None => e None
           | Some x
             => splice x (fun x => e (Some x))
           end.

      Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
        := match x with
           | Base v => v
           | UnderLet A x f
             => expr.LetIn x (fun v => @to_expr _ (f v))
           end.
      Fixpoint of_expr {t} (x : expr t) : @UnderLets (expr t)
        := match x in expr.expr t return @UnderLets (expr t) with
           | expr.LetIn A B x f
             => UnderLet x (fun v => @of_expr B (f v))
           | e => Base e
           end.
    End with_var.
    Module Export Notations.
      Global Arguments UnderLets : clear implicits.
      Delimit Scope under_lets_scope with under_lets.
      Bind Scope under_lets_scope with UnderLets.UnderLets.
      Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.
      Notation "x <---- y ; f" := (UnderLets.splice_list y (fun x => f%under_lets)) : under_lets_scope.
      Notation "x <----- y ; f" := (UnderLets.splice_option y (fun x => f%under_lets)) : under_lets_scope.
    End Notations.

    Section reify.
      Context {var : type.type base.type -> Type}.
      Local Notation type := (type.type base.type).
      Local Notation expr := (@expr.expr base.type ident var).
      Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
      Let type_base (t : base.type) : type := type.base t.
      Coercion type_base : base.type >-> type.

      Let default_reify_and_let_binds_base_cps {t : base.type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
        := fun e T k
           => match invert_expr.invert_Var e with
              | Some v => k ($v)%expr
              | None => if SubstVarLike.is_var_fst_snd_pair_opp_cast e
                        then k e
                        else UnderLets.UnderLet e (fun v => k ($v)%expr)
              end.

      Fixpoint reify_and_let_binds_base_cps {t : base.type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
        := match t return expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T with
           | base.type.type_base t
             => fun e T k
                => match invert_Literal e with
                   | Some v => k (expr.Ident (ident.Literal v))
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           | base.type.prod A B
             => fun e T k
                => match invert_pair e with
                   | Some (a, b)
                     => @reify_and_let_binds_base_cps
                          A a _
                          (fun ae
                           => @reify_and_let_binds_base_cps
                                B b _
                                (fun be
                                 => k (ae, be)%expr))
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           | base.type.list A
             => fun e T k
                => match reflect_list e with
                   | Some ls
                     => list_rect
                          _
                          (fun k => k []%expr)
                          (fun x _ rec k
                           => @reify_and_let_binds_base_cps
                                A x _
                                (fun xe
                                 => rec (fun xse => k (xe :: xse)%expr)))
                          ls
                          k
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           | base.type.option A
             => fun e T k
                => match reflect_option e with
                   | Some ls
                     => option_rect
                          _
                          (fun x k
                           => @reify_and_let_binds_base_cps
                                A x _
                                (fun xe
                                 => k (#ident.Some @ xe)%expr))
                          (fun k => k (#ident.None)%expr)
                          ls
                          k
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           end%under_lets.

      Fixpoint let_bind_return {t} : expr t -> expr t
        := match t return expr t -> expr t with
           | type.base t
             => fun e => to_expr (v <-- of_expr e; reify_and_let_binds_base_cps v _ Base)
           | type.arrow s d
             => fun e
                => expr.Abs (fun v => @let_bind_return
                                        d
                                        match invert_Abs e with
                                        | Some f => f v
                                        | None => e @ $v
                                        end%expr)
           end.
    End reify.
    Definition LetBindReturn {t} (e : expr.Expr t) : expr.Expr t
      := fun var => let_bind_return (e _).
  End UnderLets.
  Export UnderLets.Notations.
End Compilers.
