Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.LetIn.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.InversionExtra.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Rewriter.Language.UnderLets.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.ZRange.Compilers.
  Import invert_expr.
  Import Language.InversionExtra.Compilers.

  (** XXX TODO: Do we still need to do UnderLets here? *)
  Module partial.
    Import UnderLets.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Let type_base (x : base_type) : type := type.base x.
      Local Coercion type_base : base_type >-> type.
      Context {ident : type -> Type}
              {var : type -> Type}.
      Local Notation expr := (@expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident var).
      Context (abstract_domain' : base_type -> Type)
              (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> UnderLets (@expr var t))
              (bottom' : forall A, abstract_domain' A)
              (skip_annotations_under : forall t, ident t -> bool).

      Definition abstract_domain (t : type)
        := type.interp abstract_domain' t.

      Fixpoint value (t : type)
        := match t return Type (* COQBUG(https://github.com/coq/coq/issues/7727) *) with
           | type.base t
             => abstract_domain t * @expr var t
           | type.arrow s d
             => value s -> UnderLets (value d)
           end%type.

      Definition value_with_lets (t : type)
        := UnderLets (value t).

      Context (interp_ident : bool (* annotate with state? *) -> forall t, ident t -> value_with_lets t).

      Fixpoint bottom {t} : abstract_domain t
        := match t with
           | type.base t => bottom' t
           | type.arrow s d => fun _ => @bottom d
           end.

      Fixpoint bottom_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow abstract_domain t
        := match t return type.for_each_lhs_of_arrow abstract_domain t with
           | type.base t => tt
           | type.arrow s d => (bottom, @bottom_for_each_lhs_of_arrow d)
           end.

      Definition state_of_value {t} : value t -> abstract_domain t
        := match t return value t -> abstract_domain t with
           | type.base t => fun '(st, v) => st
           | type.arrow s d => fun _ => bottom
           end.

      (** We need to make sure that we ignore the state of
         higher-order arrows *everywhere*, or else the proofs don't go
         through.  So we sometimes need to replace the state of
         arrow-typed values with [⊥]. *)
      Fixpoint bottomify {t} : value t -> value_with_lets t
        := match t return value t -> value_with_lets t with
           | type.base t => fun '(st, v) => Base (bottom' t, v)
           | type.arrow s d => fun f => Base (fun x => fx <-- f x; @bottomify d fx)
           end%under_lets.

      (** We drop the state of higher-order arrows *)
      Fixpoint reify (annotate_with_state : bool) (is_let_bound : bool) {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t)
        := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t) with
           | type.base t
             => fun '(st, v) 'tt
                => if annotate_with_state
                   then annotate is_let_bound t st v
                   else if is_let_bound
                        then UnderLets.UnderLet v (fun v' => UnderLets.Base ($v'))
                        else UnderLets.Base v
           | type.arrow s d
             => fun f_e '(sv, dv)
               => let sv := match s with
                           | type.base _ => sv
                           | type.arrow _ _ => bottom
                           end in
                 Base
                   (λ x , (UnderLets.to_expr
                             (fx <-- f_e (@reflect annotate_with_state _ (expr.Var x) sv);
                                @reify annotate_with_state false _ fx dv)))
           end%core%expr
      with reflect (annotate_with_state : bool) {t} : @expr var t -> abstract_domain t -> value t
           := match t return @expr var t -> abstract_domain t -> value t with
              | type.base t
                => fun e st => (st, e)
              | type.arrow s d
                => fun e absf
                   => (fun v
                       => let stv := state_of_value v in
                          (rv <-- (@reify annotate_with_state false s v bottom_for_each_lhs_of_arrow);
                             Base (@reflect annotate_with_state d (e @ rv) (absf stv))%expr))
              end%under_lets.

      Definition skip_annotations_for_App {var'} {t} (e : @expr var' t) : bool
        := match invert_AppIdent_curried e with
           | Some (existT _ (idc, args)) => skip_annotations_under _ idc
           | None => false
           end.

      Fixpoint interp (annotate_with_state : bool) {t} (e : @expr value_with_lets t) : value_with_lets t
        := let annotate_with_state := annotate_with_state && negb (skip_annotations_for_App e) in
           match e in expr.expr t return value_with_lets t with
           | expr.Ident t idc => interp_ident annotate_with_state _ idc (* Base (reflect (###idc) (abstract_interp_ident _ idc))*)
           | expr.Var t v => v
           | expr.Abs s d f => Base (fun x => @interp annotate_with_state d (f (Base x)))
           | expr.App (type.base s) d f x
             => (x' <-- @interp annotate_with_state _ x;
                   f' <-- @interp annotate_with_state (_ -> d)%etype f;
                   f' x')
           | expr.App (type.arrow s' d') d f x
             => (x' <-- @interp annotate_with_state (s' -> d')%etype x;
                   x'' <-- bottomify x';
                   f' <-- @interp annotate_with_state (_ -> d)%etype f;
                   f' x'')
           | expr.LetIn (type.arrow _ _) B x f
             => (x' <-- @interp annotate_with_state _ x;
                   @interp annotate_with_state _ (f (Base x')))
           | expr.LetIn (type.base A) B x f
             => (x' <-- @interp annotate_with_state _ x;
                   x'' <-- reify annotate_with_state true (* this forces a let-binder here *) x' tt;
                   @interp annotate_with_state _ (f (Base (reflect annotate_with_state x'' (state_of_value x')))))
           end%under_lets.

      Definition eval_with_bound' (annotate_with_state : bool) {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp annotate_with_state e; reify annotate_with_state false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' false e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify true false (reflect true e bottom) st).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t).

        (** like [expr.interp (@ident_extract) e], except we replace
            all higher-order state with bottom *)
        Fixpoint extract' {t} (e : @expr abstract_domain t) : abstract_domain t
          := match e in expr.expr t return abstract_domain t with
             | expr.Ident t idc => ident_extract t idc
             | expr.Var t v => v
             | expr.Abs s d f => fun v : abstract_domain s => @extract' _ (f v)
             | expr.App (type.base s) d f x
               => @extract' _ f (@extract' _ x)
             | expr.App (type.arrow s' d') d f x
               => @extract' _ f (@bottom (type.arrow s' d'))
             | expr.LetIn A B x f => dlet y := @extract' _ x in @extract' _ (f y)
             end.

        Definition extract_gen {t} (e : @expr abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
          : abstract_domain' (type.final_codomain t)
          := type.app_curried (extract' e) bound.
      End extract.
    End with_var.

    Module ident.
      Section with_var.
        Local Notation type := (type base.type).
        Let type_base (x : base.type.base) : base.type := base.type.type_base x.
        Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base : base.type >-> type.type.
        Local Coercion type_base : base.type.base >-> base.type.
        Context {var : type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation UnderLets := (@UnderLets base.type ident var).
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Local Notation value_with_lets := (@value_with_lets base.type ident var abstract_domain').
        Local Notation value := (@value base.type ident var abstract_domain').
        Context (annotate_expr : forall t, abstract_domain' t -> option (@expr var (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (extract_option_state : forall A, abstract_domain' (base.type.option A) -> option (option (abstract_domain' A)))
                (is_annotated_for : forall t t', @expr var t -> abstract_domain' t' -> bool)
                (annotation_to_cast : forall s d, @expr var (s -> d) -> option (@expr var s -> @expr var d))
                (skip_annotations_under : forall t, ident t -> bool)
                (strip_annotation : forall t, ident t -> option (value t)).

        (** TODO: Is it okay to commute annotations? *)
        Definition update_annotation {t} (st : abstract_domain' t) (e : @expr var t) : @expr var t
          := match e, annotate_expr _ st with
             | (cst' @ e'), Some cst
               => if is_annotated_for _ _ cst' st
                  then e
                  else cst @ e
             | _, Some cst => cst @ e
             | _, None => e
             end%expr_pat%expr.

        Definition annotate_with_expr (is_let_bound : bool) {t}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := let cst_e := update_annotation st e (*match annotate_expr _ st with
                          | Some cst => ###cst @ e
                          | None => e
                          end%expr*) in
             if is_let_bound
             then UnderLet cst_e (fun v => Base ($v)%expr)
             else Base cst_e.

        Definition annotate_base (is_let_bound : bool) {t : base.type.base}
                   (st : abstract_domain' t) (e : @expr var t)
          : UnderLets (@expr var t)
          := annotate_with_expr is_let_bound st e.

        Fixpoint annotate (is_let_bound : bool) {t : base.type} : abstract_domain' t -> @expr var t -> UnderLets (@expr var t)
          := match t return abstract_domain' t -> @expr var t -> UnderLets (@expr var t) with
             | base.type.type_base t => annotate_base is_let_bound
             | base.type.unit
               => fun _ e
                  => (* we need to keep let-bound unit expressions around for comments *)
                    if is_let_bound
                    then UnderLet e (fun v => Base ($v)%expr)
                    else Base e
             | base.type.prod A B
               => fun st e
                  => match invert_pair e with
                     | Some (x, y)
                       => let stx := abstract_interp_ident _ ident.fst st in
                          let sty := abstract_interp_ident _ ident.snd st in
                          (x' <-- @annotate is_let_bound A stx x;
                             y' <-- @annotate is_let_bound B sty y;
                             Base (x', y')%expr)
                     | None => annotate_with_expr is_let_bound st e
                     end
             | base.type.list A
               => fun st e
                  => match extract_list_state _ st, reflect_list e with
                     | Some ls_st, Some ls_e
                       => (retv <---- (List.map
                                         (fun '(st', e') => @annotate is_let_bound A st' e')
                                         (List.combine ls_st ls_e));
                             Base (reify_list retv))
                     | Some ls_st, None
                       => (retv <---- (List.map
                                         (fun '(n, st')
                                          => let e' := (#ident.List_nth_default @ DefaultValue.expr.base.default @ e @ ##(n:nat))%expr in
                                             @annotate is_let_bound A st' e')
                                         (List.combine (List.seq 0 (List.length ls_st)) ls_st));
                             Base (reify_list retv))
                     | None, _ => annotate_with_expr is_let_bound st e
                     end
             | base.type.option A
               => fun st e
                  => match extract_option_state _ st, reflect_option e with
                     | Some v_st, Some v_e
                       => (retv <----- (Option.map
                                          (fun '(st', e') => @annotate is_let_bound A st' e')
                                          (Option.combine v_st v_e));
                             Base (reify_option retv))
                     | Some _, None
                     | None, _
                       => annotate_with_expr is_let_bound st e
                     end
             end%under_lets.

        Local Notation reify := (@reify base.type ident var abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident var abstract_domain' annotate bottom').

        (** We manually rewrite with the rule for [nth_default], as the eliminator for eta-expanding lists in the input *)
        Definition interp_ident (annotate_with_state : bool) {t} (idc : ident t) : value_with_lets t
          := match idc in ident t return value_with_lets t with
             | ident.List_nth_default T as idc
               => let default := reflect annotate_with_state (###idc) (abstract_interp_ident _ idc) in
                  Base
                    (fun default_arg
                     => default <-- default default_arg;
                          Base
                            (fun ls_arg
                             => default <-- default ls_arg;
                                  Base
                                    (fun n_arg
                                     => default <-- default n_arg;
                                          ls' <-- @reify annotate_with_state false (base.type.list T) ls_arg tt;
                                          Base
                                            (fst default,
                                             match reflect_list ls', invert_Literal (snd n_arg) with
                                             | Some ls, Some n
                                               => nth_default (snd default_arg) ls n
                                             | _, _ => snd default
                                             end))))
             | idc => Base
                        match strip_annotation _ idc with
                        | Some v => v
                        | None => reflect annotate_with_state (###idc) (abstract_interp_ident _ idc)
                        end
             end%core%under_lets%expr.

        Fixpoint strip_all_annotations' (should_strip : bool) {t} (e : @expr var t) : @expr var t
          := match e in expr.expr t return expr t with
             | expr.Ident _ _ as e
             | expr.Var _ _ as e
               => e
             | expr.Abs s d f
               => expr.Abs (fun x => strip_all_annotations' should_strip (f x))
             | expr.App s d f x
               => let should_strip
                      := (should_strip || match invert_AppIdent_curried f with
                                          | Some (existT _ (idc, _)) => skip_annotations_under _ idc
                                          | None => false
                                          end)%bool in
                  let f := strip_all_annotations' should_strip f in
                  let x := strip_all_annotations' should_strip x in
                  if should_strip
                  then match annotation_to_cast _ _ f with
                       | Some f => f x
                       | None => expr.App f x
                       end
                  else expr.App f x
             | expr.LetIn A B x f
               => expr.LetIn (strip_all_annotations' should_strip x) (fun v => strip_all_annotations' should_strip (f v))
             end.
        Definition strip_all_annotations {t} (e : @expr var t) : @expr var t
          := @strip_all_annotations' false t e.

        Definition eval_with_bound (skip_annotations_under : forall t, ident t -> bool) (annotate_with_state : bool) {t} (e : @expr value_with_lets t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eval_with_bound' base.type ident var abstract_domain' annotate bottom' skip_annotations_under interp_ident annotate_with_state t e st.

        Definition eval {t} (e : @expr value_with_lets t) : @expr var t
          := @eval' base.type ident var abstract_domain' annotate bottom' (fun _ _ => false) interp_ident t e.

        Definition eta_expand_with_bound {t} (e : @expr var t)
                   (st : type.for_each_lhs_of_arrow abstract_domain t)
          : @expr var t
          := @eta_expand_with_bound' base.type ident var abstract_domain' annotate bottom' t e st.

        Definition extract {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
          := @extract_gen base.type ident abstract_domain' bottom' abstract_interp_ident t e bound.
      End with_var.
    End ident.

    Definition default_relax_zrange (v : zrange) : option zrange := Some v.

    Section specialized.
      Local Notation abstract_domain' := ZRange.type.base.option.interp.
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation value_with_lets var := (@value_with_lets base.type ident var abstract_domain').
      Local Notation value var := (@value base.type ident var abstract_domain').
      Notation expr := (@expr base.type ident).
      Notation Expr := (@expr.Expr base.type ident).
      Local Notation type := (type base.type).
      Let type_base (x : base.type.base) : base.type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : base.type.base >-> base.type.
      Local Notation tZ := (base.type.type_base base.type.Z).

      Section with_relax.
        Context (relax_zrange : zrange -> option zrange).

        Let always_relax_zrange : zrange -> zrange
          := fun range => match relax_zrange (ZRange.normalize range) with
                          | Some r => r
                          | None => range
                          end.

        Definition annotation_of_state (st : abstract_domain' base.type.Z) : option zrange
          := option_map always_relax_zrange st.

        Local Notation cstZ r
          := (expr.App
                (d:=type.arrow (type.base tZ) (type.base tZ))
                (expr.Ident ident.Z_cast)
                (expr.Ident (@ident.Literal base.type.zrange r%zrange))).
        Local Notation cstZZ r1 r2
          := (expr.App
                (d:=type.arrow (type.base (tZ * tZ)) (type.base (tZ * tZ)))
                (expr.Ident ident.Z_cast2)
                (#(@ident.Literal base.type.zrange r1%zrange), #(@ident.Literal base.type.zrange r2%zrange))%expr_pat).

        Definition annotate_expr {var} t : abstract_domain' t -> option (@expr var (t -> t))
          := match t return abstract_domain' t -> option (expr (t -> t)) with
             | tZ
               => fun st => st' <- annotation_of_state st; Some (cstZ st')
             | tZ * tZ
               => fun '(sta, stb) => sta' <- annotation_of_state sta; stb' <- annotation_of_state stb; Some (cstZZ sta' stb')
             | _ => fun _ => None
             end%option%etype.

        Definition abstract_interp_ident {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) t (idc : ident t) : type.interp abstract_domain' t
          := ZRange.ident.option.interp assume_cast_truncates idc.

        Definition always_strip_annotation {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {var} t (idc : ident t) : option (value var t)
          := match idc in ident t return option (value var t) with
             | ident.Z_cast as idc
             | ident.Z_cast2 as idc
               => let tZ_type := (fun t (idc : ident (type.base _ -> type.base t -> type.base t)) => t) _ idc in (* we want Coq to pick up the Z type for bounds tightness, not the zrange type (where "tighter" means "equal") *)
                  Some
                    (fun '(r_orig, re)
                     => Base
                          (fun '(r_known, e)
                           => Base
                                ((abstract_interp_ident assume_cast_truncates _ idc r_orig r_known,
                                  let do_strip
                                      := match ZRange.type.base.option.lift_Some r_known, ZRange.type.base.option.lift_Some r_orig with
                                         | Some r_known, Some r_orig
                                           => ZRange.type.base.is_tighter_than
                                                (t:=tZ_type)
                                                r_known r_orig
                                         | _, _ => false
                                         end in
                                  if do_strip
                                  then e
                                  else (###idc @ re @ e)%expr))))
             | _ => None
             end.

        Definition strip_annotation {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) (strip_annotations : bool) {var} : forall t, ident t -> option (value var t)
          := if strip_annotations
             then always_strip_annotation assume_cast_truncates
             else fun _ _ => None.

        Definition is_annotated_for {var} t t' (idc : @expr var t) : abstract_domain' t' -> bool
          := match invert_Z_cast idc, invert_Z_cast2 idc, t' with
             | Some r, _, tZ
               => fun r'
                  => option_beq zrange_beq (Some r) (annotation_of_state r')
             | _, Some (r1, r2), base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)
               => fun '(r1', r2')
                  => (option_beq zrange_beq (Some r1) (annotation_of_state r1'))
                       && (option_beq zrange_beq (Some r2) (annotation_of_state r2'))
             | _, _, _ => fun _ => false
             end.

        Definition annotation_to_cast_helper {var1} {s'sd} (idc : ident s'sd) : option (@expr var1 (type.domain (type.codomain s'sd)) -> @expr var1 (type.codomain (type.codomain s'sd)))
          := match idc with
             | ident.Z_cast => Some (fun x => x)
             | ident.Z_cast2 => Some (fun x => x)
             | _ => None
             end.

        Definition annotation_to_cast {var1} {s d} (e : @expr var1 (s -> d)) : option (@expr var1 s -> @expr var1 d)
          := match invert_AppIdent e with
             | Some (existT s' (idc, _)) => annotation_to_cast_helper idc
             | None => None
             end.

        Definition annotation_to_expr {var1} t (idc : @expr var1 t) : option (forall var2, @expr var2 t)
          := match invert_Z_cast idc, invert_Z_cast2 idc, t with
             | Some r, _, (type.base tZ -> type.base tZ)%etype
               => Some (fun var2 => cstZ r)
             | _, Some (r1, r2), (type.base (tZ * tZ) -> type.base (tZ * tZ))%etype
               => Some (fun var2 => cstZZ r1 r2)
             | _, _, _ => None
             end.
        Definition bottom' T : abstract_domain' T
          := ZRange.type.base.option.None.
        Definition extract_list_state A (st : abstract_domain' (base.type.list A)) : option (list (abstract_domain' A))
          := st.
        Definition extract_option_state A (st : abstract_domain' (base.type.option A)) : option (option (abstract_domain' A))
          := st.

        Definition strip_all_annotations strip_annotations_under {var} {t} (e : @expr var t) : @expr var t
          := @ident.strip_all_annotations var (@annotation_to_cast _) strip_annotations_under t e.

        Definition eval_with_bound {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) (skip_annotations_under : forall t, ident t -> bool) (strip_preexisting_annotations : bool) {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
          := let annotate_with_state := true in
             (@partial.ident.eval_with_bound)
               var abstract_domain' annotate_expr bottom' (abstract_interp_ident assume_cast_truncates) extract_list_state extract_option_state is_annotated_for (strip_annotation assume_cast_truncates strip_preexisting_annotations) skip_annotations_under annotate_with_state t e bound.

        Definition eta_expand_with_bound {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
          := let assume_cast_truncates := false in
             let shiftr_avoid_uint1 : shiftr_avoid_uint1_opt := false (* this doesn't actually matter for [eta_expand_with_bound], which only invokes [abstract_interp_ident] on things like [fst], [snd], etc *) in
             (@partial.ident.eta_expand_with_bound)
               var abstract_domain' annotate_expr bottom' (abstract_interp_ident assume_cast_truncates) extract_list_state extract_option_state is_annotated_for t e bound.

        Definition StripAllAnnotations strip_annotations_under {t} (e : Expr t) : Expr t
          := fun var => strip_all_annotations strip_annotations_under (e _).

        Definition EvalWithBound {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) (skip_annotations_under : forall t, ident t -> bool) (strip_preexisting_annotations : bool) {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
          := fun var => eval_with_bound assume_cast_truncates skip_annotations_under strip_preexisting_annotations (e _) bound.
        Definition EtaExpandWithBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
          := fun var => eta_expand_with_bound (e _) bound.
      End with_relax.

      Definition strip_annotations {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {var} {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : expr t
        := let strip_preexisting_annotations := true in
           let annotate_with_state := false in
           let skip_annotations_under := fun _ _ => false in
           (@partial.ident.eval_with_bound)
             var abstract_domain' (annotate_expr default_relax_zrange) bottom' (abstract_interp_ident assume_cast_truncates) extract_list_state extract_option_state (is_annotated_for default_relax_zrange) (strip_annotation assume_cast_truncates strip_preexisting_annotations) skip_annotations_under annotate_with_state t e bound.

      Definition StripAnnotations {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := fun var => strip_annotations assume_cast_truncates (e _) bound.

      Definition eval {opts : AbstractInterpretation.Options} {var} {t} (e : @expr _ t) : expr t
        := let assume_cast_truncates := false in
           let strip_preexisting_annotations := false in
           (@partial.ident.eval)
             var abstract_domain' (annotate_expr default_relax_zrange) bottom' (abstract_interp_ident assume_cast_truncates) extract_list_state extract_option_state (is_annotated_for default_relax_zrange) (strip_annotation assume_cast_truncates strip_preexisting_annotations)  t e.
      Definition Eval {opts : AbstractInterpretation.Options} {t} (e : Expr t) : Expr t
        := fun var => eval (e _).
      Definition EtaExpandWithListInfoFromBound {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : Expr t
        := EtaExpandWithBound default_relax_zrange e (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) bound).
      Definition extract {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {t} (e : expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' bottom' (abstract_interp_ident assume_cast_truncates) t e bound.
      Definition Extract {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' bottom' (abstract_interp_ident assume_cast_truncates) t (e _) bound.
    End specialized.
  End partial.
  Import API.

  Module Import CheckCasts.
    Fixpoint get_casts {t} (e : expr t) : list { t : _ & forall var, @expr var t }
      := match partial.annotation_to_expr _ e with
         | Some e => [existT _ t e]
         | None
           => match e with
              | expr.Ident t idc => nil
              | expr.Var t v => v
              | expr.Abs s d f => @get_casts _ (f nil)
              | expr.App s d f x => @get_casts _ f ++ @get_casts _ x
              | expr.LetIn A B x f => @get_casts _ x ++ @get_casts _ (f nil)
              end
         end%list.

    Definition GetUnsupportedCasts {t} (e : Expr t) : list { t : _ & forall var, @expr var t }
      := get_casts (e _).
  End CheckCasts.

  Definition PartialEvaluateWithBounds
             {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
             (relax_zrange : zrange -> option zrange)
             (assume_cast_truncates : bool)
             (skip_annotations_under : forall t, ident t -> bool)
             (strip_preexisting_annotations : bool)
             {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EvalWithBound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations (GeneralizeVar.GeneralizeVar (e _)) bound.
  Definition PartialEvaluateWithListInfoFromBounds
             {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
             {t} (e : Expr t)
             (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := partial.EtaExpandWithListInfoFromBound (GeneralizeVar.GeneralizeVar (e _)) bound.

  Definition CheckedPartialEvaluateWithBounds
             {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
             (relax_zrange : zrange -> option zrange)
             (assume_cast_truncates : bool)
             (skip_annotations_under : forall t, ident t -> bool)
             (strip_preexisting_annotations : bool)
             {t} (E : Expr t)
             (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
             (b_out : ZRange.type.base.option.interp (type.final_codomain t))
    : Expr t + (ZRange.type.base.option.interp (type.final_codomain t) * Expr t + list { t : _ & forall var, @expr var t })
    := dlet_nd e := GeneralizeVar.ToFlat E in
       let E := GeneralizeVar.FromFlat e in
       let b_computed := partial.Extract assume_cast_truncates E b_in in
       let unsupported_casts := if strip_preexisting_annotations
                                then nil
                                else CheckCasts.GetUnsupportedCasts E in
       match unsupported_casts with
       | nil => (let E := PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in in
                if ZRange.type.base.option.is_tighter_than b_computed b_out
                then @inl (Expr t) _ E
                else inr (@inl (ZRange.type.base.option.interp (type.final_codomain t) * Expr t) _ (b_computed, E)))
       | unsupported_casts => inr (inr unsupported_casts)
       end.
End Compilers.
