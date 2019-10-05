Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Language.Pre.
Require Import Crypto.Language.Language.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.HProp.
Import Coq.Lists.List ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.
Export Language.Pre.
Export Language.

Import EqNotations.
Module Compilers.
  Export Language.Pre.
  Export Language.Compilers.

  Module GoalType.
    Definition package := { exprInfo : Classes.ExprInfoT & Classes.ExprExtraInfoT }.
  End GoalType.

  Ltac get_min_and_incr min :=
    lazymatch min with
    | S ?min => let v := get_min_and_incr min in
                constr:(S v)
    | ?ev => let unif := open_constr:(eq_refl : S _ = ev) in
             O
    end.
  Ltac build_index_of_base base :=
    constr:(ltac:(let t := fresh "t" in
                  let min := open_constr:(_ : Datatypes.nat) in
                  unshelve (intro t; destruct t;
                            [ > let v := get_min_and_incr min in refine v .. ]);
                  exact O)
            : base -> Datatypes.nat).
  Ltac make_index_of_base base :=
    let res := build_index_of_base base in refine res.

  Ltac build_base_eq_dec base :=
    constr:(ltac:(decide equality)
            : forall x y : base, {x = y} + {x <> y}).
  Ltac make_base_eq_dec base :=
    let res := build_base_eq_dec base in refine res.

  Ltac build_eta_base_cps_gen base :=
    constr:(ltac:((unshelve eexists; let t := fresh in intro t; destruct t); shelve_unifiable; reflexivity)
            : forall (P : base -> Type)
                     (f : forall t, P t),
               { f' : forall t, P t | forall t, f' t = f t }).
  Ltac make_eta_base_cps_gen base := let res := build_eta_base_cps_gen base in refine res.

  Ltac build_eta_base_cps eta_base_cps_gen :=
    constr:((fun P f => proj1_sig (@eta_base_cps_gen _ f))
            : forall {P : _ -> Type} (f : forall t, P t) t, P t).
  Ltac make_eta_base_cps eta_base_cps_gen :=
    let res := build_eta_base_cps eta_base_cps_gen in refine res.

  Ltac build_base_interp eta_base_cps base_type_list index_of_base :=
    let eta_base_cps := (eval cbv in eta_base_cps) in
    let base_type_list := (eval hnf in base_type_list) in
    let index_of_base := (eval cbv in index_of_base) in
    (eval cbv [TypeList.nth] in
        (fun ty => @eta_base_cps (fun _ => Type) (fun t => TypeList.nth (index_of_base t) base_type_list True) ty)).
  Ltac make_base_interp eta_base_cps base_type_list index_of_base :=
    let res := build_base_interp eta_base_cps base_type_list index_of_base in refine res.

  Ltac build_baseHasNatAndCorrect base_interp :=
    constr:(ltac:(unshelve eexists; hnf; [ constructor | unshelve econstructor ]; cbv;
                  [ exact (fun x => x)
                  | exact (fun x => x)
                  | exact (fun P x v => v)
                  | exact (fun P x v => v) ])
            : { hasNat : base.type.BaseTypeHasNatT _ & @base.BaseHasNatCorrectT _ base_interp hasNat }).
  Ltac make_baseHasNatAndCorrect base_interp :=
    let res := build_baseHasNatAndCorrect base_interp in refine res.

  Ltac make_baseHasNat baseHasNatAndCorrect :=
    let res := (eval cbv in (projT1 baseHasNatAndCorrect)) in refine res.
  Ltac build_baseHasNat base baseHasNatAndCorrect :=
    constr:(ltac:(make_baseHasNat baseHasNatAndCorrect)
            : base.type.BaseTypeHasNatT base).

  Ltac make_baseHasNatCorrect baseHasNatAndCorrect :=
    let res := (eval cbv in (projT2 baseHasNatAndCorrect)) in refine res.
  Ltac build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect :=
    constr:(ltac:(make_baseHasNatCorrect baseHasNatAndCorrect)
            : @base.BaseHasNatCorrectT _ base_interp baseHasNat).

  Ltac build_base_beq_and_reflect base :=
    constr:(ltac:(unshelve eexists;
                  [ let x := fresh "x" in
                    let y := fresh "y" in
                    intros x y; destruct x, y
                  | apply reflect_of_beq;
                    [ let x := fresh in
                      let y := fresh in
                      intros x y; destruct x, y; try reflexivity; instantiate (1:=Datatypes.false);
                      intro; exfalso; apply diff_false_true; assumption
                    | let x := fresh in
                      let y := fresh in
                      intros x y ?; subst y; destruct x; reflexivity ] ])
            : { base_beq : _ & reflect_rel (@eq base) base_beq }).
  Ltac make_base_beq_and_reflect base :=
    let res := build_base_beq_and_reflect base in refine res.

  Ltac build_base_beq base_beq_and_reflect := (eval cbv in (projT1 base_beq_and_reflect)).
  Ltac make_base_beq base_beq_and_reflect :=
    let res := build_base_beq base_beq_and_reflect in refine res.

  Ltac make_reflect_base_beq base_beq_and_reflect := refine (projT2 base_beq_and_reflect).
  Ltac build_reflect_base_beq base base_beq base_beq_and_reflect :=
    constr:(ltac:(make_reflect_base_beq base_beq_and_reflect)
            : reflect_rel (@eq base) base_beq).

  Ltac build_base_interp_beq base_interp :=
    (eval cbv beta in
        (ltac:(let t := fresh "t" in
               intro t; destruct t;
               let h := head base_interp in
               cbv [h];
               refine ((fun T (beq : T -> T -> Datatypes.bool) (_ : reflect_rel (@eq T) beq) => beq) _ _ _))
         : forall t, base_interp t -> base_interp t -> Datatypes.bool)).
  Ltac make_base_interp_beq base_interp := let v := build_base_interp_beq base_interp in refine v.

  Ltac build_reflect_base_interp_eq base_interp base_interp_beq :=
    constr:(ltac:(let t := fresh "t" in
                  intro t; destruct t; cbv [base_interp base_interp_beq]; typeclasses eauto)
            : forall t, reflect_rel (@eq (base_interp t)) (@base_interp_beq t)).
  Ltac make_reflect_base_interp_eq base_interp base_interp_beq :=
    let res := build_reflect_base_interp_eq base_interp base_interp_beq in refine res.

  Ltac build_try_make_base_transport_cps base_eq_dec eta_base_cps :=
    constr:((fun (P : _ -> Type) (t1 t2 : _)
             => @eta_base_cps
                  _
                  (fun t1
                   => @eta_base_cps
                        (fun t2 => ~> option (P t1 -> P t2))
                        (fun t2
                         => match base_eq_dec t1 t2 with
                            | left pf => (return (Some (rew [fun t2 => P t1 -> P t2] pf in id)))
                            | right _ => (return None)
                            end)
                        t2)
                  t1)%cps
            : @type.try_make_transport_cpsT _).
  Ltac make_try_make_base_transport_cps base_eq_dec eta_base_cps :=
    let res := build_try_make_base_transport_cps base_eq_dec eta_base_cps in
    refine res.

  Ltac build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq :=
    constr:(ltac:(let P := fresh "P" in
                  let t1 := fresh "t1" in
                  let t2 := fresh "t2" in
                  intros P t1 t2; revert P t2; induction t1, t2; cbn;
                  Reflect.reflect_beq_to_eq_using reflect_base_beq; reflexivity)
            : @type.try_make_transport_cps_correctT _ _ try_make_base_transport_cps reflect_base_beq).
  Ltac make_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq :=
    let res := build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq in
    refine res.

  Ltac uneta_fun_push_eagerly term :=
    let term := (eval cbv beta in term) in
    lazymatch term with
    | fun a => ?f a => uneta_fun_push_eagerly f
    | (fun (a : ?A) => @?f a)
      => lazymatch constr:(
                     fun a : A
                     => ltac:(let f' := uneta_fun_push_eagerly (f a) in
                              exact f')) with
         | fun a => ?f a => uneta_fun_push_eagerly f
         | ?f => f
         end
    | ident.eagerly (?f ?x) => uneta_fun_push_eagerly (ident.eagerly f x)
    | ?f ?x => let f' := uneta_fun_push_eagerly f in
               let x' := uneta_fun_push_eagerly x in
               (eval cbv beta in (f' x'))
    | ?f => f
    end.
  Ltac build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident :=
    constr:(ltac:(let ident_interp_head := head ident_interp in
                  let baseHasNat' := (eval hnf in baseHasNat) in
                  let baseHasNatCorrect' := (eval hnf in baseHasNatCorrect) in
                  change baseHasNatCorrect with baseHasNatCorrect';
                  unshelve econstructor; [ econstructor; intros; shelve | constructor ]; intros;
                  lazymatch goal with
                  | [ |- ?ii ?id = ?v ]
                    => let id' := (eval cbv in id) in
                       change (ii id' = v); cbv [ident_interp_head];
                       change baseHasNat with baseHasNat'; cbv [base.of_nat base.to_nat];
                       match goal with
                       | [ |- ?LHS = ?v ] => let v' := uneta_fun_push_eagerly v in change (LHS = v')
                       end;
                       lazymatch goal with
                       | [ |- _ = ?v ]
                         => reify_ident v ltac:(fun idc => unify id' idc) ltac:(fun term => fail 0 "could not reify" term "as an ident") ltac:(fun _ => fail 0 "could not reify" v "as an ident")
                       end
                  end; reflexivity)
            : { buildEagerIdent : _ & @ident.BuildInterpEagerIdentCorrectT _ _ _ ident_interp baseHasNat buildEagerIdent baseHasNatCorrect }).
  Ltac make_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident :=
    let res := build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident in refine res.

  Ltac make_buildEagerIdent buildEagerIdentAndInterpCorrect :=
    let v := (eval hnf in (projT1 buildEagerIdentAndInterpCorrect)) in
    exact v.
  Ltac build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect :=
    constr:(ltac:(make_buildEagerIdent buildEagerIdentAndInterpCorrect)
            : @ident.BuildEagerIdentT _ ident baseHasNat).

  Ltac make_buildInterpEagerIdentCorrect buildEagerIdentAndInterpCorrect :=
    refine (projT2 buildEagerIdentAndInterpCorrect).
  Ltac build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect :=
    constr:(ltac:(make_buildInterpEagerIdentCorrect buildEagerIdentAndInterpCorrect)
            : @ident.BuildInterpEagerIdentCorrectT _ _ _ ident_interp _ buildEagerIdent baseHasNatCorrect).

  Ltac build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent :=
    constr:(ltac:(unshelve eexists; hnf; [ | split ]; cbv;
                  let idc := fresh "idc" in
                  intros ? idc; destruct idc;
                  try (((instantiate (1 := Datatypes.None) + idtac); reflexivity)))
            : { toRestrictedIdent : _
                                    & @ident.ToFromRestrictedIdentT _ _ baseHasNat buildEagerIdent toRestrictedIdent }).
  Ltac make_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent :=
    let res := build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent in refine res.

  Ltac make_toRestrictedIdent toRestrictedIdentAndCorrect :=
    let v := (eval hnf in (projT1 toRestrictedIdentAndCorrect)) in
    exact v.
  Ltac build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect :=
    constr:(ltac:(make_toRestrictedIdent toRestrictedIdentAndCorrect)
            : @ident.ToRestrictedIdentT _ ident baseHasNat).

  Ltac make_toFromRestrictedIdent toRestrictedIdentAndCorrect :=
    let v := (eval hnf in (projT2 toRestrictedIdentAndCorrect)) in
    exact v.
  Ltac build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect :=
    constr:(ltac:(make_toFromRestrictedIdent toRestrictedIdentAndCorrect)
            : @ident.ToFromRestrictedIdentT _ _ baseHasNat buildEagerIdent toRestrictedIdent).

  Ltac build_buildIdentAndInterpCorrect ident_interp reify_ident :=
    constr:(ltac:(let ident_interp_head := head ident_interp in
                  unshelve econstructor;
                  [ econstructor; intros;
                    lazymatch goal with
                    | [ |- ?ident (type.base base.type.unit) ] => solve [ constructor ]
                    | _ => shelve
                    end
                  | constructor ];
                  intros;
                  lazymatch goal with
                  | [ |- ?ii ?id = ?v ]
                    => let id' := (eval cbv in id) in
                       change (ii id' = v); cbv [ident_interp_head];
                       fold (@base.interp);
                       let v := match goal with |- _ = ?v => v end in
                       reify_ident v ltac:(fun idc => unify id' idc) ltac:(fun term => fail 0 "could not reify" term "as an ident") ltac:(fun _ => fail 0 "could not reify" v "as an ident")
                  end; reflexivity)
            : { buildIdent : _
                             & @ident.BuildInterpIdentCorrectT _ _ _ buildIdent ident_interp }).
  Ltac make_buildIdentAndInterpCorrect ident_interp reify_ident :=
    let res := build_buildIdentAndInterpCorrect ident_interp reify_ident in refine res.

  Ltac make_buildIdent buildIdentAndInterpCorrect :=
    let v := (eval hnf in (projT1 buildIdentAndInterpCorrect)) in
    exact v.
  Ltac build_buildIdent base_interp ident buildIdentAndInterpCorrect :=
    constr:(ltac:(make_buildIdent buildIdentAndInterpCorrect)
            : @ident.BuildIdentT _ base_interp ident).

  Ltac make_buildInterpIdentCorrect buildIdentAndInterpCorrect :=
    refine (projT2 buildIdentAndInterpCorrect).
  Ltac build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect :=
    constr:(ltac:(make_buildInterpIdentCorrect buildIdentAndInterpCorrect)
            : @ident.BuildInterpIdentCorrectT _ _ _ buildIdent ident_interp).

  Ltac build_ident_is_var_like ident ident_interp var_like_idents :=
    (eval cbv beta zeta in
        (ltac:(let t := fresh "t" in
               let idc := fresh "idc" in
               let idc' := fresh "idc'" in
               let ident_interp_head := head (@ident_interp) in
               intros t idc; pose (@ident_interp _ idc) as idc';
               destruct idc; cbn [ident_interp_head] in idc';
               let idcv := (eval cbv [idc'] in idc') in
               let idc_head := head idcv in
               lazymatch (eval hnf in var_like_idents) with
               | context[GallinaIdentList.cons idc_head]
                 => refine Datatypes.true
               | _ => refine Datatypes.false
               end)
         : forall {t} (idc : ident t), Datatypes.bool)).
  Ltac make_ident_is_var_like ident ident_interp var_like_idents :=
    let res := build_ident_is_var_like ident ident_interp var_like_idents in refine res.

  Ltac build_eqv_Reflexive_Proper ident_interp base_interp :=
    constr:(ltac:(let idc := fresh in
                  let ident_interp_head := head ident_interp in
                  let base_interp_head := head base_interp in
                  intros ? idc;
                  destruct idc; cbn [type.eqv ident_interp_head type.interp base.interp base_interp_head];
                  cbv [ident.eagerly];
                  try solve [ typeclasses eauto
                            | cbv [respectful]; repeat intro; subst; cbv; break_innermost_match; eauto using eq_refl with nocore
                            | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper || apply list_rect_arrow_Proper); repeat intro; eauto ];
                  match goal with
                  | [ |- ?G ] => idtac "WARNING: Could not automatically prove Proper lemma" G;
                                 idtac "  Please ensure this goal can be solved by typeclasses eauto"
                  end)
            : forall {t} idc, Proper type.eqv (@ident_interp t idc)).
  Ltac make_eqv_Reflexive_Proper ident_interp base_interp :=
    let res := build_eqv_Reflexive_Proper ident_interp base_interp in refine res.

  Ltac make_ident_interp_Proper eqv_Reflexive_Proper :=
    let idc := fresh "idc" in
    let idc' := fresh "idc'" in
    intros ? idc idc' ?; subst idc'; apply eqv_Reflexive_Proper.
  Ltac build_ident_interp_Proper ident_interp eqv_Reflexive_Proper :=
    constr:(ltac:(make_ident_interp_Proper eqv_Reflexive_Proper)
            : forall {t}, Proper (eq ==> type.eqv) (@ident_interp t)).

  Ltac build_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq :=
    constr:(ltac:(pose proof reflect_base_beq;
                  pose proof (_ : reflect_rel (@eq (type.type base_type)) _);
                  unshelve
                    (unshelve econstructor;
                     [ constructor; let idc := fresh "idc" in intros ? idc; destruct idc; shelve
                     | constructor;
                       (let idc := fresh "idc" in
                        intros ? idc;
                        split;
                        [ destruct idc; shelve
                        | ]) ];
                     repeat first [ match goal with
                                    | [ |- match ?x with _ => _ end _ _ -> _ ] => is_var x; destruct x
                                    | [ |- match ?x with _ => _ end _ -> _ ] => is_var x; destruct x
                                    | [ |- False -> _ ] => intro; exfalso; assumption
                                    | [ |- _ = _ -> _ ] => intro; subst
                                    | [ H : existT _ _ ?idc = existT _ _ ?idc' |- _ ]
                                      => is_var idc; destruct idc; try discriminate; []
                                    end
                                  | cbv; match goal with
                                         | [ |- ?ev = ?x ]
                                           => is_evar ev; tryif has_evar x then fail else reflexivity
                                         end ]);
                  try first [ exact Datatypes.None
                            | exact Datatypes.false
                            | cbv; intro; inversion_option; subst; solve [ reflexivity | exfalso; now apply diff_false_true ] ])
            : { invertIdent : _
                              & @invert_expr.BuildInvertIdentCorrectT _ base_interp _ invertIdent buildIdent }).
  Ltac make_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq :=
    let res := build_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq in refine res.

  Ltac make_invertIdent invertIdentAndCorrect :=
    let res := (eval cbv in (projT1 invertIdentAndCorrect)) in refine res.
  Ltac build_invertIdent base_interp ident invertIdentAndCorrect :=
    constr:(ltac:(make_invertIdent invertIdentAndCorrect)
            : @invert_expr.InvertIdentT _ base_interp ident).

  Ltac make_buildInvertIdentCorrect invertIdentAndCorrect :=
    refine (projT2 invertIdentAndCorrect).
  Ltac build_buildInvertIdentCorrect base_interp invertIdent buildIdent invertIdentAndCorrect :=
    constr:(ltac:(make_buildInvertIdentCorrect invertIdentAndCorrect)
            : @invert_expr.BuildInvertIdentCorrectT _ base_interp _ invertIdent buildIdent).

  Ltac inhabit := (constructor; fail) + (constructor; inhabit).
  Ltac build_base_default base_interp :=
    constr:(ltac:(let t := fresh "t" in
                  intro t; destruct t; hnf; inhabit)
            : @DefaultValue.type.base.DefaultT _ base_interp).
  Ltac make_base_default base_interp := let res := build_base_default base_interp in refine res.

  Ltac make_exprInfoAndExprExtraInfo base ident base_interp ident_interp base_default reflect_base_interp_eq try_make_base_transport_cps_correct toFromRestrictedIdent buildInvertIdentCorrect buildInterpIdentCorrect buildInterpEagerIdentCorrect ident_interp_Proper :=
    (exists {|
          Classes.base := base;
          Classes.ident := ident;
          Classes.base_interp := base_interp;
          Classes.ident_interp := ident_interp
        |});
    econstructor;
    first [ exact base_default
          | exact (@reflect_base_interp_eq)
          | exact try_make_base_transport_cps_correct
          | exact toFromRestrictedIdent
          | exact buildInvertIdentCorrect
          | exact (@buildInterpIdentCorrect)
          | exact (@buildInterpEagerIdentCorrect)
          | exact (@ident_interp_Proper) ].
  Ltac build_exprInfoAndExprExtraInfo base ident base_interp ident_interp base_default reflect_base_interp_eq try_make_base_transport_cps_correct toFromRestrictedIdent buildInvertIdentCorrect buildInterpIdentCorrect buildInterpEagerIdentCorrect ident_interp_Proper :=
    let res := make_exprInfoAndExprExtraInfo base ident base_interp ident_interp base_default reflect_base_interp_eq try_make_base_transport_cps_correct toFromRestrictedIdent buildInvertIdentCorrect buildInterpIdentCorrect buildInterpEagerIdentCorrect ident_interp_Proper in refine res.

  Ltac base_type_reified_hint base_type reify_type :=
    lazymatch goal with
    | [ |- @type.reified_of base_type _ ?T ?e ]
      => solve [ let rT := reify_type T in unify e rT; reflexivity | idtac "ERROR: Failed to reify" T ]
    end.

  Ltac expr_reified_hint base_type ident reify_base_type reify_ident :=
    lazymatch goal with
    | [ |- @expr.Reified_of _ ident _ _ ?t ?v ?e ]
      => solve [ let rv := expr.Reify constr:(base_type) ident ltac:(reify_base_type) ltac:(reify_ident) v in unify e rv; reflexivity | idtac "ERROR: Failed to reify" v "(of type" t "); try setting Reify.debug_level to see output" ]
    end.


  Definition var_like_idents : GallinaIdentList.t
    := [@ident.literal
        ; @Datatypes.nil
        ; @Datatypes.cons
        ; @Datatypes.pair
        ; @Datatypes.fst
        ; @Datatypes.snd
        ; Z.opp
        ; ident.cast
        ; ident.cast2
        ; Z.combine_at_bitwidth]%gi_list.

  Definition base_type_list : TypeList.t
    := [BinInt.Z; Datatypes.bool; Datatypes.nat; ZRange.zrange]%type_list.

  Inductive base := Z | bool | nat | zrange. (* Not Variant because COQBUG(https://github.com/coq/coq/issues/7738) *)

  Definition index_of_base : base -> Datatypes.nat
    := ltac:(make_index_of_base base).

  Local Notation base_type := (@base.type base).

  Definition eta_base_cps_gen := ltac:(make_eta_base_cps_gen base).

  Definition eta_base_cps : forall {P : base -> Type} (f : forall t, P t), forall t, P t
    := ltac:(make_eta_base_cps eta_base_cps_gen).

  Definition base_interp := ltac:(make_base_interp (@eta_base_cps) base_type_list index_of_base).

  Local Notation base_type_interp := (base.interp base_interp).

  Ltac reify_base ty :=
    let __ := Reify.debug_enter_reify_base_type ty in
    lazymatch eval cbv beta in ty with
    | Datatypes.nat => nat
    | Datatypes.bool => bool
    | BinInt.Z => Z
    | ZRange.zrange => zrange
    | base_interp ?T => T
    | @base.interp base base_interp (@base.type.type_base base ?T) => T
    | @type.interp base_type (@base.interp base base_interp) (@Compilers.type.base base_type (@base.type.type_base base ?T)) => T
    | _ => constr_fail_with ltac:(fun _ => fail 1 "Unrecognized type:" ty)
    end.
  Ltac reify_base_type ty := Language.Compilers.base.reify base reify_base ty.
  Ltac reify_type ty := Language.Compilers.type.reify reify_base_type constr:(base_type) ty.

  Bind Scope etype_scope with base.

  Section ident.
    Import Language.Compilers.ident.
    Local Notation type := (type base_type).
    Local Notation ttype := type.

    Section with_base.
      Let type_base (x : Compilers.base) : base_type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : Compilers.base >-> base.type.
      Section with_scope.
        Import base.type.
        Local Notation nat := Compilers.nat.
        Notation type := ttype.
        (* N.B. [ident] must have essentially flat structure for the
           python script constructing [pattern.ident] to work *)
        Inductive ident : type -> Type :=
        | ident_Literal {t:Compilers.base} (v : base_interp t) : ident t
        | ident_Nat_succ : ident (nat -> nat)
        | ident_Nat_pred : ident (nat -> nat)
        | ident_Nat_max : ident (nat -> nat -> nat)
        | ident_Nat_mul : ident (nat -> nat -> nat)
        | ident_Nat_add : ident (nat -> nat -> nat)
        | ident_Nat_sub : ident (nat -> nat -> nat)
        | ident_Nat_eqb : ident (nat -> nat -> bool)
        | ident_nil {t} : ident (list t)
        | ident_cons {t:base_type} : ident (t -> list t -> list t)
        | ident_tt : ident unit
        | ident_pair {A B:base_type} : ident (A -> B -> A * B)
        | ident_fst {A B} : ident (A * B -> A)
        | ident_snd {A B} : ident (A * B -> B)
        | ident_prod_rect {A B T:base_type} : ident ((A -> B -> T) -> A * B -> T)
        | ident_bool_rect {T:base_type} : ident ((unit -> T) -> (unit -> T) -> bool -> T)
        | ident_nat_rect {P:base_type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | ident_nat_rect_arrow {P Q:base_type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | ident_eager_nat_rect {P:base_type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | ident_eager_nat_rect_arrow {P Q:base_type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | ident_list_rect {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | ident_list_rect_arrow {A P Q:base_type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | ident_eager_list_rect {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | ident_eager_list_rect_arrow {A P Q:base_type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | ident_list_case {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P) -> list A -> P)
        | ident_List_length {T} : ident (list T -> nat)
        | ident_List_seq : ident (nat -> nat -> list nat)
        | ident_List_firstn {A:base_type} : ident (nat -> list A -> list A)
        | ident_List_skipn {A:base_type} : ident (nat -> list A -> list A)
        | ident_List_repeat {A:base_type} : ident (A -> nat -> list A)
        | ident_List_combine {A B} : ident (list A -> list B -> list (A * B))
        | ident_List_map {A B:base_type} : ident ((A -> B) -> list A -> list B)
        | ident_List_app {A} : ident (list A -> list A -> list A)
        | ident_List_rev {A} : ident (list A -> list A)
        | ident_List_flat_map {A B:base_type} : ident ((A -> (list B)) -> list A -> (list B))
        | ident_List_partition {A:base_type} : ident ((A -> bool) -> list A -> (list A * list A))
        | ident_List_fold_right {A B:base_type} : ident ((B -> A -> A) -> A -> list B -> A)
        | ident_List_update_nth {T:base_type} : ident (nat -> (T -> T) -> list T -> list T)
        | ident_List_nth_default {T:base_type} : ident (T -> list T -> nat -> T)
        | ident_eager_List_nth_default {T:base_type} : ident (T -> list T -> nat -> T)
        | ident_Z_add : ident (Z -> Z -> Z)
        | ident_Z_mul : ident (Z -> Z -> Z)
        | ident_Z_pow : ident (Z -> Z -> Z)
        | ident_Z_sub : ident (Z -> Z -> Z)
        | ident_Z_opp : ident (Z -> Z)
        | ident_Z_div : ident (Z -> Z -> Z)
        | ident_Z_modulo : ident (Z -> Z -> Z)
        | ident_Z_log2 : ident (Z -> Z)
        | ident_Z_log2_up : ident (Z -> Z)
        | ident_Z_eqb : ident (Z -> Z -> bool)
        | ident_Z_leb : ident (Z -> Z -> bool)
        | ident_Z_ltb : ident (Z -> Z -> bool)
        | ident_Z_geb : ident (Z -> Z -> bool)
        | ident_Z_gtb : ident (Z -> Z -> bool)
        | ident_Z_of_nat : ident (nat -> Z)
        | ident_Z_to_nat : ident (Z -> nat)
        | ident_Z_shiftr : ident (Z -> Z -> Z)
        | ident_Z_shiftl : ident (Z -> Z -> Z)
        | ident_Z_land : ident (Z -> Z -> Z)
        | ident_Z_lor : ident (Z -> Z -> Z)
        | ident_Z_min : ident (Z -> Z -> Z)
        | ident_Z_max : ident (Z -> Z -> Z)
        | ident_Z_bneg : ident (Z -> Z)
        | ident_Z_lnot_modulo : ident (Z -> Z -> Z)
        | ident_Z_truncating_shiftl : ident (Z -> Z -> Z -> Z)
        | ident_Z_mul_split : ident (Z -> Z -> Z -> Z * Z)
        | ident_Z_add_get_carry : ident (Z -> Z -> Z -> (Z * Z))
        | ident_Z_add_with_carry : ident (Z -> Z -> Z -> Z)
        | ident_Z_add_with_get_carry : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | ident_Z_sub_get_borrow : ident (Z -> Z -> Z -> (Z * Z))
        | ident_Z_sub_with_get_borrow : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | ident_Z_zselect : ident (Z -> Z -> Z -> Z)
        | ident_Z_add_modulo : ident (Z -> Z -> Z -> Z)
        | ident_Z_rshi : ident (Z -> Z -> Z -> Z -> Z)
        | ident_Z_cc_m : ident (Z -> Z -> Z)
        | ident_Z_combine_at_bitwidth : ident (Z -> Z -> Z -> Z)
        | ident_Z_cast : ident (zrange -> Z -> Z)
        | ident_Z_cast2 : ident ((zrange * zrange) -> (Z * Z) -> (Z * Z))
        | ident_Some {A:base_type} : ident (A -> option A)
        | ident_None {A:base_type} : ident (option A)
        | ident_option_rect {A P : base_type} : ident ((A -> P) -> (unit -> P) -> option A -> P)
        | ident_Build_zrange : ident (Z -> Z -> zrange)
        | ident_zrange_rect {P:base_type} : ident ((Z -> Z -> P) -> zrange -> P)
        | ident_fancy_add : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | ident_fancy_addc : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | ident_fancy_sub : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | ident_fancy_subb : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | ident_fancy_mulll : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mullh : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mulhl : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mulhh : ident (Z * (Z * Z) -> Z)
        | ident_fancy_rshi : ident ((Z * Z) * (Z * Z) -> Z)
        | ident_fancy_selc : ident (Z * Z * Z -> Z)
        | ident_fancy_selm : ident (Z * (Z * Z * Z) -> Z)
        | ident_fancy_sell : ident (Z * Z * Z -> Z)
        | ident_fancy_addm : ident (Z * Z * Z -> Z)
        .
      End with_scope.
    End with_base.
  End ident.

  Definition ident_interp {t} (idc : ident t) : type.interp base_type_interp t
    := match idc in ident t return type.interp base_type_interp t with
       | ident_Literal _ v => ident.literal v
       | ident_Nat_succ => Nat.succ
       | ident_Nat_pred => Nat.pred
       | ident_Nat_max => Nat.max
       | ident_Nat_mul => Nat.mul
       | ident_Nat_add => Nat.add
       | ident_Nat_sub => Nat.sub
       | ident_Nat_eqb => Nat.eqb
       | ident_nil t => Datatypes.nil
       | ident_cons t => Datatypes.cons
       | ident_tt => Datatypes.tt
       | ident_pair A B => Datatypes.pair
       | ident_fst A B => Datatypes.fst
       | ident_snd A B => Datatypes.snd
       | ident_prod_rect A B T => @prod_rect_nodep _ _ _
       | ident_bool_rect T => @ident.Thunked.bool_rect _
       | ident_nat_rect P => @ident.Thunked.nat_rect _
       | ident_eager_nat_rect P => ident.eagerly (@ident.Thunked.nat_rect) _
       | ident_nat_rect_arrow P Q => @nat_rect_nodep _
       | ident_eager_nat_rect_arrow P Q => ident.eagerly (@nat_rect_nodep) _
       | ident_list_rect A P => @ident.Thunked.list_rect _ _
       | ident_eager_list_rect A P => ident.eagerly (@ident.Thunked.list_rect) _ _
       | ident_list_rect_arrow A P Q => @list_rect_nodep _ _
       | ident_eager_list_rect_arrow A P Q => ident.eagerly (@list_rect_nodep) _ _
       | ident_list_case A P => @ident.Thunked.list_case _ _
       | ident_List_length T => @List.length _
       | ident_List_seq => List.seq
       | ident_List_firstn A => @List.firstn _
       | ident_List_skipn A => @List.skipn _
       | ident_List_repeat A => @repeat _
       | ident_List_combine A B => @List.combine _ _
       | ident_List_map A B => @List.map _ _
       | ident_List_app A => @List.app _
       | ident_List_rev A => @List.rev _
       | ident_List_flat_map A B => @List.flat_map _ _
       | ident_List_partition A => @List.partition _
       | ident_List_fold_right A B => @List.fold_right _ _
       | ident_List_update_nth T => update_nth
       | ident_List_nth_default T => @nth_default _
       | ident_eager_List_nth_default T => @nth_default _
       | ident_Z_add => Z.add
       | ident_Z_mul => Z.mul
       | ident_Z_pow => Z.pow
       | ident_Z_sub => Z.sub
       | ident_Z_opp => Z.opp
       | ident_Z_div => Z.div
       | ident_Z_modulo => Z.modulo
       | ident_Z_eqb => Z.eqb
       | ident_Z_leb => Z.leb
       | ident_Z_ltb => Z.ltb
       | ident_Z_geb => Z.geb
       | ident_Z_gtb => Z.gtb
       | ident_Z_log2 => Z.log2
       | ident_Z_log2_up => Z.log2_up
       | ident_Z_of_nat => Z.of_nat
       | ident_Z_to_nat => Z.to_nat
       | ident_Z_shiftr => Z.shiftr
       | ident_Z_shiftl => Z.shiftl
       | ident_Z_land => Z.land
       | ident_Z_lor => Z.lor
       | ident_Z_min => Z.min
       | ident_Z_max => Z.max
       | ident_Z_mul_split => Z.mul_split
       | ident_Z_add_get_carry => Z.add_get_carry_full
       | ident_Z_add_with_carry => Z.add_with_carry
       | ident_Z_add_with_get_carry => Z.add_with_get_carry_full
       | ident_Z_sub_get_borrow => Z.sub_get_borrow_full
       | ident_Z_sub_with_get_borrow => Z.sub_with_get_borrow_full
       | ident_Z_zselect => Z.zselect
       | ident_Z_add_modulo => Z.add_modulo
       | ident_Z_truncating_shiftl => Z.truncating_shiftl
       | ident_Z_bneg => Z.bneg
       | ident_Z_lnot_modulo => Z.lnot_modulo
       | ident_Z_rshi => Z.rshi
       | ident_Z_cc_m => Z.cc_m
       | ident_Z_combine_at_bitwidth => Z.combine_at_bitwidth
       | ident_Z_cast => ident.cast
       | ident_Z_cast2 => ident.cast2
       | ident_Some A => @Datatypes.Some _
       | ident_None A => @Datatypes.None _
       | ident_option_rect A P => @ident.Thunked.option_rect _ _
       | ident_Build_zrange => ZRange.Build_zrange
       | ident_zrange_rect A => @ZRange.zrange_rect_nodep _
       | ident_fancy_add => ident.fancy.add
       | ident_fancy_addc => ident.fancy.addc
       | ident_fancy_sub => ident.fancy.sub
       | ident_fancy_subb => ident.fancy.subb
       | ident_fancy_mulll => ident.fancy.mulll
       | ident_fancy_mullh => ident.fancy.mullh
       | ident_fancy_mulhl => ident.fancy.mulhl
       | ident_fancy_mulhh => ident.fancy.mulhh
       | ident_fancy_rshi => ident.fancy.rshi
       | ident_fancy_selc => ident.fancy.selc
       | ident_fancy_selm => ident.fancy.selm
       | ident_fancy_sell => ident.fancy.sell
       | ident_fancy_addm => ident.fancy.addm
       end.

  (** TODO: MOVE ME? *)
  Ltac require_primitive_const_extra term := fail 0 "Not a known const:" term.
  Ltac require_primitive_const term :=
    lazymatch term with
    | Datatypes.S ?n => require_primitive_const n
    | Datatypes.O => idtac
    | Datatypes.true => idtac
    | Datatypes.false => idtac
    (*| Datatypes.tt => idtac*)
    | Z0 => idtac
    | Zpos ?p => require_primitive_const p
    | Zneg ?p => require_primitive_const p
    | xI ?p => require_primitive_const p
    | xO ?p => require_primitive_const p
    | xH => idtac
    | ZRange.Build_zrange ?x ?y
      => require_primitive_const x; require_primitive_const y
    | ident.literal ?x => idtac
    | ?term => require_primitive_const_extra term
    end.
  Ltac is_primitive_const term :=
    match constr:(Set) with
    | _ => let check := match goal with
                        | _ => require_primitive_const term
                        end in
           true
    | _ => false
    end.

  Ltac reify_ident
       term
       then_tac
       reify_rec
       else_tac :=
    (*let __ := match goal with _ => idtac "attempting to reify_op" term end in*)
    let term_is_primitive_const := is_primitive_const term in
    lazymatch term_is_primitive_const with
    | true
      =>
      let T := type of term in
      let rT := reify_base T in
      then_tac (@ident_Literal rT term)
    | false
      =>
      lazymatch term with
      | Nat.succ => then_tac ident_Nat_succ
      | Nat.add => then_tac ident_Nat_add
      | Nat.sub => then_tac ident_Nat_sub
      | Nat.eqb => then_tac ident_Nat_eqb
      | Nat.mul => then_tac ident_Nat_mul
      | Nat.max => then_tac ident_Nat_max
      | Nat.pred => then_tac ident_Nat_pred
      | Datatypes.S => then_tac ident_Nat_succ
      | Datatypes.tt => then_tac ident_tt
      | @Datatypes.nil ?T
        => let rT := reify_base_type T in
           then_tac (@ident_nil rT)
      | @Datatypes.cons ?T
        => let rT := reify_base_type T in
           then_tac (@ident_cons rT)
      | @Datatypes.fst ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_fst rA rB)
      | @Datatypes.snd ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_snd rA rB)
      | @Datatypes.pair ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_pair rA rB)
      | @Datatypes.bool_rect ?T0 ?Ptrue ?Pfalse
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@bool_rect_nodep T Ptrue Pfalse)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.bool_rect T' Ptrue Pfalse)
           end
      | @bool_rect_nodep ?T ?Ptrue ?Pfalse
        => reify_rec (@ident.Thunked.bool_rect T (fun _ : Datatypes.unit => Ptrue) (fun _ : Datatypes.unit => Pfalse))
      | @ident.Thunked.bool_rect ?T
        => let rT := reify_base_type T in
           then_tac (@ident_bool_rect rT)
      | @Datatypes.option_rect ?A ?T0 ?PSome ?PNone
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@option_rect_nodep A T PSome PNone)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.option_rect A T' PSome PNone)
           end
      | @option_rect_nodep ?A ?T ?PSome ?PNone
        => reify_rec (@ident.Thunked.option_rect A T PSome (fun _ : Datatypes.unit => PNone))
      | @ident.Thunked.option_rect ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_option_rect rA rT)
      | @Datatypes.prod_rect ?A ?B ?T0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@prod_rect_nodep A B T)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.prod_rect A B T')
           end
      | @prod_rect_nodep ?A ?B ?T
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           let rT := reify_base_type T in
           then_tac (@ident_prod_rect rA rB rT)
      | @ZRange.zrange_rect ?T0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@ZRange.zrange_rect_nodep T)
           | T0 => else_tac ()
           | ?T' => reify_rec (@ZRange.zrange_rect T')
           end
      | @ZRange.zrange_rect_nodep ?T
        => let rT := reify_base_type T in
           then_tac (@ident_zrange_rect rT)
      | @Datatypes.nat_rect ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@nat_rect_nodep T P0)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.nat_rect T' P0)
           end
      | @nat_rect_nodep ?T ?P0
        => lazymatch T with
           | ?P -> ?Q => else_tac ()
           | _ => reify_rec (@ident.Thunked.nat_rect T (fun _ : Datatypes.unit => P0))
           end
      | @nat_rect_nodep ?T
        => lazymatch T with
           | ?P -> ?Q
             => let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_nat_rect_arrow rP rQ)
           | _ => else_tac ()
           end
      | @ident.Thunked.nat_rect ?T
        => let rT := reify_base_type T in
           then_tac (@ident_nat_rect rT)
      | ident.eagerly (@Datatypes.nat_rect) ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (ident.eagerly (@nat_rect_nodep) T P0)
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.nat_rect) T' P0)
           end
      | ident.eagerly (@nat_rect_nodep) ?T ?P0
        => lazymatch T with
           | ?P -> ?Q => else_tac ()
           | _ => reify_rec (ident.eagerly (@ident.Thunked.nat_rect) T (fun _ : Datatypes.unit => P0))
           end
      | ident.eagerly (@nat_rect_nodep) ?T
        => lazymatch T with
           | ?P -> ?Q
             => let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_eager_nat_rect_arrow rP rQ)
           | _ => else_tac ()
           end
      | ident.eagerly (@ident.Thunked.nat_rect) ?T
        => let rT := reify_base_type T in
           then_tac (@ident_eager_nat_rect rT)
      | @Datatypes.list_rect ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@list_rect_nodep A T Pnil)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.list_rect A T' Pnil)
           end
      | @list_rect_nodep ?A ?T ?Pnil
        => lazymatch T with
           | _ -> _ => else_tac ()
           | _ => reify_rec (@ident.Thunked.list_rect A T (fun _ : Datatypes.unit => Pnil))
           end
      | @list_rect_nodep ?A ?T
        => lazymatch T with
           | ?P -> ?Q
             => let rA := reify_base_type A in
                let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_list_rect_arrow rA rP rQ)
           | _ => else_tac ()
           end
      | @ident.Thunked.list_rect ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_list_rect rA rT)
      | ident.eagerly (@Datatypes.list_rect) ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (ident.eagerly (@list_rect_nodep) A T Pnil)
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.list_rect) A T' Pnil)
           end
      | ident.eagerly (@list_rect_nodep) ?A ?T ?Pnil
        => lazymatch T with
           | _ -> _ => else_tac ()
           | _ => reify_rec (ident.eagerly (@ident.Thunked.list_rect) A T (fun _ : Datatypes.unit => Pnil))
           end
      | ident.eagerly (@list_rect_nodep) ?A ?T
        => lazymatch T with
           | ?P -> ?Q
             => let rA := reify_base_type A in
                let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_eager_list_rect_arrow rA rP rQ)
           | _ => else_tac ()
           end
      | ident.eagerly (@ident.Thunked.list_rect) ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_eager_list_rect rA rT)
      | @ListUtil.list_case ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@ListUtil.list_case_nodep A T Pnil)
           | T0 => else_tac ()
           | ?T' => reify_rec (@ListUtil.list_case A T' Pnil)
           end
      | @ListUtil.list_case_nodep ?A ?T ?Pnil
        => lazymatch T with
           | _ -> _ => else_tac ()
           | _ => reify_rec (@ident.Thunked.list_case A T (fun _ : Datatypes.unit => Pnil))
           end
      | @ident.Thunked.list_case ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_list_case rA rT)
      | @List.length ?A =>
        let rA := reify_base_type A in
        then_tac (@ident_List_length rA)
      | List.seq => then_tac ident_List_seq
      | @List.firstn ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_firstn rA)
      | @List.skipn ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_skipn rA)
      | @repeat ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_repeat rA)
      | @List.combine ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_combine rA rB)
      | @List.map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_map rA rB)
      | @List.flat_map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_flat_map rA rB)
      | @List.partition ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_partition rA)
      | @List.app ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_app rA)
      | @List.map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_map rA rB)
      | @List.rev ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_rev rA)
      | @List.fold_right ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_fold_right rA rB)
      | @update_nth ?T
        => let rT := reify_base_type T in
           then_tac (@ident_List_update_nth rT)
      | @List.nth_default ?T
        => let rT := reify_base_type T in
           then_tac (@ident_List_nth_default rT)
      | ident.eagerly (@List.nth_default) ?T
        => let rT := reify_base_type T in
           then_tac (@ident_eager_List_nth_default rT)
      | Z.add => then_tac ident_Z_add
      | Z.mul => then_tac ident_Z_mul
      | Z.pow => then_tac ident_Z_pow
      | Z.sub => then_tac ident_Z_sub
      | Z.opp => then_tac ident_Z_opp
      | Z.div => then_tac ident_Z_div
      | Z.modulo => then_tac ident_Z_modulo
      | Z.eqb => then_tac ident_Z_eqb
      | Z.leb => then_tac ident_Z_leb
      | Z.ltb => then_tac ident_Z_ltb
      | Z.geb => then_tac ident_Z_geb
      | Z.gtb => then_tac ident_Z_gtb
      | Z.log2 => then_tac ident_Z_log2
      | Z.log2_up => then_tac ident_Z_log2_up
      | Z.shiftl => then_tac ident_Z_shiftl
      | Z.shiftr => then_tac ident_Z_shiftr
      | Z.land => then_tac ident_Z_land
      | Z.lor => then_tac ident_Z_lor
      | Z.min => then_tac ident_Z_min
      | Z.max => then_tac ident_Z_max
      | Z.bneg => then_tac ident_Z_bneg
      | Z.lnot_modulo => then_tac ident_Z_lnot_modulo
      | Z.truncating_shiftl => then_tac ident_Z_truncating_shiftl
      | Z.of_nat => then_tac ident_Z_of_nat
      | Z.to_nat => then_tac ident_Z_to_nat
      | Z.mul_split => then_tac ident_Z_mul_split
      | Z.add_get_carry_full => then_tac ident_Z_add_get_carry
      | Z.add_with_carry => then_tac ident_Z_add_with_carry
      | Z.add_with_get_carry_full => then_tac ident_Z_add_with_get_carry
      | Z.sub_get_borrow_full => then_tac ident_Z_sub_get_borrow
      | Z.sub_with_get_borrow_full => then_tac ident_Z_sub_with_get_borrow
      | Z.zselect => then_tac ident_Z_zselect
      | Z.add_modulo => then_tac ident_Z_add_modulo
      | Z.rshi => then_tac ident_Z_rshi
      | Z.cc_m => then_tac ident_Z_cc_m
      | Z.combine_at_bitwidth => then_tac ident_Z_combine_at_bitwidth
      | Datatypes.tt => then_tac ident_tt
      | ident.cast => then_tac ident_Z_cast
      | ident.cast2 => then_tac ident_Z_cast2
      | @Some ?A
        => let rA := reify_base_type A in
           then_tac (@ident_Some rA)
      | @None ?A
        => let rA := reify_base_type A in
           then_tac (@ident_None rA)
      | ZRange.Build_zrange => then_tac ident_Build_zrange
      | ident.fancy.add => then_tac ident_fancy_add
      | ident.fancy.addc => then_tac ident_fancy_addc
      | ident.fancy.sub => then_tac ident_fancy_sub
      | ident.fancy.subb => then_tac ident_fancy_subb
      | ident.fancy.mulll => then_tac ident_fancy_mulll
      | ident.fancy.mullh => then_tac ident_fancy_mullh
      | ident.fancy.mulhl => then_tac ident_fancy_mulhl
      | ident.fancy.mulhh => then_tac ident_fancy_mulhh
      | ident.fancy.rshi => then_tac ident_fancy_rshi
      | ident.fancy.selc => then_tac ident_fancy_selc
      | ident.fancy.selm => then_tac ident_fancy_selm
      | ident.fancy.sell => then_tac ident_fancy_sell
      | ident.fancy.addm => then_tac ident_fancy_addm
      | ident.eagerly (?f ?x) => reify_rec (ident.eagerly f x)
      | @ident_interp _ ?idc => then_tac idc
      | _ => else_tac ()
      end
    end.

  Definition base_eq_dec := ltac:(make_base_eq_dec base).

  Definition base_beq_and_reflect := ltac:(make_base_beq_and_reflect base).
  Definition base_beq := ltac:(make_base_beq base_beq_and_reflect).
  Definition reflect_base_beq : reflect_rel (@eq base) base_beq := ltac:(make_reflect_base_beq base_beq_and_reflect).

  Definition baseHasNatAndCorrect := ltac:(make_baseHasNatAndCorrect base_interp).
  Definition baseHasNat : base.type.BaseTypeHasNatT base := ltac:(make_baseHasNat baseHasNatAndCorrect).
  Definition baseHasNatCorrect : base.BaseHasNatCorrectT base_interp := ltac:(make_baseHasNatCorrect baseHasNatAndCorrect).

  Definition base_interp_beq : forall {t}, base_interp t -> base_interp t -> Datatypes.bool
    := ltac:(make_base_interp_beq base_interp).

  Definition reflect_base_interp_eq : forall {t}, reflect_rel (@eq (base_interp t)) (@base_interp_beq t)
    := ltac:(make_reflect_base_interp_eq base_interp (@base_interp_beq)).

  Definition try_make_base_transport_cps : @type.try_make_transport_cpsT base
    := ltac:(make_try_make_base_transport_cps base_eq_dec (@eta_base_cps)).

  Definition try_make_base_transport_cps_correct : @type.try_make_transport_cps_correctT base base_beq try_make_base_transport_cps reflect_base_beq
    := ltac:(make_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq).

  Definition buildEagerIdentAndInterpCorrect := ltac:(make_buildEagerIdentAndInterpCorrect (@ident_interp) baseHasNat baseHasNatCorrect ltac:(reify_ident)).

  Definition buildEagerIdent : ident.BuildEagerIdentT ident
    := ltac:(make_buildEagerIdent buildEagerIdentAndInterpCorrect).
  Definition buildInterpEagerIdentCorrect : @ident.BuildInterpEagerIdentCorrectT _ _ _ (@ident_interp) _ buildEagerIdent baseHasNatCorrect
    := ltac:(make_buildInterpEagerIdentCorrect buildEagerIdentAndInterpCorrect).

  Definition toRestrictedIdentAndCorrect := ltac:(make_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent).
  Definition toRestrictedIdent : @ident.ToRestrictedIdentT _ ident baseHasNat
    := ltac:(make_toRestrictedIdent toRestrictedIdentAndCorrect).
  Definition toFromRestrictedIdent : @ident.ToFromRestrictedIdentT _ ident baseHasNat buildEagerIdent toRestrictedIdent
    := ltac:(make_toFromRestrictedIdent toRestrictedIdentAndCorrect).


  Definition buildIdentAndInterpCorrect
    := ltac:(make_buildIdentAndInterpCorrect (@ident_interp) ltac:(reify_ident)).
  Definition buildIdent : @ident.BuildIdentT base base_interp ident
    := ltac:(make_buildIdent buildIdentAndInterpCorrect).
  Definition buildInterpIdentCorrect
    : @ident.BuildInterpIdentCorrectT base base_interp ident buildIdent (@ident_interp)
    := ltac:(make_buildInterpIdentCorrect buildIdentAndInterpCorrect).

  Definition ident_is_var_like : forall {t} (idc : ident t), Datatypes.bool
    := ltac:(make_ident_is_var_like ident (@ident_interp) var_like_idents).

  Definition eqv_Reflexive_Proper : forall {t} (idc : ident t), Proper type.eqv (@ident_interp t idc)
    := ltac:(make_eqv_Reflexive_Proper (@ident_interp) base_interp).

  Definition ident_interp_Proper : forall {t}, Proper (eq ==> type.eqv) (@ident_interp t)
    := ltac:(make_ident_interp_Proper (@eqv_Reflexive_Proper)).

  Definition invertIdentAndCorrect := ltac:(make_invertIdentAndCorrect (@base_type) base_interp buildIdent reflect_base_beq).
  Definition invertIdent : @invert_expr.InvertIdentT base base_interp ident
    := ltac:(make_invertIdent invertIdentAndCorrect).
  Definition buildInvertIdentCorrect : @invert_expr.BuildInvertIdentCorrectT base base_interp ident invertIdent buildIdent
    := ltac:(make_buildInvertIdentCorrect invertIdentAndCorrect).

  Definition base_default : @DefaultValue.type.base.DefaultT base base_interp
    := ltac:(make_base_default base_interp).

  Definition exprInfoAndExprExtraInfo : GoalType.package
    := ltac:(make_exprInfoAndExprExtraInfo base ident base_interp (@ident_interp) base_default (@reflect_base_interp_eq) try_make_base_transport_cps_correct toFromRestrictedIdent buildInvertIdentCorrect (@buildInterpIdentCorrect) buildInterpEagerIdentCorrect (@ident_interp_Proper)).

  Global Strategy -1000 [base_interp ident_interp].

  Global Hint Extern 1 => base_type_reified_hint (@base_type) ltac:(reify_type) : typeclass_instances.
  Global Hint Extern 1 => expr_reified_hint (@base_type) ident ltac:(reify_base_type) ltac:(reify_ident) : typeclass_instances.
End Compilers.
