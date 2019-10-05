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
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.CacheTerm.
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

  Ltac find_evar_tail x :=
    lazymatch x with
    | Datatypes.cons _ ?x => find_evar_tail x
    | ?ev => let __ := match goal with _ => is_evar ev end in
             ev
    end.
  Ltac build_all_gen T mk P :=
    let res := open_constr:(_ : list T) in
    let fill_next v :=
        let next := find_evar_tail res in
        let __ := open_constr:(eq_refl : next = v) in
        constr:(I) in
    let __ := open_constr:(
                ltac:(intros;
                      let v' := fresh "v'" in
                      lazymatch goal with
                      | [ v : _ |- _ ] => pose v as v'; destruct v
                      end;
                      let v := (eval cbv [v'] in v') in
                      let h := head v in
                      let v' := mk h in
                      let __ := fill_next open_constr:(Datatypes.cons v' _) in
                      constructor)
                : P) in
    let __ := fill_next uconstr:(Datatypes.nil) in
    res.
  Ltac build_all_base base := build_all_gen base ltac:(fun x => x) (base -> True).
  Ltac make_all_base base :=
    let res := build_all_base base in refine res.


  Ltac build_all_base_and_interp all_base base_interp :=
    let all_base := (eval cbv in all_base) in
    let base_interp_head := head base_interp in
    (eval cbv [List.map base_interp_head] in
        (List.map (fun v => (v, base_interp v : Type)) all_base)).
  Ltac make_all_base_and_interp all_base base_interp :=
    let res := build_all_base_and_interp all_base base_interp in refine res.

  Ltac reify_base_via_list base base_interp all_base_and_interp :=
    let all_base_and_interp := (eval hnf in all_base_and_interp) in
    let all_base_and_interp := (eval cbv beta in all_base_and_interp) in
    fun ty
    => let ty := (eval cbv beta in ty) in
       let __ := Reify.debug_enter_reify_base_type ty in
       lazymatch all_base_and_interp with
       | context[Datatypes.cons (?rty, ty)] => rty
       | _
         => lazymatch ty with
            | base_interp ?T => T
            | @base.interp base base_interp (@base.type.type_base base ?T) => T
            | @type.interp (base.type base) (@base.interp base base_interp) (@Compilers.type.base (base.type base) (@base.type.type_base base ?T)) => T
            | _ => constr_fail_with ltac:(fun _ => fail 1 "Unrecognized type:" ty)
            end
       end.

  Ltac reify_base_type_via_list base base_interp all_base_and_interp :=
    Language.Compilers.base.reify base ltac:(reify_base_via_list base base_interp all_base_and_interp).
  Ltac reify_type_via_list base base_interp all_base_and_interp :=
    Language.Compilers.type.reify ltac:(reify_base_type_via_list base base_interp all_base_and_interp) constr:(base.type base).

  Ltac ident_type_of_interped_type reify_type base base_interp ident ty :=
    let recur := ident_type_of_interped_type reify_type base base_interp ident in
    let is_sort := lazymatch ty with
                   | forall T : Type, _ => true
                   | forall T : Set , _ => true
                   | forall T : Prop, _ => true
                   | _ => false
                   end in
    lazymatch is_sort with
    | true
      => lazymatch ty with
         | forall x : ?T, ?F
           => let F' := fresh in
              let t := fresh "t" in
              let rT := constr:(base.type base) in
              let interp_rT := constr:(base.interp base_interp) in
              constr:(forall t : rT,
                         match interp_rT t return _ with
                         | x
                           => match F return _ with
                              | F'
                                => ltac:(let Fv := (eval cbv [x F'] in F') in
                                         clear x F';
                                         let __ := type of Fv in (* force recomputation of universes *)
                                         let res := recur Fv in
                                         exact res)
                              end
                         end)
         end
    | false
      => let rT := reify_type ty in
         constr:(ident rT)
    end.

  Ltac ident_type_of_interped_type_via_list base base_interp all_base_and_interp :=
    let reify_type := ltac:(reify_type_via_list base base_interp all_base_and_interp) in
    let base_interp_head := head base_interp in
    fun is_literal ty ident
    => let res
           := lazymatch is_literal with
              | true
                => constr:(forall t : base, base_interp t -> ident (type.base (base.type.type_base t)))
              | false
                => ident_type_of_interped_type reify_type base base_interp ident ty
              end in
       (eval cbv [base_interp_head] in res).

  Ltac print_ident_of_named base base_interp all_base_and_interp :=
    let get_type := ident_type_of_interped_type_via_list base base_interp all_base_and_interp in
    fun idc
    => let v := lazymatch idc with
                | with_name _ ?v => v
                | without_name ?v => v
                end in
       let is_literal := lazymatch v with
                         | @ident.literal => true
                         | _ => false
                         end in
       let ty := type of v in
       let ty := (eval cbv beta in ty) in
       let ident := fresh "ident" in
       let rty := constr:(fun ident : _ -> Type
                          => ltac:(let res := get_type is_literal ty ident in exact res)) in
       let print_rty name :=
           lazymatch rty with
           | fun ident : ?T => ?F
             => let F' := fresh in
                let __
                    := constr:(fun ident : T
                               => match F return _ with
                                  | F' => ltac:(let F' := (eval cbv [F'] in F') in
                                                idtac "|" name ":" F';
                                                exact I)
                                  end) in
                idtac
           end in
       lazymatch idc with
       | with_name name _ => print_rty name
       | _ => let name := fresh "ident_" v in
              print_rty name
       end.

  Ltac print_ident_via base base_interp all_base_and_interp all_ident_named_interped :=
    let all_ident_named_interped := (eval hnf in all_ident_named_interped) in
    let do_print := print_ident_of_named base base_interp all_base_and_interp in
    let type := constr:(type.type (base.type base)) in
    let type_to_Type := constr:(type -> Type) in
    let rec iter ls
        := lazymatch ls with
           | @GallinaIdentList.cons _ ?v ?rest
             => do_print v; iter rest
           | GallinaIdentList.nil => idtac
           end in
    idtac "Inductive ident :" type_to_Type ":=";
    iter all_ident_named_interped;
    idtac ".".

  Ltac print_ident_ind base base_type_list all_ident_named_interped :=
    (* we wrap everything in constr:(...) to inline [abstract] *)
    let __
        := constr:(
             ltac:(let eta_base_cps_gen := build_eta_base_cps_gen base in
                   let eta_base_cps := build_eta_base_cps eta_base_cps_gen in
                   let index_of_base := build_index_of_base base in
                   let base_interp := build_base_interp eta_base_cps base_type_list index_of_base in
                   let base_interp_name := fresh "temp_base_interp" in
                   let base_interp := cache_term base_interp base_interp_name in
                   let all_base := build_all_base base in
                   let all_base_and_interp := build_all_base_and_interp all_base base_interp in
                   print_ident_via base base_interp all_base_and_interp all_ident_named_interped;
                   exact I)) in
    idtac.

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
                         => reify_ident v ltac:(fun idc => unify id' idc) ltac:(fun _ => fail 0 "could not reify" v "as an ident")
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
                  [ econstructor;
                    lazymatch goal with
                    | [ |- ?ident (type.base base.type.unit) ] => solve [ constructor ]
                    | _ => intros; shelve
                    end
                  | constructor ];
                  intros;
                  lazymatch goal with
                  | [ |- ?ii ?id = ?v ]
                    => let id' := (eval cbv in id) in
                       change (ii id' = v); cbv [ident_interp_head];
                       fold (@base.interp);
                       let v := match goal with |- _ = ?v => v end in
                       reify_ident
                         v
                         ltac:(fun idc => unify id' idc)
                                ltac:(fun _ => fail 0 "could not reify" v "as an ident")
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

  Ltac build_index_of_ident ident :=
    constr:(ltac:(let t := fresh "t" in
                  let idc := fresh "idc" in
                  let min := open_constr:(_ : Datatypes.nat) in
                  unshelve (intros t idc; destruct idc;
                            [ > let v := get_min_and_incr min in refine v .. ]);
                  exact O)
            : forall t, ident t -> Datatypes.nat).
  Ltac make_index_of_ident ident :=
    let res := build_index_of_ident ident in refine res.

  Ltac build_ident_interp base_interp ident index_of_ident all_ident_named_interped :=
    let T := constr:(forall t, ident t -> type.interp (base.interp base_interp) t) in
    let res
        := (eval cbv beta iota in
               (ltac:(let t := fresh "t" in
                      let idc := fresh "idc" in
                      let v := fresh "v" in
                      let index_of_ident := (eval cbv in index_of_ident) in
                      let base_interp_head := head base_interp in
                      let all_ident_named_interped := (eval hnf in all_ident_named_interped) in
                      intros t idc;
                      pose (fun default : False => GallinaIdentList.nth (@index_of_ident _ idc) all_ident_named_interped default) as v;
                      destruct idc;
                      cbv [GallinaIdentList.nth GallinaIdentList.nth_type] in v;
                      let res := lazymatch (eval cbv [v] in v) with
                                 | fun _ => {| Named.value := ?v |} => v
                                 | ?v => constr_fail_with ltac:(fun _ => fail 1 "Invalid interpreted identifier" v)
                                 end in
                      clear v;
                      cbn [type.interp base.interp base_interp_head];
                      apply res; assumption)
                : T)) in
    constr:(res : T).
  Ltac make_ident_interp base_interp ident index_of_ident all_ident_named_interped :=
    let res := build_ident_interp base_interp ident index_of_ident all_ident_named_interped in exact res.

  Ltac build_all_idents ident :=
    build_all_gen
      { T : Type & T }
      ltac:(fun h => constr:(existT (fun T => T) _ h))
             (forall t, ident t -> True).
  Ltac make_all_idents ident :=
    let res := build_all_idents ident in refine res.

  Ltac build_all_ident_and_interp all_idents all_ident_named_interped :=
    let all_idents := (eval hnf in all_idents) in
    let all_ident_named_interped := (eval hnf in all_ident_named_interped) in
    lazymatch all_idents with
    | Datatypes.nil
      => lazymatch all_ident_named_interped with
         | GallinaIdentList.nil => GallinaAndReifiedIdentList.nil
         | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid remaining interped identifiers" all_ident_named_interped)
         end
    | Datatypes.cons (existT _ _ ?ridc) ?rest_ridc
      => lazymatch all_ident_named_interped with
         | GallinaIdentList.nil => constr_fail_with ltac:(fun _ => fail 1 "Invalid remaining identifiers" all_idents)
         | GallinaIdentList.cons {| Named.value := ?vidc |} ?rest_vidc
           => let rest := build_all_ident_and_interp rest_ridc rest_vidc in
              constr:(GallinaAndReifiedIdentList.cons ridc vidc rest)
         | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-GallinaIdentList" all_ident_named_interped)
         end
    | _ => constr_fail_with ltac:(fun _ => fail 1 "Invalid non list of existT identifiers" all_idents)
    end.
  Ltac make_all_ident_and_interp all_idents all_ident_named_interped :=
    let res := build_all_ident_and_interp all_idents all_ident_named_interped in
    refine res.

  Ltac try_build f x :=
    match constr:(Set) with
    | _ => let res := f x in
           constr:(Datatypes.Some res)
    | _ => constr:(@Datatypes.None Datatypes.unit)
    end.

  Ltac require_recursively_constructor_or_literal term :=
    lazymatch term with
    | ident.literal _ => idtac
    | ?f ?x => require_recursively_constructor_or_literal f;
               require_recursively_constructor_or_literal x
    | ?term => is_constructor term
    end.
  Ltac is_recursively_constructor_or_literal term :=
    match constr:(Set) with
    | _ => let check := match constr:(Set) with
                        | _ => require_recursively_constructor_or_literal term
                        end in
           true
    | _ => false
    end.

  Ltac try_reify_literal try_reify_base ident_Literal term :=
    let T := type of term in
    let rT := try_reify_base T in
    lazymatch rT with
    | Datatypes.Some ?rT
      => let term_is_primitive_const := is_recursively_constructor_or_literal term in
         lazymatch term_is_primitive_const with
         | true => constr:(Datatypes.Some (@ident_Literal rT term))
         | false => constr:(@Datatypes.None unit)
         end
    | Datatypes.None => constr:(@Datatypes.None unit)
    end.

  Ltac get_head_with_eagerly_then_plug_reified_types reify_base_type lookup_cps term then_tac else_tac :=
    let recr := get_head_with_eagerly_then_plug_reified_types reify_base_type lookup_cps in
    lazymatch term with
    | ident.eagerly ?f => lookup_cps term then_tac else_tac
    | ?f ?x
      => recr
           f
           ltac:(fun rf
                 => lazymatch type of rf with
                    | forall t, _
                      => let rx := reify_base_type x in
                         then_tac (rf rx)
                    | _ => else_tac ()
                    end)
                  else_tac
    | _ => lookup_cps term then_tac else_tac
    end.

  Ltac reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp ident_interp :=
    let all_ident_and_interp := (eval hnf in all_ident_and_interp) in
    let try_reify_base := try_build ltac:(reify_base_via_list base base_interp all_base_and_interp) in
    let reify_base := reify_base_via_list base base_interp all_base_and_interp in
    let reify_base_type := reify_base_type_via_list base base_interp all_base_and_interp in
    let ident_Literal := let idc := constr:(@ident.literal) in
                         lazymatch all_ident_and_interp with
                         | context[GallinaAndReifiedIdentList.cons ?ridc idc] => ridc
                         | _ => constr_fail_with ltac:(fun _ => fail 1 "Missing reification for" idc "in" all_ident_and_interp)
                         end in
    fun term then_tac else_tac
    => let as_lit := try_reify_literal try_reify_base ident_Literal term in
       lazymatch as_lit with
       | Datatypes.Some ?ridc => then_tac ridc
       | Datatypes.None
         => lazymatch term with
            | @ident_interp _ ?idc => then_tac idc
            | _
              => get_head_with_eagerly_then_plug_reified_types
                   reify_base_type
                   ltac:(fun idc then_tac else_tac
                         => let __ := Reify.debug_enter_lookup_ident idc in
                            lazymatch all_ident_and_interp with
                            | context[GallinaAndReifiedIdentList.cons ?ridc idc]
                              => let __ := Reify.debug_leave_lookup_ident_success idc ridc in
                                 then_tac ridc
                            | _
                              => let __ := Reify.debug_leave_lookup_ident_failure idc in
                                 else_tac ()
                            end)
                   term
                   then_tac
                   else_tac
            end
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

  Definition all_ident_named_interped : GallinaIdentList.t
    := [with_name ident_Literal (@ident.literal)
        ; with_name ident_Nat_succ Nat.succ
        ; with_name ident_Nat_pred Nat.pred
        ; with_name ident_Nat_max Nat.max
        ; with_name ident_Nat_mul Nat.mul
        ; with_name ident_Nat_add Nat.add
        ; with_name ident_Nat_sub Nat.sub
        ; with_name ident_Nat_eqb Nat.eqb
        ; with_name ident_nil (@Datatypes.nil)
        ; with_name ident_cons (@Datatypes.cons)
        ; with_name ident_tt Datatypes.tt
        ; with_name ident_pair (@Datatypes.pair)
        ; with_name ident_fst (@Datatypes.fst)
        ; with_name ident_snd (@Datatypes.snd)
        ; with_name ident_prod_rect (@prod_rect_nodep)
        ; with_name ident_bool_rect (@ident.Thunked.bool_rect)
        ; with_name ident_nat_rect (@ident.Thunked.nat_rect)
        ; with_name ident_eager_nat_rect (ident.eagerly (@ident.Thunked.nat_rect))
        ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
        ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
        ; with_name ident_list_rect (@ident.Thunked.list_rect)
        ; with_name ident_eager_list_rect (ident.eagerly (@ident.Thunked.list_rect))
        ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
        ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
        ; with_name ident_list_case (@ident.Thunked.list_case)
        ; with_name ident_List_length (@List.length)
        ; with_name ident_List_seq (@List.seq)
        ; with_name ident_List_firstn (@List.firstn)
        ; with_name ident_List_skipn (@List.skipn)
        ; with_name ident_List_repeat (@repeat)
        ; with_name ident_List_combine (@List.combine)
        ; with_name ident_List_map (@List.map)
        ; with_name ident_List_app (@List.app)
        ; with_name ident_List_rev (@List.rev)
        ; with_name ident_List_flat_map (@List.flat_map)
        ; with_name ident_List_partition (@List.partition)
        ; with_name ident_List_fold_right (@List.fold_right)
        ; with_name ident_List_update_nth (@update_nth)
        ; with_name ident_List_nth_default (@nth_default)
        ; with_name ident_eager_List_nth_default (ident.eagerly (@nth_default))
        ; with_name ident_Z_add Z.add
        ; with_name ident_Z_mul Z.mul
        ; with_name ident_Z_pow Z.pow
        ; with_name ident_Z_sub Z.sub
        ; with_name ident_Z_opp Z.opp
        ; with_name ident_Z_div Z.div
        ; with_name ident_Z_modulo Z.modulo
        ; with_name ident_Z_eqb Z.eqb
        ; with_name ident_Z_leb Z.leb
        ; with_name ident_Z_ltb Z.ltb
        ; with_name ident_Z_geb Z.geb
        ; with_name ident_Z_gtb Z.gtb
        ; with_name ident_Z_log2 Z.log2
        ; with_name ident_Z_log2_up Z.log2_up
        ; with_name ident_Z_of_nat Z.of_nat
        ; with_name ident_Z_to_nat Z.to_nat
        ; with_name ident_Z_shiftr Z.shiftr
        ; with_name ident_Z_shiftl Z.shiftl
        ; with_name ident_Z_land Z.land
        ; with_name ident_Z_lor Z.lor
        ; with_name ident_Z_min Z.min
        ; with_name ident_Z_max Z.max
        ; with_name ident_Z_mul_split Z.mul_split
        ; with_name ident_Z_add_get_carry Z.add_get_carry_full
        ; with_name ident_Z_add_with_carry Z.add_with_carry
        ; with_name ident_Z_add_with_get_carry Z.add_with_get_carry_full
        ; with_name ident_Z_sub_get_borrow Z.sub_get_borrow_full
        ; with_name ident_Z_sub_with_get_borrow Z.sub_with_get_borrow_full
        ; with_name ident_Z_zselect Z.zselect
        ; with_name ident_Z_add_modulo Z.add_modulo
        ; with_name ident_Z_truncating_shiftl Z.truncating_shiftl
        ; with_name ident_Z_bneg Z.bneg
        ; with_name ident_Z_lnot_modulo Z.lnot_modulo
        ; with_name ident_Z_rshi Z.rshi
        ; with_name ident_Z_cc_m Z.cc_m
        ; with_name ident_Z_combine_at_bitwidth Z.combine_at_bitwidth
        ; with_name ident_Z_cast ident.cast
        ; with_name ident_Z_cast2 ident.cast2
        ; with_name ident_Some (@Datatypes.Some)
        ; with_name ident_None (@Datatypes.None)
        ; with_name ident_option_rect (@ident.Thunked.option_rect)
        ; with_name ident_Build_zrange ZRange.Build_zrange
        ; with_name ident_zrange_rect (@ZRange.zrange_rect_nodep)
        ; with_name ident_fancy_add ident.fancy.add
        ; with_name ident_fancy_addc ident.fancy.addc
        ; with_name ident_fancy_sub ident.fancy.sub
        ; with_name ident_fancy_subb ident.fancy.subb
        ; with_name ident_fancy_mulll ident.fancy.mulll
        ; with_name ident_fancy_mullh ident.fancy.mullh
        ; with_name ident_fancy_mulhl ident.fancy.mulhl
        ; with_name ident_fancy_mulhh ident.fancy.mulhh
        ; with_name ident_fancy_rshi ident.fancy.rshi
        ; with_name ident_fancy_selc ident.fancy.selc
        ; with_name ident_fancy_selm ident.fancy.selm
        ; with_name ident_fancy_sell ident.fancy.sell
        ; with_name ident_fancy_addm ident.fancy.addm
       ]%gi_list.

  Section print_ident.
    Local Set Printing All.
    Local Set Printing Width 10000.
    (*Goal True. print_ident_ind base base_type_list all_ident_named_interped. Abort.*)
  End print_ident.

  Inductive ident : (forall _ : type.type (base.type.type base), Type) :=
  | ident_Literal : (forall (t : base) (_ : match t return Type with
                                            | Z => BinNums.Z
                                            | bool => Datatypes.bool
                                            | nat => Datatypes.nat
                                            | zrange => ZRange.zrange
                                            end), ident (@type.base (base.type.type base) (@base.type.type_base base t)))
  | ident_Nat_succ : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat))))
  | ident_Nat_pred : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat))))
  | ident_Nat_max : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat)))))
  | ident_Nat_mul : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat)))))
  | ident_Nat_add : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat)))))
  | ident_Nat_sub : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base nat)))))
  | ident_Nat_eqb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_nil : (forall t : base.type.type base, ident (@type.base (base.type.type base) (@base.type.list base t)))
  | ident_cons : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t)))))
  | ident_tt : (ident (@type.base (base.type.type base) (@base.type.unit base)))
  | ident_pair : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) (@base.type.prod base t t0)))))
  | ident_fst : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base t t0)) (@type.base (base.type.type base) t)))
  | ident_snd : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base t t0)) (@type.base (base.type.type base) t0)))
  | ident_prod_rect : (forall t t0 t1 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base t t0)) (@type.base (base.type.type base) t1))))
  | ident_bool_rect : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base bool)) (@type.base (base.type.type base) t)))))
  | ident_nat_rect : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) t)))))
  | ident_eager_nat_rect : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) t)))))
  | ident_nat_rect_arrow : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0))))))
  | ident_eager_nat_rect_arrow : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0))))))
  | ident_list_rect : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t0)))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) t0)))))
  | ident_eager_list_rect : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t0)))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) t0)))))
  | ident_list_rect_arrow : (forall t t0 t1 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1))))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1))))))
  | ident_eager_list_rect_arrow : (forall t t0 t1 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1))))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.base (base.type.type base) t1))))))
  | ident_list_case : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) t0))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) t0)))))
  | ident_List_length : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.type_base base nat))))
  | ident_List_seq : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.list base (@base.type.type_base base nat))))))
  | ident_List_firstn : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t)))))
  | ident_List_skipn : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t)))))
  | ident_List_repeat : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.list base t)))))
  | ident_List_combine : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t0)) (@type.base (base.type.type base) (@base.type.list base (@base.type.prod base t t0))))))
  | ident_List_map : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t0)))))
  | ident_List_app : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t)))))
  | ident_List_rev : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t))))
  | ident_List_flat_map : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) (@base.type.list base t0))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t0)))))
  | ident_List_partition : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) (@base.type.type_base base bool))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.list base t) (@base.type.list base t))))))
  | ident_List_fold_right : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t0) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t0)) (@type.base (base.type.type base) t)))))
  | ident_List_update_nth : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.base (base.type.type base) (@base.type.list base t))))))
  | ident_List_nth_default : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) t)))))
  | ident_eager_List_nth_default : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.list base t)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) t)))))
  | ident_Z_add : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_mul : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_pow : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_sub : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_opp : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_Z_div : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_modulo : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_eqb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_Z_leb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_Z_ltb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_Z_geb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_Z_gtb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base bool)))))
  | ident_Z_log2 : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_Z_log2_up : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_Z_of_nat : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base nat)) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_Z_to_nat : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base nat))))
  | ident_Z_shiftr : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_shiftl : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_land : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_lor : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_min : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_max : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_mul_split : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))))
  | ident_Z_add_get_carry : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))))
  | ident_Z_add_with_carry : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))))
  | ident_Z_add_with_get_carry : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z))))))))
  | ident_Z_sub_get_borrow : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))))
  | ident_Z_sub_with_get_borrow : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z))))))))
  | ident_Z_zselect : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))))
  | ident_Z_add_modulo : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))))
  | ident_Z_truncating_shiftl : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))))
  | ident_Z_bneg : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_Z_lnot_modulo : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_rshi : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))))
  | ident_Z_cc_m : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_combine_at_bitwidth : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z))))))
  | ident_Z_cast : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base zrange)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base Z)))))
  | ident_Z_cast2 : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base zrange) (@base.type.type_base base zrange))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z))) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z))))))
  | ident_Some : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) (@base.type.option base t))))
  | ident_None : (forall t : base.type.type base, ident (@type.base (base.type.type base) (@base.type.option base t)))
  | ident_option_rect : (forall t t0 : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) t) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.unit base)) (@type.base (base.type.type base) t0)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.option base t)) (@type.base (base.type.type base) t0)))))
  | ident_Build_zrange : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) (@base.type.type_base base zrange)))))
  | ident_zrange_rect : (forall t : base.type.type base, ident (@type.arrow (base.type.type base) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base Z)) (@type.base (base.type.type base) t))) (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.type_base base zrange)) (@type.base (base.type.type base) t))))
  | ident_fancy_add : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))
  | ident_fancy_addc : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))
  | ident_fancy_sub : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))
  | ident_fancy_subb : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))))
  | ident_fancy_mulll : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_mullh : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_mulhl : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_mulhh : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_rshi : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_selc : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_selm : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.type_base base Z) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z)))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_sell : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  | ident_fancy_addm : (ident (@type.arrow (base.type.type base) (@type.base (base.type.type base) (@base.type.prod base (@base.type.prod base (@base.type.type_base base Z) (@base.type.type_base base Z)) (@base.type.type_base base Z))) (@type.base (base.type.type base) (@base.type.type_base base Z))))
  .

  Definition index_of_base : base -> Datatypes.nat
    := ltac:(make_index_of_base base).

  Local Notation base_type := (@base.type base).

  Definition eta_base_cps_gen := ltac:(make_eta_base_cps_gen base).

  Definition eta_base_cps : forall {P : base -> Type} (f : forall t, P t), forall t, P t
    := ltac:(make_eta_base_cps eta_base_cps_gen).

  Definition base_interp := ltac:(make_base_interp (@eta_base_cps) base_type_list index_of_base).

  Local Notation base_type_interp := (base.interp base_interp).

  Definition all_base := ltac:(make_all_base base).
  Definition all_base_and_interp := ltac:(make_all_base_and_interp all_base base_interp).
  Definition index_of_ident := ltac:(make_index_of_ident ident).

  Definition ident_interp : forall {t}, ident t -> type.interp base_type_interp t
    := ltac:(make_ident_interp base_interp ident index_of_ident all_ident_named_interped).

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

  Definition all_idents := ltac:(make_all_idents ident).
  Definition all_ident_and_interp := ltac:(make_all_ident_and_interp all_idents all_ident_named_interped).

  Local Ltac do_reify_ident := reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp (@ident_interp).

  Definition buildEagerIdentAndInterpCorrect := ltac:(make_buildEagerIdentAndInterpCorrect (@ident_interp) baseHasNat baseHasNatCorrect ltac:(do_reify_ident)).

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
    := ltac:(make_buildIdentAndInterpCorrect (@ident_interp) ltac:(do_reify_ident)).
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

  Ltac reify_base := reify_base_via_list base base_interp all_base_and_interp.
  Ltac reify_base_type := reify_base_type_via_list base base_interp all_base_and_interp.
  Ltac reify_type := reify_type_via_list base base_interp all_base_and_interp.
  Ltac reify_ident :=
    let tac := ltac:(reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp (@ident_interp)) in
    fun term then_tac reify_rec else_tac => tac term then_tac else_tac.

  Global Strategy -1000 [base_interp ident_interp].
  Global Hint Extern 1 => base_type_reified_hint (@base_type) ltac:(reify_type) : typeclass_instances.
  Global Hint Extern 1 => expr_reified_hint (@base_type) ident ltac:(reify_base_type) ltac:(reify_ident) : typeclass_instances.
End Compilers.
