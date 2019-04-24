Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.PrimitiveSigma.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Require Import Crypto.Language.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Crypto.Util.Tuple.
Import ListNotations. Local Open Scope list_scope.
Import PrimitiveSigma.Primitive.

Import EqNotations.
Module Compilers.
  Set Boolean Equality Schemes.
  Set Decidable Equality Schemes.
  Local Set Primitive Projections.
  Export Language.Compilers.

  Local Notation "'plet' x := y 'in' z" := (match y return _ with x => z end).
  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).
  Local Notation type_of_list_cps := (fold_right (fun a K => a -> K)).

  Definition app_type_of_list {K} {ls : list Type} (f : type_of_list_cps K ls) (args : type_of_list ls) : K
    := list_rect
         (fun ls
          => type_of_list_cps K ls -> type_of_list ls -> K)
         (fun v _ => v)
         (fun T Ts rec f x
          => rec (f (fst x)) (snd x))
         ls
         f args.

  Definition lam_type_of_list {ls K} : (type_of_list ls -> K) -> type_of_list_cps K ls
    := list_rect
         (fun ls => (type_of_list ls -> K) -> type_of_list_cps K ls)
         (fun f => f tt)
         (fun T Ts rec k t => rec (fun ts => k (t, ts)))
         ls.

  Fixpoint list_app_type_of_list {ls1 ls2 : list Type} : type_of_list ls1 -> type_of_list ls2 -> type_of_list (ls1 ++ ls2)
    := match ls1 return type_of_list ls1 -> type_of_list ls2 -> type_of_list (ls1 ++ ls2) with
       | nil => fun _ x => x
       | cons T Ts => fun tts rest => (fst tts, @list_app_type_of_list Ts ls2 (snd tts) rest)
       end.

  Fixpoint list_unapp_type_of_list {ls1 ls2 : list Type} : type_of_list (ls1 ++ ls2) -> type_of_list ls1 * type_of_list ls2
    := match ls1 return type_of_list (ls1 ++ ls2) -> type_of_list ls1 * type_of_list ls2 with
       | nil => fun x => (tt, x)
       | cons T Ts
         => fun tts
            => let '(t2, t2s) := @list_unapp_type_of_list Ts ls2 (snd tts) in
               (fst tts, t2, t2s)
       end.

  Fixpoint lift_type_of_list_map {A} {ls : list A} {P1 P2 : A -> Type} (F : forall a, P1 a -> P2 a) {struct ls}
    : type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls)
    := match ls return type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls) with
       | nil => fun x => x
       | T :: Ts
         => fun v_vs
            => (F T (fst v_vs),
                @lift_type_of_list_map A Ts P1 P2 F (snd v_vs))
       end.

  Module pattern.
    Notation EvarMap := (PositiveMap.t Compilers.base.type).
    Module base.
      Local Notation einterp := type.interp.
      Module type.
        Inductive type := var (p : positive) | type_base (t : Compilers.base.type.base) | prod (A B : type) | list (A : type) | option (A : type).
      End type.
      Notation type := type.type.

      Fixpoint relax (t : Compilers.base.type) : type
        := match t with
           | Compilers.base.type.type_base t => type.type_base t
           | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
           | Compilers.base.type.list A => type.list (relax A)
           | Compilers.base.type.option A => type.option (relax A)
           end.

      Definition lookup_default (p : positive) (evar_map : EvarMap) : Compilers.base.type
        := match PositiveMap.find p evar_map with
           | Datatypes.Some t => t
           | Datatypes.None => Compilers.base.type.type_base base.type.unit
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : Compilers.base.type
        := match ptype with
           | type.var p => lookup_default p evar_map
           | type.type_base t => Compilers.base.type.type_base t
           | type.prod A B
             => Compilers.base.type.prod (subst_default A evar_map) (subst_default B evar_map)
           | type.list A => Compilers.base.type.list (subst_default A evar_map)
           | type.option A => Compilers.base.type.option (subst_default A evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.var p => PositiveSet.add p PositiveSet.empty
           | type.type_base t => PositiveSet.empty
           | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
           | type.list A => collect_vars A
           | type.option A => collect_vars A
           end.

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
        Notation "' n" := (type.var n) : pbtype_scope.
        Notation "' n" := (type.base (type.var n)) : ptype_scope.
        Notation "'1" := (type.var 1) : pbtype_scope.
        Notation "'2" := (type.var 2) : pbtype_scope.
        Notation "'3" := (type.var 3) : pbtype_scope.
        Notation "'4" := (type.var 4) : pbtype_scope.
        Notation "'5" := (type.var 5) : pbtype_scope.
        Notation "'1" := (type.base (type.var 1)) : ptype_scope.
        Notation "'2" := (type.base (type.var 2)) : ptype_scope.
        Notation "'3" := (type.base (type.var 3)) : ptype_scope.
        Notation "'4" := (type.base (type.var 4)) : ptype_scope.
        Notation "'5" := (type.base (type.var 5)) : ptype_scope.
      End Notations.
    End base.
    Notation type := (type.type base.type).
    Export base.Notations.

    Module type.
      Fixpoint relax (t : type.type Compilers.base.type) : type
        := match t with
           | type.base t => type.base (base.relax t)
           | type.arrow s d => type.arrow (relax s) (relax d)
           end.

      Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type Compilers.base.type
        := match ptype with
           | type.base t => type.base (base.subst_default t evar_map)
           | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
           end.

      Fixpoint collect_vars (t : type) : PositiveSet.t
        := match t with
           | type.base t => base.collect_vars t
           | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
           end.
    End type.

    Module Generate.
      Module Import Tactics.
        Ltac find_evar_tail x :=
          lazymatch x with
          | Datatypes.cons _ ?x => find_evar_tail x
          | ?ev => let __ := match goal with _ => is_evar ev end in
                   ev
          end.
        Ltac build_all_idents_gen P :=
          let res := open_constr:(_ : list { T : Type & T }) in
          let fill_next v :=
              let next := find_evar_tail res in
              let __ := open_constr:(eq_refl : next = v) in
              constr:(I) in
          let __ := open_constr:(
                      ltac:(intros;
                            let idc' := fresh "idc'" in
                            lazymatch goal with
                            | [ idc : _ |- _ ] => pose idc as idc'; destruct idc
                            end;
                            let idc := (eval cbv [idc'] in idc') in
                            let h := head idc in
                            let __ := fill_next open_constr:(Datatypes.cons (existT (fun T => T) _ h) _) in
                            constructor)
                      : P) in
          let __ := fill_next uconstr:(Datatypes.nil) in
          res.
        Ltac build_all_idents := build_all_idents_gen (forall t (idc : Compilers.ident.ident t), True).
        Ltac make_all_idents := let v := build_all_idents in refine v.

        Ltac strip_default v :=
          let v := lazymatch v with
                   | (fun _ => ?v) => v
                   | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not eliminate dependency on dummy default argument in" v)
                   end in
          v.
        Ltac strip2_args v :=
          let v := lazymatch v with
                   | (fun _ _ => ?v) => v
                   | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not eliminate dependency on first two dummy arguments in" v)
                   end in
          v.

        Ltac do_make_eta_ident_cps_gen_gen do_destruct_base :=
          unshelve eexists; intros;
          lazymatch goal with idc : _ |- _ => destruct idc end;
          lazymatch do_destruct_base with
          | true => repeat match goal with t : base.type.base |- _ => destruct t end
          | false => idtac
          end;
          shelve_unifiable; reflexivity.
        Ltac do_make_eta_ident_cps_gen := do_make_eta_ident_cps_gen_gen false.
        Ltac do_make_eta_ident_cps_gen_expand_literal := do_make_eta_ident_cps_gen_gen true.

        Ltac build_eta_ident_cps_gen_gen do_destruct_base ident :=
          let has_arg := lazymatch type of ident with
                         | _ -> Set => true
                         | _ -> Type => true
                         | Set => false
                         | Type => false
                         | ?T => constr_fail_with ltac:(fun _ => fail 1 "Invalid type of ident (" ident "):" T "(expected Type or _ -> Type)")
                         end in
          let T := lazymatch has_arg with
                   | true
                     => constr:(
                          forall (T : forall t, ident t -> Type)
                                 (f : forall t idc, T t idc),
                            { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc })
                   | false
                     => constr:(
                          forall (T : ident -> Type)
                                 (f : forall idc, T idc),
                            { f' : forall idc, T idc | forall idc, f' idc = f idc })
                   end in
          constr:(ltac:(do_make_eta_ident_cps_gen_gen do_destruct_base)
                  : T).
        Ltac build_eta_ident_cps_gen := build_eta_ident_cps_gen_gen false.
        Ltac build_eta_ident_cps_gen_expand_literal := build_eta_ident_cps_gen_gen true.
        Ltac make_eta_ident_cps_gen_gen do_destruct_base ident :=
          let res := build_eta_ident_cps_gen_gen do_destruct_base ident in refine res.
        Ltac make_eta_ident_cps_gen := make_eta_ident_cps_gen_gen false.
        Ltac make_eta_ident_cps_gen_expand_literal := make_eta_ident_cps_gen_gen true.

        Ltac get_ctor_number' ctor all_idents :=
          lazymatch all_idents with
          | Datatypes.cons ctor _ => Datatypes.O
          | Datatypes.cons (existT _ _ ctor) _ => Datatypes.O
          | Datatypes.cons _ ?xs => let v := get_ctor_number' ctor xs in
                                    constr:(Datatypes.S v)
          | Datatypes.nil => constr_fail_with ltac:(fun _ => fail 1 "Could not find" ctor)
          end.

        Ltac find_ctor ctor from_all_idents to_all_idents :=
          let n := get_ctor_number' ctor from_all_idents in
          let v := (eval cbv [List.nth] in (fun default => List.nth n to_all_idents default)) in
          let v := lazymatch v with
                   | (fun _ => ?v) => v
                   | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not find" ctor "from" from_all_idents "(index" n ") in" to_all_idents "(failed to eliminate dependency on dummy default argument in" v ")")
                   end in
          v.

        Ltac make_ident_index ty all_idents :=
          let all_idents := (eval hnf in all_idents) in
          let v := (eval cbv [id] in
                       (ltac:(intros;
                              let idc := lazymatch goal with idc : _ |- _ => idc end in
                              let idc' := fresh "idc'" in
                              pose idc as idc';
                              destruct idc;
                              let idc := (eval cbv [idc'] in idc') in
                              let idc := head idc in
                              let n := get_ctor_number' idc all_idents in
                              exact n)
                        : ty)) in
          refine v.
      End Tactics.

      Section __.
        Context (all_idents : list { T : Type & T })
                (ident_index : forall t, ident t -> nat)
                (eta_ident_cps_gen
                 : forall {T : forall t, Compilers.ident.ident t -> Type}
                          (f : forall t idc, T t idc),
                    { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).

        Definition eta_ident_cps_gen2
                   {T0 : forall t, Compilers.ident.ident t -> Type}
                   (f0 : forall t idc, T0 t idc)
                   {T1 : forall t idc, T0 t idc -> Type}
                   (f1 : forall t idc, T1 t idc (f0 t idc))
          : { f' : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc)
            | forall t idc,
                f' t idc = rew [T1 t idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) t idc)) in f1 t idc }.
        Proof. apply eta_ident_cps_gen. Defined.

        Definition eta_ident_cps_gen3
                   {T0 : forall t, Compilers.ident.ident t -> Type}
                   (f0 : forall t idc, T0 t idc)
                   {T1 : forall t idc, T0 t idc -> Type}
                   (f1 : forall t idc, T1 t idc (f0 t idc))
                   {T2 : forall t idc x, T1 t idc x -> Type}
                   (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
          : { f' : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)
            | forall t idc,
                f' t idc
                = rew [T2 t idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)) in
                  match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) t idc) as p return T2 t idc _ (rew [T1 t idc] p in f1 t idc) with
                  | eq_refl => f2 t idc
                  end }.
        Proof. apply eta_ident_cps_gen. Defined.
      End __.

      Module Raw.
        Module ident.
          Inductive kind_of_type := GallinaType (_ : Type) | BaseBaseType | BaseType.
          Definition Type_of_kind_of_type (T : kind_of_type)
            := match T with
               | GallinaType T => T
               | BaseBaseType => Compilers.base.type.base
               | BaseType => Compilers.base.type.type
               end.

          Notation type_of_list_of_kind ls
            := (type_of_list (List.map Type_of_kind_of_type ls)).

          Record preident_infos :=
            {
              dep_types : list Type; (* types which show up in the type of other infos *)
              indep_types : list kind_of_type; (* types which show up in the type of the ident, but not in the type of other lists *)
              indep_args : type_of_list dep_types -> list Type;
              to_type : forall d : type_of_list dep_types, type_of_list_of_kind indep_types -> Compilers.type Compilers.base.type;
              to_ident : forall (d : type_of_list dep_types) (i : type_of_list_of_kind indep_types), type_of_list (indep_args d) -> Compilers.ident.ident (to_type d i)
            }.

          Record ident_infos :=
            {
              preinfos :> preident_infos;
              dep_types_dec_transparent : forall x y : type_of_list (dep_types preinfos), {x = y} + {x <> y};
              indep_args_beq : _;
              indep_args_reflect
              : forall x, reflect_rel (@eq (type_of_list (indep_args preinfos x))) (indep_args_beq x);
              indep_types_beq : _;
              indep_types_reflect
              : reflect_rel (@eq (type_of_list_of_kind (indep_types preinfos))) indep_types_beq;
            }.

          Definition ident_args (pi : preident_infos)
            := { t : type_of_list (dep_types pi) & type_of_list_of_kind (indep_types pi) * type_of_list (indep_args pi t) }%type.

          Definition assemble_ident {pi} (args : ident_args pi)
            := to_ident pi (projT1 args) (Datatypes.fst (projT2 args)) (Datatypes.snd (projT2 args)).

          Section __.
            Context (all_pattern_idents : list { T : Type & T })
                    (pattern_ident_index : forall t, Compilers.ident.ident t -> nat)
                    (eta_pattern_ident_cps_gen
                     : forall {T : forall t, Compilers.ident.ident t -> Type}
                              (f : forall t idc, T t idc),
                        { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).
            Context (ident : Set)
                    (all_idents : list ident)
                    (ident_index : ident -> nat)
                    (ident_index_idempotent : forall idc, List.nth_error all_idents (ident_index idc) = Some idc)
                    (eta_ident_cps_gen
                     : forall {T : ident -> Type}
                              (f : forall idc, T idc),
                        { f' : forall idc, T idc | forall idc, f' idc = f idc }).

            Definition eta_ident_cps_gen2
                       {T0 : ident -> Type}
                       (f0 : forall idc, T0 idc)
                       {T1 : forall idc, T0 idc -> Type}
                       (f1 : forall idc, T1 idc (f0 idc))
              : { f' : forall idc, T1 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc)
                | forall idc,
                    f' idc = rew [T1 idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) idc)) in f1 idc }.
            Proof. apply eta_ident_cps_gen. Defined.

            Definition eta_ident_cps_gen3
                       {T0 : ident -> Type}
                       (f0 : forall idc, T0 idc)
                       {T1 : forall idc, T0 idc -> Type}
                       (f1 : forall idc, T1 idc (f0 idc))
                       {T2 : forall idc x, T1 idc x -> Type}
                       (f2 : forall idc, T2 idc (f0 idc) (f1 idc))
              : { f' : forall idc, T2 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) idc)
                | forall idc,
                    f' idc
                    = rew [T2 idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) idc)) in
                      match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) idc) as p return T2 idc _ (rew [T1 idc] p in f1 idc) with
                      | eq_refl => f2 idc
                      end }.
            Proof. apply eta_ident_cps_gen. Defined.

            Definition ident_beq : ident -> ident -> bool
              := fun idc1 idc2
                 => proj1_sig
                      (@eta_ident_cps_gen
                         _
                         (fun idc1
                          => proj1_sig
                               (@eta_ident_cps_gen
                                  _
                                  (fun idc2
                                   => Nat.eqb (ident_index idc1) (ident_index idc2)))
                               idc2))
                      idc1.

            Local Ltac rew_proj2_sig :=
              repeat match goal with
                     | [ |- context[@proj1_sig _ (fun _ => forall x, _ = _) ?p] ]
                       => rewrite !(proj2_sig p)
                     | [ |- context[@proj1_sig _ (fun _ => forall x y, _ = _) ?p] ]
                       => rewrite !(proj2_sig p)
                     end.

            Definition nat_eqb_refl_transparent (x : nat) : Nat.eqb x x = true.
            Proof. induction x; cbn; constructor + assumption. Defined.

            Definition ident_lb (x y : ident) : x = y -> ident_beq x y = true.
            Proof.
              intro H; subst y; cbv [ident_beq];
                rew_proj2_sig; apply nat_eqb_refl_transparent.
            Defined.

            Lemma ident_index_inj idc1 idc2 : ident_index idc1 = ident_index idc2 -> idc1 = idc2.
            Proof.
              intro H.
              pose proof (ident_index_idempotent idc1) as H1.
              pose proof (ident_index_idempotent idc2) as H2.
              rewrite H in H1; rewrite H1 in H2.
              set (sidc1 := Some idc1) in *.
              set (sidc2 := Some idc2) in *.
              change (match sidc1, sidc2 with Some idc1, Some idc2 => idc1 = idc2 | _, _ => True end).
              clearbody sidc2; subst sidc2 sidc1; reflexivity.
            Defined.

            Definition nat_eqb_bl_transparent (x y : nat) : Nat.eqb x y = true -> x = y.
            Proof.
              revert y; induction x, y; cbn; intro; try apply f_equal; auto using eq_refl with nocore;
                exfalso; apply Bool.diff_false_true; assumption.
            Defined.

            Definition ident_bl (x y : ident) : ident_beq x y = true -> x = y.
            Proof.
              cbv [ident_beq]; rew_proj2_sig; intro H.
              apply nat_eqb_bl_transparent in H.
              apply ident_index_inj in H.
              exact H.
            Defined.

            Definition ident_beq_if (x y : ident) : if ident_beq x y then x = y else True.
            Proof.
              generalize (ident_beq x y), (ident_bl x y).
              intros b H; destruct b; exact I + auto using eq_refl with nocore.
            Defined.

            Definition ident_transport_opt (P : ident -> Type) {x y : ident} : P x -> Datatypes.option (P y)
              := fun v
                 => (if ident_beq x y as b return (if b then x = y else True) -> _
                     then fun pf => Datatypes.Some
                                      match pf in (_ = y) return P y with
                                      | eq_refl => v
                                      end
                     else fun _ => Datatypes.None)
                      (@ident_beq_if x y).

            Definition ident_to_cident : ident -> { T : Type & T }
              := proj1_sig
                   (@eta_ident_cps_gen
                      _
                      (fun idc => List.nth_default (@existT Type _ True I) all_pattern_idents (ident_index idc))).

            Context (ident_infos_of : ident -> ident_infos)
                    (split_ident_gen
                     : forall {t} (idc : Compilers.ident.ident t),
                        { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                         | { pf : _ = _
                                           | idc = rew [Compilers.ident.ident] pf in assemble_ident args } } }).

            Definition prefull_types : ident -> Type
              := fun idc => ident_args (ident_infos_of idc).
            Definition full_types : ident -> Type
              := proj1_sig (@eta_ident_cps_gen _ prefull_types).
            Definition is_simple : ident -> bool
              := fun idc
                 => let ii := ident_infos_of idc in
                    match dep_types ii, indep_types ii return _ with (* COQBUG(https://github.com/coq/coq/issues/9955) *)
                    | [], [] => true
                    | _, _ => false
                    end.
            Definition type_of : forall (pidc : ident), full_types pidc -> Compilers.type Compilers.base.type
              := proj1_sig
                   (@eta_ident_cps_gen2
                      _ prefull_types
                      (fun pidc full_types_pidc => full_types_pidc -> Compilers.type Compilers.base.type)
                      (fun pidc args
                       => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))).

            Definition folded_invert_bind_args : forall {t} (idc : Compilers.ident.ident t) (pidc : ident), Datatypes.option (full_types pidc)
              := fun t idc pidc
                 => proj1_sig
                      (@eta_pattern_ident_cps_gen
                         _
                         (fun t idc
                          => proj1_sig
                               (@eta_ident_cps_gen2
                                  _ prefull_types
                                  (fun pidc full_types_pidc => Datatypes.option full_types_pidc)
                                  (fun pidc
                                   => let '(existT ridc (exist args _)) := @split_ident_gen _ idc in
                                      ident_transport_opt
                                        (fun idc => ident_args (ident_infos_of idc))
                                        args))
                               pidc))
                      t idc.

            Definition to_typed : forall (pidc : ident) (args : full_types pidc), Compilers.ident.ident (type_of pidc args)
              := proj1_sig
                   (@eta_ident_cps_gen3
                      _ prefull_types
                      (fun pidc full_types_pidc => full_types_pidc -> Compilers.type Compilers.base.type)
                      (fun pidc args => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))
                      (fun pidc full_types_pidc type_of_pidc => forall args : full_types_pidc, Compilers.ident.ident (type_of_pidc args))
                      (fun pidc args
                       => to_ident _ _ _ (Datatypes.snd (projT2 args)))).

            Definition try_unify_split_args {ridc1 ridc2 : ident}
              : forall {dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1)))}
                       {dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2)))}
              (*(idt1 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc1))))
                   (idt2 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc2))))*),
                type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2))
              := (if ident_beq ridc1 ridc2 as b return (if b then ridc1 = ridc2 else True) -> _
                  then fun pf
                       => match pf in (_ = ridc2) return forall (dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1))))
                                                                (dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2))))
                            (*(idt1 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc1))))
                                                            (idt2 : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc2))))*),
                              type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                          | eq_refl
                            => fun dt1 dt2 (*idt1 idt2*)
                               => match dep_types_dec_transparent _ dt1 dt2 with
                                  | left pf
                                    => match pf in (_ = dt2) return type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                                       | eq_refl
                                         => (*if indep_types_beq _ idt1 idt2
                                        then*) Datatypes.Some
                                                 (*else fun _ => Datatypes.None*)
                                       end
                                  | right _ => fun _ => Datatypes.None
                                  end
                          end
                  else fun _ _ _ _ (*_ _*) => Datatypes.None)
                   (ident_beq_if ridc1 ridc2).
          End __.

          Module Tactics.
            Ltac map_projT2 ls :=
              lazymatch eval cbv beta in ls with
              | Datatypes.nil => uconstr:(Datatypes.nil)
              | Datatypes.cons (existT _ _ ?v) ?ls
                => let ls' := map_projT2 ls in
                   constr:(Datatypes.cons v ls')
              end.

            Ltac build_all_idents ident :=
              let v := build_all_idents_gen (ident -> True) in
              map_projT2 v.
            Ltac make_all_idents ident := let v := build_all_idents ident in refine v.

            Ltac prove_ident_index_idempotent _ :=
              let idc := fresh "idc" in
              intro idc; destruct idc; vm_compute; reflexivity.

            Ltac build_ident_index_idempotent all_idents ident_index :=
              constr:(ltac:(prove_ident_index_idempotent ())
                      : forall idc, List.nth_error all_idents (ident_index idc) = Some idc).
            Ltac make_ident_index_idempotent all_idents ident_index :=
              let v := build_ident_index_idempotent all_idents ident_index in refine v.
            Ltac fun_to_curried_ident_infos f :=
              let type_to_kind T
                  := lazymatch (eval cbv beta in T) with
                     | Compilers.base.type.base => BaseBaseType
                     | Compilers.base.type.type => BaseType
                     | ?T => constr:(GallinaType T)
                     end in
              let T := type of f in
              lazymatch (eval cbv beta in T) with
              | forall (x : ?A), _
                => let f' := fresh in
                   let f := (eval cbv beta in
                                (fun x : A
                                 => match f x return _ with
                                    | f'
                                      => ltac:(let f := (eval cbv [f'] in f') in
                                               let res := fun_to_curried_ident_infos f in
                                               exact res)
                                    end)) in
                   let v
                       := match f with
                          | (fun x : ?A => {| dep_types := Datatypes.nil ; indep_types := Datatypes.nil ; indep_args := ?ida ; to_type := ?tt ; to_ident := @?ti x |})
                            => let d := fresh "d" in
                               let i := fresh "i" in
                               let a := fresh "a" in
                               constr:({| dep_types := Datatypes.nil ; indep_types := Datatypes.nil ; indep_args := (fun d => (A:Type) :: ida d) ; to_type := tt ; to_ident := fun d i a => ti (Datatypes.fst a) d i (Datatypes.snd a) |})
                          | (fun x : ?A => {| dep_types := Datatypes.nil ; indep_types := ?idt ; indep_args := ?ida ; to_type := @?tt x ; to_ident := @?ti x |})
                            => let d := fresh "d" in
                               let i := fresh "i" in
                               let a := fresh "a" in
                               let A := type_to_kind A in
                               constr:({| dep_types := Datatypes.nil ; indep_types := A :: idt ; indep_args := ida ; to_type := (fun d i => tt (Datatypes.fst i) d (Datatypes.snd i)) ; to_ident := fun d i a => ti (Datatypes.fst i) d (Datatypes.snd i) a |})
                          | (fun x : ?A => {| dep_types := ?dt ; indep_types := ?idt ; indep_args := @?ida x ; to_type := @?tt x ; to_ident := @?ti x |})
                            => let d := fresh "d" in
                               let i := fresh "i" in
                               let a := fresh "a" in
                               (*let A := type_to_kind A in*)
                               constr:({| dep_types := (A:Type) :: dt ; indep_types := idt ; indep_args := (fun d => ida (Datatypes.fst d) (Datatypes.snd d)) ; to_type := (fun d i => tt (Datatypes.fst d) (Datatypes.snd d) i) ; to_ident := fun d i a => ti (Datatypes.fst d) (Datatypes.snd d) i a |})
                          end in
                   (eval cbv beta in v)
              | Compilers.ident.ident ?t
                => constr:({| dep_types := Datatypes.nil ; indep_types := Datatypes.nil ; indep_args := (fun _ => Datatypes.nil) ; to_type := (fun _ _ => t) ; to_ident := fun _ _ _ => f |})
              end.

            Ltac build_ident_infos_of ident_to_cident :=
              let idc := fresh "idc" in
              let T := fresh in
              let v
                  := constr:(
                       fun idc
                       => match ident_to_cident idc return ident_infos with
                          | T
                            => ltac:(destruct idc;
                                     let T := (eval cbv in (projT2 T)) in
                                     let v := fun_to_curried_ident_infos T in
                                     let v := (eval cbv [type_of_list List.map Type_of_kind_of_type] in v) in
                                     let c := constr:(@Build_ident_infos v) in
                                     let T := type of c in
                                     let T := (eval cbv [dep_types indep_types indep_args type_of_list List.map Type_of_kind_of_type] in T) in
                                     refine ((c : T) _ _ _ _ _);
                                     repeat decide equality)
                          end) in
              let v := (eval cbv [dep_types indep_types indep_args type_of_list preinfos List.map Type_of_kind_of_type Datatypes.prod_rect base.type.base_rect unit_rect sumbool_rect prod_rec unit_rec sumbool_rec base.type.base_rec eq_ind_r eq_ind eq_sym eq_rec eq_rect] in v) in
              v.
            Ltac make_ident_infos_of ident_to_cident := let v := build_ident_infos_of ident_to_cident in refine v.

            Ltac refine_sigT_and_pair :=
              repeat first [ exact Datatypes.tt
                           | progress cbn [Datatypes.fst Datatypes.snd projT1 projT2]
                           | match goal with
                             | [ |- context[Datatypes.fst ?ev] ]
                               => is_evar ev;
                                  let __ := open_constr:(eq_refl : ev = (_, _)) in
                                  cbn [Datatypes.fst Datatypes.snd]
                             | [ |- context[Datatypes.snd ?ev] ]
                               => is_evar ev;
                                  let __ := open_constr:(eq_refl : ev = (_, _)) in
                                  cbn [Datatypes.fst Datatypes.snd]
                             | [ |- context[projT1 ?ev] ]
                               => is_evar ev;
                                  let __ := open_constr:(eq_refl : ev = existT _ _ _) in
                                  cbn [projT1 projT2]
                             | [ |- context[projT2 ?ev] ]
                               => is_evar ev;
                                  let __ := open_constr:(eq_refl : ev = existT _ _ _) in
                                  cbn [projT1 projT2]
                             end ].

            Ltac build_split_ident_gen ident ident_infos_of all_idents all_pattern_idents :=
              let t := fresh "t" in
              let idc := fresh "idc" in
              let idc' := fresh "idc'" in
              let ridc := fresh "ridc" in
              let v := (eval cbv beta iota zeta in
                           (fun t (idc : Compilers.ident.ident t)
                            => let idc' := idc in
                               ltac:(destruct idc;
                                     let idc := (eval cbv [idc'] in idc') in
                                     let ctor := head idc in
                                     let all_idents := (eval cbv [all_idents] in all_idents) in
                                     let all_tidents := (eval cbv [all_pattern_idents] in all_pattern_idents) in
                                     let ridc := find_ctor ctor all_tidents all_idents in
                                     (exists ridc);
                                     cbv [ident_infos_of ident_args type_of_list indep_args dep_types indep_types preinfos assemble_ident to_ident List.map Type_of_kind_of_type];
                                     unshelve (eexists; refine_sigT_and_pair; try constructor);
                                     cbv [to_type Datatypes.fst];
                                     try solve [ repeat unshelve esplit ])
                               : { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                                  | { pf : _ = _
                                                    | idc = rew [Compilers.ident.ident] pf in assemble_ident args } } })) in
              v.
            Ltac make_split_ident_gen ident ident_infos_of all_idents all_pattern_idents :=
              let v := build_split_ident_gen ident ident_infos_of all_idents all_pattern_idents in refine v.

            Ltac build_invert_bind_args eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen :=
              (eval cbv [folded_invert_bind_args eta_pattern_ident_cps_gen proj1_sig eta_ident_cps_gen2 eta_ident_cps_gen proj1_sig proj2_sig eq_rect eq_sym split_ident_gen projT2 ident_transport_opt ident_beq ident_index Nat.eqb ident_beq_if ident_bl eq_ind_r eq_ind nat_eqb_bl_transparent nat_ind ident_index_inj ident_index_idempotent f_equal] in
                  (@folded_invert_bind_args eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen)).
            Ltac make_invert_bind_args eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen :=
              let v := build_invert_bind_args eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen in refine v.

            Module MakeIdent.
              Ltac map_projT2 tac ls :=
                lazymatch ls with
                | Datatypes.nil => idtac
                | Datatypes.cons (existT _ _ ?v) ?ls
                  => tac v; map_projT2 tac ls
                end.
              Ltac fill_forall_args v :=
                let T := type of v in
                lazymatch (eval cbv beta in T) with
                | ?A -> ?B => v
                | forall x : ?A, _ => fill_forall_args open_constr:(v _)
                | _ => v
                end.
              Ltac print_ident :=
                let all_idents := Compilers.pattern.Generate.Tactics.build_all_idents in
                idtac "        Inductive ident :=";
                let v := all_idents in
                map_projT2 ltac:(fun v => let v := fill_forall_args v in idtac "        |" v) v;
                idtac "        .".
              Import Compilers.ident.
              Local Unset Printing Notations.
              (*Goal True. print_ident. Abort.*)
            End MakeIdent.
          End Tactics.
        End ident.
      End Raw.

      Module ident.
        Definition Type_of_kind_of_type (T : Raw.ident.kind_of_type)
          := match T with
             | Raw.ident.GallinaType T => T
             | Raw.ident.BaseBaseType => Compilers.base.type.base
             | Raw.ident.BaseType => pattern.base.type.type
             end.

        Notation full_type_of_list_of_kind ls
          := (type_of_list (List.map Raw.ident.Type_of_kind_of_type ls)).

        Notation type_of_list_of_kind ls
          := (type_of_list (List.map Type_of_kind_of_type ls)).

        Definition relax_kind_of_type {T} : Raw.ident.Type_of_kind_of_type T -> Type_of_kind_of_type T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => pattern.base.relax
             end.
        Definition subst_default_kind_of_type (evm : EvarMap) {T} : Type_of_kind_of_type T -> Raw.ident.Type_of_kind_of_type T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => fun t => pattern.base.subst_default t evm
             end.

        Local Notation dep_types := Raw.ident.dep_types.
        Local Notation preinfos := Raw.ident.preinfos.
        Local Notation indep_types := Raw.ident.indep_types.
        Local Notation indep_args := Raw.ident.indep_args.
        Local Notation iffT A B := ((A -> B) * (B -> A))%type.

        Section __.
          Context (all_pattern_idents : list { T : Type & T })
                  (pattern_ident_index : forall t, Compilers.ident.ident t -> nat)
                  (eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal
                   : forall {T : forall t, Compilers.ident.ident t -> Type}
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).
          Context (raw_ident : Set)
                  (all_raw_idents : list raw_ident)
                  (raw_ident_index : raw_ident -> nat)
                  (raw_ident_index_idempotent : forall idc, List.nth_error all_raw_idents (raw_ident_index idc) = Some idc)
                  (eta_raw_ident_cps_gen
                   : forall {T : raw_ident -> Type}
                            (f : forall idc, T idc),
                      { f' : forall idc, T idc | forall idc, f' idc = f idc }).
          Context (raw_ident_infos_of : raw_ident -> Raw.ident.ident_infos)
                  (split_raw_ident_gen
                   : forall {t} (idc : Compilers.ident.ident t),
                      { ridc : raw_ident
                               & { args : Raw.ident.ident_args (preinfos (raw_ident_infos_of ridc))
                                 | { pf : _ = _
                                   | idc = rew [Compilers.ident.ident] pf in Raw.ident.assemble_ident args } } }).
          Context (ident : type -> Type)
                  (all_idents : list { T : Type & T })
                  (eta_ident_cps_gen
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc })
                  (eta_ident_cps_gen_expand_literal
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).

          Definition eta_ident_cps_gen2
                     {T0 : forall t, ident t -> Type}
                     (f0 : forall t idc, T0 t idc)
                     {T1 : forall t (idc : ident t), T0 t idc -> Type}
                     (f1 : forall t idc, T1 t idc (f0 t idc))
            : { f' : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc)
              | forall t idc,
                  f' t idc = rew [T1 t idc] (eq_sym (proj2_sig (@eta_ident_cps_gen T0 f0) t idc)) in f1 t idc }.
          Proof. apply eta_ident_cps_gen. Defined.

          Definition eta_ident_cps_gen3
                     {T0 : forall t, ident t -> Type}
                     (f0 : forall t idc, T0 t idc)
                     {T1 : forall t idc, T0 t idc -> Type}
                     (f1 : forall t idc, T1 t idc (f0 t idc))
                     {T2 : forall t idc x, T1 t idc x -> Type}
                     (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
            : { f' : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (proj1_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)
              | forall t idc,
                  f' t idc
                  = rew [T2 t idc _] (eq_sym (proj2_sig (@eta_ident_cps_gen2 T0 f0 T1 f1) t idc)) in
                    match eq_sym (proj2_sig (@eta_ident_cps_gen _ f0) t idc) as p return T2 t idc _ (rew [T1 t idc] p in f1 t idc) with
                    | eq_refl => f2 t idc
                    end }.
          Proof. apply eta_ident_cps_gen. Defined.

          Context (split_types
                   : forall t (idc : ident t), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type)
                  (add_types_from_raw_sig
                   : forall (ridc : raw_ident)
                            (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                            (idt : type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc)))),
                      { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } }).

          Definition split_types_subst_default : forall {t} (idc : ident t) (evm : EvarMap), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * full_type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type
            := fun t idc evm
               => let res := @split_types t idc in
                  existT _ (projT1 res) (Datatypes.fst (projT2 res),
                                         lift_type_of_list_map (@subst_default_kind_of_type evm) (Datatypes.snd (projT2 res))).

          Context (to_type_split_types_subst_default_eq
                   : forall t idc evm,
                      Raw.ident.to_type
                        (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default t idc evm))))
                        (Datatypes.fst (projT2 (split_types_subst_default idc evm)))
                        (Datatypes.snd (projT2 (split_types_subst_default idc evm)))
                      = type.subst_default t evm)
                  (projT1_add_types_from_raw_sig_eq
                   : forall t idc,
                      projT1
                        (add_types_from_raw_sig
                           (projT1 (split_raw_ident_gen t idc))
                           (projT1 (proj1_sig (projT2 (split_raw_ident_gen t idc))))
                           (lift_type_of_list_map
                              (@relax_kind_of_type)
                              (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))))
                      = type.relax t).

          Definition prearg_types : forall {t} (idc : ident t), list Type
            := (fun t idc
                => let st := @split_types t idc in
                   let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                   indep_args pi (Datatypes.fst (projT2 st))).

          Definition strip_types : forall {t} (idc : ident t), raw_ident
            := proj1_sig
                 (@eta_ident_cps_gen
                    _
                    (fun t idc => projT1 (@split_types t idc))).
          Definition arg_types : forall {t} (idc : ident t), list Type
            := proj1_sig (@eta_ident_cps_gen _ (@prearg_types)).

          Definition to_typed : forall {t} (idc : ident t) (evm : EvarMap), type_of_list (arg_types idc) -> Compilers.ident.ident (type.subst_default t evm)
            := fun t (idc : ident t) (evm : EvarMap)
               => proj1_sig
                    (@eta_ident_cps_gen2
                       _ (@prearg_types)
                       (fun t idc arg_types_idc
                        => forall args : type_of_list arg_types_idc,
                            Compilers.ident.ident (type.subst_default t evm)
                       (*let st := @split_types _ idc in
                           let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                           Raw.ident.to_type
                             pi
                             (Datatypes.fst (projT2 st))
                             (lift_type_of_list_map
                                (@subst_default_kind_of_type evm)
                                (Datatypes.snd (projT2 st)))*))
                       (fun t idc args
                        => rew [Compilers.ident.ident] to_type_split_types_subst_default_eq t idc evm in
                            let st := @split_types_subst_default _ idc evm in
                            (@Raw.ident.assemble_ident
                               (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default _ idc evm))))
                               (existT
                                  _ (Datatypes.fst (projT2 st))
                                  (Datatypes.snd (projT2 st), args)))))
                    t idc.

          Definition type_of_list_arg_types_beq : forall t idc, type_of_list (@arg_types t idc) -> type_of_list (@arg_types t idc) -> bool
            := proj1_sig
                 (@eta_ident_cps_gen2
                    _ (@prearg_types)
                    (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
                    (fun t idc
                     => Raw.ident.indep_args_beq _ _)).

          Definition reflect_type_of_list_arg_types_beq : forall {t idc}, reflect_rel (@eq (type_of_list (@arg_types t idc))) (@type_of_list_arg_types_beq t idc)
            := proj1_sig
                 (@eta_ident_cps_gen3
                    _ (@prearg_types)
                    (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
                    (fun t idc => Raw.ident.indep_args_beq _ _)
                    (fun t idc arg_types_idc beq => reflect_rel (@eq (type_of_list arg_types_idc)) beq)
                    (fun t idc => Raw.ident.indep_args_reflect _ _)).

          Definition preof_typed_ident_sig : forall {t} (idc : Compilers.ident.ident t), _
            := fun t idc
               => add_types_from_raw_sig
                    (projT1 (split_raw_ident_gen t idc))
                    (projT1 (proj1_sig (projT2 (split_raw_ident_gen t idc))))
                    (lift_type_of_list_map
                       (@relax_kind_of_type)
                       (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))).
          Definition preof_typed_ident : forall {t} (idc : Compilers.ident.ident t), ident (type.relax t)
            := fun t idc
               => rew [ident] projT1_add_types_from_raw_sig_eq t idc in
                   proj1_sig
                     (projT2
                        (@preof_typed_ident_sig t idc)).
          Definition of_typed_ident : forall {t} (idc : Compilers.ident.ident t), ident (type.relax t)
            := proj1_sig (eta_pattern_ident_cps_gen _ (@preof_typed_ident)).

          Definition arg_types_of_typed_ident : forall {t} (idc : Compilers.ident.ident t), type_of_list (arg_types (of_typed_ident idc)).
          Proof.
            refine (proj1_sig
                      (@pattern.Generate.eta_ident_cps_gen2
                         eta_pattern_ident_cps_gen
                         _ (@preof_typed_ident)
                         (fun t idc of_typed_ident_idc => type_of_list (arg_types of_typed_ident_idc))
                         (fun t idc
                          => match projT1_add_types_from_raw_sig_eq t idc as H'
                                   return type_of_list (arg_types (rew [ident] H' in proj1_sig (projT2 (@preof_typed_ident_sig _ idc))))
                             with
                             | eq_refl
                               => rew <- [type_of_list]
                                      (proj2_sig (eta_ident_cps_gen _ (@prearg_types))
                                                 (projT1 (preof_typed_ident_sig idc))
                                                 (proj1_sig (projT2 (preof_typed_ident_sig idc)))) in
                                   rew <- [fun k' => type_of_list (indep_args (preinfos (raw_ident_infos_of (projT1 k'))) (Datatypes.fst (projT2 k')))]
                                       (proj2_sig (projT2 (@preof_typed_ident_sig t idc))) in
                                   _
                             end))).
            refine (let st := split_raw_ident_gen _ idc in
                    let args := proj1_sig (projT2 st) in
                    Datatypes.snd (projT2 args)).
          Defined.

          Local Notation raw_try_unify_split_args := (@Raw.ident.try_unify_split_args raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of).

          Definition folded_unify : forall {t t'} (pidc : ident t) (idc : Compilers.ident.ident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@arg_types t pidc))
            := fun t t' (pidc : ident t) (idc : Compilers.ident.ident t') (*evm : EvarMap*)
               => proj1_sig
                    (eta_ident_cps_gen_expand_literal
                       _
                       (fun t pidc
                        => proj1_sig
                             (eta_pattern_ident_cps_gen_expand_literal
                                _
                                (fun t' idc
                                 => proj1_sig
                                      (@eta_ident_cps_gen2
                                         _ (@prearg_types)
                                         (fun _ idc arg_types_idc => type_of_list arg_types_idc -> Datatypes.option (type_of_list (@arg_types t pidc)))
                                         (fun t idc
                                          => proj1_sig
                                               (@eta_ident_cps_gen2
                                                  _ (@prearg_types)
                                                  (fun _ pidc arg_types_pidc => type_of_list (@prearg_types _ idc) -> Datatypes.option (type_of_list arg_types_pidc))
                                                  (fun t' pidc idc_indep_args
                                                   => raw_try_unify_split_args
                                                        (*(Datatypes.snd (projT2 (@split_types_subst_default _ idc evm)))
                                                    (Datatypes.snd (projT2 (@split_types_subst_default _ pidc evm)))*)
                                                        idc_indep_args))
                                               _ pidc))
                                      _ (of_typed_ident idc) (@arg_types_of_typed_ident _ idc)))
                             _ idc))
                    _ pidc.
        End __.

        Module Tactics.
          Ltac build_eta_ident_cps eta_pattern_ident_cps_gen :=
            (eval cbv [eta_pattern_ident_cps_gen proj1_sig] in
                (fun T t idc f
                 => proj1_sig (eta_pattern_ident_cps_gen (fun t _ => T t) f) t idc)).
          Ltac make_eta_ident_cps eta_pattern_ident_cps_gen :=
            let res := build_eta_ident_cps eta_pattern_ident_cps_gen in refine res.

          Ltac build_all_idents ident := build_all_idents_gen (forall t (idc : ident t), True).
          Ltac make_all_idents ident := let v := build_all_idents ident in refine v.

          Ltac collect_args' f cur :=
            lazymatch f with
            | ?f ?x => collect_args' f (x, cur)
            | _ => cur
            end.
          Ltac collect_args f := collect_args' f Datatypes.tt.

          Ltac build_split_types ident raw_ident raw_ident_infos_of all_idents all_raw_idents :=
            let t := fresh "t" in
            let idc := fresh "idc" in
            let idc' := fresh "idc'" in
            let v := constr:(
                       fun t (idc : ident t)
                       => let idc' := idc in
                          ltac:(destruct idc;
                                let idc := (eval cbv [idc'] in idc') in
                                let ctor := head idc in
                                let all_idents := (eval cbv [all_idents] in all_idents) in
                                let all_ridents := (eval cbv [all_raw_idents] in all_raw_idents) in
                                let v := find_ctor ctor all_idents all_ridents in
                                let args := collect_args idc in
                                let f := (eval cbv [list_unapp_type_of_list dep_types preinfos raw_ident_infos_of indep_types List.app List.map Type_of_kind_of_type] in
                                             (@list_unapp_type_of_list
                                                (dep_types (preinfos (raw_ident_infos_of v)))
                                                (List.map Type_of_kind_of_type (indep_types (preinfos (raw_ident_infos_of v)))))) in
                                refine (existT
                                          _
                                          v
                                          (f args)))
                          : { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type) in
            let v := (eval cbn [Datatypes.fst Datatypes.snd] in v) in
            v.
          Ltac make_split_types ident raw_ident raw_ident_infos_of all_idents all_raw_idents := let v := build_split_types ident raw_ident raw_ident_infos_of all_idents all_raw_idents in refine v.

          Ltac build_add_types_from_raw_sig ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types :=
            let ridc := fresh "ridc" in
            let ridc' := fresh "ridc'" in
            let dt := fresh "dt" in
            let idt := fresh "idt" in
            let v := (eval cbv [id] in
                         (fun (ridc : raw_ident)
                              (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                              (idt : type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))))
                          => let ridc' := ridc in
                             ltac:(destruct ridc;
                                   let ridc := (eval cbv [ridc'] in ridc') in
                                   let all_idents := (eval cbv [all_idents] in all_idents) in
                                   let all_ridents := (eval cbv [all_raw_idents] in all_raw_idents) in
                                   let v := find_ctor ridc all_ridents all_idents in
                                   let v := (eval cbv [projT2] in (projT2 v)) in
                                   eexists;
                                   unshelve eexists;
                                   [ eapply v
                                   | cbv [split_types]; apply f_equal;
                                     repeat match goal with
                                            | [ |- (_, _) = _ ] => apply Prod.path_prod; cbn [Datatypes.fst Datatypes.snd]
                                            | [ |- Datatypes.tt = ?x ] => destruct x; reflexivity
                                            | [ |- ?ev = _ ] => is_evar ev; reflexivity
                                            end ])
                             : { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } })) in
            v.
          Ltac make_add_types_from_raw_sig ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types :=
            let v := build_add_types_from_raw_sig ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types in refine v.

          Ltac prove_to_type_split_types_subst_default_eq _ :=
            let t := fresh "t" in
            let idc := fresh "idc" in
            let evm := fresh "evm" in
            intros t idc evm;
            destruct idc; cbv -[type.subst_default base.subst_default];
            cbn [type.subst_default base.subst_default]; reflexivity.
          Ltac build_to_type_split_types_subst_default_eq raw_ident raw_ident_infos_of ident split_types :=
            constr:(ltac:(prove_to_type_split_types_subst_default_eq ())
                    : forall t idc evm,
                       Raw.ident.to_type
                         (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default raw_ident raw_ident_infos_of ident split_types t idc evm))))
                         (Datatypes.fst (projT2 (@split_types_subst_default raw_ident raw_ident_infos_of ident split_types t idc evm)))
                         (Datatypes.snd (projT2 (@split_types_subst_default raw_ident raw_ident_infos_of ident split_types t idc evm)))
                       = type.subst_default t evm).

          Ltac make_to_type_split_types_subst_default_eq raw_ident raw_ident_infos_of ident split_types :=
            let res := build_to_type_split_types_subst_default_eq raw_ident raw_ident_infos_of ident split_types in refine res.

          Ltac prove_projT1_add_types_from_raw_sig_eq _ :=
            let t := fresh "t" in
            let idc := fresh "idc" in
            intros t idc;
            destruct idc; cbv -[type.relax base.relax];
            cbn [type.relax base.relax]; reflexivity.
          Ltac build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen :=
            constr:(ltac:(prove_projT1_add_types_from_raw_sig_eq ())
                    : forall t idc,
                       projT1
                         (add_types_from_raw_sig
                            (projT1 (split_raw_ident_gen t idc))
                            (projT1 (proj1_sig (projT2 (split_raw_ident_gen t idc))))
                            (lift_type_of_list_map
                               (@relax_kind_of_type)
                               (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))))
                       = type.relax t).
          Ltac make_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen :=
            let res := build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen in refine res.

          Ltac build_arg_types_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types :=
            (eval cbv -[base.interp] in
                (@arg_types raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types)).
          Ltac make_arg_types_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types :=
            let res := build_arg_types_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types in refine res.

          Ltac build_type_of_list_arg_types_beq_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded :=
            (eval cbv -[Prod.prod_beq arg_types_unfolded type_of_list base.interp_beq base.base_interp_beq Z.eqb base.base_interp ZRange.zrange_beq] in
                (proj1_sig
                   (@eta_ident_cps_gen
                      (fun t idc => type_of_list (@arg_types_unfolded t idc) -> type_of_list (@arg_types_unfolded t idc) -> bool)
                      (@type_of_list_arg_types_beq raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types)))).
          Ltac make_type_of_list_arg_types_beq_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded :=
            let res := build_type_of_list_arg_types_beq_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded in refine res.

          Ltac build_to_typed_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded :=
            let v := (eval cbv -[type.subst_default base.subst_default arg_types_unfolded type_of_list base.base_interp Datatypes.fst Datatypes.snd] in
                         (fun t (idc : ident t) (evm : EvarMap)
                          => proj1_sig
                               (@eta_ident_cps_gen
                                  (fun t idc => type_of_list (@arg_types_unfolded t idc) -> Compilers.ident.ident (type.subst_default t evm))
                                  (fun t idc => @to_typed raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq t idc evm))
                               t idc)) in
            let v := (eval cbn [Datatypes.fst Datatypes.snd type_of_list] in v) in
            v.
          Ltac make_to_typed_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded :=
            let res := build_to_typed_unfolded raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded in refine res.

          Ltac build_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
            let v := (eval cbv -[type.relax base.relax] in
                         (@of_typed_ident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)) in
            let v := (eval cbn [type.relax base.relax] in v) in
            v.
          Ltac make_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
            let res := build_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in refine res.

          Ltac build_arg_types_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded :=
            (eval cbv -[type.relax base.relax type_of_list of_typed_ident arg_types_unfolded of_typed_ident_unfolded base.base_interp] in
                (proj1_sig
                   (@eta_pattern_ident_cps_gen
                      (fun t idc => type_of_list (@arg_types_unfolded _ (@of_typed_ident_unfolded _ idc)))
                      (@arg_types_of_typed_ident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)))).
          Ltac make_arg_types_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded :=
            let res := build_arg_types_of_typed_ident_unfolded eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded in refine res.

          Ltac build_unify eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
            let v := (eval vm_compute in (@folded_unify eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)) in
            constr:(v <: forall {t t'} (pidc : ident t) (idc : Compilers.ident.ident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@arg_types raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types t pidc))).
          Ltac make_unify eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
            let res := build_unify eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in refine res.

          Module PrintIdent.
            Ltac map_projT2 tac ls :=
              lazymatch ls with
              | Datatypes.nil => idtac
              | Datatypes.cons (existT _ _ ?v) ?ls
                => tac v; map_projT2 tac ls
              end.
            Ltac fill_forall_args v :=
              let T := type of v in
              lazymatch (eval cbv beta in T) with
              | ?A -> ?B => v
              | forall x : ?A, _ => fill_forall_args open_constr:(v _)
              | _ => v
              end.
            Ltac strip_nondep T :=
              lazymatch T with
              | ?A -> ?B => strip_nondep B
              | forall x : ?A, ?B
                => let B' := fresh in
                   constr:(forall x : A,
                              match B return _ with
                              | B' => ltac:(let B := (eval cbv [B'] in B') in
                                            clear B';
                                            let B := strip_nondep B in
                                            exact B)
                              end)
              | ?T => T
              end.
            Ltac print_ident :=
              let all_idents := Compilers.pattern.Generate.Tactics.build_all_idents in
              epose proof (_ : type -> Set) as ident;
              idtac "      Inductive ident : type -> Set :=";
              let v := (eval cbv [Compilers.base.interp] in all_idents) in
              map_projT2 ltac:(fun v
                               => let T := type of v in
                                  let T := (eval cbv [Compilers.base.interp] in T) in
                                  let T := strip_nondep T in
                                  let T := (eval pattern Compilers.base.type.type, Compilers.base.type.prod, Compilers.base.type.list, Compilers.base.type.option, (@Compilers.base.type.type_base), (@Compilers.ident) in T) in
                                  let T := lazymatch T with
                                           | ?f _ _ _ _ _ _ => f
                                           end in
                                  let T := (eval cbv beta in
                                               (T base.type.type base.type.prod base.type.list base.type.option (@base.type.type_base) (@ident))) in
                                  let v := fill_forall_args v in
                                  idtac "        |" v ":" T) v;
              idtac "      .".
            Import Compilers.ident.
            Local Set Printing Coercions.
            Local Unset Printing Notations.
            Local Set Printing Width 10000.
            (*Goal True. print_ident. Abort.*)
          End PrintIdent.
        End Tactics.
      End ident.
    End Generate.
    Import Generate.Tactics.

    Definition all_idents : list { T : Type & T } := ltac:(make_all_idents).

    Definition ident_index : forall t, ident t -> nat
      := ltac:(make_ident_index (forall t, ident t -> nat) all_idents).

    Definition eta_ident_cps_gen
      : forall (T : forall t, Compilers.ident.ident t -> Type)
               (f : forall t idc, T t idc),
        { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }
      := ltac:(make_eta_ident_cps_gen Compilers.ident.ident).

    Definition eta_ident_cps_gen_expand_literal
      : forall (T : forall t, Compilers.ident.ident t -> Type)
               (f : forall t idc, T t idc),
        { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }
      := ltac:(make_eta_ident_cps_gen_expand_literal Compilers.ident.ident).

    Local Notation eta_ident_cps_gen2 := (@Generate.eta_ident_cps_gen2 (@eta_ident_cps_gen)).
    Local Notation eta_ident_cps_gen3 := (@Generate.eta_ident_cps_gen3 (@eta_ident_cps_gen)).

    Module Raw.
      Module ident.
        Module PrintIdent.
          Import Generate.Raw.ident.Tactics.MakeIdent.
          Import Compilers.ident.
          Local Unset Printing Notations.
          (*Goal True. print_ident. Abort.*)
        End PrintIdent.

        Local Unset Decidable Equality Schemes.
        Local Unset Boolean Equality Schemes.
        Inductive ident :=
        | Literal
        | Nat_succ
        | Nat_pred
        | Nat_max
        | Nat_mul
        | Nat_add
        | Nat_sub
        | Nat_eqb
        | nil
        | cons
        | pair
        | fst
        | snd
        | prod_rect
        | bool_rect
        | nat_rect
        | nat_rect_arrow
        | eager_nat_rect
        | eager_nat_rect_arrow
        | list_rect
        | list_rect_arrow
        | eager_list_rect
        | eager_list_rect_arrow
        | list_case
        | List_length
        | List_seq
        | List_firstn
        | List_skipn
        | List_repeat
        | List_combine
        | List_map
        | List_app
        | List_rev
        | List_flat_map
        | List_partition
        | List_fold_right
        | List_update_nth
        | List_nth_default
        | eager_List_nth_default
        | Z_add
        | Z_mul
        | Z_pow
        | Z_sub
        | Z_opp
        | Z_div
        | Z_modulo
        | Z_log2
        | Z_log2_up
        | Z_eqb
        | Z_leb
        | Z_ltb
        | Z_geb
        | Z_gtb
        | Z_of_nat
        | Z_to_nat
        | Z_shiftr
        | Z_shiftl
        | Z_land
        | Z_lor
        | Z_min
        | Z_max
        | Z_bneg
        | Z_lnot_modulo
        | Z_mul_split
        | Z_add_get_carry
        | Z_add_with_carry
        | Z_add_with_get_carry
        | Z_sub_get_borrow
        | Z_sub_with_get_borrow
        | Z_zselect
        | Z_add_modulo
        | Z_rshi
        | Z_cc_m
        | Z_combine_at_bitwidth
        | Z_cast
        | Z_cast2
        | option_Some
        | option_None
        | option_rect
        | Build_zrange
        | zrange_rect
        | fancy_add
        | fancy_addc
        | fancy_sub
        | fancy_subb
        | fancy_mulll
        | fancy_mullh
        | fancy_mulhl
        | fancy_mulhh
        | fancy_rshi
        | fancy_selc
        | fancy_selm
        | fancy_sell
        | fancy_addm
        .

        Import Generate.Raw.ident.
        Import Generate.Raw.ident.Tactics.

        Definition all_idents : list ident := ltac:(make_all_idents ident).

        Definition ident_index : ident -> nat
          := ltac:(make_ident_index (ident -> nat) all_idents).

        Definition ident_index_idempotent : forall idc, List.nth_error all_idents (ident_index idc) = Some idc
          := ltac:(make_ident_index_idempotent all_idents ident_index).

        Definition eta_ident_cps_gen
          : forall (T : ident -> Type)
                   (f : forall idc, T idc),
            { f' : forall idc, T idc | forall idc, f' idc = f idc }
          := ltac:(make_eta_ident_cps_gen ident).
        Notation eta_ident_cps_gen2 := (@eta_ident_cps_gen2 ident eta_ident_cps_gen).
        Notation eta_ident_cps_gen3 := (@eta_ident_cps_gen3 ident eta_ident_cps_gen).
        Notation ident_beq := (@ident_beq ident ident_index eta_ident_cps_gen).
        Notation ident_lb := (@ident_lb ident ident_index eta_ident_cps_gen).
        Notation ident_index_inj := (@ident_index_inj ident all_idents ident_index ident_index_idempotent).
        Notation ident_bl := (@ident_bl ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen).
        Notation ident_beq_if := (@ident_beq_if ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen).
        Notation ident_transport_opt := (@ident_transport_opt ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen).
        Notation ident_to_cident := (@ident_to_cident pattern.all_idents ident ident_index eta_ident_cps_gen).

        Definition ident_infos_of : ident -> ident_infos := ltac:(make_ident_infos_of (@ident_to_cident)).
        Definition split_ident_gen
          : forall t (idc : Compilers.ident.ident t),
            { ridc : ident & { args : ident_args (ident_infos_of ridc)
                             | { pf : _ = _
                               | idc = rew [Compilers.ident.ident] pf in assemble_ident args } } }
          := ltac:(make_split_ident_gen ident ident_infos_of all_idents pattern.all_idents).

        Notation prefull_types := (@prefull_types ident ident_infos_of).
        Notation full_types := (@full_types ident eta_ident_cps_gen ident_infos_of).
        Notation is_simple := (@is_simple ident ident_infos_of).
        Notation type_of := (@type_of ident eta_ident_cps_gen ident_infos_of).
        Notation folded_invert_bind_args := (@folded_invert_bind_args (@pattern.eta_ident_cps_gen) ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen).

        Definition invert_bind_args : forall {t} (idc : Compilers.ident.ident t) (pidc : ident), Datatypes.option (full_types pidc)
          := ltac:(make_invert_bind_args (@pattern.eta_ident_cps_gen) ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen).

        Notation to_typed := (@to_typed ident eta_ident_cps_gen ident_infos_of).
        Notation try_unify_split_args := (@try_unify_split_args ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of).
      End ident.
      Notation ident := ident.ident.
    End Raw.

    Module ident.
      Import Generate.
      Import Generate.ident.
      Import Generate.ident.Tactics.

      Definition eta_ident_cps
        : forall (T : Compilers.type Compilers.base.type -> Type) t (idc : Compilers.ident.ident t)
                 (f : forall t', Compilers.ident.ident t' -> T t'),
          T t
        := ltac:(make_eta_ident_cps (@pattern.eta_ident_cps_gen)).

      Module PrintIdent.
        Import Generate.ident.Tactics.PrintIdent.
        Import Compilers.ident.
        Local Set Printing Coercions.
        Local Unset Printing Notations.
        Local Set Printing Width 10000.
        (*Goal True. print_ident. Abort.*)
      End PrintIdent.
      Local Unset Decidable Equality Schemes.
      Inductive ident : type -> Set :=
      | Literal : (forall t : base.type.base, ident (type.base (base.type.type_base t)))
      | Nat_succ : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat))))
      | Nat_pred : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat))))
      | Nat_max : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_mul : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_add : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_sub : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.nat)))))
      | Nat_eqb : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.bool)))))
      | nil : (forall t : base.type.type, ident (type.base (base.type.list t)))
      | cons : (forall t : base.type.type, ident (type.arrow (type.base t) (type.arrow (type.base (base.type.list t)) (type.base (base.type.list t)))))
      | pair : (forall A B : base.type.type, ident (type.arrow (type.base A) (type.arrow (type.base B) (type.base (base.type.prod A B)))))
      | fst : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.prod A B)) (type.base A)))
      | snd : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.prod A B)) (type.base B)))
      | prod_rect : (forall A B T : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.arrow (type.base B) (type.base T))) (type.arrow (type.base (base.type.prod A B)) (type.base T))))
      | bool_rect : (forall T : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base T)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base T)) (type.arrow (type.base (base.type.type_base base.type.bool)) (type.base T)))))
      | nat_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base P)))))
      | nat_rect_arrow : (forall P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base Q))))))
      | eager_nat_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base P)))))
      | eager_nat_rect_arrow : (forall P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q)))) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base P) (type.base Q))))))
      | list_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | list_rect_arrow : (forall A P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | eager_list_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base P)))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | eager_list_rect_arrow : (forall A P Q : base.type.type, ident (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.arrow (type.arrow (type.base P) (type.base Q)) (type.arrow (type.base P) (type.base Q))))) (type.arrow (type.base (base.type.list A)) (type.arrow (type.base P) (type.base Q))))))
      | list_case : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.arrow (type.base A) (type.arrow (type.base (base.type.list A)) (type.base P))) (type.arrow (type.base (base.type.list A)) (type.base P)))))
      | List_length : (forall T : base.type.type, ident (type.arrow (type.base (base.type.list T)) (type.base (base.type.type_base base.type.nat))))
      | List_seq : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.list (base.type.type_base base.type.nat))))))
      | List_firstn : (forall A : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_skipn : (forall A : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_repeat : (forall A : base.type.type, ident (type.arrow (type.base A) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.list A)))))
      | List_combine : (forall A B : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.arrow (type.base (base.type.list B)) (type.base (base.type.list (base.type.prod A B))))))
      | List_map : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base B)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list B)))))
      | List_app : (forall A : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A)))))
      | List_rev : (forall A : base.type.type, ident (type.arrow (type.base (base.type.list A)) (type.base (base.type.list A))))
      | List_flat_map : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base (base.type.list B))) (type.arrow (type.base (base.type.list A)) (type.base (base.type.list B)))))
      | List_partition : (forall A : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base (base.type.type_base base.type.bool))) (type.arrow (type.base (base.type.list A)) (type.base (base.type.prod (base.type.list A) (base.type.list A))))))
      | List_fold_right : (forall A B : base.type.type, ident (type.arrow (type.arrow (type.base B) (type.arrow (type.base A) (type.base A))) (type.arrow (type.base A) (type.arrow (type.base (base.type.list B)) (type.base A)))))
      | List_update_nth : (forall T : base.type.type, ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.arrow (type.arrow (type.base T) (type.base T)) (type.arrow (type.base (base.type.list T)) (type.base (base.type.list T))))))
      | List_nth_default : (forall T : base.type.type, ident (type.arrow (type.base T) (type.arrow (type.base (base.type.list T)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base T)))))
      | eager_List_nth_default : (forall T : base.type.type, ident (type.arrow (type.base T) (type.arrow (type.base (base.type.list T)) (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base T)))))
      | Z_add : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_mul : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_pow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_sub : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_opp : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_div : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_log2 : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_log2_up : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_eqb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_leb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_ltb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_geb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_gtb : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.bool)))))
      | Z_of_nat : (ident (type.arrow (type.base (base.type.type_base base.type.nat)) (type.base (base.type.type_base base.type.Z))))
      | Z_to_nat : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.nat))))
      | Z_shiftr : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_shiftl : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_land : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_lor : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_min : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_max : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_bneg : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_lnot_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_mul_split : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_add_get_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_add_with_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_add_with_get_carry : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))))))))
      | Z_sub_get_borrow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))))
      | Z_sub_with_get_borrow : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))))))))
      | Z_zselect : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_add_modulo : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_rshi : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))))
      | Z_cc_m : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z)))))
      | Z_combine_at_bitwidth : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))))
      | Z_cast : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.Z))))
      | Z_cast2 : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | option_Some : (forall A : base.type.type, ident (type.arrow (type.base A) (type.base (base.type.option A))))
      | option_None : (forall A : base.type.type, ident (type.base (base.type.option A)))
      | option_rect : (forall A P : base.type.type, ident (type.arrow (type.arrow (type.base A) (type.base P)) (type.arrow (type.arrow (type.base (base.type.type_base base.type.unit)) (type.base P)) (type.arrow (type.base (base.type.option A)) (type.base P)))))
      | Build_zrange : (ident (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base (base.type.type_base base.type.zrange)))))
      | zrange_rect : (forall P : base.type.type, ident (type.arrow (type.arrow (type.base (base.type.type_base base.type.Z)) (type.arrow (type.base (base.type.type_base base.type.Z)) (type.base P))) (type.arrow (type.base (base.type.type_base base.type.zrange)) (type.base P))))
      | fancy_add : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_addc : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_sub : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_subb : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))))
      | fancy_mulll : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mullh : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mulhl : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_mulhh : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_rshi : (ident (type.arrow (type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_selc : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_selm : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_sell : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      | fancy_addm : (ident (type.arrow (type.base (base.type.prod (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)) (base.type.type_base base.type.Z))) (type.base (base.type.type_base base.type.Z))))
      .

      Definition all_idents : list { T : Type & T } := ltac:(make_all_idents ident).

      Definition eta_ident_cps_gen
        : forall (T : forall t, ident t -> Type)
                 (f : forall t idc, T t idc),
          { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }
        := ltac:(make_eta_ident_cps_gen ident).

      Definition eta_ident_cps_gen_expand_literal
        : forall (T : forall t, ident t -> Type)
                 (f : forall t idc, T t idc),
          { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }
        := ltac:(make_eta_ident_cps_gen_expand_literal ident).

      Notation eta_ident_cps_gen2 := (@eta_ident_cps_gen2 ident eta_ident_cps_gen).
      Notation eta_ident_cps_gen3 := (@eta_ident_cps_gen3 ident eta_ident_cps_gen).
      Local Notation dep_types := Generate.Raw.ident.dep_types.
      Local Notation preinfos := Generate.Raw.ident.preinfos.
      Local Notation indep_types := Generate.Raw.ident.indep_types.
      Local Notation indep_args := Generate.Raw.ident.indep_args.
      Local Notation iffT A B := ((A -> B) * (B -> A))%type.

      Definition split_types : forall t (idc : ident t), { ridc : Raw.ident & type_of_list (dep_types (preinfos (Raw.ident.ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (Raw.ident.ident_infos_of ridc))) }%type
        := ltac:(make_split_types ident Raw.ident Raw.ident.ident_infos_of all_idents Raw.ident.all_idents).

      Definition add_types_from_raw_sig
        : forall (ridc : Raw.ident)
                 (dt : type_of_list (dep_types (preinfos (Raw.ident.ident_infos_of ridc))))
                 (idt : type_of_list_of_kind (indep_types (preinfos (Raw.ident.ident_infos_of ridc)))),
          { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } }
        := ltac:(make_add_types_from_raw_sig ident Raw.ident.ident Raw.ident.ident_infos_of all_idents Raw.ident.all_idents split_types).

      Notation split_types_subst_default := (@split_types_subst_default Raw.ident Raw.ident.ident_infos_of ident split_types).

      Definition to_type_split_types_subst_default_eq
        : forall t idc evm,
          Raw.ident.to_type
            (preinfos (Raw.ident.ident_infos_of (projT1 (@split_types_subst_default t idc evm))))
            (Datatypes.fst (projT2 (split_types_subst_default idc evm)))
            (Datatypes.snd (projT2 (split_types_subst_default idc evm)))
          = type.subst_default t evm
        := ltac:(make_to_type_split_types_subst_default_eq Raw.ident Raw.ident.ident_infos_of ident split_types).

      Definition projT1_add_types_from_raw_sig_eq
        : forall t idc,
          projT1
            (add_types_from_raw_sig
               (projT1 (@Raw.ident.split_ident_gen t idc))
               (projT1 (proj1_sig (projT2 (@Raw.ident.split_ident_gen t idc))))
               (lift_type_of_list_map
                  (@relax_kind_of_type)
                  (Datatypes.fst (projT2 (proj1_sig (projT2 (@Raw.ident.split_ident_gen t idc)))))))
          = type.relax t
        := ltac:(make_projT1_add_types_from_raw_sig_eq (@add_types_from_raw_sig) (@Raw.ident.split_ident_gen)).

      Notation prearg_types := (@prearg_types Raw.ident Raw.ident.ident_infos_of ident split_types).
      Notation strip_types := (@strip_types Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types).
      Notation arg_types := (@arg_types Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types).
      Notation to_typed := (@to_typed Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types (@to_type_split_types_subst_default_eq)).
      Notation type_of_list_arg_types_beq := (@type_of_list_arg_types_beq Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types).
      Notation reflect_type_of_list_arg_types_beq := (@reflect_type_of_list_arg_types_beq Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types).
      Notation preof_typed_ident_sig := (@preof_typed_ident_sig Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident split_types add_types_from_raw_sig).
      Notation preof_typed_ident := (@preof_typed_ident Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).
      Notation of_typed_ident := (@of_typed_ident pattern.eta_ident_cps_gen Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).
      Notation arg_types_of_typed_ident := (@arg_types_of_typed_ident pattern.eta_ident_cps_gen Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).
      Notation folded_unify := (@folded_unify pattern.eta_ident_cps_gen pattern.eta_ident_cps_gen_expand_literal Raw.ident Raw.ident.all_idents Raw.ident.ident_index Raw.ident.ident_index_idempotent Raw.ident.eta_ident_cps_gen Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).

      Definition arg_types_unfolded : forall t (idc : ident t), list Type
        := ltac:(make_arg_types_unfolded Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types).

      Definition to_typed_unfolded : forall t (idc : ident t) (evm : EvarMap), type_of_list (@arg_types_unfolded _ idc) -> Compilers.ident.ident (type.subst_default t evm)
        := ltac:(make_to_typed_unfolded Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded).

      Definition type_of_list_arg_types_beq_unfolded : forall t idc, type_of_list (@arg_types_unfolded t idc) -> type_of_list (@arg_types_unfolded t idc) -> bool
        := ltac:(make_type_of_list_arg_types_beq_unfolded Raw.ident Raw.ident.ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded).

      Definition of_typed_ident_unfolded : forall t (idc : Compilers.ident.ident t), ident (type.relax t)
        := ltac:(make_of_typed_ident_unfolded pattern.eta_ident_cps_gen Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).

      Definition arg_types_of_typed_ident_unfolded : forall t (idc : Compilers.ident.ident t), type_of_list (arg_types_unfolded _ (of_typed_ident_unfolded _ idc))
        := ltac:(make_arg_types_of_typed_ident_unfolded pattern.eta_ident_cps_gen Raw.ident Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded).

      Definition unify : forall {t t'} (pidc : ident t) (idc : Compilers.ident.ident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@arg_types t pidc))
        := ltac:(make_unify pattern.eta_ident_cps_gen pattern.eta_ident_cps_gen_expand_literal Raw.ident Raw.ident.all_idents Raw.ident.ident_index Raw.ident.ident_index_idempotent Raw.ident.eta_ident_cps_gen Raw.ident.ident_infos_of Raw.ident.split_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq).
    End ident.
  End pattern.
End Compilers.
