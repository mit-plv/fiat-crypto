Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.JMeq.
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
            => (F T (Datatypes.fst v_vs),
                @lift_type_of_list_map A Ts P1 P2 F (Datatypes.snd v_vs))
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

    Module Import Tactics.
      Ltac build_all_idents_gen P :=
        let idc' := fresh "idc'" in
        let res := open_constr:(_ : list { T : Type & T }) in
        let fill_next v :=
            let next := match res with
                        | context[?ev]
                          => let __ := match goal with _ => is_evar ev end in
                             ev
                        end in
            let __ := open_constr:(eq_refl : next = v) in
            constr:(I) in
        let __ := open_constr:(
                    ltac:(intros;
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

      Ltac make_eta_ident_cps_gen_gen do_destruct_base :=
        unshelve eexists; intros;
        lazymatch goal with idc : _ |- _ => destruct idc end;
        lazymatch do_destruct_base with
        | true => repeat match goal with t : base.type.base |- _ => destruct t end
        | false => idtac
        end;
        shelve_unifiable; reflexivity.
      Ltac make_eta_ident_cps_gen := make_eta_ident_cps_gen_gen false.
      Ltac make_eta_ident_cps_gen_expand_literal := make_eta_ident_cps_gen_gen true.

      Ltac get_ctor_number' ctor all_idents :=
        lazymatch all_idents with
        | Datatypes.cons ctor _ => Datatypes.O
        | Datatypes.cons (existT _ _ ctor) _ => Datatypes.O
        | Datatypes.cons _ ?xs => let v := get_ctor_number' ctor xs in
                                  constr:(Datatypes.S v)
        end.

      Ltac find_ctor ctor from_all_idents to_all_idents :=
        let n := get_ctor_number' ctor from_all_idents in
        let v := (eval cbv [List.nth] in (fun default => List.nth n to_all_idents default)) in
        let v := lazymatch v with
                 | (fun _ => ?v) => v
                 | _ => constr_fail_with ltac:(fun _ => fail 1 "Could not find" ctor "from" from_all_idents "(index" n ") in" to_all_idents "(failed to eliminate dependency on dummy default argument in" v ")")
                 end in
        v.
    End Tactics.

    Definition all_idents : list { T : Type & T } := ltac:(make_all_idents).

    Definition eta_ident_cps_gen
               {T : forall t, Compilers.ident.ident t -> Type}
               (f : forall t idc, T t idc)
      : { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }.
    Proof. make_eta_ident_cps_gen. Defined.

    Definition eta_ident_cps_gen_expand_literal
               {T : forall t, Compilers.ident.ident t -> Type}
               (f : forall t idc, T t idc)
      : { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }.
    Proof. make_eta_ident_cps_gen_expand_literal. Defined.

    Definition eta_ident_cps_gen2
               {T0 : forall t, Compilers.ident.ident t -> Type}
               (f0 : forall t idc, T0 t idc)
               {T1 : forall t (idc : Compilers.ident.ident t), T0 t idc -> Type}
               (f1 : forall t idc, T1 t idc (f0 t idc))
      : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc).
    Proof. intros t idc; cbv [proj1_sig eta_ident_cps_gen]; destruct idc; exact (f1 _ _). Defined.

    Definition eta_ident_cps_gen3
               {T0 : forall t, Compilers.ident.ident t -> Type}
               (f0 : forall t idc, T0 t idc)
               {T1 : forall t (idc : Compilers.ident.ident t), T0 t idc -> Type}
               (f1 : forall t idc, T1 t idc (f0 t idc))
               {T2 : forall t idc x, T1 t idc x -> Type}
               (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
      : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (@eta_ident_cps_gen2 T0 f0 T1 f1 t idc).
    Proof. intros t idc; cbv [proj1_sig eta_ident_cps_gen eta_ident_cps_gen2]; destruct idc; exact (f2 _ _). Defined.

    Module Raw.
      Module ident.
        Local Unset Decidable Equality Schemes.
        Module MakeIdent.
          Import Compilers.ident.
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
            idtac "        Inductive ident :=";
            let v := (eval cbv [pattern.all_idents] in pattern.all_idents) in
            map_projT2 ltac:(fun v => let v := fill_forall_args v in idtac "        |" v) v;
            idtac "        .".
          Local Unset Printing Notations.
          (*Goal True. print_ident. Abort.*)
        End MakeIdent.
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

        Module Import Tactics.
          Ltac map_projT2 ls :=
            lazymatch eval cbv beta in ls with
            | Datatypes.nil => uconstr:(Datatypes.nil)
            | Datatypes.cons (existT _ _ ?v) ?ls
              => let ls' := map_projT2 ls in
                 constr:(Datatypes.cons v ls')
            end.

          Ltac build_all_idents :=
            let v := build_all_idents_gen (ident -> True) in
            map_projT2 v.
          Ltac make_all_idents := let v := build_all_idents in refine v.
        End Tactics.

        Definition all_idents : list ident := ltac:(make_all_idents).

        Definition eta_ident_cps_gen {T : ident -> Type}
                   (f : forall idc, T idc)

          : { f' : forall idc, T idc | forall idc, f' idc = f idc }.
        Proof. make_eta_ident_cps_gen. Defined.

        Definition eta_ident_cps_gen2
                   {T0 : ident -> Type}
                   (f0 : forall idc, T0 idc)
                   {T1 : forall idc, T0 idc -> Type}
                   (f1 : forall idc, T1 idc (f0 idc))
          : forall idc, T1 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc).
        Proof. intros idc; cbv [proj1_sig eta_ident_cps_gen]; destruct idc; exact (f1 _). Defined.

        Definition eta_ident_cps_gen3
                   {T0 : ident -> Type}
                   (f0 : forall idc, T0 idc)
                   {T1 : forall idc, T0 idc -> Type}
                   (f1 : forall idc, T1 idc (f0 idc))
                   {T2 : forall idc x, T1 idc x -> Type}
                   (f2 : forall idc, T2 idc (f0 idc) (f1 idc))
          : forall idc, T2 idc (proj1_sig (@eta_ident_cps_gen T0 f0) idc) (@eta_ident_cps_gen2 T0 f0 T1 f1 idc).
        Proof. intros idc; cbv [proj1_sig eta_ident_cps_gen eta_ident_cps_gen2]; destruct idc; exact (f2 _). Defined.

        Definition ident_lb (x y : ident) : x = y -> ident_beq x y = true.
        Proof. intro H; subst y; destruct x; reflexivity. Defined.
        Definition ident_beq_if (x y : ident) : if ident_beq x y then x = y else True.
        Proof. destruct x, y; cbv; constructor. Defined.
        Definition ident_bl (x y : ident) : ident_beq x y = true -> x = y.
        Proof.
          generalize (ident_beq_if x y); destruct (ident_beq x y); intros;
            first [ assumption | exfalso; apply Bool.diff_false_true; assumption ].
        Defined.

        Definition ident_transport_opt (P : ident -> Type) {x y : ident} : P x -> Datatypes.option (P y)
          := Eval cbv [ident_beq ident_beq_if] in
              fun v
              => (if ident_beq x y as b return (if b then x = y else True) -> _
                  then fun pf => Datatypes.Some
                                   match pf in (_ = y) return P y with
                                   | eq_refl => v
                                   end
                  else fun _ => Datatypes.None)
                   (@ident_beq_if x y).

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
            : forall x, reflect_rel (@eq (type_of_list (indep_args preinfos x))) (indep_args_beq x)
          }.

        Definition ident_args (pi : preident_infos)
          := { t : type_of_list (dep_types pi) & type_of_list_of_kind (indep_types pi) * type_of_list (indep_args pi t) }%type.

        Definition assemble_ident {pi} (args : ident_args pi)
          := to_ident pi (projT1 args) (Datatypes.fst (projT2 args)) (Datatypes.snd (projT2 args)).

        Ltac build_ident_to_cident :=
          let v
              := (eval cbv [proj1_sig eta_ident_cps_gen List.find List.combine all_idents pattern.all_idents ident_beq] in
                     (fun default
                      => proj1_sig
                           (@eta_ident_cps_gen
                              (fun _ => { T : Type & T })
                              (fun idc
                               => match List.find
                                          (fun '(idc', v) => ident_beq idc idc')
                                          (List.combine all_idents pattern.all_idents) with
                                  | Datatypes.Some (_, v) => v
                                  | Datatypes.None => default
                                  end)))) in
          let v := strip_default v in
          v.
        Ltac make_ident_to_cident := let v := build_ident_to_cident in refine v.

        Definition ident_to_cident : ident -> { T : Type & T } := ltac:(make_ident_to_cident).

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

        Ltac build_ident_infos_of :=
          let idc := fresh "idc" in
          let T := fresh in
          let v
              := constr:(
                   fun idc : ident
                   => match ident_to_cident idc return ident_infos with
                      | T
                        => ltac:(destruct idc;
                                 let T := (eval cbv [T ident_to_cident projT2] in (projT2 T)) in
                                 let v := fun_to_curried_ident_infos T in
                                 let v := (eval cbv [type_of_list List.map Type_of_kind_of_type] in v) in
                                 let c := constr:(@Build_ident_infos v) in
                                 let T := type of c in
                                 let T := (eval cbv [dep_types indep_types indep_args type_of_list List.map Type_of_kind_of_type] in T) in
                                 refine ((c : T) _ _ _);
                                 repeat decide equality)
                      end) in
          let v := (eval cbv [dep_types indep_types indep_args type_of_list preinfos List.map Type_of_kind_of_type Datatypes.prod_rect base.type.base_rect unit_rect sumbool_rect prod_rec unit_rec sumbool_rec base.type.base_rec eq_ind_r eq_ind eq_sym eq_rec eq_rect] in v) in
          v.
        Ltac make_ident_infos_of := let v := build_ident_infos_of in refine v.

        Definition ident_infos_of : ident -> ident_infos := ltac:(make_ident_infos_of).

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

        Ltac build_split_ident_gen :=
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
                                 let all_tidents := (eval cbv [pattern.all_idents] in pattern.all_idents) in
                                 let ridc := find_ctor ctor all_tidents all_idents in
                                 (exists ridc);
                                 cbv [ident_infos_of ident_args type_of_list indep_args dep_types indep_types preinfos assemble_ident to_ident List.map Type_of_kind_of_type];
                                 unshelve (eexists; refine_sigT_and_pair; try constructor);
                                 repeat esplit)
                           : { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                              | JMeq idc (assemble_ident args) } })) in
          v.
        Ltac make_split_ident_gen := let v := build_split_ident_gen in refine v.

        Definition split_ident_gen
          : forall {t} (idc : Compilers.ident.ident t),
            { ridc : ident & { args : ident_args (ident_infos_of ridc)
                             | JMeq idc (assemble_ident args) } }
          := ltac:(make_split_ident_gen).

        Ltac do_reduce v :=
          let v := (eval cbv [proj1_sig eta_ident_cps_gen eta_ident_cps_gen2 eta_ident_cps_gen3 ident_args ident_infos_of type_of_list dep_types indep_types indep_args preinfos to_type ident_transport_opt split_ident_gen pattern.eta_ident_cps_gen to_ident to_type List.map Type_of_kind_of_type] in v) in
          v.

        Definition full_types : ident -> Type
          := ltac:(let v := do_reduce
                              (proj1_sig
                                 (eta_ident_cps_gen
                                    (fun idc
                                     => ident_args (ident_infos_of idc)))) in
                   refine v).
        Definition is_simple : ident -> bool
          := ltac:(let v := do_reduce
                              (proj1_sig
                                 (eta_ident_cps_gen
                                    (fun idc
                                     => let ii := ident_infos_of idc in
                                        match dep_types ii, indep_types ii return _ with (* COQBUG(https://github.com/coq/coq/issues/9955) *)
                                        | [], [] => true
                                        | _, _ => false
                                        end))) in
                   refine v).
        Definition type_of : forall (pidc : ident), full_types pidc -> Compilers.type Compilers.base.type
          := ltac:(let v := do_reduce
                              (@eta_ident_cps_gen2
                                 _ (fun idc => ident_args (ident_infos_of idc))
                                 (fun pidc full_types_pidc
                                  => full_types_pidc -> Compilers.type Compilers.base.type)
                                 (fun pidc args
                                  => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))) in
                   refine v).
        Definition invert_bind_args : forall {t} (idc : Compilers.ident.ident t) (pidc : ident), Datatypes.option (full_types pidc)
          := ltac:(let v := do_reduce
                              (fun t idc pidc
                               => proj1_sig
                                    (pattern.eta_ident_cps_gen
                                       (fun t idc
                                        => @eta_ident_cps_gen2
                                             _ (fun idc => ident_args (ident_infos_of idc))
                                             (fun pidc full_types_pidc => Datatypes.option full_types_pidc)
                                             (fun pidc
                                              => let '(existT ridc (exist args _)) := split_ident_gen idc in
                                                 ident_transport_opt
                                                   (fun idc => ident_args (ident_infos_of idc))
                                                   args)
                                             pidc))
                                    t idc) in
                   refine v).
        Definition to_typed : forall (pidc : ident) (args : full_types pidc), Compilers.ident.ident (type_of pidc args)
          := ltac:(let v := do_reduce
                              (@eta_ident_cps_gen3
                                 _ (fun idc => ident_args (ident_infos_of idc))
                                 (fun pidc full_types_pidc => full_types_pidc -> Compilers.type Compilers.base.type)
                                 (fun pidc args => to_type (ident_infos_of pidc) (projT1 args) (Datatypes.fst (projT2 args)))
                                 (fun pidc full_types_pidc type_of_pidc => forall args : full_types_pidc, Compilers.ident.ident (type_of_pidc args))
                                 (fun pidc args
                                  => to_ident _ _ _ (Datatypes.snd (projT2 args)))) in
                   refine v).
      End ident.
      Notation ident := ident.ident.
    End Raw.

    Module ident.
      Local Unset Decidable Equality Schemes.

      Definition eta_ident_cps {T : Compilers.type Compilers.base.type -> Type} {t} (idc : Compilers.ident.ident t)
                 (f : forall t', Compilers.ident.ident t' -> T t')
        : T t
        := Eval cbv [eta_ident_cps_gen proj1_sig] in
            proj1_sig (@eta_ident_cps_gen (fun t _ => T t) f) t idc.

      Module PrintIdent.
        Import Compilers.ident.
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
          epose proof (_ : type -> Set) as ident;
          idtac "      Inductive ident : type -> Set :=";
          let v := (eval cbv [pattern.all_idents Compilers.base.interp] in pattern.all_idents) in
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
        Local Set Printing Coercions.
        Local Unset Printing Notations.
        Local Set Printing Width 10000.
        (*Goal True. print_ident. Abort.*)
      End PrintIdent.
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

      Ltac build_all_idents := build_all_idents_gen (forall t (idc : ident t), True).
      Ltac make_all_idents := let v := build_all_idents in refine v.

      Definition all_idents : list { T : Type & T } := ltac:(make_all_idents).

      Definition eta_ident_cps_gen
                 {T : forall t, ident t -> Type}
                 (f : forall t idc, T t idc)
        : { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }.
      Proof. make_eta_ident_cps_gen. Defined.

      Definition eta_ident_cps_gen_expand_literal
                 {T : forall t, ident t -> Type}
                 (f : forall t idc, T t idc)
        : { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }.
      Proof. make_eta_ident_cps_gen_expand_literal. Defined.

      Definition eta_ident_cps_gen2
                 {T0 : forall t, ident t -> Type}
                 (f0 : forall t idc, T0 t idc)
                 {T1 : forall t (idc : ident t), T0 t idc -> Type}
                 (f1 : forall t idc, T1 t idc (f0 t idc))
        : forall t idc, T1 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc).
      Proof. intros t idc; cbv [proj1_sig eta_ident_cps_gen]; destruct idc; exact (f1 _ _). Defined.

      Definition eta_ident_cps_gen3
                 {T0 : forall t, ident t -> Type}
                 (f0 : forall t idc, T0 t idc)
                 {T1 : forall t (idc : ident t), T0 t idc -> Type}
                 (f1 : forall t idc, T1 t idc (f0 t idc))
                 {T2 : forall t idc x, T1 t idc x -> Type}
                 (f2 : forall t idc, T2 t idc (f0 t idc) (f1 t idc))
        : forall t idc, T2 t idc (proj1_sig (@eta_ident_cps_gen T0 f0) t idc) (@eta_ident_cps_gen2 T0 f0 T1 f1 t idc).
      Proof. intros t idc; cbv [proj1_sig eta_ident_cps_gen eta_ident_cps_gen2]; destruct idc; exact (f2 _ _). Defined.

      Definition Type_of_kind_of_type (T : Raw.ident.kind_of_type)
        := match T with
           | Raw.ident.GallinaType T => T
           | Raw.ident.BaseBaseType => Compilers.base.type.base
           | Raw.ident.BaseType => pattern.base.type.type
           end.

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
      Local Notation ident_infos_of := Raw.ident.ident_infos_of.
      Local Notation indep_types := Raw.ident.indep_types.
      Local Notation indep_args := Raw.ident.indep_args.
      Local Notation iffT A B := ((A -> B) * (B -> A))%type.

      Ltac collect_args' f cur :=
        lazymatch f with
        | ?f ?x => collect_args' f (x, cur)
        | _ => cur
        end.
      Ltac collect_args f := collect_args' f Datatypes.tt.

      Ltac build_split_types :=
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
                            let all_ridents := (eval cbv [Raw.ident.all_idents] in Raw.ident.all_idents) in
                            let v := find_ctor ctor all_idents all_ridents in
                            let args := collect_args idc in
                            let f := (eval cbv [list_unapp_type_of_list dep_types preinfos ident_infos_of indep_types List.app List.map Type_of_kind_of_type] in
                                         (@list_unapp_type_of_list
                                            (dep_types (preinfos (ident_infos_of v)))
                                            (List.map Type_of_kind_of_type (indep_types (preinfos (ident_infos_of v)))))) in
                            refine (existT
                                      _
                                      v
                                      (f args)))
                      : { ridc : Raw.ident & type_of_list (dep_types (preinfos (ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc))) }%type) in
        let v := (eval cbn [Datatypes.fst Datatypes.snd] in v) in
        v.
      Ltac make_split_types := let v := build_split_types in refine v.

      Ltac build_add_types_from_raw_sig split_types :=
        let ridc := fresh "ridc" in
        let ridc' := fresh "ridc'" in
        let dt := fresh "dt" in
        let idt := fresh "idt" in
        let v := (eval cbv [id] in
                     (fun (ridc : Raw.ident)
                          (dt : type_of_list (dep_types (preinfos (ident_infos_of ridc))))
                          (idt : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc))))
                      => let ridc' := ridc in
                         ltac:(destruct ridc;
                               let ridc := (eval cbv [ridc'] in ridc') in
                               let all_idents := (eval cbv [all_idents] in all_idents) in
                               let all_ridents := (eval cbv [Raw.ident.all_idents] in Raw.ident.all_idents) in
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
      Ltac make_add_types_from_raw_sig split_types :=
        let v := build_add_types_from_raw_sig split_types in refine v.

      Definition split_types : forall {t} (idc : ident t), { ridc : Raw.ident & type_of_list (dep_types (preinfos (ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc))) }%type
        := ltac:(make_split_types).

      Definition add_types_from_raw_sig
        : forall (ridc : Raw.ident)
                 (dt : type_of_list (dep_types (preinfos (ident_infos_of ridc))))
                 (idt : type_of_list_of_kind (indep_types (preinfos (ident_infos_of ridc)))),
          { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } }
        := ltac:(make_add_types_from_raw_sig (@split_types)).

      Definition prearg_types : forall {t} (idc : ident t), list Type
        := (fun t idc
            => let st := @split_types t idc in
               let pi := preinfos (ident_infos_of (projT1 st)) in
               indep_args pi (Datatypes.fst (projT2 st))).

      Definition try_unify_split_args {ridc1 ridc2 : Raw.ident.ident}
        : forall {dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1)))}
                 {dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2)))},
          type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2))
        := (if Raw.ident.ident_beq ridc1 ridc2 as b return (if b then ridc1 = ridc2 else True) -> _
            then fun pf
                 => match pf in (_ = ridc2) return forall (dt1 : type_of_list (dep_types (preinfos (ident_infos_of ridc1))))
                                                          (dt2 : type_of_list (dep_types (preinfos (ident_infos_of ridc2)))),
                        type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                    | eq_refl
                      => fun dt1 dt2
                         => match Raw.ident.dep_types_dec_transparent _ dt1 dt2 with
                            | left pf
                              => match pf in (_ = dt2) return type_of_list (indep_args _ dt1) -> Datatypes.option (type_of_list (indep_args _ dt2)) with
                                 | eq_refl => Datatypes.Some
                                 end
                            | right _ => fun _ => Datatypes.None
                            end
                    end
            else fun _ _ _ _ => Datatypes.None)
             (Raw.ident.ident_beq_if ridc1 ridc2).

      Ltac do_reduce v :=
        let v := (eval cbv [proj1_sig pattern.eta_ident_cps_gen pattern.eta_ident_cps_gen2 eta_ident_cps_gen eta_ident_cps_gen2 eta_ident_cps_gen3 eta_ident_cps_gen_expand_literal pattern.eta_ident_cps_gen_expand_literal split_types projT1 projT2 preinfos dep_types indep_types ident_infos_of split_types add_types_from_raw_sig type_of_list List.map List.app Type_of_kind_of_type indep_args lift_type_of_list_map relax_kind_of_type subst_default_kind_of_type Raw.ident.assemble_ident Raw.ident.to_type prearg_types Raw.ident.Type_of_kind_of_type Raw.ident.to_ident Raw.ident.indep_args_beq Raw.ident.split_ident_gen Raw.ident.dep_types_dec_transparent try_unify_split_args Raw.ident.ident_beq_if Raw.ident.dep_types_dec_transparent Raw.ident.ident_beq] in v) in
        let v := (eval cbn [Datatypes.fst Datatypes.snd] in v) in
        v.

      Definition strip_types : forall {t} (idc : ident t), Raw.ident
        := ltac:(let v := do_reduce
                            (proj1_sig
                               (eta_ident_cps_gen
                                  (fun t idc => projT1 (@split_types t idc)))) in
                 refine v).
      Definition arg_types : forall {t} (idc : ident t), list Type
        := ltac:(let v := (eval cbv [prearg_types] in (@prearg_types)) in
                 let v := do_reduce
                            (proj1_sig
                               (eta_ident_cps_gen
                                  v)) in
                 refine v).
      Definition to_typed : forall {t} (idc : ident t) (evm : EvarMap), type_of_list (arg_types idc) -> Compilers.ident.ident (pattern.type.subst_default t evm)
        := ltac:(let v := constr:
                          (fun t (idc : ident t) (evm : EvarMap)
                           => @eta_ident_cps_gen2
                                _ (@prearg_types)
                                (fun t idc arg_types_idc
                                 => forall args : type_of_list arg_types_idc,
                                     Compilers.ident.ident
                                       (let st := @split_types _ idc in
                                        let pi := preinfos (ident_infos_of (projT1 st)) in
                                        Raw.ident.to_type
                                          pi
                                          (Datatypes.fst (projT2 st))
                                          (lift_type_of_list_map
                                             (@subst_default_kind_of_type evm)
                                             (Datatypes.snd (projT2 st)))))
                                (fun t idc args
                                 => let st := @split_types _ idc in
                                    (@Raw.ident.assemble_ident
                                       (preinfos (ident_infos_of (projT1 (@split_types _ idc))))
                                       (existT
                                          _ (Datatypes.fst (projT2 st))
                                          (lift_type_of_list_map (@subst_default_kind_of_type evm) (Datatypes.snd (projT2 st)), args))))
                                t idc) in
                 let V' := fresh "V'" in
                 let v := constr:(
                            (fun t (idc : ident t) (evm : EvarMap)
                             => match v t idc evm return type_of_list (@arg_types _ idc) -> Compilers.ident.ident (pattern.type.subst_default t evm) with
                                | V'
                                  => ltac:(destruct idc;
                                             let v := (eval cbv [V'] in V') in
                                             clear V';
                                               let v := do_reduce v in
                                               refine v)
                                end)) in
                 let v := (eval cbv [id] in v) in
                 refine v).
      Definition type_of_list_arg_types_beq : forall t idc, type_of_list (@arg_types t idc) -> type_of_list (@arg_types t idc) -> bool
        := ltac:(let v := do_reduce
                            (@eta_ident_cps_gen2
                               _ (@prearg_types)
                               (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
                               (fun t idc
                                => Raw.ident.indep_args_beq _ _)) in
                 refine v).
      Definition reflect_type_of_list_arg_types_beq : forall {t idc}, reflect_rel (@eq (type_of_list (@arg_types t idc))) (@type_of_list_arg_types_beq t idc)
        := @eta_ident_cps_gen3
             _ (@prearg_types)
             (fun t idc arg_types_idc => type_of_list arg_types_idc -> type_of_list arg_types_idc -> bool)
             (fun t idc => Raw.ident.indep_args_beq _ _)
             (fun t idc arg_types_idc beq => reflect_rel (@eq (type_of_list arg_types_idc)) beq)
             (fun t idc => Raw.ident.indep_args_reflect _ _).
      Definition preof_typed_ident
        := (fun t (idc : Compilers.ident.ident t)
            => proj1_sig
                 (projT2
                    (add_types_from_raw_sig
                       (projT1 (Raw.ident.split_ident_gen idc))
                       (projT1 (proj1_sig (projT2 (Raw.ident.split_ident_gen idc))))
                       (lift_type_of_list_map
                          (@relax_kind_of_type)
                          (Datatypes.fst (projT2 (proj1_sig (projT2 (Raw.ident.split_ident_gen idc))))))))).
      Definition of_typed_ident : forall {t} (idc : Compilers.ident.ident t), ident (type.relax t)
        := ltac:(let v := (eval cbv [preof_typed_ident] in
                              (proj1_sig
                                 (pattern.eta_ident_cps_gen
                                    preof_typed_ident))) in
                 let V' := fresh "V'" in
                 let v := constr:(
                            (fun t (idc : Compilers.ident.ident t)
                             => match v t idc return ident (type.relax t) with
                                | V'
                                  => ltac:(destruct idc;
                                             let v := (eval cbv [V'] in V') in
                                             clear V';
                                               let v := do_reduce v in
                                               refine v)
                                end)) in
                 let v := (eval cbv [id] in v) in
                 refine v).
      Definition arg_types_of_typed_ident : forall {t} (idc : Compilers.ident.ident t), type_of_list (arg_types (of_typed_ident idc))
        := ltac:(let v := constr:(fun t (idc : Compilers.ident.ident t)
                                  => let st := Raw.ident.split_ident_gen idc in
                                     let args := proj1_sig (projT2 st) in
                                     Datatypes.snd (projT2 args)) in
                 let V' := fresh "V'" in
                 let v := constr:(
                            (fun t (idc : Compilers.ident.ident t)
                             => match v t idc return type_of_list (arg_types (of_typed_ident idc)) with
                                | V'
                                  => ltac:(destruct idc;
                                             let v := (eval cbv [V'] in V') in
                                             clear V';
                                               let v := do_reduce v in
                                               refine v)
                                end)) in
                 let v := (eval cbv [id] in v) in
                 refine v).

      Definition unify : forall {t t'} (pidc : ident t) (idc : Compilers.ident.ident t'), Datatypes.option (type_of_list (@arg_types t pidc))
        := ltac:(let v := constr:(fun t t' (pidc : ident t) (idc : Compilers.ident.ident t')
                                  => proj1_sig
                                       (eta_ident_cps_gen_expand_literal
                                          (fun t pidc
                                           => proj1_sig
                                                (pattern.eta_ident_cps_gen_expand_literal
                                                   (fun t' idc
                                                    => @eta_ident_cps_gen2
                                                         _ (@prearg_types)
                                                         (fun _ idc arg_types_idc => type_of_list arg_types_idc -> Datatypes.option (type_of_list (@arg_types t pidc)))
                                                         (fun t idc
                                                          => @eta_ident_cps_gen2
                                                               _ (@prearg_types)
                                                               (fun _ pidc arg_types_pidc => type_of_list (@prearg_types _ idc) -> Datatypes.option (type_of_list arg_types_pidc))
                                                               (fun t' pidc
                                                                => try_unify_split_args)
                                                               _ pidc)
                                                         _ (of_typed_ident idc) (@arg_types_of_typed_ident _ idc)))
                                                _ idc))
                                       _ pidc) in
                 let v := (eval cbv [of_typed_ident arg_types_of_typed_ident] in v) in
                 let v := (eval cbv [pattern.eta_ident_cps_gen_expand_literal proj1_sig eta_ident_cps_gen_expand_literal eta_ident_cps_gen2 split_types projT1 projT2 try_unify_split_args Raw.ident.ident_beq_if Raw.ident.dep_types_dec_transparent Raw.ident.ident_beq Raw.ident.dep_types_dec_transparent ident_infos_of Datatypes.fst Datatypes.snd] in v) in
                 refine v).

    End ident.
  End pattern.
End Compilers.
