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
Require Import Crypto.Language.Language.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersBasicLibrary.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.DebugPrint.
Import ListNotations. Local Open Scope list_scope.
Import PrimitiveSigma.Primitive.

Import EqNotations.
Module Compilers.
  Set Boolean Equality Schemes.
  Set Decidable Equality Schemes.
  Local Set Primitive Projections.
  Export Language.Compilers.
  Import IdentifiersBasicLibrary.Compilers.
  Export IdentifiersLibrary.Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).
  Local Notation type_of_list_cps := (fold_right (fun a K => a -> K)).
  Module pattern.
    Export IdentifiersLibrary.Compilers.pattern.

    Module Import Tactics.
      Ltac ident_assembly_debug_level := constr:(1%nat).

      Ltac check_debug_level_then_Set _ :=
        let lvl := ident_assembly_debug_level in
        lazymatch type of lvl with
        | nat => constr:(Set)
        | ?T => constr_run_tac ltac:(fun _ => idtac "Error: ident_assembly_debug_level should have type nat but instead has type" T)
        end.
      Ltac debug0 tac :=
        constr_run_tac tac.
      Ltac debug1 tac :=
        let lvl := ident_assembly_debug_level in
        lazymatch lvl with
        | S _ => constr_run_tac tac
        | _ => check_debug_level_then_Set ()
        end.

      Ltac time_if_debug1 :=
        let lvl := ident_assembly_debug_level in
        lazymatch lvl with
        | O => ltac:(fun tac => tac ())
        | S _ => ltac:(fun tac => time tac ())
        | ?v => ltac:(fun tac => fail 0 "Invalid non-nat ident_assembly_debug_level" v)
        end.

      Ltac warn_if_goals_remain _ :=
        [ > idtac "WARNING: Remaining goal:"; print_context_and_goal () .. ].

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
      Ltac build_all_idents ident := build_all_idents_gen (forall t (idc : ident t), True).
      Ltac cache_build_all_idents ident :=
        let name := fresh "all_idents" in
        let term := build_all_idents ident in
        cache_term term name.
      Ltac make_all_idents ident := let v := build_all_idents ident in refine v.

      Ltac build_simple_idents ident all_idents :=
        lazymatch (eval hnf in all_idents) with
        | Datatypes.cons (existT _ (ident ?T) ?idc) ?rest
          => let rest := build_simple_idents ident rest in
             constr:(Datatypes.cons (existT ident T idc) rest)
        | Datatypes.cons _ ?rest => build_simple_idents ident rest
        | Datatypes.nil => constr:(@Datatypes.nil { t : _ & ident t })
        end.
      Ltac cache_build_simple_idents ident all_idents :=
        let name := fresh "simple_idents" in
        let term := build_simple_idents ident all_idents in
        cache_term term name.

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

      Ltac do_make_eta_ident_cps_gen_gen do_destruct_base base :=
        unshelve eexists; intros;
        lazymatch goal with idc : _ |- _ => destruct idc end;
        lazymatch do_destruct_base with
        | true => repeat match goal with t : base |- _ => destruct t end
        | false => idtac
        end;
        shelve_unifiable; reflexivity.
      Ltac do_make_eta_ident_cps_gen := do_make_eta_ident_cps_gen_gen false.
      Ltac do_make_eta_ident_cps_gen_expand_literal := do_make_eta_ident_cps_gen_gen true.

      Ltac build_eta_ident_cps_gen_gen do_destruct_base base ident :=
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
        constr:(ltac:(do_make_eta_ident_cps_gen_gen do_destruct_base base)
                : T).
      Ltac build_eta_ident_cps_gen := build_eta_ident_cps_gen_gen false.
      Ltac build_eta_ident_cps_gen_expand_literal := build_eta_ident_cps_gen_gen true.
      Ltac cache_build_eta_ident_cps_gen base ident :=
        let name := fresh "eta_ident_cps_gen" in
        let term := build_eta_ident_cps_gen base ident in
        cache_term term name.
      Ltac cache_build_eta_ident_cps_gen_expand_literal base ident :=
        let name := fresh "eta_ident_cps_gen_expand_literal" in
        let term := build_eta_ident_cps_gen_expand_literal base ident in
        cache_term term name.
      Ltac make_eta_ident_cps_gen_gen do_destruct_base base ident :=
        let res := build_eta_ident_cps_gen_gen do_destruct_base base ident in refine res.
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

      Ltac build_ident_index ty all_idents :=
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
        v.
      Ltac cache_build_ident_index ty all_idents :=
        let name := fresh "ident_index" in
        let term := build_ident_index ty all_idents in
        cache_term term name.
      Ltac make_ident_index ty all_idents := let v := build_ident_index ty all_idents in refine v.
    End Tactics.

    Module Raw.
      Export IdentifiersLibrary.Compilers.pattern.Raw.
      Module ident.
        Export IdentifiersLibrary.Compilers.pattern.Raw.ident.

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
          Ltac cache_build_all_idents ident :=
            let name := fresh "all_raw_idents" in
            let term := build_all_idents ident in
            cache_term term name.
          Ltac make_all_idents ident := let v := build_all_idents ident in refine v.

          Ltac prove_ident_index_idempotent _ :=
            let idc := fresh "idc" in
            intro idc; destruct idc; vm_compute; reflexivity.

          Ltac build_ident_index_idempotent all_idents ident_index :=
            constr:(ltac:(prove_ident_index_idempotent ())
                    : forall idc, List.nth_error all_idents (ident_index idc) = Some idc).
          Ltac cache_build_ident_index_idempotent all_idents ident_index :=
            let name := fresh "raw_ident_index_idempotent" in
            let term := build_ident_index_idempotent all_idents ident_index in
            cache_term term name.
          Ltac make_ident_index_idempotent all_idents ident_index :=
            let v := build_ident_index_idempotent all_idents ident_index in refine v.
          Ltac fun_to_curried_ident_infos base cident f :=
            let type_to_kind T
                := lazymatch (eval cbv beta in T) with
                   | base => BaseBaseType
                   | Compilers.base.type.type _ => BaseType
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
                                             let res := fun_to_curried_ident_infos base cident f in
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
            | cident ?t
              => constr:({| dep_types := Datatypes.nil ; indep_types := Datatypes.nil ; indep_args := (fun _ => Datatypes.nil) ; to_type := (fun _ _ => t) ; to_ident := fun _ _ _ => f |})
            end.

          Ltac inner_build_ident_infos_of idc T base cident :=
            destruct idc;
            let T := (eval cbv in (projT2 T)) in
            let v := fun_to_curried_ident_infos base cident T in
            let v := (eval cbv [type_of_list List.map Type_of_kind_of_type] in v) in
            let c := constr:(@Build_ident_infos base cident v) in
            let T := type of c in
            let T := (eval cbv [dep_types indep_types indep_args type_of_list List.map Type_of_kind_of_type] in T) in
            refine ((c : T) _ _ _ _ _);
            repeat decide equality.

          Ltac build_ident_infos_of base reflect_base_beq reflect_base_interp_beq cident ident_to_cident :=
            let idc := fresh "idc" in
            let T := fresh in
            let H := fresh in
            let H' := fresh in
            let v
                := constr:(
                     match reflect_base_beq, reflect_base_interp_beq return _ with
                     | H, H' (* make these available in the context *)
                       => fun idc
                          => match ident_to_cident idc return @ident_infos _ cident with
                             | T
                               => ltac:(inner_build_ident_infos_of idc T base cident)
                             end
                     end) in
            let v := (eval cbv [dep_types indep_types indep_args type_of_list preinfos List.map Type_of_kind_of_type Datatypes.prod_rect (*base.type.base_rect base.type.base_rec*) unit_rect sumbool_rect prod_rec unit_rec sumbool_rec eq_ind_r eq_ind eq_sym eq_rec eq_rect] in v) in
            v.
          Ltac cache_build_ident_infos_of base reflect_base_beq reflect_base_interp_beq cident ident_to_cident :=
            let name := fresh "raw_ident_infos_of" in
            let term := build_ident_infos_of base reflect_base_beq reflect_base_interp_beq cident ident_to_cident in
            cache_term term name.
          Ltac make_ident_infos_of base reflect_base_beq reflect_base_interp_beq cident ident_to_cident := let v := build_ident_infos_of base reflect_base_beq reflect_base_interp_beq cident ident_to_cident in refine v.

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

          Ltac build_split_ident_gen cident ident ident_infos_of all_idents all_pattern_idents :=
            let t := fresh "t" in
            let idc := fresh "idc" in
            let idc' := fresh "idc'" in
            let ridc := fresh "ridc" in
            let v := (eval cbv beta iota zeta in
                         (fun t (idc : cident t)
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
                                   repeat unshelve esplit;
                                   warn_if_goals_remain ())
                             : { ridc : ident & { args : ident_args (preinfos (ident_infos_of ridc))
                                                | { pf : _ = _
                                                  | idc = rew [cident] pf in assemble_ident args } } })) in
            v.
          Ltac cache_build_split_ident_gen cident ident ident_infos_of all_idents all_pattern_idents :=
            let name := fresh "split_raw_ident_gen" in
            let term := build_split_ident_gen cident ident ident_infos_of all_idents all_pattern_idents in
            cache_term term name.
          Ltac make_split_ident_gen cident ident ident_infos_of all_idents all_pattern_idents :=
            let v := build_split_ident_gen cident ident ident_infos_of all_idents all_pattern_idents in refine v.

          Ltac build_invert_bind_args cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen :=
            (eval cbv [folded_invert_bind_args eta_pattern_ident_cps_gen proj1_sig eta_ident_cps_gen2 eta_ident_cps_gen proj1_sig proj2_sig eq_rect eq_sym split_ident_gen projT2 ident_transport_opt ident_beq ident_index Nat.eqb ident_beq_if ident_bl eq_ind_r eq_ind nat_eqb_bl_transparent nat_ind ident_index_inj ident_index_idempotent f_equal] in
                (@folded_invert_bind_args _ cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen)).
          Ltac cache_build_invert_bind_args cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen :=
            let name := fresh "raw_invert_bind_args" in
            let term := build_invert_bind_args cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen in
            cache_term term name.
          Ltac make_invert_bind_args cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen :=
            let v := build_invert_bind_args cident eta_pattern_ident_cps_gen ident all_idents ident_index ident_index_idempotent eta_ident_cps_gen ident_infos_of split_ident_gen in refine v.

          Ltac cache_build_invert_bind_args_unknown invert_bind_args :=
            let name := fresh "invert_bind_args_unknown" in
            cache_term invert_bind_args name.
        End Tactics.
      End ident.
    End Raw.

    Module ident.
      Export IdentifiersLibrary.Compilers.pattern.ident.

      Local Notation dep_types := Raw.ident.dep_types.
      Local Notation preinfos := Raw.ident.preinfos.
      Local Notation indep_types := Raw.ident.indep_types.
      Local Notation indep_args := Raw.ident.indep_args.

      Module Tactics.
        Ltac build_eta_ident_cps eta_pattern_ident_cps_gen :=
          (eval cbv [eta_pattern_ident_cps_gen proj1_sig] in
              (fun T t idc f
               => proj1_sig (eta_pattern_ident_cps_gen (fun t _ => T t) f) t idc)).
        Ltac cache_build_eta_ident_cps eta_pattern_ident_cps_gen :=
          let name := fresh "eta_ident_cps" in
          let term := build_eta_ident_cps eta_pattern_ident_cps_gen in
          cache_term term name.
        Ltac make_eta_ident_cps eta_pattern_ident_cps_gen :=
          let res := build_eta_ident_cps eta_pattern_ident_cps_gen in refine res.

        Ltac build_all_idents ident := build_all_idents_gen (forall t (idc : ident t), True).
        Ltac cache_build_all_idents ident :=
          let name := fresh "all_pattern_idents" in
          let term := build_all_idents ident in
          cache_term term name.
        Ltac make_all_idents ident := let v := build_all_idents ident in refine v.

        Ltac collect_args' f cur :=
          lazymatch f with
          | ?f ?x => collect_args' f (x, cur)
          | _ => cur
          end.
        Ltac collect_args f := collect_args' f Datatypes.tt.

        Ltac build_split_types base ident raw_ident raw_ident_infos_of all_idents all_raw_idents :=
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
                                              (List.map (Type_of_kind_of_type base) (indep_types (preinfos (raw_ident_infos_of v)))))) in
                              refine (existT
                                        _
                                        v
                                        (f args)))
                        : { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc))) }%type) in
          let v := (eval cbn [Datatypes.fst Datatypes.snd] in v) in
          v.
        Ltac cache_build_split_types base ident raw_ident raw_ident_infos_of all_idents all_raw_idents :=
          let name := fresh "split_types" in
          let term := build_split_types base ident raw_ident raw_ident_infos_of all_idents all_raw_idents in
          cache_term term name.
        Ltac make_split_types base ident raw_ident raw_ident_infos_of all_idents all_raw_idents := let v := build_split_types base ident raw_ident raw_ident_infos_of all_idents all_raw_idents in refine v.

        Ltac build_add_types_from_raw_sig base ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types :=
          let ridc := fresh "ridc" in
          let ridc' := fresh "ridc'" in
          let dt := fresh "dt" in
          let idt := fresh "idt" in
          let v := (eval cbv [id] in
                       (fun (ridc : raw_ident)
                            (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                            (idt : type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc))))
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
        Ltac cache_build_add_types_from_raw_sig base ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types :=
          let name := fresh "add_types_from_raw_sig" in
          let term := build_add_types_from_raw_sig base ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types in
          cache_term term name.
        Ltac make_add_types_from_raw_sig base ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types :=
          let v := build_add_types_from_raw_sig base ident raw_ident raw_ident_infos_of all_idents all_raw_idents split_types in refine v.

        Ltac prove_to_type_split_types_subst_default_eq _ :=
          let t := fresh "t" in
          let idc := fresh "idc" in
          let evm := fresh "evm" in
          intros t idc evm;
          destruct idc; cbv -[type.subst_default base.subst_default];
          cbn [type.subst_default base.subst_default]; reflexivity.
        Ltac build_to_type_split_types_subst_default_eq cident raw_ident raw_ident_infos_of ident split_types :=
          constr:(ltac:(prove_to_type_split_types_subst_default_eq ())
                  : forall t idc evm,
                     Raw.ident.to_type
                       (preinfos (raw_ident_infos_of (projT1 (@split_types_subst_default _ cident raw_ident raw_ident_infos_of ident split_types t idc evm))))
                       (Datatypes.fst (projT2 (@split_types_subst_default _ cident raw_ident raw_ident_infos_of ident split_types t idc evm)))
                       (Datatypes.snd (projT2 (@split_types_subst_default _ cident raw_ident raw_ident_infos_of ident split_types t idc evm)))
                     = type.subst_default t evm).
        Ltac cache_build_to_type_split_types_subst_default_eq cident raw_ident raw_ident_infos_of ident split_types :=
          let name := fresh "to_type_split_types_subst_default_eq" in
          let term := build_to_type_split_types_subst_default_eq cident raw_ident raw_ident_infos_of ident split_types in
          cache_term term name.
        Ltac make_to_type_split_types_subst_default_eq cident raw_ident raw_ident_infos_of ident split_types :=
          let res := build_to_type_split_types_subst_default_eq cident raw_ident raw_ident_infos_of ident split_types in refine res.

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
                             (@relax_kind_of_type _)
                             (Datatypes.fst (projT2 (proj1_sig (projT2 (split_raw_ident_gen t idc)))))))
                     = type.relax t).
        Ltac cache_build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen :=
          let name := fresh "projT1_add_types_from_raw_sig_eq" in
          let term := build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen in
          cache_term term name.
        Ltac make_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen :=
          let res := build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen in refine res.

        Ltac build_arg_types_unfolded cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types :=
          (eval cbv -[base.interp] in
              (@arg_types _ cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types)).
        Ltac cache_build_arg_types_unfolded cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types :=
          let name := fresh "arg_types_unfolded" in
          let term := build_arg_types_unfolded cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types in
          cache_term term name.
        Ltac make_arg_types_unfolded cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types :=
          let res := build_arg_types_unfolded cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types in refine res.

        Ltac build_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded :=
          (eval cbv -[Prod.prod_beq arg_types_unfolded type_of_list base.interp_beq base_interp_beq Z.eqb base_interp ZRange.zrange_beq] in
              (proj1_sig
                 (@eta_ident_cps_gen
                    (fun t idc => type_of_list (@arg_types_unfolded t idc) -> type_of_list (@arg_types_unfolded t idc) -> bool)
                    (@type_of_list_arg_types_beq _ cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types)))).
        Ltac cache_build_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded :=
          let name := fresh "type_of_list_arg_types_beq_unfolded" in
          let term := build_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded in
          cache_term term name.
        Ltac make_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded :=
          let res := build_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types arg_types_unfolded in refine res.

        Ltac build_to_typed_unfolded base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded :=
          let v := (eval cbv -[type.subst_default base.subst_default arg_types_unfolded type_of_list base_interp Datatypes.fst Datatypes.snd] in
                       (fun t (idc : ident t) (evm : EvarMap)
                        => proj1_sig
                             (@eta_ident_cps_gen
                                (fun t idc => type_of_list (@arg_types_unfolded t idc) -> cident (type.subst_default t evm))
                                (fun t idc => @to_typed _ cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq t idc evm))
                             t idc)) in
          let v := (eval cbn [Datatypes.fst Datatypes.snd type_of_list] in v) in
          v.
        Ltac cache_build_to_typed_unfolded base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded :=
          let name := fresh "to_typed_unfolded" in
          let term := build_to_typed_unfolded base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded in
          cache_term term name.
        Ltac make_to_typed_unfolded base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded :=
          let res := build_to_typed_unfolded base_interp cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded in refine res.

        Ltac build_of_typed_ident_unfolded cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let v := (eval cbv -[type.relax base.relax] in
                       (@of_typed_ident _ cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)) in
          let v := (eval cbn [type.relax base.relax] in v) in
          v.
        Ltac cache_build_of_typed_ident_unfolded cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let name := fresh "of_typed_ident_unfolded" in
          let term := build_of_typed_ident_unfolded cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in
          cache_term term name.
        Ltac make_of_typed_ident_unfolded cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let res := build_of_typed_ident_unfolded cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in refine res.

        Ltac build_arg_types_of_typed_ident_unfolded base_interp cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded :=
          (eval cbv -[type.relax base.relax type_of_list of_typed_ident arg_types_unfolded of_typed_ident_unfolded base_interp] in
              (proj1_sig
                 (@eta_pattern_ident_cps_gen
                    (fun t idc => type_of_list (@arg_types_unfolded _ (@of_typed_ident_unfolded _ idc)))
                    (@arg_types_of_typed_ident _ cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)))).
        Ltac cache_build_arg_types_of_typed_ident_unfolded base_interp cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded :=
          let name := fresh "arg_types_of_typed_ident_unfolded" in
          let term := build_arg_types_of_typed_ident_unfolded base_interp cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded in
          cache_term term name.
        Ltac make_arg_types_of_typed_ident_unfolded base_interp cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded :=
          let res := build_arg_types_of_typed_ident_unfolded base_interp cident eta_pattern_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded in refine res.

        Ltac build_unify cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let v := (eval vm_compute in (@folded_unify (*base*)_ cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq)) in
          constr:(v <: forall {t t'} (pidc : ident t) (idc : cident t') (*evm : EvarMap*), Datatypes.option (type_of_list (@arg_types _ cident raw_ident raw_ident_infos_of ident eta_ident_cps_gen split_types t pidc))).
        Ltac cache_build_unify cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let name := fresh "unify" in
          let term := build_unify cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in
          cache_term term name.
        Ltac make_unify cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq :=
          let res := build_unify cident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in refine res.

        Ltac cache_build_unify_unknown unify :=
          let name := fresh "unify_unknown" in
          cache_term unify name.
      End Tactics.

      Module Tactic.
        Ltac build_package ident_package raw_ident pattern_ident :=
          let exprInfo := (eval hnf in (Basic.GoalType.exprInfo ident_package)) in
          let exprExtraInfo := (eval hnf in (Basic.GoalType.exprExtraInfo ident_package)) in
          let base_interp := lazymatch (eval hnf in exprInfo) with {| Classes.base_interp := ?base_interp |} => base_interp end in
          let ident := lazymatch (eval hnf in exprInfo) with {| Classes.ident := ?ident |} => ident end in
          let base_interp_beq := lazymatch (eval hnf in exprExtraInfo) with {| Classes.base_interp_beq := ?base_interp_beq |} => base_interp_beq end in
          let reflect_base_beq := lazymatch (eval hnf in exprExtraInfo) with {| Classes.reflect_base_beq := ?reflect_base_beq |} => reflect_base_beq end in
          let reflect_base_interp_beq := lazymatch (eval hnf in exprExtraInfo) with {| Classes.reflect_base_interp_beq := ?reflect_base_interp_beq |} => reflect_base_interp_beq end in
          let base := lazymatch type of ident with
                      | Compilers.type.type (Compilers.base.type ?base) -> _ => base
                      | ?T => let exp := uconstr:(Compilers.type.type (Compilers.base.type ?base)) in
                              constr_fail_with ltac:(fun _ => fail 1 "Invalid type" T "of ident (" ident "); expected" exp)
                      end in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_idents...") in
          let all_idents := Compilers.pattern.Tactics.cache_build_all_idents ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_index...") in
          let ident_index := Compilers.pattern.Tactics.cache_build_ident_index (forall t, ident t -> nat) all_idents in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_ident_cps_gen...") in
          let eta_ident_cps_gen := Compilers.pattern.Tactics.cache_build_eta_ident_cps_gen base ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_ident_cps_gen_expand_literal...") in
          let eta_ident_cps_gen_expand_literal := Compilers.pattern.Tactics.cache_build_eta_ident_cps_gen_expand_literal base ident in
          (*let eta_ident_cps_gen2 := constr:(@Compilers.pattern.eta_ident_cps_gen2 eta_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_ident_cps_gen3...") in
        let eta_ident_cps_gen3 := constr:(@Compilers.pattern.eta_ident_cps_gen3 eta_ident_cps_gen) in*)
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_ident_cps...") in
          let eta_ident_cps := Compilers.pattern.ident.Tactics.cache_build_eta_ident_cps eta_ident_cps_gen in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building simple_idents...") in
          let simple_idents := Compilers.pattern.Tactics.cache_build_simple_idents ident all_idents in


          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_raw_idents...") in
          let all_raw_idents := Compilers.pattern.Raw.ident.Tactics.cache_build_all_idents raw_ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_index...") in
          let raw_ident_index := Compilers.pattern.Tactics.cache_build_ident_index (raw_ident -> nat) all_raw_idents in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_index_idempotent...") in
          let raw_ident_index_idempotent := Compilers.pattern.Raw.ident.Tactics.cache_build_ident_index_idempotent all_raw_idents raw_ident_index in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_raw_ident_cps_gen...") in
          let eta_raw_ident_cps_gen := Compilers.pattern.Tactics.cache_build_eta_ident_cps_gen base raw_ident in
          (*let eta_raw_ident_cps_gen2 := constr:(@Raw.ident.eta_ident_cps_gen2 raw_ident eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_raw_ident_cps_gen3...") in
        let eta_raw_ident_cps_gen3 := constr:(@Raw.ident.eta_ident_cps_gen3 raw_ident eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_beq...") in
        let raw_ident_beq := constr:(@Raw.ident.ident_beq raw_ident raw_ident_index eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_lb...") in
        let raw_ident_lb := constr:(@Raw.ident.ident_lb raw_ident raw_ident_index eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_index_inj...") in
        let raw_ident_index_inj := constr:(@Raw.ident.ident_index_inj raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_bl...") in
        let raw_ident_bl := constr:(@Raw.ident.ident_bl raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_beq_if...") in
        let raw_ident_beq_if := constr:(@Raw.ident.ident_beq_if raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_transport_opt...") in
        let raw_ident_transport_opt := constr:(@Raw.ident.ident_transport_opt raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen) in*)
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_to_ident...") in
          let raw_ident_to_ident := constr:(@Raw.ident.ident_to_cident all_idents raw_ident raw_ident_index eta_raw_ident_cps_gen) in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building raw_ident_infos_of...") in
          let raw_ident_infos_of := Compilers.pattern.Raw.ident.Tactics.cache_build_ident_infos_of base reflect_base_beq reflect_base_interp_beq ident raw_ident_to_ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building split_raw_ident_gen...") in
          let split_raw_ident_gen := Compilers.pattern.Raw.ident.Tactics.cache_build_split_ident_gen ident raw_ident raw_ident_infos_of all_raw_idents all_idents in
          (*let prefull_types := constr:(@Raw.ident.prefull_types raw_ident raw_ident_infos_of) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building full_types...") in
        let full_types := constr:(@Raw.ident.full_types raw_ident eta_raw_ident_cps_gen raw_ident_infos_of) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building is_simple...") in
        let is_simple := constr:(@Raw.ident.is_simple raw_ident raw_ident_infos_of) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building type_of...") in
        let type_of := constr:(@Raw.ident.type_of raw_ident eta_raw_ident_cps_gen raw_ident_infos_of) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building folded_invert_bind_args...") in
        let folded_invert_bind_args := constr:(@Raw.ident.folded_invert_bind_args base ident eta_ident_cps_gen raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen) in*)
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building invert_bind_args...") in
          let invert_bind_args := Compilers.pattern.Raw.ident.Tactics.cache_build_invert_bind_args ident eta_ident_cps_gen raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building invert_bind_args_unknown...") in
          let invert_bind_args_unknown := Compilers.pattern.Raw.ident.Tactics.cache_build_invert_bind_args_unknown invert_bind_args in
          (*let raw_to_typed := constr:(@Raw.ident.to_typed raw_ident eta_raw_ident_cps_gen raw_ident_infos_of) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building try_unify_split_args...") in
        let try_unify_split_args := constr:(@Raw.ident.try_unify_split_args raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of) in*)


          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_pattern_idents...") in
          let all_pattern_idents := Compilers.pattern.ident.Tactics.cache_build_all_idents pattern_ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_pattern_ident_cps_gen...") in
          let eta_pattern_ident_cps_gen := Compilers.pattern.Tactics.cache_build_eta_ident_cps_gen base pattern_ident in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_pattern_ident_cps_gen_expand_literal...") in
          let eta_pattern_ident_cps_gen_expand_literal := Compilers.pattern.Tactics.cache_build_eta_ident_cps_gen_expand_literal base pattern_ident in
          (*let eta_pattern_ident_cps_gen2 := constr:(@ident.eta_ident_cps_gen2 pattern_ident eta_pattern_ident_cps_gen) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_pattern_ident_cps_gen3...") in
        let eta_pattern_ident_cps_gen3 := constr:(@ident.eta_ident_cps_gen3 pattern_ident eta_pattern_ident_cps_gen) in*)
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building split_types...") in
          let split_types := Compilers.pattern.ident.Tactics.cache_build_split_types base pattern_ident raw_ident raw_ident_infos_of all_pattern_idents all_raw_idents in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building add_types_from_raw_sig...") in
          let add_types_from_raw_sig := Compilers.pattern.ident.Tactics.cache_build_add_types_from_raw_sig base pattern_ident raw_ident raw_ident_infos_of all_pattern_idents all_raw_idents split_types in
          (*let split_types_subst_default := constr:(@ident.split_types_subst_default raw_ident raw_ident_infos_of pattern_ident split_types) in*)
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building to_type_split_types_subst_default_eq...") in
          let to_type_split_types_subst_default_eq := Compilers.pattern.ident.Tactics.cache_build_to_type_split_types_subst_default_eq ident raw_ident raw_ident_infos_of pattern_ident split_types in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building projT1_add_types_from_raw_sig_eq...") in
          let projT1_add_types_from_raw_sig_eq := Compilers.pattern.ident.Tactics.cache_build_projT1_add_types_from_raw_sig_eq add_types_from_raw_sig split_raw_ident_gen in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building arg_types_unfolded...") in
          let arg_types_unfolded := Compilers.pattern.ident.Tactics.cache_build_arg_types_unfolded ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building type_of_list_arg_types_beq_unfolded...") in
          let type_of_list_arg_types_beq_unfolded := Compilers.pattern.ident.Tactics.cache_build_type_of_list_arg_types_beq_unfolded base_interp_beq base_interp ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types arg_types_unfolded in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building to_typed_unfolded...") in
          let to_typed_unfolded := Compilers.pattern.ident.Tactics.cache_build_to_typed_unfolded base_interp ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types to_type_split_types_subst_default_eq arg_types_unfolded in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building of_typed_ident_unfolded...") in
          let of_typed_ident_unfolded := Compilers.pattern.ident.Tactics.cache_build_of_typed_ident_unfolded ident eta_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen pattern_ident split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building arg_types_of_typed_ident_unfolded...") in
          let arg_types_of_typed_ident_unfolded := Compilers.pattern.ident.Tactics.cache_build_arg_types_of_typed_ident_unfolded base_interp ident eta_ident_cps_gen raw_ident raw_ident_infos_of split_raw_ident_gen pattern_ident eta_pattern_ident_cps_gen split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq arg_types_unfolded of_typed_ident_unfolded in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building unify...") in
          let unify := Compilers.pattern.ident.Tactics.cache_build_unify ident eta_ident_cps_gen eta_ident_cps_gen_expand_literal raw_ident all_raw_idents raw_ident_index raw_ident_index_idempotent eta_raw_ident_cps_gen raw_ident_infos_of split_raw_ident_gen pattern_ident eta_pattern_ident_cps_gen eta_pattern_ident_cps_gen_expand_literal split_types add_types_from_raw_sig projT1_add_types_from_raw_sig_eq in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building unify_unknown...") in
          let unify_unknown := Compilers.pattern.ident.Tactics.cache_build_unify_unknown unify in
          let __ := Tactics.debug1 ltac:(fun _ => idtac "Building final ident package...") in
          constr:(@GoalType.Build_package
                    base ident
                    all_idents
                    ident_index
                    eta_ident_cps_gen
                    eta_ident_cps_gen_expand_literal
                    eta_ident_cps
                    simple_idents
                    raw_ident
                    all_raw_idents
                    raw_ident_index
                    raw_ident_index_idempotent
                    eta_raw_ident_cps_gen
                    raw_ident_infos_of
                    split_raw_ident_gen
                    invert_bind_args
                    invert_bind_args_unknown
                    pattern_ident
                    all_pattern_idents
                    eta_pattern_ident_cps_gen
                    eta_pattern_ident_cps_gen_expand_literal
                    split_types
                    add_types_from_raw_sig
                    to_type_split_types_subst_default_eq
                    projT1_add_types_from_raw_sig_eq
                    arg_types_unfolded
                    to_typed_unfolded
                    type_of_list_arg_types_beq_unfolded
                    of_typed_ident_unfolded
                    arg_types_of_typed_ident_unfolded
                    unify
                    unify_unknown).
        Ltac make_package_via ident_package raw_ident pattern_ident :=
          let res := build_package ident_package raw_ident pattern_ident in refine res.
        Ltac make_package :=
          idtac;
          lazymatch goal with
          | [ |- GoalType.package_with_args ?ident_package ?raw_ident ?pattern_ident ]
            => cbv [GoalType.package_with_args];
               make_package_via ident_package raw_ident pattern_ident
          end.
        Ltac cache_build_package ident_package raw_ident pattern_ident :=
          let name := fresh "pattern_package" in
          let term := build_package ident_package raw_ident pattern_ident in
          cache_term term name.
      End Tactic.
    End ident.
  End pattern.
End Compilers.
