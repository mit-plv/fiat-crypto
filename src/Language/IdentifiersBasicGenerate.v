Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Language.Pre.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.IdentifiersBasicLibrary.
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
Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.HProp.
Import Coq.Lists.List ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Pre.
  Import Language.Compilers.
  Export IdentifiersBasicLibrary.Compilers.

  Module Basic.
    Export IdentifiersBasicLibrary.Compilers.Basic.

    Module ScrapeTactics.
      Ltac scrape_preprocess T :=
        let T := Compilers.expr.reify_preprocess T in
        let T := Compilers.expr.reify_ident_preprocess T in
        T.

      Ltac scrape_data_of_type' scrape_data_of_term so_far T :=
        let recr := scrape_data_of_type' scrape_data_of_term in
        let T := scrape_preprocess T in
        let is_var_T := match constr:(Set) with
                        | _ => let __ := match constr:(Set) with _ => is_var T end in
                               true
                        | _ => false
                        end in
        lazymatch is_var_T with
        | true => so_far
        | false
          => lazymatch T with
             | forall x : ?T, @?F x => recr so_far F
             | Type => so_far
             | Set => so_far
             | Prop => so_far
             | Datatypes.list (* hardcoded *) => so_far
             | Datatypes.option (* hardcoded *) => so_far
             | Datatypes.unit (* hardcoded *) => so_far
             | Datatypes.prod (* hardcoded *) => so_far
             | ?x = ?y
               => let so_far := scrape_data_of_term so_far x in
                  scrape_data_of_term so_far y
             | ?f ?x
               => let so_far := recr so_far f in
                  recr so_far x
             | fun x : ?T => ?F
               => let so_far := recr so_far T in
                  let F' := fresh in
                  lazymatch
                    constr:(
                      fun x : T =>
                        match F return _ with
                        | F' =>
                          ltac:(
                            let F := (eval cbv delta [F'] in F') in
                            clear F';
                            let so_far := recr so_far F in
                            exact so_far)
                        end)
                  with
                  | fun _ => ?so_far => so_far
                  | ?term => constr_fail_with ltac:(fun _ => fail 1 "cannot eliminate functional dependencies of" term)
                  end
             | ?ty
               => let base_type_list_named := lazymatch so_far with {| ScrapedData.base_type_list_named := ?base_type_list_named |} => base_type_list_named end in
                  lazymatch base_type_list_named with
                  | context[GallinaIdentList.cons {| Named.value := ty |}] (* already present *)
                    => so_far
                  | _ => lazymatch so_far with
                         | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
                              ; ScrapedData.base_type_list_named := ?base_type_list_named |}
                           => constr:({| ScrapedData.all_ident_named_interped := all_ident_named_interped
                                         ; ScrapedData.base_type_list_named := GallinaIdentList.cons (without_name ty) base_type_list_named |})
                         end
                  end
             end
        end.

      Ltac require_type_or_arrow T :=
        lazymatch (eval cbv beta in T) with
        | Type => idtac
        | Set => idtac
        | Prop => idtac
        | forall x : ?A, @?F x
          => let __ := constr:(forall x : A,
                                  ltac:(require_type_or_arrow (F x); exact True)) in
             idtac
        end.

      Ltac scrape_data_of_term so_far term :=
        let scrape_data_of_type := scrape_data_of_type' scrape_data_of_term in
        let recr := scrape_data_of_term in
        let term := scrape_preprocess term in
        let is_var_term := match constr:(Set) with
                           | _ => let __ := match constr:(Set) with _ => is_var term end in
                                  true
                           | _ => false
                           end in
        let is_a_type :=
            let T := type of term in
            match constr:(Set) with
            | _ => let __ := match constr:(Set) with _ => require_type_or_arrow T end in
                   true
            | _ => false
            end in
        let try_add term :=
            let all_ident_named_interped := lazymatch so_far with {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped |} => all_ident_named_interped end in
            lazymatch all_ident_named_interped with
            | context[GallinaIdentList.cons {| Named.value := term |}] (* already present *)
              => so_far
            | _ => lazymatch so_far with
                   | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
                        ; ScrapedData.base_type_list_named := ?base_type_list_named |}
                     => constr:({| ScrapedData.all_ident_named_interped := GallinaIdentList.cons (without_name term) all_ident_named_interped
                                   ; ScrapedData.base_type_list_named := base_type_list_named |})
                   end
            end in
        lazymatch is_var_term with
        | true => so_far
        | false =>
          lazymatch is_a_type with
          | true => scrape_data_of_type so_far term
          | false =>
            lazymatch term with
            | ident.eagerly ?t => try_add term
            | ?f ?x
              => let so_far := recr so_far f in
                 recr so_far x
            | fun x : ?T => ?F
              => let so_far := scrape_data_of_type so_far T in
                 let F' := fresh in
                 lazymatch
                   constr:(
                     fun x : T =>
                       match F return _ with
                       | F' =>
                         ltac:(
                           let F := (eval cbv delta [F'] in F') in
                           clear F';
                           let so_far := recr so_far F in
                           exact so_far)
                       end)
                 with
                 | fun _ => ?so_far => so_far
                 | ?term => constr_fail_with ltac:(fun _ => fail 1 "cannot eliminate functional dependencies of" term)
                 end
            | ?term => try_add term
            end
          end
        end.

      Ltac scrape_data_of_type so_far T
        := scrape_data_of_type' scrape_data_of_term so_far T.

      Notation initial_type_list :=
        ([without_name Datatypes.nat]%gi_list)
          (only parsing).
      Notation initial_term_list :=
        ([without_name (@ident.literal)
          ; without_name (@Datatypes.nil)
          ; without_name (@Datatypes.cons)
          ; without_name (@Datatypes.Some)
          ; without_name (@Datatypes.None)
          ; without_name (@Datatypes.pair)
          ; without_name (@Datatypes.tt)
          ; with_name ident_nat_rect (@ident.Thunked.nat_rect)
          ; with_name ident_eager_nat_rect (ident.eagerly (@ident.Thunked.nat_rect))
          ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
          ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
          ; with_name ident_list_rect (@ident.Thunked.list_rect)
          ; with_name ident_eager_list_rect (ident.eagerly (@ident.Thunked.list_rect))
          ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
          ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
          ; with_name ident_List_nth_default (@nth_default)
          ; with_name ident_eager_List_nth_default (ident.eagerly (@nth_default))
         ]%gi_list)
          (only parsing).

      Ltac scrape_data_of_rulesT rules :=
        let rec iter so_far ls :=
            lazymatch (eval hnf in ls) with
            | Datatypes.cons (_, ?T) ?rest
              => let so_far := scrape_data_of_type so_far T in
                 iter so_far rest
            | Datatypes.nil => so_far
            | ?term => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-list-of-pair rewrite rules" term)
            end in
        iter {| ScrapedData.all_ident_named_interped := initial_term_list
                ; ScrapedData.base_type_list_named := initial_type_list |}
             rules.

      Ltac build_scrape_data rules_proofs :=
        let expected_type := uconstr:(PrimitiveHList.hlist (@snd bool Prop) ?[rewrite_rules]) in
        lazymatch (type of rules_proofs) with
        | PrimitiveHList.hlist _ ?rewrite_rulesT
          => scrape_data_of_rulesT rewrite_rulesT
        | ?T => constr_fail_with ltac:(fun _ => fail 1 "Unexpected type" T "of rewrite rules proofs" rules_proofs "; expected" expected_type)
        end.
      Ltac make_scrape_data_via rules_proofs :=
        let res := build_scrape_data rules_proofs in refine res.
      Ltac make_scrape_data :=
        idtac;
        lazymatch goal with
        | [ |- ScrapedData.t_with_args ?rules_proofs ]
          => cbv [ScrapedData.t_with_args];
             make_scrape_data_via rules_proofs
        end.
    End ScrapeTactics.

    Module Import Tactics.
      Ltac ident_basic_assembly_debug_level := constr:(1%nat).

      Ltac check_debug_level_then_Set _ :=
        let lvl := ident_basic_assembly_debug_level in
        lazymatch type of lvl with
        | nat => constr:(Set)
        | ?T => constr_run_tac ltac:(fun _ => idtac "Error: ident_basic_assembly_debug_level should have type nat but instead has type" T)
        end.
      Ltac debug0 tac :=
        constr_run_tac tac.
      Ltac debug1 tac :=
        let lvl := ident_basic_assembly_debug_level in
        lazymatch lvl with
        | S _ => constr_run_tac tac
        | _ => check_debug_level_then_Set ()
        end.

      Ltac time_if_debug1 :=
        let lvl := ident_basic_assembly_debug_level in
        lazymatch lvl with
        | O => ltac:(fun tac => tac ())
        | S _ => ltac:(fun tac => time tac ())
        | ?v => ltac:(fun tac => fail 0 "Invalid non-nat ident_basic_assembly_debug_level" v)
        end.

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
      Ltac build_all_base base :=
        build_all_gen base ltac:(fun x => x) (base -> True).
      Ltac make_all_base base :=
        let res := build_all_base base in refine res.


      Ltac build_all_base_and_interp all_base base_interp :=
        let all_base := (eval cbv in all_base) in
        let base_interp_head := head base_interp in
        (eval cbv [List.map base_interp_head] in
            (List.map (fun v => (v, base_interp v : Type)) all_base)).
      Ltac make_all_base_and_interp all_base base_interp :=
        let res := build_all_base_and_interp all_base base_interp in refine res.


      Ltac build_base_type_list base_type_list_named :=
        let rec iter ls :=
            lazymatch (eval hnf in ls) with
            | GallinaIdentList.nil => TypeList.nil
            | GallinaIdentList.cons {| Named.value := ?T |} ?rest
              => let rest := iter rest in
                 constr:(TypeList.cons T rest)
            end in
        iter base_type_list_named.
      Ltac make_base_type_list base_type_list_named :=
        let res := build_base_type_list base_type_list_named in refine res.

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
      Ltac reify_pattern_base_type_via_list base base_interp all_base_and_interp :=
        Language.Compilers.pattern.base.reify base ltac:(reify_base_via_list base base_interp all_base_and_interp).
      Ltac reify_pattern_type_via_list base base_interp all_base_and_interp :=
        Language.Compilers.type.reify ltac:(reify_pattern_base_type_via_list base base_interp all_base_and_interp) constr:(pattern.base.type base).

      Ltac ident_type_of_interped_type reify_type base_type base_type_interp ident ty :=
        let recur := ident_type_of_interped_type reify_type base_type base_type_interp ident in
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
                  constr:(forall t : base_type,
                             match base_type_interp t return _ with
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

      Ltac ident_type_of_interped_type_via_list base base_interp all_base_and_interp is_pattern :=
        let reify_type := lazymatch is_pattern with
                          | false => reify_type_via_list base base_interp all_base_and_interp
                          | true => reify_pattern_type_via_list base base_interp all_base_and_interp
                          end in
        let base_type := lazymatch is_pattern with
                         | false => constr:(base.type base)
                         | true => constr:(pattern.base.type base)
                         end in
        let base_interp_head := head base_interp in
        fun lookup is_literal ty ident
        => let base_type_interp := lazymatch is_pattern with
                                   | false => constr:(base.interp base_interp)
                                   | true => constr:(pattern.base.interp base_interp lookup)
                                   end in
           let res
               := lazymatch is_literal with
                  | true
                    => let t := fresh "t" in
                       lazymatch is_pattern with
                       | false => constr:(forall t : base, base_interp t -> ident (type.base (base.type.type_base t)))
                       | true => constr:(forall t : base, ident (type.base (pattern.base.type.type_base t)))
                       end
                  | false
                    => ident_type_of_interped_type reify_type base_type base_type_interp ident ty
                  end in
           (eval cbv [base_interp_head] in res).

      Ltac build_base_elim base_type_list_named :=
        let base := fresh "base" in
        constr:(forall (base : Set),
                   ltac:(let rec iter ls :=
                             lazymatch (eval hnf in ls) with
                             | GallinaIdentList.nil => exact base
                             | @GallinaIdentList.cons _ ?v ?rest
                               => lazymatch v with
                                  | with_name name _ => refine (forall (name : base), _)
                                  | without_name ?T
                                    => let name := fresh T in
                                       refine (forall name : base, _)
                                  end;
                                  iter rest
                             end in
                         iter base_type_list_named)).

      Ltac print_ind_of_elim elimT :=
        lazymatch elimT with
        | forall ind : ?T, ?P
          => idtac "Inductive" ind ":" T ":=";
             let P' := fresh in
             let __ :=
                 constr:(
                   fun ind : T =>
                     match P return True with
                     | P' =>
                       ltac:(
                         let P := (eval cbv delta [P'] in P') in
                         let rec iter T :=
                             let rest := match T with
                                         | ?A -> ?rest => rest
                                         | _ => Datatypes.tt
                                         end in
                             lazymatch rest with
                             | Datatypes.tt => idtac "."
                             | _ => lazymatch T with
                                    | forall ctor : ?ty, _ =>
                                      idtac "|" ctor ":" ty;
                                      iter rest
                                    end
                             end in
                         iter P;
                         exact I)
                     end) in
             idtac
        end.

      Ltac build_raw_ident_elim all_ident_named_interped :=
        let raw_ident := fresh "raw_ident" in
        constr:(forall (raw_ident : Set),
                   ltac:(let rec iter ls :=
                             lazymatch (eval hnf in ls) with
                             | GallinaIdentList.nil => exact raw_ident
                             | @GallinaIdentList.cons _ ?v ?rest
                               => let name := lazymatch v with
                                              | with_name name _ => fresh "raw_" name
                                              | without_name ?T => fresh "raw_ident_" T
                                              end in
                                  refine (forall name : raw_ident, _);
                                  iter rest
                             end in
                         iter all_ident_named_interped)).

      Ltac get_ident_type_of_named base base_interp all_base_and_interp is_pattern :=
        let get_type := ident_type_of_interped_type_via_list base base_interp all_base_and_interp is_pattern in
        fun lookup ident idc
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
           get_type lookup is_literal ty ident.

      Ltac build_ident_elim_via base base_interp all_base_and_interp all_ident_named_interped is_pattern :=
        let get_type := get_ident_type_of_named base base_interp all_base_and_interp is_pattern in
        let ident := lazymatch is_pattern with
                     | false => fresh "ident"
                     | true => fresh "pattern_ident"
                     end in
        let base_type := lazymatch is_pattern with
                         | false => constr:(base.type base)
                         | true => constr:(pattern.base.type base)
                         end in
        let lookup := fresh in
        let t := fresh "t" in
        let res
            := constr:(forall (lookup : positive -> Type)
                              (ident : forall t : type.type base_type, Type),
                          ltac:(let base_type_interp
                                    := lazymatch is_pattern with
                                       | false => constr:(base.interp base_interp)
                                       | true => constr:(pattern.base.interp base_interp lookup)
                                       end in
                                let rec iter ls :=
                                    lazymatch (eval hnf in ls) with
                                    | GallinaIdentList.nil
                                      => let t := fresh "t" in exact (forall t, ident t)
                                    | @GallinaIdentList.cons _ ?v ?rest
                                      => let name
                                             := lazymatch is_pattern with
                                                | false
                                                  => lazymatch v with
                                                     | with_name name _ => fresh name
                                                     | without_name ?T => fresh "ident_" T
                                                     end
                                                | true
                                                  => lazymatch v with
                                                     | with_name name _ => fresh "pattern_" name
                                                     | without_name ?T => fresh "pattern_ident_" T
                                                     end
                                                end in
                                         let ty := get_type lookup ident v in
                                         refine (forall name : ty, _);
                                         iter rest
                                    end in
                                iter all_ident_named_interped)) in
        lazymatch res with
        | _ -> ?res => res
        | ?res => constr_fail_with ltac:(fun _ => fail 1 "Cannot eliminate functional dependencies of" res)
        end.

      Ltac build_ident_elim base base_type_list_named all_ident_named_interped is_pattern :=
        (eval cbv beta zeta in
            (ltac:(let eta_base_cps_gen := build_eta_base_cps_gen base in
                   let eta_base_cps := build_eta_base_cps eta_base_cps_gen in
                   let index_of_base := build_index_of_base base in
                   let base_type_list := build_base_type_list base_type_list_named in
                   let base_interp := build_base_interp eta_base_cps base_type_list index_of_base in
                   let base_interp_name := fresh "temp_base_interp" in
                   let base_interp := cache_term base_interp base_interp_name in
                   let all_base := build_all_base base in
                   let all_base_and_interp := build_all_base_and_interp all_base base_interp in
                   let ty := build_ident_elim_via base base_interp all_base_and_interp all_ident_named_interped is_pattern in
                   exact ty))).

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

      Ltac build_base_beq base_beq_and_reflect
        := (eval cbv in (projT1 base_beq_and_reflect)).
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

      Ltac build_reflect_base_interp_beq base_interp base_interp_beq :=
        constr:(ltac:(let t := fresh "t" in
                      intro t; destruct t; cbv [base_interp base_interp_beq]; typeclasses eauto)
                : forall t, reflect_rel (@eq (base_interp t)) (@base_interp_beq t)).
      Ltac make_reflect_base_interp_beq base_interp base_interp_beq :=
        let res := build_reflect_base_interp_beq base_interp base_interp_beq in refine res.

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

      Ltac base_type_reified_hint base_type reify_type :=
        lazymatch goal with
        | [ |- @type.reified_of base_type _ ?T ?e ]
          => (* solve [ *) let rT := reify_type T in unify e rT; reflexivity (* | idtac "ERROR: Failed to reify" T ] *)
        end.

      Ltac expr_reified_hint base_type ident reify_base_type reify_ident :=
        lazymatch goal with
        | [ |- @expr.Reified_of _ ident _ _ ?t ?v ?e ]
          => (*solve [ *) let rv := expr.Reify constr:(base_type) ident ltac:(reify_base_type) ltac:(reify_ident) v in unify e rv; reflexivity (* | idtac "ERROR: Failed to reify" v "(of type" t "); try setting Reify.debug_level to see output" ] *)
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

      Ltac reify_package_of_package pkg :=
        constr:(GoalType.exprReifyInfo pkg).

      Ltac call_with_base_via_reify_package tac reify_pkg :=
        let pkgT := type of reify_pkg in
        let exprInfo := lazymatch (eval hnf in pkgT) with @GoalType.ExprReifyInfoT ?exprInfo => (eval hnf in exprInfo) end in
        let exprReifyInfo := (eval hnf in reify_pkg) in
        lazymatch exprInfo with
        | {| Classes.base := ?base
             ; Classes.base_interp := ?base_interp |}
          => lazymatch exprReifyInfo with
             | {| GoalType.all_base_and_interp := ?all_base_and_interp
                  ; GoalType.all_ident_and_interp := ?all_ident_and_interp |}
               => tac base base_interp all_base_and_interp
             end
        end.

      Ltac reify_base_via_reify_package := call_with_base_via_reify_package ltac:(reify_base_via_list).
      Ltac reify_base_type_via_reify_package := call_with_base_via_reify_package ltac:(reify_base_type_via_list).
      Ltac reify_type_via_reify_package := call_with_base_via_reify_package ltac:(reify_type_via_list).
      Ltac reify_ident_via_reify_package reify_pkg :=
        let pkgT := type of reify_pkg in
        let exprInfo := lazymatch (eval hnf in pkgT) with @GoalType.ExprReifyInfoT ?exprInfo => (eval hnf in exprInfo) end in
        let exprReifyInfo := (eval hnf in reify_pkg) in
        lazymatch exprInfo with
        | {| Classes.base := ?base
             ; Classes.base_interp := ?base_interp
             ; Classes.ident_interp := ?ident_interp |}
          => lazymatch exprReifyInfo with
             | {| GoalType.all_base_and_interp := ?all_base_and_interp
                  ; GoalType.all_ident_and_interp := ?all_ident_and_interp |}
               => reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp ident_interp
             end
        end.
      Ltac base_type_reified_hint_via_reify_package reify_pkg :=
        let pkgT := type of reify_pkg in
        let exprInfo := lazymatch (eval hnf in pkgT) with @GoalType.ExprReifyInfoT ?exprInfo => (eval hnf in exprInfo) end in
        lazymatch exprInfo with
        | {| Classes.base := ?base
             ; Classes.ident := ?ident |}
          => let base_type := constr:(base.type base) in
             let reify_type := reify_type_via_reify_package reify_pkg in
             base_type_reified_hint base_type reify_type
        end.
      Ltac expr_reified_hint_via_reify_package reify_pkg :=
        let pkgT := type of reify_pkg in
        let exprInfo := lazymatch (eval hnf in pkgT) with @GoalType.ExprReifyInfoT ?exprInfo => (eval hnf in exprInfo) end in
        lazymatch exprInfo with
        | {| Classes.base := ?base
             ; Classes.ident := ?ident |}
          => let base_type := constr:(base.type base) in
             let reify_base_type := reify_base_type_via_reify_package reify_pkg in
             let reify_ident := reify_ident_via_reify_package reify_pkg in
             expr_reified_hint base_type ident reify_base_type reify_ident
        end.

      Ltac cache_build_index_of_base base :=
        let name := fresh "index_of_base" in
        let term := build_index_of_base base in
        cache_term term name.

      Ltac cache_build_base_eq_dec base :=
        let name := fresh "base_eq_dec" in
        let term := build_base_eq_dec base in
        cache_term term name.

      Ltac cache_build_eta_base_cps_gen base :=
        let name := fresh "eta_base_cps_gen" in
        let term := build_eta_base_cps_gen base in
        cache_term term name.

      Ltac cache_build_eta_base_cps eta_base_cps_gen :=
        let name := fresh "eta_base_cps" in
        let term := build_eta_base_cps eta_base_cps_gen in
        cache_term term name.

      Ltac cache_build_base_interp eta_base_cps base_type_list index_of_base :=
        let name := fresh "base_interp" in
        let term := build_base_interp eta_base_cps base_type_list index_of_base in
        cache_term term name.

      Ltac cache_build_all_gen T mk P :=
        let name := fresh "all_gen" in
        let term := build_all_gen T mk P in
        cache_term term name.

      Ltac cache_build_all_base base :=
        let name := fresh "all_base" in
        let term := build_all_base base in
        cache_term term name.

      Ltac cache_build_all_base_and_interp all_base base_interp :=
        let name := fresh "all_base_and_interp" in
        let term := build_all_base_and_interp all_base base_interp in
        cache_term term name.

      Ltac cache_build_base_type_list base_type_list_named :=
        let name := fresh "base_type_list" in
        let term := build_base_type_list base_type_list_named in
        cache_term term name.

      Ltac cache_build_baseHasNatAndCorrect base_interp :=
        let name := fresh "baseHasNatAndCorrect" in
        let term := build_baseHasNatAndCorrect base_interp in
        cache_term term name.

      Ltac cache_build_baseHasNat base baseHasNatAndCorrect :=
        let name := fresh "baseHasNat" in
        let term := build_baseHasNat base baseHasNatAndCorrect in
        cache_term term name.

      Ltac cache_build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect :=
        let name := fresh "baseHasNatCorrect" in
        let term := build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect in
        cache_term term name.

      Ltac cache_build_base_beq_and_reflect base :=
        let name := fresh "base_beq_and_reflect" in
        let term := build_base_beq_and_reflect base in
        cache_term term name.

      Ltac cache_build_base_beq base_beq_and_reflect :=
        let name := fresh "base_beq" in
        let term := build_base_beq base_beq_and_reflect in
        cache_term term name.

      Ltac cache_build_reflect_base_beq base base_beq base_beq_and_reflect :=
        let name := fresh "reflect_base_beq" in
        let term := build_reflect_base_beq base base_beq base_beq_and_reflect in
        cache_term term name.

      Ltac cache_build_base_interp_beq base_interp :=
        let name := fresh "base_interp_beq" in
        let term := build_base_interp_beq base_interp in
        cache_term term name.

      Ltac cache_build_reflect_base_interp_beq base_interp base_interp_beq :=
        let name := fresh "reflect_base_interp_beq" in
        let term := build_reflect_base_interp_beq base_interp base_interp_beq in
        cache_term term name.

      Ltac cache_build_try_make_base_transport_cps base_eq_dec eta_base_cps :=
        let name := fresh "try_make_base_transport_cps" in
        let term := build_try_make_base_transport_cps base_eq_dec eta_base_cps in
        cache_term term name.

      Ltac cache_build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq :=
        let name := fresh "try_make_base_transport_cps_correct" in
        let term := build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq in
        cache_term term name.

      Ltac cache_build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident :=
        let name := fresh "buildEagerIdentAndInterpCorrect" in
        let term := build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident in
        cache_term term name.

      Ltac cache_build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect :=
        let name := fresh "buildEagerIdent" in
        let term := build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect :=
        let name := fresh "buildInterpEagerIdentCorrect" in
        let term := build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent :=
        let name := fresh "toRestrictedIdentAndCorrect" in
        let term := build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent in
        cache_term term name.

      Ltac cache_build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect :=
        let name := fresh "toRestrictedIdent" in
        let term := build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect :=
        let name := fresh "toFromRestrictedIdent" in
        let term := build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_buildIdentAndInterpCorrect ident_interp reify_ident :=
        let name := fresh "buildIdentAndInterpCorrect" in
        let term := build_buildIdentAndInterpCorrect ident_interp reify_ident in
        cache_term term name.

      Ltac cache_build_buildIdent base_interp ident buildIdentAndInterpCorrect :=
        let name := fresh "buildIdent" in
        let term := build_buildIdent base_interp ident buildIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect :=
        let name := fresh "buildInterpIdentCorrect" in
        let term := build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect in
        cache_term term name.

      Ltac cache_build_ident_is_var_like ident ident_interp var_like_idents :=
        let name := fresh "ident_is_var_like" in
        let term := build_ident_is_var_like ident ident_interp var_like_idents in
        cache_term term name.

      Ltac cache_build_eqv_Reflexive_Proper ident_interp base_interp :=
        let name := fresh "eqv_Reflexive_Proper" in
        let term := build_eqv_Reflexive_Proper ident_interp base_interp in
        cache_term term name.

      Ltac cache_build_ident_interp_Proper ident_interp eqv_Reflexive_Proper :=
        let name := fresh "ident_interp_Proper" in
        let term := build_ident_interp_Proper ident_interp eqv_Reflexive_Proper in
        cache_term term name.

      Ltac cache_build_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq :=
        let name := fresh "invertIdentAndCorrect" in
        let term := build_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq in
        cache_term term name.

      Ltac cache_build_invertIdent base_interp ident invertIdentAndCorrect :=
        let name := fresh "invertIdent" in
        let term := build_invertIdent base_interp ident invertIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_buildInvertIdentCorrect base_interp invertIdent buildIdent invertIdentAndCorrect :=
        let name := fresh "buildInvertIdentCorrect" in
        let term := build_buildInvertIdentCorrect base_interp invertIdent buildIdent invertIdentAndCorrect in
        cache_term term name.

      Ltac cache_build_base_default base_interp :=
        let name := fresh "base_default" in
        let term := build_base_default base_interp in
        cache_term term name.

      Ltac cache_build_index_of_ident ident :=
        let name := fresh "index_of_ident" in
        let term := build_index_of_ident ident in
        cache_term term name.

      Ltac cache_build_ident_interp base_interp ident index_of_ident all_ident_named_interped :=
        let name := fresh "ident_interp" in
        let term := build_ident_interp base_interp ident index_of_ident all_ident_named_interped in
        cache_term term name.

      Ltac cache_build_all_idents ident :=
        let name := fresh "all_idents" in
        let term := build_all_idents ident in
        cache_term term name.

      Ltac cache_build_all_ident_and_interp all_idents all_ident_named_interped :=
        let name := fresh "all_ident_and_interp" in
        let term := build_all_ident_and_interp all_idents all_ident_named_interped in
        cache_term term name.
    End Tactics.

    Module PrintHelpers.
      Ltac make_ident_from_build build :=
        idtac;
        lazymatch goal with
        | [ |- GoalType.ident_elim_with_args ?scraped_data ?base ]
          => cbv [GoalType.ident_elim_with_args];
             lazymatch (eval hnf in scraped_data) with
             | {| ScrapedData.base_type_list_named := ?base_type_list_named
                  ; ScrapedData.all_ident_named_interped := ?all_ident_named_interped |}
               => let res := build base base_type_list_named all_ident_named_interped in
                  refine res
             end
        end.
    End PrintHelpers.

    Module PrintBase.
      Ltac build_base_elim base_type_list_named :=
        Tactics.build_base_elim base_type_list_named.

      Ltac make_base_elim :=
        idtac;
        lazymatch goal with
        | [ |- GoalType.base_elim_with_args ?scraped_data ]
          => cbv [GoalType.base_elim_with_args];
             lazymatch (eval hnf in scraped_data) with
             | {| ScrapedData.base_type_list_named := ?base_type_list_named |}
               => let res := build_base_elim base_type_list_named in
                  refine res
             end
        end.

      Ltac print_base base_type_list_named :=
        let elimT := build_base_elim base_type_list_named in
        Tactics.print_ind_of_elim elimT.
    End PrintBase.

    Module PrintIdent.
      Import PrintHelpers.
      Ltac build_ident_elim base base_type_list_named all_ident_named_interped :=
        Tactics.build_ident_elim base base_type_list_named all_ident_named_interped false.
      Ltac build_pattern_ident_elim base base_type_list_named all_ident_named_interped :=
        Tactics.build_ident_elim base base_type_list_named all_ident_named_interped true.
      Ltac build_raw_ident_elim all_ident_named_interped :=
        Tactics.build_raw_ident_elim all_ident_named_interped.

      Ltac make_ident_elim := make_ident_from_build build_ident_elim.
      Ltac make_pattern_ident_elim := make_ident_from_build build_pattern_ident_elim.
      Ltac make_raw_ident_elim :=
        make_ident_from_build ltac:(fun base base_type_list_named all_ident_named_interped => build_raw_ident_elim all_ident_named_interped).

      Ltac print_ident base base_type_list_named all_ident_named_interped :=
        let ident_elimT := build_ident_elim base base_type_list_named all_ident_named_interped in
        let pattern_ident_elimT := build_pattern_ident_elim base base_type_list_named all_ident_named_interped in
        let raw_ident_elimT := build_raw_ident_elim all_ident_named_interped in
        print_ind_of_elim ident_elimT;
        print_ind_of_elim pattern_ident_elimT;
        print_ind_of_elim raw_ident_elimT.
    End PrintIdent.

    Module Tactic.
      Ltac reify_package_of_package := Tactics.reify_package_of_package.

      Ltac reify_base_via_reify_package := Tactics.reify_base_via_reify_package.
      Ltac reify_base_type_via_reify_package := Tactics.reify_base_type_via_reify_package.
      Ltac reify_type_via_reify_package := Tactics.reify_type_via_reify_package.
      Ltac reify_ident_via_reify_package := Tactics.reify_ident_via_reify_package.
      Ltac base_type_reified_hint_via_reify_package := Tactics.base_type_reified_hint_via_reify_package.
      Ltac expr_reified_hint_via_reify_package := Tactics.expr_reified_hint_via_reify_package.

      Ltac build_package base ident base_type_list_named var_like_idents all_ident_named_interped :=
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building index_of_base...") in
        let index_of_base := cache_build_index_of_base base in
        let base_type := constr:(@base.type base) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_type_list...") in
        let base_type_list := cache_build_base_type_list base_type_list_named in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_base_cps_gen...") in
        let eta_base_cps_gen := cache_build_eta_base_cps_gen base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eta_base_cps...") in
        let eta_base_cps := cache_build_eta_base_cps eta_base_cps_gen in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_interp...") in
        let base_interp := cache_build_base_interp eta_base_cps base_type_list index_of_base in
        let base_type_interp := constr:(base.interp base_interp) in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_base...") in
        let all_base := cache_build_all_base base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_base_and_interp...") in
        let all_base_and_interp := cache_build_all_base_and_interp all_base base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building index_of_ident...") in
        let index_of_ident := cache_build_index_of_ident ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_interp...") in
        let ident_interp := cache_build_ident_interp base_interp ident index_of_ident all_ident_named_interped in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_eq_dec...") in
        let base_eq_dec := cache_build_base_eq_dec base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_beq_and_reflect...") in
        let base_beq_and_reflect := cache_build_base_beq_and_reflect base in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_beq...") in
        let base_beq := cache_build_base_beq base_beq_and_reflect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building reflect_base_beq...") in
        let reflect_base_beq := cache_build_reflect_base_beq base base_beq base_beq_and_reflect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNatAndCorrect...") in
        let baseHasNatAndCorrect := cache_build_baseHasNatAndCorrect base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNat...") in
        let baseHasNat := cache_build_baseHasNat base baseHasNatAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building baseHasNatCorrect...") in
        let baseHasNatCorrect := cache_build_baseHasNatCorrect base_interp baseHasNat baseHasNatAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_interp_beq...") in
        let base_interp_beq := cache_build_base_interp_beq base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building reflect_base_interp_beq...") in
        let reflect_base_interp_beq := cache_build_reflect_base_interp_beq base_interp base_interp_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building try_make_base_transport_cps...") in
        let try_make_base_transport_cps := cache_build_try_make_base_transport_cps base_eq_dec eta_base_cps in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building try_make_base_transport_cps_correct...") in
        let try_make_base_transport_cps_correct := cache_build_try_make_base_transport_cps_correct try_make_base_transport_cps reflect_base_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_idents...") in
        let all_idents := cache_build_all_idents ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building all_ident_and_interp...") in
        let all_ident_and_interp := cache_build_all_ident_and_interp all_idents all_ident_named_interped in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildEagerIdentAndInterpCorrect...") in
        let reify_ident := reify_ident_via_list base base_interp all_base_and_interp all_ident_and_interp (@ident_interp) in
        let buildEagerIdentAndInterpCorrect := cache_build_buildEagerIdentAndInterpCorrect ident_interp baseHasNat baseHasNatCorrect reify_ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildEagerIdent...") in
        let buildEagerIdent := cache_build_buildEagerIdent ident baseHasNat buildEagerIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInterpEagerIdentCorrect...") in
        let buildInterpEagerIdentCorrect := cache_build_buildInterpEagerIdentCorrect ident_interp buildEagerIdent baseHasNatCorrect buildEagerIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toRestrictedIdentAndCorrect...") in
        let toRestrictedIdentAndCorrect := cache_build_toRestrictedIdentAndCorrect baseHasNat buildEagerIdent in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toRestrictedIdent...") in
        let toRestrictedIdent := cache_build_toRestrictedIdent ident baseHasNat toRestrictedIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building toFromRestrictedIdent...") in
        let toFromRestrictedIdent := cache_build_toFromRestrictedIdent baseHasNat buildEagerIdent toRestrictedIdent toRestrictedIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildIdentAndInterpCorrect...") in
        let buildIdentAndInterpCorrect := cache_build_buildIdentAndInterpCorrect ident_interp reify_ident in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildIdent...") in
        let buildIdent := cache_build_buildIdent base_interp ident buildIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInterpIdentCorrect...") in
        let buildInterpIdentCorrect := cache_build_buildInterpIdentCorrect ident_interp buildIdent buildIdentAndInterpCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_is_var_like...") in
        let ident_is_var_like := cache_build_ident_is_var_like ident ident_interp var_like_idents in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building eqv_Reflexive_Proper...") in
        let eqv_Reflexive_Proper := cache_build_eqv_Reflexive_Proper ident_interp base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building ident_interp_Proper...") in
        let ident_interp_Proper := cache_build_ident_interp_Proper ident_interp eqv_Reflexive_Proper in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building invertIdentAndCorrect...") in
        let invertIdentAndCorrect := cache_build_invertIdentAndCorrect base_type base_interp buildIdent reflect_base_beq in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building invertIdent...") in
        let invertIdent := cache_build_invertIdent base_interp ident invertIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building buildInvertIdentCorrect...") in
        let buildInvertIdentCorrect := cache_build_buildInvertIdentCorrect base_interp invertIdent buildIdent invertIdentAndCorrect in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building base_default...") in
        let base_default := cache_build_base_default base_interp in
        let __ := Tactics.debug1 ltac:(fun _ => idtac "Building package...") in
        let exprInfo
            := constr:(@Classes.Build_ExprInfoT
                         base
                         ident
                         base_interp
                         ident_interp) in
        constr:(@GoalType.Build_package
                  exprInfo
                  (ltac:(
                     econstructor;
                     first [ exact base_default
                           | exact (@reflect_base_interp_beq)
                           | exact try_make_base_transport_cps_correct
                           | exact toFromRestrictedIdent
                           | exact buildInvertIdentCorrect
                           | exact (@buildInterpIdentCorrect)
                           | exact (@buildInterpEagerIdentCorrect)
                           | exact (@ident_interp_Proper) ]))
                  (@GoalType.Build_ExprReifyInfoT
                     exprInfo
                     all_base_and_interp
                     all_ident_and_interp)
                  ident_is_var_like).
      Ltac make_package_via base ident base_type_list_named var_like_idents all_ident_named_interped :=
        let res := build_package base ident base_type_list_named var_like_idents all_ident_named_interped in refine res.

      Ltac build_package_of_scraped scraped_data var_like_idents base ident :=
        lazymatch (eval hnf in scraped_data) with
        | {| ScrapedData.all_ident_named_interped := ?all_ident_named_interped
             ; ScrapedData.base_type_list_named := ?base_type_list_named |}
          => build_package base ident base_type_list_named var_like_idents all_ident_named_interped
        end.
      Ltac make_package_of_scraped scraped_data var_like_idents base ident :=
        let res := build_package_of_scraped scraped_data var_like_idents base ident in refine res.
      Ltac make_package :=
        idtac;
        lazymatch goal with
        | [ |- GoalType.package_with_args ?scraped_data ?var_like_idents ?base ?ident ]
          => cbv [GoalType.package_with_args];
             make_package_of_scraped scraped_data var_like_idents base ident
        end.
      Ltac cache_build_package_of_scraped scraped_data var_like_idents base ident :=
        let name := fresh "package" in
        let term := build_package_of_scraped scraped_data var_like_idents base ident in
        cache_term term name.
    End Tactic.
  End Basic.
End Compilers.
