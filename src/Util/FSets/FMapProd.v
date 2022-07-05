Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.SetoidListFlatMap.
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Relations.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Prod.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Prod.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapFacts.
Require Import Crypto.Util.Sorting.Sorted.Proper.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.

Local Set Implicit Arguments.
(* TODO: move to global settings *)
Local Set Keyed Unification.
Local Open Scope option_scope.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope type_scope.

Module ProdWSfun_gen (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).
  Module Type ESig := ProdTyp E1 E2 <+ HasEq <+ IsEqOrig <+ HasEqDec.
  Module Type ESigCompat (E : ESig).
    Axiom eq_alt : forall x y, E.eq x y <-> RelProd E1.eq E2.eq x y.
  End ESigCompat.
  Module E1 <: DecidableTypeBoth := E1 <+ UpdateEq.
  Global Remove Hints E1.eq_refl E1.eq_sym E1.eq_trans : core.
  Module E2 <: DecidableTypeBoth := E2 <+ UpdateEq.
  Global Remove Hints E2.eq_refl E2.eq_sym E2.eq_trans : core.
  Module M1' := M1 <+ WFacts_fun E1 <+ WFacts_fun_RemoveHints E1 <+ WAdditionalFacts_fun E1.
  Module M2' := M2 <+ WFacts_fun E2 <+ WFacts_fun_RemoveHints E2 <+ WAdditionalFacts_fun E2.
  Local Existing Instances
        M1'.Empty_m_Proper M1'.In_m_Proper M1'.MapsTo_m_Proper M1'.add_m_Proper M1'.find_m_Proper M1'.is_empty_m_Proper M1'.map_m_Proper M1'.mem_m_Proper M1'.remove_m_Proper
        M2'.Empty_m_Proper M2'.In_m_Proper M2'.MapsTo_m_Proper M2'.add_m_Proper M2'.find_m_Proper M2'.is_empty_m_Proper M2'.map_m_Proper M2'.mem_m_Proper M2'.remove_m_Proper
  | 10.
  Local Existing Instances
        M1'.eq_key_equiv M1'.eq_key_elt_equiv M1'.Equal_Equivalence
        M2'.eq_key_equiv M2'.eq_key_elt_equiv M2'.Equal_Equivalence
  | 10.
  Local Existing Instances
        M1'.Proper_eq_key_elt_iff M1'.Proper_eq_key_elt_impl M1'.Proper_eq_key_elt_flip_impl M1'.Proper_eq_key_elt_iff' M1'.Proper_eq_key_elt_impl' M1'.Proper_eq_key_elt_flip_impl' M1'.Proper_eq_key_iff M1'.Proper_eq_key_impl M1'.Proper_eq_key_flip_impl M1'.find_Proper_eq M1'.MapsTo_Proper_eq_iff M1'.In_compat M1'.Proper_Equiv_eq_impl M1'.Proper_Equiv_eq_flip_impl M1'.Proper_Equiv_eq_iff M1'.Proper_Equiv_eq_impl_pointwise M1'.Proper_Equiv_eq_flip_impl_pointwise M1'.Proper_Equiv_eq_iff_pointwise
        M2'.Proper_eq_key_elt_iff M2'.Proper_eq_key_elt_impl M2'.Proper_eq_key_elt_flip_impl M2'.Proper_eq_key_elt_iff' M2'.Proper_eq_key_elt_impl' M2'.Proper_eq_key_elt_flip_impl' M2'.Proper_eq_key_iff M2'.Proper_eq_key_impl M2'.Proper_eq_key_flip_impl M2'.find_Proper_eq M2'.MapsTo_Proper_eq_iff M2'.In_compat M2'.Proper_Equiv_eq_impl M2'.Proper_Equiv_eq_flip_impl M2'.Proper_Equiv_eq_iff M2'.Proper_Equiv_eq_impl_pointwise M2'.Proper_Equiv_eq_flip_impl_pointwise M2'.Proper_Equiv_eq_iff_pointwise
  .
  Module ProdWSfun_gen (E : ESig) (ECompat : ESigCompat E) <: WSfun E.
    Module E' <: DecidableTypeBoth := E <+ UpdateEq <+ ECompat.
    Global Remove Hints E'.eq_refl E'.eq_sym E'.eq_trans : core.
    Local Hint Resolve E1.eq_refl E1.eq_sym E1.eq_trans
          E2.eq_refl E2.eq_sym E2.eq_trans
          E'.eq_refl E'.eq_sym E'.eq_trans
      : core.

    Definition key := E.t.

    Global Hint Transparent key : core.

    (* Create a record so that the normal form of the type isn't exponentially sized when we nest things, see COQBUG(https://github.com/coq/coq/issues/16172) *)
    Record M2_t_NonEmpty elt := { M2_m :> M2.t elt ; M2_NonEmpty :> ~M2.Empty M2_m }.
    Global Arguments Build_M2_t_NonEmpty [elt] _ _.
    Local Notation M2_mk := (@Build_M2_t_NonEmpty _).
    Definition t elt := M1.t (M2_t_NonEmpty elt).

    Local Ltac t_obgl :=
      repeat first [ progress intros
                   | progress cbv [M2.Empty Option.value not option_map] in *
                   | progress cbn [M2_m] in *
                   | reflexivity
                   | exfalso; assumption
                   | congruence
                   | match goal with
                     | [ H := _ |- _ ] => subst H
                     | [ H : forall a e, M2.MapsTo _ _ (M2.add _ _ _) -> False |- _ ]
                       => specialize (H _ _ ltac:(eapply M2.add_1; reflexivity))
                     | [ H : context[M2.is_empty] |- _ ]
                       => rewrite M2.is_empty_1 in H by assumption
                     | [ H : forall a e, M2.MapsTo a e (M2.mapi ?f ?m) -> False |- _ ]
                       => assert (forall a e, M2.MapsTo a e m -> False)
                         by (let H' := fresh in
                             intros ? ? H'; eapply M2.mapi_1 in H'; destruct H' as [?[? H']];
                             eapply H, H');
                          clear H
                     | [ H : forall k e, _ = _ -> M2.In _ _ \/ M2.In _ _ -> False |- _ ]
                       => pose proof (fun k e pf pf' => H k e (pf pf') (or_introl pf'));
                          pose proof (fun k e pf pf' => H k e (pf pf') (or_intror pf'));
                          clear H
                     end
                   | progress subst
                   | progress specialize_under_binders_by eapply M2.map_1
                   | progress destruct_head' M2_t_NonEmpty
                   | progress destruct_head'_and
                   | progress destruct_head' option
                   | progress break_innermost_match_hyps
                   | progress specialize_under_binders_by (match goal with |- M2.MapsTo _ _ (M2.map2 _ _ _) => idtac end;
                                                           eapply M2.find_2;
                                                           rewrite M2.map2_1) ].

    Local Obligation Tactic := try abstract t_obgl; t_obgl.

    Definition empty elt : t elt := @M1.empty _.
    Definition is_empty elt : t elt -> bool := @M1.is_empty _.
    Program Definition add elt (k : key) (v : elt) (m : t elt) : t elt
      := let m2 := M2.add (snd k) v (Option.value (option_map (@M2_m _) (M1.find (fst k) m)) (@M2.empty _)) in
         M1.add (fst k) (M2_mk m2 _) m.
    Definition find elt (k : key) (m : t elt) : option elt
      := m2 <- M1.find (fst k) m; M2.find (snd k) (M2_m m2).
    Program Definition remove elt (k : key) (m : t elt) : t elt
      := match M1.find (fst k) m with
         | None => m
         | Some m2
           => let m2 := M2.remove (snd k) m2 in
              match M2.is_empty m2 with
              | true => M1.remove (fst k) m
              | false => M1.add (fst k) (M2_mk m2 _) m
              end
         end.
    Definition mem elt (k : key) (m : t elt) : bool
      := match find k m with Some _ => true | _ => false end.
    Program Definition map elt elt' (f : elt -> elt') : t elt -> t elt'
      := M1.map (fun m => M2_mk (M2.map f (M2_m m)) _).
    Program Definition mapi elt elt' (f : key -> elt -> elt') : t elt -> t elt'
      := M1.mapi (fun k1 m => M2_mk (M2.mapi (fun k2 => f (k1, k2)) (M2_m m)) _).
    Program Definition map2 elt elt' elt'' (f : option elt -> option elt' -> option elt'')
            (f' := match f None None with
                   | None => f
                   | _ => fun x y => match x, y with
                                     | None, None => None
                                     | _, _ => f x y
                                     end
                   end)
      : t elt -> t elt' -> t elt''
      := M1.map2 (fun m1 m2
                  => if match m1, m2 with None, None => true | _, _ => false end
                     then None
                     else
                       let m1' := Option.value (option_map (@M2_m _) m1) (M2.empty _) in
                       let m2' := Option.value (option_map (@M2_m _) m2) (M2.empty _) in
                       let m' := M2.map2 f' m1' m2' in
                       match M2.is_empty m' with
                       | true => None
                       | false => Some (M2_mk m' _)
                       end).
    Definition elements elt (m : t elt) : list (key * elt)
      := List.flat_map (fun '(k1, m) => List.map (fun '(k2, v) => ((k1, k2), v)) (M2.elements (M2_m m))) (M1.elements m).
    Definition cardinal elt (m : t elt) : nat := List.length (elements m).
    Definition fold elt A (f : key -> elt -> A -> A) : t elt -> A -> A
      := M1.fold (fun k1 m => M2.fold (fun k2 => f (k1, k2)) (M2_m m)).
    Definition equal elt (eqb : elt -> elt -> bool) : t elt -> t elt -> bool
      := M1.equal (fun m m' => M2.equal eqb (M2_m m) (M2_m m')).
    Definition MapsTo elt (k : key) (v : elt) (m : t elt) : Prop
      := exists m2, M1.MapsTo (fst k) m2 m /\ M2.MapsTo (snd k) v (M2_m m2).
    Definition eq_key elt (p p':key*elt) := E.eq (fst p) (fst p').
    Definition eq_key_elt elt (p p':key*elt) :=
      E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    Definition In elt (k : key) (m : t elt) := exists e, MapsTo k e m.
    Definition Empty elt (m : t elt) := forall a e, ~ MapsTo a e m.
    Definition Equal elt (m m' : t elt) := forall y, find y m = find y m'.
    Definition Equiv elt (eq_elt:elt->elt->Prop) m m' :=
      (forall k, In k m <-> In k m') /\
        (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb elt (cmp: elt->elt->bool) := Equiv (Cmp cmp).

    Module Import _Extra1.
      Local Instance eq_key_equiv elt : Equivalence (@eq_key elt) | 10.
      Proof.
        split; cbv; intros; break_innermost_match; break_innermost_match_hyps; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
      Qed.
      Local Instance eq_key_elt_equiv elt : Equivalence (@eq_key_elt elt) | 10.
      Proof.
        split; cbv; intros; break_innermost_match; break_innermost_match_hyps; destruct_head'_and; split; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
      Qed.

      Definition Empty_alt elt (m : t elt) : Prop := M1.Empty m.
      (*Definition In_alt elt (k : key) (m : t elt) : Prop := liftKT_ (@M1.In elt) (@M2.In elt).
    Definition Equal_alt elt (m m' : t elt) : Prop := M1.Equal (fst m) (fst m') /\ M2.Equal (snd m) (snd m').*)
      Definition Equiv_alt elt (cmp : elt -> elt -> Prop) (m m' : t elt) : Prop := M1.Equiv (fun m m' => M2.Equiv cmp (M2_m m) (M2_m m')) m m'.
      (*Definition Equivb_alt elt (cmp : elt -> elt -> bool) (m m' : t elt) : Prop := M1.Equivb cmp (fst m) (fst m') /\ M2.Equivb cmp (snd m) (snd m').
       *)

      (*  Lemma In_alt_iff elt k (s : t elt) : In k s <-> In_alt k s.
    Proof. t_alt_iff. Qed.
    Lemma Equal_alt_iff elt (s s' : t elt) : Equal s s' <-> Equal_alt s s'.
    Proof. t_alt_iff. Qed.*)
      Lemma Empty_alt_iff elt (s : t elt) : Empty s <-> Empty_alt s.
      Proof.
        cbv [Empty Empty_alt MapsTo M1.Empty M2.Empty not M2.key key M1.key E.t].
        split; repeat intro.
        all: repeat first [ progress destruct_head' M2_t_NonEmpty
                          | progress destruct_head'_ex
                          | progress destruct_head'_and
                          | progress specialize_dep_under_binders_by apply pair
                          | progress specialize_dep_under_binders_by eexists
                          | progress cbn [fst snd proj1_sig] in *
                          | progress specialize_under_binders_by eassumption
                          | solve [ eauto ] ].
      Qed.
      Lemma Equiv_alt_iff elt eq_elt (s s' : t elt) : Equiv eq_elt s s' <-> Equiv_alt eq_elt s s'.
      Proof.
        cbv [Equiv Equiv_alt MapsTo In M1.Equiv M2.Equiv M1.In M2.In key M1.key M2.key not].
        setoid_rewrite M1'.find_mapsto_iff; setoid_rewrite M2'.find_mapsto_iff.
        split; [ pose I as FWD | pose I as BAK ].
        all: repeat first [ progress intros
                          | progress destruct_head' M2_t_NonEmpty
                          | progress destruct_head'_ex
                          | progress destruct_head'_and
                          | progress split_iff
                          | progress specialize_dep_under_binders_by apply pair
                          | progress specialize_dep_under_binders_by eexists
                          | progress cbn [fst snd ProdWSfun_gen.M2_m] in *
                          | progress cbv [not] in *
                          | apply conj
                          | match goal with
                            | [ |- context[@M1.find ?a ?b ?c] ] => destruct (@M1.find a b c) eqn:?
                            | [ |- context[@M2.find ?a ?b ?c] ] => destruct (@M2.find a b c) eqn:?
                            end
                          | solve [ eauto ]
                          | congruence
                          | progress specialize_under_binders_by eassumption ].
        all: lazymatch goal with
             | [ H : forall t e, M2.find t ?m = Some e -> ex _, H' : M2.Empty ?m -> False |- _ ]
               => specialize (fun t e H' => H t e ltac:(apply M2.find_1, M2.elements_2, H'));
                  let H'' := fresh in
                  let H''' := fresh in
                  pose proof H' as H'';
                  cbv [M2.Empty not] in H'';
                  specialize (fun (H''' : forall a e, ~ _) => H'' (fun a e pf => ltac:(eapply (H''' a e), M2.elements_1, pf)));
                  setoid_rewrite InA_alt in H'';
                  cbv [not M2.eq_key_elt] in H'';
                  destruct (M2.elements m);
                  cbn [List.In] in H'';
                  [ specialize (H'' ltac:(firstorder tauto));
                    exfalso; assumption
                  | specialize_under_binders_by eapply InA_cons_hd ]
             end.
        all: repeat first [ progress cbv [M2.eq_key_elt] in *
                          | progress cbn [fst snd proj1_sig] in *
                          | progress destruct_head' M2_t_NonEmpty
                          | progress destruct_head'_ex
                          | progress destruct_head'_and
                          | progress specialize_dep_under_binders_by apply conj
                          | progress specialize_dep_under_binders_by reflexivity
                          | congruence ].
      Qed.
      (*
    Lemma Equivb_alt_iff elt cmp (s s' : t elt) : Equivb cmp s s' <-> Equivb_alt cmp s s'.
    Proof. t_alt_iff. Qed.
       *)
    End _Extra1.
    Local Existing Instances eq_key_equiv eq_key_elt_equiv | 10.

    Create HintDb prod_map_alt discriminated.
    Create HintDb prod_map_alt1 discriminated.
    Create HintDb prod_map_alt2 discriminated.
    Create HintDb prod_map_alt3 discriminated.

    Global
      Hint Unfold
      (*In_alt*)
      empty
      is_empty
      mem
      add
      find
      remove
      mem
      map
      mapi
      map2
      elements
      cardinal
      fold
      equal
      MapsTo
      In
      Empty
      Empty_alt
      Equiv_alt
      (*Equivb_alt*)
      eq_key
      eq_key_elt
      M1.eq_key
      M1.eq_key_elt
      M2.eq_key
      M2.eq_key_elt
      option_map
      RelProd
      relation_conjunction
      predicate_intersection
      pointwise_extension
      RelCompFun
      Option.bind
      option_map
      Option.value
      not
      : prod_map_alt.

    Hint Rewrite (*In_alt_iff*) Empty_alt_iff (*Equal_alt_iff*) Equiv_alt_iff (*Equivb_alt_iff*)
         M1.cardinal_1
         M1.fold_1
         M2.cardinal_1
         M2.fold_1
         M1'.find_mapsto_iff
         M2'.find_mapsto_iff
         M1'.find_empty
         M2'.find_empty
         M1'.add_o
         M2'.add_o
         M1'.remove_o
         M2'.remove_o
         M1'.map_o
         M2'.map_o
         M1'.map2_o
         M2'.map2_o
         E'.eq_alt
         Bool.andb_true_iff
         InA_app_iff
         map_length
         app_length
         fold_left_map
         fold_left_app
         in_map_iff
         in_flat_map
      : prod_map_alt.

    Global Hint Resolve
           M1.MapsTo_1
           M1.mem_1
           M1.empty_1
           M1'.empty_1'
           M1.is_empty_1
           M1.add_1
           M1.remove_1
           M1.find_1
           M1.elements_1
           M1.equal_1
           M1.map_1
           M1.mapi_1
           M1.map2_1
           M2.MapsTo_1
           M2.mem_1
           M2.empty_1
           M2'.empty_1'
           M2.is_empty_1
           M2.add_1
           M2.remove_1
           M2.find_1
           M2.elements_1
           M2.equal_1
           M2.map_1
           M2.mapi_1
           M2.map2_1
      : prod_map_alt1.
    Global Hint Resolve
           M1.mem_2
           M1.is_empty_2
           M1.add_2
           M1.remove_2
           M1.find_2
           M1.elements_2
           M1.equal_2
           M1.map_2
           M1.mapi_2
           M1.map2_2
           M2.mem_2
           M2.is_empty_2
           M2.add_2
           M2.remove_2
           M2.find_2
           M2.elements_2
           M2.equal_2
           M2.map_2
           M2.mapi_2
           M2.map2_2
      : prod_map_alt2.
    Global Hint Resolve
           M1.add_3
           M1.remove_3
           M1.elements_3w
           M2.add_3
           M2.remove_3
           M2.elements_3w
      : prod_map_alt3.

    Hint Constructors ex and or
      : prod_map_alt1 prod_map_alt2 prod_map_alt3.
    Hint Extern 10
         => progress unfold M1.In, M2.In in *
             : prod_map_alt1 prod_map_alt2 prod_map_alt3.

  Local Ltac t :=
    repeat first [ progress intros
                 | progress subst
                 | progress inversion_option
                 | progress inversion_pair
                 | progress inversion_list
                 | reflexivity
                 | discriminate
                 | progress cbv [not] in *
                 | solve [ exfalso; auto with nocore ]
                 | progress specialize_by_assumption
                 | progress destruct_head'_ex
                 | progress destruct_head'_and
                 | progress break_innermost_match
                 | progress break_innermost_match_hyps
                 | progress destruct_head'_or
                 | progress cbv [Option.is_Some Option.is_None Option.value Option.bind M1.eq_key_elt M2.eq_key_elt] in *
                 | progress autounfold with prod_map_alt in *
                 | match goal with
                   | [ H : eqlistA _ nil _ |- _ ] => inversion H; clear H
                   | [ H : eqlistA _ _ nil |- _ ] => inversion H; clear H
                   | [ H : eqlistA _ (_ :: _) _ |- _ ] => inversion H; clear H
                   | [ H : eqlistA _ _ (_ :: _) |- _ ] => inversion H; clear H
                   | [ H : InA _ _ (_ :: _) |- _ ] => inversion H; clear H
                   | [ H : InA _ _ nil |- _ ] => inversion H; clear H
                   | [ H : List.In _ (List.map _ _) |- _ ] => rewrite in_map_iff in H
                   | [ H : List.In _ (List.flat_map _ _) |- _ ] => rewrite in_flat_map in H
                   | [ H : ?x = ?x |- _ ] => clear H
                   | [ H : ?T, H' : ?T |- _ ] => clear H
                   | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                   | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                   | [ H : Some _ = ?x |- _ ] => symmetry in H
                   | [ H : None = ?x |- _ ] => symmetry in H
                   end
                 | progress autorewrite with prod_map_alt in *
                 | solve [ eauto using ex_intro, eq_refl with nocore ]
                 | progress specialize_by reflexivity
                 | progress specialize_under_binders_by reflexivity
                 | progress specialize_under_binders_by progress autorewrite with prod_map_alt
                 | progress cbn in * ].

  Local Ltac pose_MapsTo_as_find lem :=
    let H := fresh in
    first [ (pose proof M1.find_1 as H + pose proof M2.find_1 as H);
            guarded_specialize_hyp_under_binders_by guard_nondep H ltac:(eapply lem; try first [ eapply M1.find_2 | eapply M2.find_2 ])
          | pose proof lem as H;
            guarded_specialize_hyp_under_binders_by guard_nondep H ltac:(first [ eapply M1.find_2 | eapply M2.find_2 ]) ].

    Local Ltac spec_t_step_quick
      := first [ progress intros
               | progress cbn [fst snd proj1_sig] in *
               | apply (f_equal2 (@pair _ _))
               | progress destruct_head'_False
               | rewrite <- andb_lazy_alt
               | progress repeat autorewrite with prod_map_alt in *
               | progress change E1.t with M1.key in *
               | progress change E2.t with M2.key in *
               | progress repeat autounfold with prod_map_alt in *
               | match goal with H : _ |- _ => refine H end
               | congruence
               | reflexivity
               | progress auto
               | exact _
               | progress destruct_head'_and
               | progress destruct_head'_ex
               | progress break_innermost_match_hyps
               | progress break_innermost_match
               | progress destruct_head'_or
               | progress specialize_under_binders_by eassumption
               | progress inversion_option
               | progress subst
               | match goal with
                 | [ H : M1.MapsTo ?k ?v ?m, H' : context[M1.find ?k ?m] |- _ ]
                   => erewrite M1.find_1 in H' by exact H
                 | [ H : M2.MapsTo ?k ?v ?m, H' : context[M2.find ?k ?m] |- _ ]
                   => erewrite M2.find_1 in H' by exact H
                 end
               | progress specialize_under_binders_by apply conj ].

    Global Hint Extern 100
           => spec_t_step_quick
             : prod_map_alt1 prod_map_alt2 prod_map_alt3.

    Local Ltac saturate_find_step :=
      let cleanup :=
        repeat match goal with
               | [ H : ?T, H' : ?T |- _ ] => clear H'
               end in
      first [ progress inversion_option
            | progress subst
            | exfalso; assumption
            | progress cleanup
            | progress (specialize_under_binders_by (idtac; match goal with |- _ -> False => eauto with nocore end); cleanup)
            | match goal with
              | [ H : E1.eq _ _ |- _ ]
                => unique pose proof (E1.eq_sym H)
              | [ H : E1.eq _ _, H' : context[E1.eq _ _ -> False] |- _ ]
                => lazymatch type of H' with | _ -> False => fail | _ => idtac end;
                   clear H'
              | [ H : E1.eq _ _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              | [ H : E2.eq _ _ |- _ ]
                => unique pose proof (E2.eq_sym H)
              | [ H : E2.eq _ _, H' : context[E2.eq _ _ -> False] |- _ ]
                => lazymatch type of H' with | _ -> False => fail | _ => idtac end;
                   clear H'
              | [ H : E2.eq _ _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              | [ H : context[forall a, M1.find _ _ = _], H' : M1.find _ _ = _ |- _ ]
                => let H'' := fresh in
                   pose proof H' as H'';
                   rewrite H in H'' by fail;
                   let T := type of H'' in
                   lazymatch T with
                   | Some _ = Some _
                     => progress inversion_option; progress subst
                   | Some _ = None => inversion_option
                   | None = Some _ => inversion_option
                   | _
                     => revert H'';
                        lazymatch goal with
                        | [ H : T |- _ ] => fail
                        | _ => idtac T; intro
                        end
                   end
              | [ H : context[forall a, M2.find _ _ = _], H' : M2.find _ _ = _ |- _ ]
                => let H'' := fresh in
                   pose proof H' as H'';
                   rewrite H in H'' by fail;
                   let T := type of H'' in
                   lazymatch T with
                   | Some _ = Some _
                     => progress inversion_option; progress subst
                   | Some _ = None => inversion_option
                   | None = Some _ => inversion_option
                   | _
                     => revert H'';
                        lazymatch goal with
                        | [ H : T |- _ ] => fail
                        | _ => idtac T; intro
                        end
                   end
              end
            | progress (specialize_gen_under_binders_by' true ltac:(eauto with nocore); cleanup)
            | match goal with
              | [ H : M1.find _ _ = Some _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              | [ H : M2.find _ _ = Some _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              end ].
    Local Ltac saturate_find := repeat saturate_find_step.

    Local Hint Extern 2 => Proper_compose_hint : typeclass_instances.

    Local Ltac spec_t_nosubst_step :=
      first [ progress intros
            | exfalso; assumption
            | reflexivity
            | progress inversion_option
            | progress subst
            | progress destruct_head'_ex
            | progress destruct_head'_and
            | progress destruct_head' key
            | progress cbn [fst snd] in *
            | progress specialize_by_assumption
            | progress specialize_by reflexivity
            | progress specialize_under_binders_by apply conj
            | progress specialize_under_binders_by eapply ex_intro
            | progress autorewrite with prod_map_alt in *
            | progress autounfold with prod_map_alt in *
            | setoid_rewrite M1'.find_mapsto_iff
            | setoid_rewrite M2'.find_mapsto_iff
            | match goal with
              | [ H : ?x = ?x |- _ ] => clear H
              | [ H : true = _ |- _ ] => symmetry in H
              | [ H : context[M1.MapsTo] |- _ ] => setoid_rewrite M1'.find_mapsto_iff in H
              | [ H : context[M2.MapsTo] |- _ ] => setoid_rewrite M2'.find_mapsto_iff in H
              | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
              | [ H : forall x, Some x = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
              | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
              | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
              end
            | progress break_innermost_match
            | progress break_innermost_match_hyps
            | match goal with
              | [ |- iff _ _ ] => split
              end
            | congruence
            | solve [ eauto ]
            | match goal with
              | [ |- context[@M1.find ?elt ?x ?m] ] => destruct (@M1.find elt x m) eqn:?
              | [ |- context[@M2.find ?elt ?x ?m] ] => destruct (@M2.find elt x m) eqn:?
              end
            | (* should figure out how to generalize these into lemmas *)
              match goal with
              | [ H : M1.is_empty (M1.remove ?k ?m) = true, H' : M1.find ?k' ?m = Some _, H'' : E2.eq ?k ?k' -> False |- _ ]
                => exfalso; clear -H H' H'';
                   apply M1.is_empty_2 in H;
                   cbv [M1.Empty] in H;
                   setoid_rewrite M1'.find_mapsto_iff in H;
                   specialize (H k')
              | [ H : M2.is_empty (M2.remove ?k ?m) = true, H' : M2.find ?k' ?m = Some _, H'' : E2.eq ?k ?k' -> False |- _ ]
                => exfalso; clear -H H' H'';
                   apply M2.is_empty_2 in H;
                   cbv [M2.Empty] in H;
                   setoid_rewrite M2'.find_mapsto_iff in H;
                   specialize (H k')
              end ].
    Local Ltac spec_t_step :=
      first [ spec_t_nosubst_step
            | progress setoid_subst_rel E1.eq
            | progress setoid_subst_rel E2.eq ].

    Local Ltac spec_t := repeat spec_t_step.

    Module Import _Extra2.
      Lemma find_iff elt0 k v m0 : @MapsTo elt0 k v m0 <-> find k m0 = Some v.
      Proof using Type. clear; spec_t. Qed.
      Lemma add_full elt m0 v x' y' : @find elt y' (add x' v m0) = if E.eq_dec x' y' then Some v else find y' m0.
      Proof using Type. clear; spec_t. Qed.
      Lemma remove_full elt m0 x' y' : @find elt y' (remove x' m0) = if E.eq_dec x' y' then None else find y' m0.
      Proof using Type. clear; spec_t. Qed.
      Lemma map_full : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'), find x (map f m) = option_map f (find x m).
      Proof using Type. spec_t. Qed.
    End _Extra2.

    Section Spec.

      Variable elt:Type.
      Variable elt' elt'' : Type.
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Proof using Type. clear; spec_t. Qed.
      Lemma mem_1 : In x m -> mem x m = true.
      Proof using Type. clear; spec_t. Qed.
      Lemma mem_2 : mem x m = true -> In x m.
      Proof using Type. clear; spec_t. Qed.
      Lemma empty_1 : Empty (@empty elt).
      Proof using Type. clear; pose proof M1.empty_1; spec_t. Qed.
      Lemma is_empty_1 : Empty m -> is_empty m = true.
      Proof using Type. clear; pose proof M1.is_empty_1; spec_t. Qed.
      Lemma is_empty_2 : is_empty m = true -> Empty m.
      Proof using Type. clear; pose proof M1.is_empty_2; spec_t. Qed.
      Lemma find_1 : MapsTo x e m -> find x m = Some e.
      Proof using Type. apply find_iff. Qed.
      Lemma find_2 : find x m = Some e -> MapsTo x e m.
      Proof using Type. apply find_iff. Qed.
      Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
      Proof using Type. clear; intros; rewrite !find_iff, !add_full in *; spec_t. Qed.
      Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Proof using Type. clear; intros; rewrite !find_iff, !add_full in *; spec_t. Qed.
      Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Proof using Type. clear; intros; rewrite !find_iff, !add_full in *; spec_t. Qed.
      Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove_full; spec_t. Qed.
      Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove_full; spec_t. Qed.
      Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove_full; spec_t. Qed.
      Let elements_iff :
        InA (@eq_key_elt _) (x,e) (elements m) <-> MapsTo x e m.
      Proof using Type.
        clear; cbv [MapsTo elements].
        setoid_rewrite M1'.elements_mapsto_iff.
        setoid_rewrite M2'.elements_mapsto_iff.
        setoid_rewrite InA_alt.
        setoid_rewrite in_flat_map.
        repeat first [ setoid_rewrite ECompat.eq_alt
                     | spec_t_step
                     | progress destruct_head' prod ].
        all: repeat first [ eexists (_, _) | apply conj | rewrite in_map_iff | eexists ]; cbn [fst snd].
        all: try eassumption.
        all: try exact eq_refl.
        all: reflexivity.
      Qed.
      Lemma elements_1 :
        MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
      Proof using Type. apply elements_iff. Qed.
      Lemma elements_2 :
        InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
      Proof using Type. apply elements_iff. Qed.
      Lemma elements_3w : NoDupA (@eq_key _) (elements m).
      Proof using Type.
        clear.
        pose proof (M1.elements_3w m).
        cbv [elements].
        eapply @NoDupA_flat_map; try eassumption; try exact _.
        { rewrite Forall_map, Forall_forall; intros; break_innermost_match.
          eapply NoDupA_map_inv'; [ | apply M2.elements_3w ].
          spec_t. }
        { cbv [eq_key M1.eq_key]; intros; rewrite !InA_alt in *.
          spec_t. }
      Qed.
      Lemma cardinal_1 : cardinal m = length (elements m).
      Proof using Type. clear; spec_t. Qed.

      Hint Rewrite fold_left_flat_map fold_left_map : prod_map_alt.
      Lemma fold_1 :
        forall (A : Type) (i : A) (f : key -> elt -> A -> A),
          fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Proof using Type.
        clear; repeat first [ f_equiv; repeat intro; []
                            | progress spec_t ].
      Qed.

      Variable cmp : elt -> elt -> bool.
      Let equal_iff : Equivb cmp m m' <-> equal cmp m m' = true.
      Proof using Type.
        clear; cbv [equal Equivb] in *.
        rewrite Equiv_alt_iff, <- M1'.equal_iff.
        cbv [Equiv_alt M1.Equivb Cmp].
        f_equiv; repeat intro.
        rewrite <- M2'.equal_iff; reflexivity.
      Qed.
      Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Proof using Type. apply equal_iff. Qed.
      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof using Type. apply equal_iff. Qed.
    End Spec.

    Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
    Proof using Type. intros *; rewrite !find_iff, map_full; cbv [option_map]; break_innermost_match; spec_t. Qed.
    Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.
    Proof using Type. intros *; cbv [In]; setoid_rewrite find_iff; setoid_rewrite map_full; cbv [option_map]; break_innermost_match; spec_t. Qed.
    Lemma mapi_1 (elt elt':Type)(m: t elt)(x:key)(e:elt)
          (f:key->elt->elt')
      : MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
    Proof using Type.
      cbv [mapi].
      all: repeat first [ match goal with
                          | [ |- context[M1.mapi ?f ?m] ]
                            => pose proof (fun k e => @M1.mapi_1 _ _ m k e f);
                               set (M1.mapi f m) in *
                          | [ |- context[M2.mapi ?f ?m] ]
                            => pose proof (fun k e => @M2.mapi_1 _ _ m k e f);
                               set (M2.mapi f m) in *
                          end
                        | setoid_rewrite ECompat.eq_alt
                        | spec_t_nosubst_step
                        | specialize_under_binders_by eassumption
                        | match goal with
                          | [ H : E1.eq _ ?x |- _ ] => setoid_subst'' E1.eq x
                          | [ H : E2.eq _ ?x |- _ ] => setoid_subst'' E2.eq x
                          end ].
      eexists (_, _); eauto.
    Qed.
    Lemma mapi_2
      : forall (elt elt':Type)(m: t elt)(x:key)
               (f:key->elt->elt'), In x (mapi f m) -> In x m.
    Proof using Type.
      cbv [mapi In].
      all: repeat first [ match goal with
                          | [ H : context[M1.mapi ?f ?m] |- _ ]
                            => pose proof (fun k => @M1.mapi_2 _ _ m k f);
                               pose proof (fun k e => @M1.mapi_1 _ _ m k e f);
                               set (M1.mapi f m) in *
                          | [ H : context[M2.mapi ?f ?m] |- _ ]
                            => pose proof (fun k => @M2.mapi_2 _ _ m k f);
                               pose proof (fun k e => @M2.mapi_1 _ _ m k e f);
                               set (M2.mapi f m) in *
                          end
                        | setoid_rewrite ECompat.eq_alt
                        | spec_t_nosubst_step
                        | progress cbv [M1.In M2.In] in *
                        | progress cbn [proj1_sig] in *
                        | specialize_under_binders_by eassumption ].
    Qed.
    Lemma map2_1
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').
    Proof using Type.
      cbv [In].
      setoid_rewrite find_iff.
      intros.
      all: cbv [find map2] in *.
      all: rewrite M1.map2_1
        by (cbv [M1.In find Option.bind option_map Option.value] in *; setoid_rewrite M1'.find_mapsto_iff; break_innermost_match_hyps; destruct_head'_or; destruct_head'_ex; inversion_option; eauto).
      cbv [Option.value option_map Option.bind] in *.
      break_match; break_match_hyps.
      all: inversion_option; subst; cbn [proj1_sig] in *.
      all: try discriminate.
      all: try solve [ destruct_head'_or; destruct_head'_ex; congruence ].
      all: break_match; break_match_hyps.
      all: try discriminate.
      all: repeat match goal with
                  | [ H : ?x = ?x |- _ ] => clear H
                  | [ H : false = _ |- _ ] => symmetry in H
                  | [ H : true = _ |- _ ] => symmetry in H
                  end.
      all: lazymatch goal with
           | [ H : M2.is_empty (M2.map2 _ _ _) = true |- _ ]
             => apply M2.is_empty_2 in H;
                cbv [M2.Empty not] in H;
                setoid_rewrite M2'.find_mapsto_iff in H;
                specialize_under_binders_by (rewrite M2.map2_1; cbv [M2.In]; try setoid_rewrite M2'.find_mapsto_iff; destruct_head'_or; destruct_head'_ex; eauto)
           | _
             => rewrite @M2.map2_1 in *
                 by (cbv [M2.In]; setoid_rewrite M2'.find_mapsto_iff; destruct_head'_or; destruct_head'_ex; inversion_option; eauto)
           end.
      all: repeat first [ reflexivity
                        | progress rewrite ?M2'.find_empty in *
                        | progress inversion_option
                        | progress subst
                        | destruct_head'_or; destruct_head'_ex; congruence
                        | destruct_head'_or; destruct_head'_ex; []
                        | progress break_match
                        | progress break_match_hyps
                        | solve [ eauto ]
                        | match goal with
                          | [ H : ?x = Some _ |- _ ] => rewrite H in *
                          | [ H : ?x = None |- _ ] => rewrite H in *
                          | [ |- None = Some _ ] => exfalso
                          | [ |- None = ?x ] => destruct x eqn:?
                          end ].
    Qed.
    Lemma map2_2
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
    Proof using Type.
      cbv [In].
      setoid_rewrite find_iff.
      cbv [find map2 Option.bind].
      intros * HIn.
      repeat first [ progress destruct_head'_ex
                   | progress inversion_option
                   | match goal with
                     | [ H : match ?x with _ => _ end = Some _ |- _ ]
                       => destruct x eqn:?
                     end ].
      lazymatch goal with
      | [ H : M1.find _ (M1.map2 _ _ _) = Some _ |- _ ]
        => pose proof M1.map2_2 as H';
           cbv [M1.In] in H';
           setoid_rewrite M1'.find_mapsto_iff in H';
           specialize_under_binders_by (eexists; exact H)
      end.
      pose proof M1.map2_1 as H'';
        cbv [M1.In] in H'';
        setoid_rewrite M1'.find_mapsto_iff in H'';
        specialize_under_binders_by exact H'.
      destruct H' as [[? H']|[? H']];
        rewrite H' in *;
        rewrite H'' in *.
      all: cbv [option_map Option.bind Option.value] in *.
      all: repeat first [ progress inversion_option
                        | progress subst
                        | progress cbn [M2_m] in *
                        | progress break_match_hyps ].
      all: lazymatch goal with
           | [ H : context[M2.find _ (M2.map2 _ _ _)] |- _ ]
             => let H' := fresh in
                pose proof M2.map2_2 as H';
                cbv [M2.In] in H';
                setoid_rewrite M2'.find_mapsto_iff in H';
                specialize_under_binders_by (eexists; exact H);
                rewrite M2.map2_1 in H
                    by (cbv [M2.In]; setoid_rewrite M2'.find_mapsto_iff; exact H')
           end.
      all: repeat first [ progress inversion_option
                        | progress subst
                        | progress cbn [proj1_sig] in *
                        | rewrite M2'.find_empty in *
                        | solve [ eauto ]
                        | destruct_head'_or; destruct_head'_ex; inversion_option; subst; []
                        | progress break_match_hyps ].
    Qed.
  End ProdWSfun_gen.
End ProdWSfun_gen.

Module ProdWSfun (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) (M1 : WSfun E1) (M2 : WSfun E2).
  Module _ProdWSfun.
    Module Outer := ProdWSfun_gen E1 E2 M1 M2.
    Module E := ProdDecidableTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> RelProd E1.eq E2.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
    End ECompat.
    Module Inner := Outer.ProdWSfun_gen E ECompat.
  End _ProdWSfun.
  Include _ProdWSfun.Inner.
End ProdWSfun.

Module ProdUsualWeakMap (M1 : UsualWS) (M2 : UsualWS) <: UsualWS.
  Module Outer := ProdWSfun_gen M1.E M2.E M1 M2.
  Module E := ProdUsualDecidableTypeOrig M1.E M2.E.
  Module ECompat <: Outer.ESigCompat E.
    Lemma eq_alt : forall x y, E.eq x y <-> RelProd M1.E.eq M2.E.eq x y.
    Proof. cbv; intros; break_innermost_match; intuition congruence. Qed.
  End ECompat.
  Module Inner := Outer.ProdWSfun_gen E ECompat.
  Include Inner.
End ProdUsualWeakMap.

Module ProdWeakMap (M1 : WS) (M2 : WS) <: WS.
  Include ProdWSfun M1.E M2.E M1 M2.
  Module E := _ProdWSfun.E.
End ProdWeakMap.

Module ProdSfun_gen (E1 : OrderedTypeOrig) (E2 : OrderedTypeOrig) (M1 : Sfun E1) (M2 : Sfun E2).
  Module ProdWSfun := ProdWSfun_gen E1 E2 M1 M2.
  Module P := ProdHasLt E1 E2.
  Module Type ESig := ProdWSfun.ESig <+ HasLt <+ HasMiniOrderedType.
  Module Type ESigCompat (E : ESig).
    Include ProdWSfun.ESigCompat E.
    Axiom lt_alt : forall x y, E.lt x y <-> P.lt x y.
  End ESigCompat.
  Module ProdSfun_gen (E : ESig) (ECompat : ESigCompat E) <: Sfun E.
    Include ProdWSfun.ProdWSfun_gen E ECompat.
    Module E1' := E1 <+ UpdateStrOrder.
    Global Remove Hints E1'.eq_refl E1'.eq_sym E1'.eq_trans : core.
    Module E2' := E2 <+ UpdateStrOrder.
    Global Remove Hints E2'.eq_refl E2'.eq_sym E2'.eq_trans : core.
    Local Existing Instances _Extra1.eq_key_equiv _Extra1.eq_key_elt_equiv.
    Local Hint Resolve E1'.eq_refl E1'.eq_sym E1'.eq_trans
          E2'.eq_refl E2'.eq_sym E2'.eq_trans
      : core.
    Section elt.
      Variable elt:Type.
      Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

      Lemma elements_3 m : sort lt_key (elements m).
      Proof using Type.
        pose proof (M1.elements_3 m).
        cbv [elements].
        eapply @SortA_flat_map with (eqA:=@eq_key _) (eqB:=eq); try eassumption; try rewrite Forall_map, Forall_forall.
        all: match goal with
             | [ |- ?G ] => has_evar G; shelve
             | _ => idtac
             end.
        all: try exact _.
        all: lazymatch goal with
             | [ |- Transitive _ ]
               => cbv [M1.lt_key]; repeat intro; eapply E1.lt_trans; eassumption
             | _ => idtac
             end.
        { match goal with
          | [ |- context[Sorted] ]
            => intros; break_innermost_match; rewrite Sorted_map_iff
          end.
          eapply Sorted_Proper_impl; [ | | apply M2.elements_3 ]; [ | reflexivity ];
            repeat intro; break_innermost_match; cbv [lt_key M2.lt_key] in *; rewrite ECompat.lt_alt; cbv [P.lt]; cbn [fst snd] in *;
            destruct_head'_and; subst.
          pose proof (_ : Proper (_ ==> E2.eq ==> _) E2.lt).
          setoid_subst_rel E2.eq.
          eauto. }
        Unshelve.
        { cbv [M1.lt_key lt_key].
          intros; rewrite ECompat.lt_alt; cbv [P.lt]; break_innermost_match_hyps.
          rewrite InA_alt in *; destruct_head'_ex; destruct_head'_and.
          cbv [eq_key] in *; rewrite ECompat.eq_alt in *.
          repeat autounfold with prod_map_alt in *.
          rewrite in_map_iff in *.
          destruct_head'_ex; destruct_head'_and; break_innermost_match_hyps.
          subst.
          cbn [fst snd] in *.
          repeat match goal with H : List.In _ _ |- _ => clear H end.
          setoid_subst_rel E1.eq.
          left; assumption. }
      Qed.
    End elt.
  End ProdSfun_gen.
End ProdSfun_gen.

Module ProdSfun (E1 : OrderedTypeOrig) (E2 : OrderedTypeOrig) (M1 : Sfun E1) (M2 : Sfun E2).
  Module _ProdSfun.
    Module Outer := ProdSfun_gen E1 E2 M1 M2.
    Module E := ProdOrderedTypeOrig E1 E2.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> RelProd E1.eq E2.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
      Lemma lt_alt : forall x y, E.lt x y <-> E.lt x y.
      Proof. cbv [E.lt]; reflexivity. Qed.
    End ECompat.
    Module Inner := Outer.ProdSfun_gen E ECompat.
  End _ProdSfun.
  Include _ProdSfun.Inner.
End ProdSfun.

Module ProdUsualMap (M1 : UsualS) (M2 : UsualS) <: UsualS.
  Module Outer := ProdSfun_gen M1.E M2.E M1 M2.
  Module E := ProdUsualOrderedTypeOrig M1.E M2.E.
  Module ECompat <: Outer.ESigCompat E.
    Lemma eq_alt : forall x y, E.eq x y <-> RelProd M1.E.eq M2.E.eq x y.
    Proof. cbv; intros; break_innermost_match; intuition congruence. Qed.
    Lemma lt_alt : forall x y, E.lt x y <-> E.lt x y.
    Proof. cbv [E.lt]; reflexivity. Qed.
  End ECompat.
  Module Inner := Outer.ProdSfun_gen E ECompat.
  Include Inner.
End ProdUsualMap.

Module ProdMap (M1 : S) (M2 : S) <: S.
  Include ProdSfun M1.E M2.E M1 M2.
  Module E := _ProdSfun.E.
End ProdMap.

(* TODO:
Module IsoSord (S' : Sord) (Data' : IsoMiniOrderedType S'.Data) (E : IsoMiniOrderedType S'.MapS.E) (S'_iso : IsoMiniOrderedType S') <: Sord <: IsoOrderedType S'.
  Module Data <: IsoOrderedType S'.Data := Data' <+ OT_of_MOT.
  Module MapS <: S := IsoS S'.MapS E.
  Import MapS.

  Definition t := MapS.t Data.t.

  Definition eq : t -> t -> Prop.
    refine (_ S'.eq).
    compute.
    pose MapS.E.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)


  Include S.
  Include OT_of_MOT.
End IsoSord.
  Definition t := MapS.t Data.t.

  Print IsoMiniOrderedType.
  Definition eq : t -> t -> Prop := S'.eq.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)

End Sord.

*)
