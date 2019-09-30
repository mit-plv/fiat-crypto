Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLetsProofs.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.Rewriter.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CPSId.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.TransparentAssert.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.
  Import Rewriter.ProofsCommon.Compilers.
  Import expr.Notations.
  Import Rewriter.Compilers.RewriteRules.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.

  Module Import RewriteRules.
    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.
      Import Rewriter.ProofsCommon.Compilers.RewriteRules.Compile.

      Section with_var.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation pbase_type := (pattern.base.type base).
        Local Notation type := (type.type base_type).
        Local Notation ptype := (type.type pbase_type).
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base_beq : base -> base -> bool}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
                {ident var : type -> Type}
                (eta_ident_cps : forall {T : type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : ptype -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool)
                (pident_unify_unknown_correct
                 : forall t t' idc idc', pident_unify_unknown t t' idc idc' = pident_unify t t' idc idc')
                (invert_bind_args_unknown_correct
                 : forall t idc pidc, invert_bind_args_unknown t idc pidc = invert_bind_args t idc pidc)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (raw_pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_raw_pident p f)
                (raw_pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc).

        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Local Notation value' := (@value' base_type ident var).
        Local Notation value := (@value base_type ident var).
        Local Notation value_with_lets := (@value_with_lets base_type ident var).
        Local Notation Base_value := (@Base_value base_type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident var).
        Local Notation rawexpr := (@rawexpr base ident var).
        Local Notation eval_decision_tree := (@eval_decision_tree base ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr_cps_gen := (@reveal_rawexpr_cps_gen base ident var).
        Local Notation reveal_rawexpr_cps := (@reveal_rawexpr_cps base ident var).
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT base ident var pident pident_arg_types).
        Local Notation rewrite_with_rule := (@rewrite_with_rule base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.

        Context (reify_and_let_binds_base_cps : forall (t : base_type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T).

        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e1 === e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.

        Local Existing Instance SetoidList.eqlistA_equiv.

        Local Ltac rew_swap_list_step :=
          match goal with
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2, H' : context[swap_list ?a ?b ?ls2] |- _ ]
            => rewrite (swap_swap_list H) in H'
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls2] ]
            => rewrite (swap_swap_list H)
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls1] ]
            => rewrite H
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2,
                  H' : swap_list ?a ?b ?ls3 = Some ?ls4,
                       Hl : eqlistA ?R ?ls2 ?ls3
              |- _ ]
            => unique pose proof (swap_swap_list_eqlistA H H' Hl)
          end.

        Local Ltac rew_eval_decision_tree_step :=
          match goal with
          | [ H : (forall ctx' cont', eval_decision_tree ctx' ?d cont' = None \/ _)
              |- context[eval_decision_tree ?ctx ?d ?cont] ]
            => let H' := fresh in
               destruct (H ctx cont) as [H' | [? [? [H' ?] ] ] ]; rewrite H'
          end.

        Local Hint Constructors eqlistA.
        Local Hint Unfold rawexpr_equiv.
        Local Hint Unfold rawexpr_equiv_expr.

        Lemma eval_decision_tree_correct_Switch_cons
              {T} ctx icase icases app_case d cont
              (res := @eval_decision_tree T ctx (Switch (icase :: icases) app_case d) cont)
          : (exists b,
                res = match ctx with
                      | r :: ctx
                        => eval_decision_tree ctx (snd icase) (fun k ctx' => cont k (reveal_rawexpr_cps_gen (Some b) r _ id :: ctx'))
                      | _ => None
                      end)
            \/ res = eval_decision_tree ctx (Switch icases app_case d) cont
            \/ res = match app_case with
                     | Some app_case => eval_decision_tree ctx app_case cont
                     | None => None
                     end
            \/ res = eval_decision_tree ctx d cont.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          destruct icase as [p icase]; subst res; cbn [fst snd].
          destruct ctx as [|r ctx]; [ now cbn; auto | ].
          destruct r.
          all: cbn [eval_decision_tree fold_right].
          all: destruct app_case as [app_case|].
          all: repeat first [ match goal with
                              | [ |- context[?x = ?x \/ _] ] => solve [ auto ]
                              | [ |- context[_ \/ ?x = ?x] ] => solve [ auto ]
                              | [ H : ?x = ?y |- context[?y = ?x \/ _] ] => solve [ auto ]
                              | [ H : ?y = ?x |- context[?x = ?y \/ _] ] => solve [ auto ]
                              | [ H : _ = ?v |- (exists b, ?v = _) \/ _ ]
                                => left; eexists; (idtac + symmetry); eassumption
                              | [ H : ?v = _ |- (exists b, ?v = _) \/ _ ]
                                => left; eexists; (idtac + symmetry); eassumption
                              | [ H : context[invert_bind_args_unknown ?a ?b ?c] |- _ ] => rewrite invert_bind_args_unknown_correct in H
                              | [ |- context[invert_bind_args_unknown ?a ?b ?c] ] => rewrite invert_bind_args_unknown_correct
                              | [ H : context[eval_decision_tree _ _ (fun _ _ => None)] |- _ ]
                                => rewrite eval_decision_tree_cont_None in H
                              | [ |- context[eval_decision_tree _ _ (fun _ _ => None)] ]
                                => rewrite eval_decision_tree_cont_None
                              | [ |- (exists b, ?f _ = ?f _) \/ _ ]
                                => left; eexists; reflexivity
                              end
                            | progress subst
                            | progress inversion_sigma
                            | progress inversion_option
                            | progress cbv [reveal_rawexpr_cps reveal_rawexpr_cps_gen value] in *
                            | progress cbn [value'] in *
                            | progress expr.invert_match
                            | break_match_hyps_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                            | break_match_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                            | match goal with
                              | [ |- context[match ?d with Failure => _ | _ => _ end] ] => is_var d; destruct d
                              end
                            | progress cbn [eq_rect Option.sequence Option.sequence_return] in *
                            | progress cbv [id option_bind' Option.bind Option.sequence Option.sequence_return] in *
                            | match goal with
                              | [ H : invert_bind_args _ _ _ = Some _ |- _ ]
                                => pose proof (@raw_pident_to_typed_invert_bind_args _ _ _ _ H);
                                   generalize dependent (@raw_pident_to_typed_invert_bind_args_type _ _ _ _ H); clear H; intros
                              | [ |- context[rew [?P] ?pf in ?v] ]
                                => lazymatch type of pf with
                                   | ?t1 = ?t2
                                     => generalize dependent v; generalize dependent pf;
                                        (generalize dependent t1 || generalize dependent t2);
                                        intros; subst
                                   end
                              | [ H : ?t = rew [?P] ?pf in ?v |- _ ]
                                => generalize dependent t; intros; subst
                              | [ H : context[rew [?P] ?pf in ?v] |- _ ]
                                => lazymatch type of pf with
                                   | ?t1 = ?t2
                                     => generalize dependent v; generalize dependent pf;
                                        (generalize dependent t1 || generalize dependent t2);
                                        intros; subst
                                   end
                              | [ |- context[match @fold_right ?A ?B ?f ?v ?ls with Some _ => _ | _ => _ end] ]
                                => destruct (@fold_right A B f v ls) eqn:?
                              end
                            | break_innermost_match_step ].
        Qed.

        Fixpoint eval_decision_tree_correct {T} d ctx cont
                 (res := @eval_decision_tree T ctx d cont)
                 {struct d}
          : res = None
            \/ exists n ctx',
              res = cont n ctx'
              /\ SetoidList.eqlistA rawexpr_equiv ctx ctx'.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          specialize (eval_decision_tree_correct T).
          subst res; cbv zeta in *; destruct d.
          all: [ > specialize (eval_decision_tree_correct ltac:(assumption))
               | clear eval_decision_tree_correct
               |
               | specialize (eval_decision_tree_correct ltac:(assumption)) ].
          { cbn [eval_decision_tree]; cbv [Option.sequence]; break_innermost_match; eauto.
            all: right; repeat esplit; (idtac + symmetry); (eassumption + reflexivity). }
          { cbn; eauto. }
          { let d := match goal with d : decision_tree |- _ => d end in
            pose proof (eval_decision_tree_correct d) as eval_decision_tree_correct_default.
            let app_case := match goal with app_case : option decision_tree |- _ => app_case end in
            pose proof (match app_case return match app_case with Some _ => _ | _ => _ end with
                        | Some app_case => eval_decision_tree_correct app_case
                        | None => I
                        end) as eval_decision_tree_correct_app_case.
            let icases := match goal with icases : list (_ * decision_tree) |- _ => icases end in
            induction icases as [|icase icases IHicases];
              [ clear eval_decision_tree_correct | specialize (eval_decision_tree_correct (snd icase)) ].
            (* now that we have set up guardedness correctly, we can
               stop worrying so much about what order we destruct
               things in *)
            2: destruct (@eval_decision_tree_correct_Switch_cons _ ctx icase icases app_case d cont)
              as [ [? H] | [H| [H|H] ] ];
              rewrite H; try assumption.
            all: destruct app_case as [app_case|]; try (left; reflexivity).
            all: destruct ctx as [|ctx0 ctx]; [ try (left; reflexivity) | ].
            all: try destruct ctx0.
            all: cbn [eval_decision_tree fold_right]; cbv [reveal_rawexpr_cps reveal_rawexpr_cps_gen Option.sequence Option.sequence_return].
            all: repeat first [ rew_eval_decision_tree_step
                              | progress cbv [value id] in *
                              | progress cbn [value'] in *
                              | assumption
                              | reflexivity
                              | progress subst
                              | progress inversion_option
                              | expr.invert_match_step
                              | match goal with
                                | [ |- ?x = ?x \/ _ ] => left; reflexivity
                                | [ |- Some _ = None \/ _ ] => right
                                | [ |- None = Some _ \/ _ ] => right
                                | [ |- ?v = None \/ _ ]
                                  => lazymatch v with
                                     | match ?d with Failure => None | TryLeaf _ _ => None | _ => _ end
                                       => let H := fresh in
                                          assert (H : v = None) by (destruct d; auto); rewrite H
                                     | match ?d with Failure => ?x | TryLeaf _ _ => ?y | _ => _ end
                                       => let H := fresh in
                                          assert (H : v = x \/ v = y) by (destruct d; auto);
                                          destruct H as [H|H]; rewrite H
                                     end
                                | [ |- context[match ?x with nil => None | cons _ _ => _ end] ]
                                  => is_var x; destruct x
                                | [ |- match match ?x with nil => None | cons _ _ => _ end with None => None | Some _ => _ end = None \/ _ ]
                                  => is_var x; destruct x; [ left; reflexivity | ]
                                | [ |- _ \/ exists n ctx', ?f ?a ?b = ?f n ctx' /\ _ ]
                                  => right; exists a, b; split; [ reflexivity | ]
                                | [ |- exists n ctx', ?f ?a ?b = ?f n ctx' /\ _ ]
                                  => right; exists a, b; split; [ reflexivity | ]
                                | [ H : ?f ?a ?b = Some ?v |- exists n ctx', Some ?v = ?f n ctx' /\ _ ]
                                  => exists a, b; split; [ symmetry; assumption | ]
                                end
                              | break_match_hyps_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                              | match goal with
                                | [ H : rawexpr_equiv ?a ?b |- eqlistA _ _ _ ] => unique assert (rawexpr_equiv b a) by (symmetry; exact H)
                                | [ H : eqlistA _ (_ :: _) _ |- eqlistA _ _ _ ] => inversion H; clear H; subst
                                | [ H : eqlistA _ nil _ |- eqlistA _ _ _ ] => inversion H; clear H; subst
                                | [ |- eqlistA _ (cons _ _) (cons _ _) ] => constructor
                                | [ |- eqlistA _ nil nil ] => constructor
                                | [ |- rawexpr_equiv _ _ ] => solve [ auto ]
                                | [ |- rawexpr_equiv (rValue ?v) ?r ] => change (rawexpr_equiv (rExpr v) r)
                                end
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step ]. }
          { cbn [eval_decision_tree];
              repeat first [ rew_eval_decision_tree_step
                           | rew_swap_list_step
                           | solve [ eauto ]
                           | break_innermost_match_step ]. }
        Qed.

        Lemma eval_rewrite_rules_correct
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (maybe_do_again
               := fun (should_do_again : bool) (t : base_type)
                  => if should_do_again return ((@expr.expr base_type ident (if should_do_again then value else var) t) -> UnderLets (expr t))
                     then do_again t
                     else UnderLets.Base)
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              (e : rawexpr)
              (res := @eval_rewrite_rules do_again d rew_rules e)
          : res = UnderLets.Base (expr_of_rawexpr e)
            \/ exists n pf e',
              nth_error rew_rules n = Some pf
              /\ Some res
                 = rewrite_with_rule do_again e' pf
              /\ rawexpr_equiv e e'.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          subst res; cbv [eval_rewrite_rules].
          refine (let H := eval_decision_tree_correct d [e] _ in _).
          destruct H as [H| [? [? [H ?] ] ] ]; rewrite H; cbn [Option.sequence Option.sequence_return];
            [ left; reflexivity | ]; clear H.
          inversion_head' eqlistA.
          unfold Option.bind at 1.
          break_innermost_match_step; [ | left; reflexivity ].
          cbn [Option.bind Option.sequence Option.sequence_return].
          match goal with
          | [ |- (Option.sequence_return ?x ?y) = _ \/ _ ]
            => destruct x eqn:?
          end; [ | left; reflexivity ]; cbn [Option.sequence_return].
          right; repeat esplit; try eassumption; auto.
        Qed.
      End with_var.

      Section with_interp.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation pbase_type := (pattern.base.type base).
        Local Notation type := (type.type base_type).
        Local Notation ptype := (type.type pbase_type).
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base_beq : base -> base -> bool}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
                {ident : type -> Type}
                {base_interp : base -> Type}
                {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                (eta_ident_cps : forall {T : type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : ptype -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool)
                (pident_unify_unknown_correct
                 : forall t t' idc idc', pident_unify_unknown t t' idc idc' = pident_unify t t' idc idc')
                (invert_bind_args_unknown_correct
                 : forall t idc pidc, invert_bind_args_unknown t idc pidc = invert_bind_args t idc pidc)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (raw_pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_raw_pident p f)
                (raw_pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc)
                (pident_to_typed
                 : forall t idc (evm : EvarMap),
                    type_of_list (pident_arg_types t idc) -> ident (pattern.type.subst_default t evm))
                (ident_interp_Proper : forall t, Proper (eq ==> type.eqv) (@ident_interp t))
                (pident_unify_to_typed
                 : forall t t' idc idc' v,
                    pident_unify t t' idc idc' = Some v
                    -> forall evm pf,
                      rew [ident] pf in @pident_to_typed t idc evm v = idc').

        Local Notation var := (type.interp (base.interp base_interp)) (only parsing).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Local Notation value' := (@value' base_type ident var).
        Local Notation value := (@value base_type ident var).
        Local Notation value_with_lets := (@value_with_lets base_type ident var).
        Local Notation Base_value := (@Base_value base_type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident var).
        Local Notation rawexpr := (@rawexpr base ident var).
        Local Notation eval_decision_tree := (@eval_decision_tree base ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT base ident var pident pident_arg_types).
        Local Notation rewrite_with_rule := (@rewrite_with_rule base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation reify := (@reify base ident var).
        Local Notation reflect := (@reflect base ident var).
        Local Notation rewrite_rule_data_interp_goodT := (@rewrite_rule_data_interp_goodT base try_make_transport_base_cps ident pident pident_arg_types pident_to_typed base_interp ident_interp).
        Local Notation rewrite_rules_interp_goodT := (@rewrite_rules_interp_goodT base try_make_transport_base_cps ident pident pident_arg_types pident_to_typed base_interp ident_interp).
        Local Notation rewrite_ruleTP := (@rewrite_ruleTP base ident var pident pident_arg_types).
        Local Notation rewrite_ruleT := (@rewrite_ruleT base ident var pident pident_arg_types).
        Local Notation unify_pattern := (@unify_pattern base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation unify_pattern' := (@unify_pattern' base try_make_transport_base_cps ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation assemble_identifier_rewriters := (@assemble_identifier_rewriters base try_make_transport_base_cps base_beq ident var eta_ident_cps pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation assemble_identifier_rewriters' := (@assemble_identifier_rewriters' base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation pattern_default_interp' := (@pattern_default_interp' base ident pident pident_arg_types pident_to_typed base_interp (@ident_interp)).
        Local Notation pattern_default_interp := (@pattern_default_interp base ident pident pident_arg_types pident_to_typed base_interp (@ident_interp)).
        Local Notation pattern_collect_vars := (@pattern.collect_vars base pident).
        Local Notation app_with_unification_resultT_cps := (@app_with_unification_resultT_cps base try_make_transport_base_cps pident pident_arg_types).
        Local Notation app_transport_with_unification_resultT'_cps := (@app_transport_with_unification_resultT'_cps base try_make_transport_base_cps pident pident_arg_types).
        Local Notation with_unification_resultT' := (@with_unification_resultT' base pident pident_arg_types).
        Local Notation value'_interp := (@value'_interp base ident base_interp ident_interp).
        Local Notation eval_decision_tree_correct := (@eval_decision_tree_correct base ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple invert_bind_args_unknown_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args).
        Local Notation expr_interp_related := (@expr.interp_related _ ident _ ident_interp).
        Local Notation UnderLets_interp_related := (@UnderLets.interp_related _ ident _ ident_interp _ _ expr_interp_related).
        Local Notation rawexpr_interp_related := (@rawexpr_interp_related base ident base_interp ident_interp).
        Local Notation value_interp_related := (@value_interp_related base ident base_interp ident_interp).
        Local Notation unification_resultT'_interp_related := (@unification_resultT'_interp_related base ident pident pident_arg_types base_interp ident_interp).
        Local Notation unification_resultT_interp_related := (@unification_resultT_interp_related base ident pident pident_arg_types base_interp ident_interp).
        Local Notation preunify_types := (@preunify_types base base_beq ident var pident).
        Local Notation unify_types := (@unify_types base base_beq ident var pident).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.

        Context (reify_and_let_binds_base_cps : forall (t : base_type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T)
                (interp_reify_and_let_binds_base
                 : forall t e v,
                    expr_interp_related e v
                    -> UnderLets_interp_related (@reify_and_let_binds_base_cps t e _ UnderLets.Base) v).

        Local Notation reify_and_let_binds_cps := (@reify_and_let_binds_cps base ident var reify_and_let_binds_base_cps).
        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

        Local Lemma pident_unify_to_typed'
          : forall t t' idc idc' v,
            pident_unify t t' idc idc' = Some v
            -> forall evm pf,
              @pident_to_typed t idc evm v = rew [ident] pf in idc'.
        Proof using pident_unify_to_typed.
          intros t t' idc idc' v H evm pf.
          pose proof (@pident_unify_to_typed t t' idc idc' v H evm (eq_sym pf)).
          subst; reflexivity.
        Qed.

        Lemma interp_reify_and_let_binds {with_lets t v1 v}
          : value_interp_related v1 v
            -> UnderLets_interp_related (@reify_and_let_binds_cps with_lets t v1 _ UnderLets.Base) v.
        Proof using interp_reify_and_let_binds_base.
          cbv [reify_and_let_binds_cps]; break_innermost_match;
            repeat first [ progress intros
                         | progress destruct_head'_ex
                         | progress destruct_head'_and
                         | progress subst
                         | solve [ eauto ]
                         | apply reify_interp_related
                         | eapply @UnderLets.splice_interp_related_of_ex with (RA:=expr_interp_related);
                           eexists (fun x => x), _; repeat apply conj;
                           [ eassumption | | reflexivity ] ].
        Qed.

        Fixpoint types_match_with (evm : EvarMap) {t} (e : rawexpr) (p : pattern t) {struct p} : Prop
          := match p, e with
             | pattern.Wildcard t, e
               => pattern.type.subst t evm = Some (type_of_rawexpr e)
             | pattern.Ident t idc, rIdent known t' _ _ _
               => pattern.type.subst t evm = Some t'
             | pattern.App s d f x, rApp f' x' _ _
               => @types_match_with evm _ f' f
                  /\ @types_match_with evm _ x' x
             | pattern.Ident _ _, _
             | pattern.App _ _ _ _, _
               => False
             end.

        Lemma preunify_types_to_match_with {t re p evm}
          : match @preunify_types t re p with
            | Some None => True
            | Some (Some (pt, t')) => pattern.type.subst pt evm = Some t'
            | None => False
            end
            -> types_match_with evm re p.
        Proof using reflect_base_beq.
          revert re; induction p; intro; cbn [preunify_types types_match_with];
            break_innermost_match; try exact id.
          all: repeat first [ progress Bool.split_andb
                            | progress type_beq_to_eq
                            | progress inversion_option
                            | progress subst
                            | reflexivity
                            | progress cbn [Option.bind pattern.type.subst_default pattern.type.subst]
                            | rewrite pattern.type.eq_subst_default_relax
                            | rewrite pattern.type.subst_relax
                            | match goal with
                              | [ H : (forall re, match preunify_types re ?p with _ => _ end -> _)
                                  |- context[preunify_types ?re' ?p] ]
                                => specialize (H re')
                              end
                            | break_innermost_match_hyps_step
                            | progress intros
                            | solve [ auto ]
                            | exfalso; assumption
                            | progress type.inversion_type
                            | progress cbv [Option.bind] in * ].
        Qed.

        Lemma unify_types_match_with {t re p evm}
          : @unify_types t re p _ id = Some evm
            -> types_match_with evm re p.
        Proof using reflect_base_beq.
          intro H; apply preunify_types_to_match_with; revert H.
          cbv [unify_types id].
          break_innermost_match; intros; inversion_option; try exact I.
          RewriteRules.pattern.type.add_var_types_cps_id.
          cbv [option_type_type_beq] in *; break_innermost_match_hyps; type_beq_to_eq; inversion_option.
          let H := match goal with H : option_beq _ _ _ = true |- _ => H end in
          apply internal_option_dec_bl in H;
            [ | intros; type_beq_to_eq; assumption ].
          subst.
          assumption.
        Qed.

        Local Notation mk_new_evm0 evm ls
          := (fold_right
                (fun i k evm'
                 => k match PositiveMap.find i evm with
                      | Some v => PositiveMap.add i v evm'
                      | None => evm'
                      end) (fun evm' => evm')
                (List.rev ls)) (only parsing).

        Local Notation mk_new_evm' evm ps
          := (mk_new_evm0
                evm
                (PositiveSet.elements ps)) (only parsing).

        Local Notation mk_new_evm evm ps
          := (mk_new_evm' evm ps (PositiveMap.empty _)) (only parsing).

        Lemma types_match_with_Proper_evm {t p evm evm' re}
              (Hevm : forall k, PositiveSet.mem k (pattern_collect_vars p) = true -> PositiveMap.find k evm = PositiveMap.find k evm')
          : @types_match_with evm t re p <-> @types_match_with evm' t re p.
        Proof using Type.
          revert re; induction p, re; cbn [types_match_with pattern_collect_vars] in *.
          all: repeat first [ progress cbn [type_of_rawexpr] in *
                            | match goal with
                              | [ H : context[PositiveSet.mem _ (PositiveSet.union _ _)] |- _ ]
                                => setoid_rewrite PositiveSetFacts.union_b in H
                              | [ H : context[orb _ _ = true] |- _ ]
                                => setoid_rewrite Bool.orb_true_iff in H
                              end
                            | reflexivity
                            | progress split_contravariant_or
                            | progress specialize_by_assumption
                            | erewrite pattern.type.subst_eq_if_mem by eassumption
                            | match goal with
                              | [ H : _ |- _ ] => rewrite H by assumption
                              | [ |- (?x = Some ?y) <-> (?x' = Some ?y) ]
                                => cut (x = x'); [ let H := fresh in intro H; rewrite H; reflexivity | ]
                              end
                            | apply pattern.type.subst_eq_if_mem ].
        Qed.

        Lemma mem_pattern_collect_vars_types_match_with {evm t re p x}
              (H : @types_match_with evm t re p)
              (Hmem : PositiveSet.mem x (pattern_collect_vars p) = true)
          : PositiveMap.find x evm <> None.
        Proof using Type.
          revert re H; induction p; intros.
          all: repeat first [ progress cbn [pattern_collect_vars types_match_with] in *
                            | eapply pattern.type.mem_collect_vars_subst_Some_find; eassumption
                            | progress destruct_head'_and
                            | progress specialize_by_assumption
                            | assumption
                            | exfalso; assumption
                            | rewrite PositiveSetFacts.union_b, Bool.orb_true_iff in *
                            | progress destruct_head'_or
                            | break_innermost_match_hyps_step
                            | match goal with
                              | [ H : forall re, types_match_with ?evm re ?p -> _, H' : types_match_with ?evm _ ?p |- _ ] => specialize (H _ H')
                              end ].
        Qed.

        Lemma mem_collect_vars_pattern_to_type {t p k}
          : PositiveSet.mem k (pattern.type.collect_vars t) = true
            -> PositiveSet.mem k (@pattern_collect_vars t p) = true.
        Proof using Type.
          induction p.
          all: repeat first [ progress intros
                            | assumption
                            | progress cbn [pattern_collect_vars pattern.type.collect_vars] in *
                            | progress split_contravariant_or
                            | progress specialize_by_assumption
                            | rewrite PositiveSetFacts.union_b, Bool.orb_true_iff in *
                            | solve [ auto ] ].
        Qed.

        Lemma eq_subst_types_pattern_collect_vars t0 pt t evm evm0
              (evm' := mk_new_evm' evm (@pattern_collect_vars t0 pt) evm0)
              (Hty : pattern.type.subst t0 evm = Some t)
          : pattern.type.subst t0 evm' = Some t.
        Proof using Type.
          rewrite <- Hty; symmetry; apply pattern.type.subst_eq_Some_if_mem; subst evm'; intros; try congruence; [].
          rewrite pattern.base.fold_right_evar_map_find_In.
          erewrite mem_collect_vars_pattern_to_type by eassumption.
          break_innermost_match; congruence.
        Qed.

        Lemma eq_subst_types_pattern_collect_vars_empty_iff t0 pt evm (evm0:=PositiveMap.empty _)
              (evm' := mk_new_evm' evm (@pattern_collect_vars t0 pt) evm0)
          : pattern.type.subst t0 evm = pattern.type.subst t0 evm'.
        Proof using Type.
          apply pattern.type.subst_eq_if_mem; subst evm' evm0; intro.
          intro H; rewrite pattern.base.fold_right_evar_map_find_In, PositiveMap.gempty, mem_collect_vars_pattern_to_type by assumption.
          break_innermost_match; reflexivity.
        Qed.

        Lemma types_match_with_new_evm_iff {t re p evm}
              (evm' := mk_new_evm evm (pattern_collect_vars p))
          : @types_match_with evm' t re p <-> @types_match_with evm t re p.
        Proof using Type.
          clear -type_base base'; subst evm'; apply types_match_with_Proper_evm.
          intro k; rewrite pattern.base.fold_right_evar_map_find_In.
          intro H; rewrite H.
          rewrite PositiveMap.gempty.
          break_innermost_match; reflexivity.
        Qed.

        Lemma eq_type_of_rawexpr_of_types_match_with {t re p evm}
              (Ht : @types_match_with evm t re p)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
              (evm' := mk_new_evm evm (pattern_collect_vars p))
          : pattern.type.subst t evm' = Some (type_of_rawexpr re).
        Proof using Type.
          clear -Ht Ht' type_base base'.
          subst evm'.
          apply eq_subst_types_pattern_collect_vars.
          revert re Ht Ht'; induction p.
          all: repeat first [ progress intros
                            | progress cbn [type_of_rawexpr types_match_with pattern.type.subst rawexpr_types_ok] in *
                            | progress cbv [Option.bind] in *
                            | progress inversion_option
                            | progress specialize_by_assumption
                            | progress specialize_by eauto using rawexpr_types_ok_for_type_of_rawexpr
                            | progress subst
                            | assumption
                            | reflexivity
                            | exfalso; assumption
                            | progress destruct_head'_and
                            | break_innermost_match_hyps_step
                            | match goal with
                              | [ H : forall re, types_match_with ?evm re ?p -> _, H' : types_match_with ?evm _ ?p |- _ ]
                                => specialize (H _ H')
                              | [ H : rawexpr_types_ok _ _ |- _ ] => apply eq_type_of_rawexpr_of_rawexpr_types_ok in H
                              | [ H : context[type_of_rawexpr ?re] |- _ ]
                                => generalize dependent (type_of_rawexpr re)
                              | [ H : type.arrow _ _ = type.arrow _ _ |- _ ]
                                => inversion_clear H
                              end ].
        Qed.

        Lemma eq_type_of_rawexpr_of_types_match_with' {t re p evm}
              (Ht : @types_match_with evm t re p)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
              (evm' := mk_new_evm evm (pattern_collect_vars p))
          : type_of_rawexpr re = pattern.type.subst_default t evm'.
        Proof using Type.
          symmetry; eapply pattern.type.subst_Some_subst_default, eq_type_of_rawexpr_of_types_match_with; eassumption.
        Qed.

        Lemma app_transport_with_unification_resultT'_pattern_default_interp'_cps_id
              {K t p evm1 evm2 args k T k'}
          : @app_transport_with_unification_resultT'_cps
              _ t p evm1 evm2 _
              (@pattern_default_interp' K t p _ k) args
              T k'
            = (v0 <- (@app_transport_with_unification_resultT'_cps
                        _ t p evm1 evm2 _
                        (@pattern_default_interp' _ t p _ id) args
                        _ (@Some _));
                 k' (k v0))%option.
        Proof using try_make_transport_base_cps_correct.
          revert K evm1 evm2 args k T k'; induction p.
          all: repeat first [ progress intros
                            | progress cbn [pattern_default_interp' unification_resultT' app_transport_with_unification_resultT'_cps eq_rect] in *
                            | reflexivity
                            | progress inversion_option
                            | progress subst
                            | progress cbv [id Option.bind option_map] in *
                            | progress fold (@with_unification_resultT')
                            | rewrite app_lam_type_of_list
                            | break_innermost_match_step
                            | break_innermost_match_hyps_step
                            | progress rewrite_type_transport_correct
                            | progress type_beq_to_eq
                            | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                            | match goal with
                              | [ H : forall K evm1 evm2 args k T k', _ = _, H' : context[app_transport_with_unification_resultT'_cps (pattern_default_interp' _ ?evm1v ?kv) ?argsv ?Tv ?k'v] |- _ ]
                                => lazymatch kv with
                                   | @id _ => fail
                                   | (fun x => x) => fail
                                   | _ => idtac
                                   end;
                                   rewrite (H _ _ _ _ kv Tv k'v) in H'
                              | [ H : forall K evm1 evm2 args k T k', _ = _ |- context[app_transport_with_unification_resultT'_cps (pattern_default_interp' _ ?evm1v ?kv) ?argsv ?Tv ?k'v] ]
                                => lazymatch kv with
                                   | @id _ => fail
                                   | (fun x => x) => fail
                                   | _ => idtac
                                   end;
                                   rewrite (H _ _ _ _ kv Tv k'v)
                              end ].
        Qed.

        Local Ltac solve_side_condition_equations :=
          repeat
            repeat
            first [ progress intros
                  | assumption
                  | progress subst
                  | progress cbv [Option.bind] in *
                  | progress inversion_option
                  | match goal with
                    | [ |- ?x = ?x ] => reflexivity
                    | [ H : ?x = ?x |- _ ] => clear H
                    | [ H : expr_interp_related _ _ |- type_of_rawexpr _ = _ ] => clear H
                    | [ H : rawexpr_interp_related _ _ |- type_of_rawexpr _ = _ ] => clear H
                    | [ H : types_match_with _ _ _ |- type_of_rawexpr _ = _ ] => apply eq_type_of_rawexpr_of_types_match_with in H; [ | eapply rawexpr_types_ok_for_type_of_rawexpr; eassumption ]
                    | [ H : rawexpr_types_ok _ _ |- type_of_rawexpr _ = _ ] => apply eq_type_of_rawexpr_of_rawexpr_types_ok in H
                    | [ H : context[pattern.type.subst ?t (fold_right (fun i k evm' => k match PositiveMap.find i ?evm with _ => _ end) _ _ (PositiveMap.empty _))] |- _ ]
                      => rewrite <- eq_subst_types_pattern_collect_vars_empty_iff in H
                    | [ H : type.arrow _ _ = type.arrow _ _ |- _ = _ :> type ]
                      => inversion H; clear H
                    | [ |- type.arrow _ _ = type.arrow _ _ ] => apply f_equal2
                    | [ |- _ = _ :> type ]
                      => match goal with
                         | [ |- context[type_of_rawexpr ?re] ]
                           => is_var re; generalize dependent (type_of_rawexpr re)
                         | [ H : context[type_of_rawexpr ?re] |- _ ]
                           => is_var re; generalize dependent (type_of_rawexpr re)
                         end
                    end
                  | progress cbn [pattern.type.subst] in *
                  | progress break_match_hyps
                  | match goal with
                    | [ |- pattern.type.subst_default ?t _ = pattern.type.subst_default ?t _ ] => reflexivity
                    | [ |- ?t = pattern.type.subst_default _ _ ]
                      => is_var t; symmetry; apply pattern.type.subst_Some_subst_default
                    end ].

        Lemma interp_unify_pattern' {t re p evm res v}
              (Hre : rawexpr_interp_related re v)
              (H : @unify_pattern' t re p evm _ (@Some _) = Some res)
              (Ht : @types_match_with evm t re p)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
              (evm' := mk_new_evm evm (pattern_collect_vars p))
              (*Hty : type_of_rawexpr re = pattern.type.subst_default t evm'
               := eq_type_of_rawexpr_of_types_match_with' Ht Ht'*)
              (Hty : type_of_rawexpr re = pattern.type.subst_default t evm'
               := eq_type_of_rawexpr_of_types_match_with' Ht Ht')
          : exists resv : _,
              unification_resultT'_interp_related res resv
              /\ app_transport_with_unification_resultT'_cps
                   (pattern_default_interp' p evm' id) resv _ (@Some _)
                 = Some (rew Hty in v).
        Proof using pident_unify_unknown_correct pident_unify_to_typed try_make_transport_base_cps_correct.
          clear -reflect_base_beq try_make_transport_base_cps_correct pident_unify_unknown_correct pident_unify_to_typed Hre H Ht Ht' Hty type_base base'.
          clearbody Hty.
          assert (Hevm' : @types_match_with evm' t re p) by now apply types_match_with_new_evm_iff.
          clearbody evm'; cbv [unification_resultT'_interp_related].
          revert re res v evm' H Hre Hty Ht' Ht Hevm'; induction p; cbn [unify_pattern' related_unification_resultT' unification_resultT' rawexpr_interp_related app_transport_with_unification_resultT'_cps pattern_default_interp'] in *.
          all: repeat
                 ((unshelve
                     (repeat first [ progress intros
                                   | rewrite pident_unify_unknown_correct in *
                                   | progress cbv [Option.bind option_bind'] in *
                                   | progress cbn [fst snd rawexpr_interp_related eq_rect rawexpr_types_ok] in *
                                   | progress inversion_option
                                   | progress destruct_head'_ex
                                   | progress destruct_head'_and
                                   | progress inversion_sigma
                                   | progress subst
                                   | progress eliminate_hprop_eq
                                   | progress specialize_by_assumption
                                   | progress specialize_by eauto using rawexpr_types_ok_for_type_of_rawexpr
                                   | exfalso; assumption
                                   | assumption
                                   | match goal with
                                     | [ |- ?x = ?x ] => reflexivity
                                     | [ |- { x : _ | _ = x } ] => eexists; reflexivity
                                     | [ |- exists x, _ = x /\ _ ] => eexists; split; [ reflexivity | ]
                                     | [ |- exists x, _ /\ Some x = Some _ ] => eexists; split; [ | reflexivity ]
                                     end
                                   | progress cps_id'_with_option unify_pattern'_cps_id
                                   | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                                   | progress rewrite_type_transport_correct
                                   | progress type_beq_to_eq
                                   | rewrite app_lam_type_of_list
                                   | break_innermost_match_hyps_step
                                   | break_innermost_match_step
                                   | match goal with
                                     | [ |- exists x : _ * _, (_ /\ _) /\ _ ] => eexists (_, _); split; [ split; eassumption | ]
                                     | [ |- exists res, value_interp_related (value_of_rawexpr _) res ]
                                       => eexists; eapply value_of_rawexpr_interp_related; eassumption
                                     | [ |- value_interp_related (value_of_rawexpr _) _ ]
                                       => eapply value_of_rawexpr_interp_related; eassumption
                                     | [ |- Some _ = Some _ ] => apply f_equal
                                     | [ H : context[eq_type_of_rawexpr_of_types_match_with' ?H1 ?H2] |- _ ]
                                       => generalize dependent (eq_type_of_rawexpr_of_types_match_with' H1 H2)
                                     | [ H : context[rew ?pf in _] |- _ ]
                                       => tryif is_var pf then destruct pf else generalize dependent pf
                                     | [ |- context[rew ?pf in _] ]
                                       => tryif is_var pf then destruct pf else generalize dependent pf
                                     | [ |- context[rew _ in rew _ in _] ]
                                       => rewrite <- eq_trans_rew_distr
                                     | [ |- (rew ?pf1 in ?f) (rew ?pf2 in ?x) = ?f ?x ]
                                       => clear -reflect_base_beq; cbv [eq_rect]
                                     end
                                   | progress cbn [type_of_rawexpr expr.interp types_match_with pattern.type.subst pattern.type.subst_default] in *
                                   | erewrite pident_unify_to_typed' with (pf:=eq_refl) by eassumption
                                   | break_match_step ltac:(fun _ => idtac)
                                   | progress fold (@with_unification_resultT') in *
                                   | match goal with
                                     | [ H : context[app_transport_with_unification_resultT'_cps (pattern_default_interp' _ ?evm1v ?kv) ?argsv ?Tv ?k'v] |- _ ]
                                       => lazymatch kv with
                                          | @id _ => fail
                                          | (fun x => x) => fail
                                          | _ => idtac
                                          end;
                                          rewrite (@app_transport_with_unification_resultT'_pattern_default_interp'_cps_id _ _ _ _ _ argsv kv Tv k'v) in H
                                     | [ |- context[app_transport_with_unification_resultT'_cps (pattern_default_interp' _ ?evm1v ?kv) ?argsv ?Tv ?k'v] ]
                                       => lazymatch kv with
                                          | @id _ => fail
                                          | (fun x => x) => fail
                                          | _ => idtac
                                          end;
                                          setoid_rewrite (@app_transport_with_unification_resultT'_pattern_default_interp'_cps_id _ _ _ _ _ argsv kv Tv k'v)
                                     | [ H : app_transport_with_unification_resultT'_cps ?f ?x _ (@Some _) = ?a,
                                             H' : app_transport_with_unification_resultT'_cps ?f' ?x _ (@Some _) = ?a'
                                         |- _ ]
                                       => unify f f';
                                          assert (a = a') by (etransitivity; (idtac + symmetry); eassumption);
                                          clear H'
                                     | [ H : context[ex _] |- _ ]
                                       => unshelve edestruct H; clear H;
                                          lazymatch goal with
                                          | [ |- rawexpr_types_ok _ _ ] => eapply rawexpr_types_ok_for_type_of_rawexpr; eassumption
                                          | [ |- unify_pattern' _ _ _ _ _ = Some _ ] => eassumption
                                          | [ |- types_match_with ?evm _ _ ] => tryif is_evar evm then idtac else assumption
                                          | [ |- rawexpr_interp_related _ _ ] => eassumption
                                          | _ => idtac
                                          end; shelve_unifiable;
                                          [ shelve.. | ]
                                     | [ |- type_of_rawexpr _ = _ ] => solve [ solve_side_condition_equations ]
                                     | [ |- types_match_with _ _ _ ] => solve [ solve_side_condition_equations ]
                                     end ]));
                  shelve_unifiable).
          1-2:match goal with
              | [ H : ?x == ?y |- ?x = ?y ]
                => apply (type.eqv_iff_eq_of_funext (fun _ _ => functional_extensionality)), H
              end.
        Qed.

        Lemma interp_unify_pattern {t re p v res}
              (Hre : rawexpr_interp_related re v)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
              (H : @unify_pattern t re p _ (@Some _) = Some res)
              (evm' := mk_new_evm (projT1 res) (pattern_collect_vars p))
          : exists resv,
            unification_resultT_interp_related res resv
            /\ exists Hty, (app_with_unification_resultT_cps (@pattern_default_interp t p) resv _ (@Some _) = Some (existT (fun evm => type.interp (base.interp base_interp) (pattern.type.subst_default t evm)) evm' (rew Hty in v))).
        Proof using pident_unify_unknown_correct pident_unify_to_typed try_make_transport_base_cps_correct.
          subst evm'; cbv [unify_pattern unification_resultT_interp_related unification_resultT related_unification_resultT app_with_unification_resultT_cps pattern_default_interp] in *.
          repeat
            (unshelve
               (repeat first [ progress cbv [Option.bind related_sigT_by_eq] in *
                             | progress cbn [projT1 projT2 eq_rect] in *
                             | progress destruct_head'_ex
                             | progress destruct_head'_and
                             | progress inversion_option
                             | progress subst
                             | exfalso; assumption
                             | eassumption
                             | match goal with
                               | [ H : unify_types _ _ _ _ = Some _ |- _ ] => apply unify_types_match_with in H
                               | [ H : unify_pattern' _ _ _ _ _ = Some _, H'' : rawexpr_types_ok _ _ |- _ ]
                                 => let T := type of H in
                                    unique pose proof (H : id T) (* save an extra copy *);
                                    epose proof (interp_unify_pattern' _ H _ H'')
                               | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = Some _ |- _ ] => pose proof (pattern.type.app_forall_vars_lam_forall_vars H); clear H
                               | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = None |- None = Some _ ]
                                 => exfalso; revert H;
                                    lazymatch goal with
                                    | [ |- ?x = None -> False ]
                                      => change (x <> None)
                                    end;
                                    rewrite app_lam_forall_vars_not_None_iff
                               end
                             | progress cps_id'_with_option unify_types_cps_id
                             | progress cps_id'_with_option unify_pattern'_cps_id
                             | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                             | break_innermost_match_hyps_step
                             | break_innermost_match_step
                             | match goal with
                               | [ |- exists x : sigT _, _ ] => eexists (existT _ _ _)
                               | [ |- { pf : _ = _ | _ } ] => exists eq_refl
                               | [ |- { pf : _ = _ & _ } ] => exists eq_refl
                               | [ |- _ /\ _ ] => split
                               | [ |- Some _ = Some _ ] => apply f_equal
                               | [ |- existT _ _ _ = existT _ _ _ ] => apply Sigma.path_sigT_uncurried
                               | [ H : forall x : rawexpr_types_ok ?a ?b, _, H' : rawexpr_types_ok ?a ?b |- _ ] => specialize (H H')
                               end
                             | break_match_step ltac:(fun _ => idtac)
                             | reflexivity
                             | progress intros
                             | eapply mem_pattern_collect_vars_types_match_with; eassumption
                             | exists (eq_type_of_rawexpr_of_types_match_with' ltac:(eassumption) ltac:(eassumption))
                             | match goal with
                               | [ |- rew ?pf in _ = rew ?pf' in _ ]
                                 => cut (pf = pf'); generalize pf pf'; [ intros; subst; reflexivity | clear; cbv beta zeta; intros ];
                                    lazymatch goal with
                                    | [ |- ?a = ?b :> (?x = ?y) ]
                                      => generalize dependent x; generalize dependent y; intros; subst; eliminate_hprop_eq; reflexivity
                                    end
                               end ])).
          (* For 8.7 compatibility *)
          Grab Existential Variables.
          all: assumption.
        Qed.

        Lemma interp_maybe_do_again
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              {should_do_again : bool} {t e v}
              (He : (if should_do_again return @expr.expr _ _ (if should_do_again then _ else _) _ -> _
                     then expr.interp_related_gen ident_interp (fun t => value_interp_related)
                     else expr_interp_related) e v)
          : UnderLets_interp_related (@maybe_do_again _ _ _ do_again should_do_again t e) v.
        Proof using Type.
          cbv [maybe_do_again]; break_innermost_match; [ apply Hdo_again | cbn [UnderLets.interp_related] ];
            assumption.
        Qed.

        Lemma interp_rewrite_with_rule
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              (rewr : rewrite_ruleT)
              (Hrewr : rewrite_rule_data_interp_goodT (projT2 rewr))
              t re v1 v2
              (Ht : t = type_of_rawexpr re)
              (Ht' : rawexpr_types_ok re (type_of_rawexpr re))
          : @rewrite_with_rule do_again t re rewr = Some v1
            -> rawexpr_interp_related re (rew Ht in v2)
            -> UnderLets_interp_related v1 v2.
        Proof using pident_unify_to_typed pident_unify_unknown_correct try_make_transport_base_cps_correct.
          destruct rewr as [p r].
          cbv [rewrite_with_rule].
          repeat first [ match goal with
                         | [ |- Option.bind ?x _ = Some _ -> _ ]
                           => destruct x eqn:?; cbn [Option.bind]; [ | intros; solve [ inversion_option ] ]
                         end
                       | progress cps_id'_with_option unify_pattern_cps_id
                       | progress cps_id'_with_option app_with_unification_resultT_cps_id ].
          repeat first [ break_match_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                       | progress rewrite_type_transport_correct
                       | progress type_beq_to_eq
                       | progress intros
                       | progress cbv [option_bind'] in *
                       | progress cbn [Option.bind projT1 projT2 UnderLets.interp eq_rect UnderLets_interp_related] in *
                       | progress destruct_head'_sigT
                       | progress destruct_head'_sig
                       | progress inversion_option
                       | progress subst
                       | solve [ intros; inversion_option ]
                       | rewrite UnderLets_interp_related_splice_iff
                       | match goal with
                         | [ H : Option.bind ?x _ = Some _ |- _ ]
                           => destruct x eqn:?; cbn [Option.bind] in H; [ | solve [ inversion_option ] ]
                         | [ |- expr.interp _ (UnderLets.interp _ (maybe_do_again _ _ _ _)) == _ ]
                           => apply interp_maybe_do_again_gen; [ assumption | ]
                         | [ |- context[rew ?pf in _] ] => is_var pf; destruct pf
                         end ].
          repeat first [ progress destruct_head'_ex
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | exfalso; assumption
                       | progress inversion_option
                       | progress subst
                       | progress cbv [related_sigT_by_eq] in *
                       | progress cbn [projT1 projT2 eq_rect] in *
                       | match goal with
                         | [ H : unify_pattern _ _ _ _ = Some _ |- _ ] => eapply interp_unify_pattern in H; [ | eassumption | eassumption ]
                         | [ H : unification_resultT_interp_related _ _, Hrewr : rewrite_rule_data_interp_goodT _ |- _ ]
                           => specialize (Hrewr _ _ H)
                         | [ H : option_eq _ ?x ?y, H' : ?x' = Some _ |- _ ]
                           => change x with x' in H; rewrite H' in H;
                              destruct y eqn:?; cbn [option_eq] in H
                         | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : app_with_unification_resultT_cps _ _ _ (@Some _) = Some (existT _ ?evm _) |- _ ]
                           => is_var evm;
                              let H' := fresh in
                              pose proof (projT1_app_with_unification_resultT _ H) as H';
                              cbn [projT1] in H'; subst evm
                         end
                       | progress cbv [deep_rewrite_ruleTP_gen_good_relation] in *
                       | unshelve (eapply UnderLets.splice_interp_related_of_ex; eexists (fun x => rew _ in x), _; repeat apply conj;
                                   [ eassumption | intros | ]);
                         [ etransitivity; eassumption | .. ]
                       | match goal with
                         | [ H : ?R ?xv ?v
                             |- UnderLets_interp_related (fv <-- maybe_do_again _ _ _ ((rew _ in fun x => x) ?xv); _) _ ]
                           => unshelve (eapply UnderLets.splice_interp_related_of_ex;
                                        eexists (fun x => rew _ in x), (rew _ in v); repeat apply conj;
                                        [ eapply interp_maybe_do_again; try eassumption | | ])
                         end ].
          all: repeat first [ assumption
                            | progress intros
                            | reflexivity
                            | progress eliminate_hprop_eq
                            | progress cbn [UnderLets.interp_related eq_rect] in *
                            | match goal with
                              | [ |- context[rew _ in rew _ in _] ]
                                => rewrite <- eq_trans_rew_distr
                              | [ |- context[rew ?pf in _] ]
                                => tryif is_var pf then destruct pf else generalize pf
                              end ].
        Qed.

        Lemma interp_eval_rewrite_rules
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              (re : rawexpr) v
              (Hre : rawexpr_types_ok re (type_of_rawexpr re))
              (res := @eval_rewrite_rules do_again d rew_rules re)
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              (Hr : rawexpr_interp_related re v)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : UnderLets_interp_related res v.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct pident_unify_to_typed try_make_transport_base_cps_correct.
          subst res; cbv [eval_rewrite_rules].
          refine (let H := eval_decision_tree_correct d [re] _ in _).
          destruct H as [H| [? [? [H ?] ] ] ]; rewrite H; cbn [Option.sequence Option.sequence_return UnderLets_interp_related];
            [ now apply expr_of_rawexpr_interp_related | ]; clear H.
          inversion_head' eqlistA.
          unfold Option.bind at 1.
          break_innermost_match_step; [ | cbn [Option.sequence_return UnderLets_interp_related]; now apply expr_of_rawexpr_interp_related ].
          cbn [Option.bind Option.sequence Option.sequence_return UnderLets_interp_related].
          match goal with
          | [ |- ?R (Option.sequence_return ?x ?y) _ ]
            => destruct x eqn:Hinterp
          end; cbn [Option.sequence_return UnderLets.interp]; [ | now apply expr_of_rawexpr_interp_related ].
          unshelve (eapply interp_rewrite_with_rule; [ | | | eassumption | ]; try eassumption).
          { apply eq_type_of_rawexpr_equiv; assumption. }
          { eapply Hrew_rules, nth_error_In; rewrite <- sigT_eta; eassumption. }
          { erewrite <- rawexpr_types_ok_iff_of_rawexpr_equiv, <- eq_type_of_rawexpr_equiv by eassumption; assumption. }
          { apply rawexpr_interp_related_Proper_rawexpr_equiv; assumption. }
        Qed.

        (* Ltac's [repeat] is too weak :-( *)
        Local Ltac grepeat_progress tac :=
          progress (repeat tac); try (grepeat_progress tac).

        Lemma interp_assemble_identifier_rewriters'
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (dt : decision_tree)
              (rew_rules : rewrite_rulesT)
              t re K
              (res := @assemble_identifier_rewriters' dt rew_rules do_again t re K)
              (Hre : rawexpr_types_ok re (type_of_rawexpr re))
              (Ht : type_of_rawexpr re = t)
              v
              (HK : K = (fun P v => rew [P] Ht in v))(*
                      /\ rew pf in value_of_rawexpr re = ev })*)
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
              (Hr : rawexpr_interp_related re v)
          : value_interp_related res (rew Ht in v).
        Proof using raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct pident_unify_to_typed try_make_transport_base_cps_correct.
          subst K res.
          revert dependent re; induction t as [t|s IHs d IHd]; cbn [assemble_identifier_rewriters' value'_interp];
            intros; fold (@type.interp).
          { cbn [value_interp_related].
            destruct Ht; cbn [eq_rect].
            apply interp_eval_rewrite_rules; [ | exact Hdo_again | | ]; assumption. }
          { cbn [value_interp_related].
            intros x1 x2 Hx.
            lazymatch goal with
            | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl); clear IHd
            end.
            { cbv [rValueOrExpr2]; destruct s; cbn.
              all: repeat apply conj; try reflexivity.
              all: repeat match goal with
                          | [ H : _ = _ |- _ ] => revert H
                          | [ H : rawexpr_types_ok _ _ |- _ ] => revert H
                          end.
              all: clear.
              all: generalize dependent (type_of_rawexpr re); intros; subst; assumption. }
            cbn [rawexpr_interp_related type.interp type_of_rawexpr].
            do 2 eexists.
            exists (eq_sym Ht).
            unshelve eexists.
            { clear; cbv [rValueOrExpr2 type_of_rawexpr]; destruct s; reflexivity. }
            repeat apply conj.
            all: grepeat_progress
                   ltac:(first [ instantiate (1:=ltac:(eassumption))
                               | match goal with
                                 | [ |- expr_interp_related (rew [?P] ?H in ?v) ?ev ]
                                   => is_evar ev;
                                      refine (_ : expr_interp_related (rew [P] H in v) (rew [type.interp base.interp] H in _))
                                 end
                               | assumption
                               | progress cbv [eq_sym eq_rect]
                               | break_innermost_match_step
                               | reflexivity
                               | apply expr_of_rawexpr_interp_related
                               | apply reify_interp_related ]). }
        Qed.

        Lemma interp_assemble_identifier_rewriters
              (do_again : forall t : base_type, @expr.expr base_type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              t idc v
              (res := @assemble_identifier_rewriters d rew_rules do_again t idc)
              (Hdo_again : forall t e v,
                  expr.interp_related_gen ident_interp (fun t => value_interp_related) e v
                  -> UnderLets_interp_related (do_again t e) v)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
              (Hv : ident_interp t idc == v)
          : value_interp_related res v.
        Proof using eta_ident_cps_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct pident_unify_to_typed try_make_transport_base_cps_correct.
          subst res; cbv [assemble_identifier_rewriters].
          rewrite eta_ident_cps_correct.
          match goal with
          | [ |- ?R (assemble_identifier_rewriters' ?d ?rew_rules ?do_again ?t ?re' ?K) _ ]
            => apply interp_assemble_identifier_rewriters' with (re:=re') (Ht:=eq_refl)
          end.
          all: cbn [rawexpr_interp_related expr.interp rawexpr_types_ok type_of_rawexpr].
          all: try solve [ reflexivity
                         | assumption
                         | auto ].
        Qed.
      End with_interp.

      Section full.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}
                {base_interp : base -> Type}
                {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                (ident_is_var_like : forall t, ident t -> bool).
        Local Notation expr := (@expr base_type ident).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.
        Context {base_beq : base -> base -> bool}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
                {baseTypeHasNat : base.type.BaseTypeHasNatT base}
                {buildIdent : ident.BuildIdentT base_interp ident}
                {buildEagerIdent : ident.BuildEagerIdentT ident}
                {toRestrictedIdent : ident.ToRestrictedIdentT ident}
                {toFromRestrictedIdent : ident.ToFromRestrictedIdentT ident}
                {invertIdent : invert_expr.InvertIdentT base_interp ident}
                {baseHasNatCorrect : base.BaseHasNatCorrectT base_interp}
                {buildInvertIdentCorrect : invert_expr.BuildInvertIdentCorrectT}
                {ident_interp_Proper : forall t, Proper (eq ==> type.eqv) (ident_interp t)}
                {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.

        Local Notation value := (@Compile.value base_type ident).
        Local Notation value_with_lets := (@Compile.value_with_lets base_type ident).
        Local Notation UnderLets := (UnderLets.UnderLets base_type ident).
        Local Notation reflect := (@Compile.reflect base ident).
        Local Notation var := (type.interp (base.interp base_interp)).
        Local Notation value_interp_related := (@value_interp_related base ident base_interp (@ident_interp)).
        Local Notation expr_interp_related := (@expr.interp_related _ ident _ (@ident_interp)).
        Local Notation rewrite_bottomup := (@rewrite_bottomup base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps).
        Local Notation repeat_rewrite := (@repeat_rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps).
        Local Notation rewrite := (@rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps).
        Local Notation Rewrite := (@Rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps).

        Section with_rewrite_head.
          Context (rewrite_head : forall t (idc : ident t), value_with_lets t)
                  (interp_rewrite_head : forall t idc v, ident_interp _ idc == v -> value_interp_related (rewrite_head t idc) v).

          Local Ltac t :=
            repeat first [ apply interp_Base_value
                         | eassumption
                         | progress cbv beta
                         | progress intros
                         | progress destruct_head'_ex
                         | progress destruct_head'_and
                         | progress subst
                         | match goal with
                           | [ IH : forall v, expr.interp_related_gen _ _ ?e v -> _, H' : expr.interp_related_gen _ _ ?e _ |- _ ]
                             => specialize (IH _ H')
                           end
                         | apply reflect_interp_related
                         | eapply interp_splice_value_with_lets_of_ex;
                           do 2 eexists; repeat apply conj; [ eassumption | | reflexivity ]
                         | eapply @interp_splice_under_lets_with_value_of_ex with (R:=expr_interp_related);
                           do 2 eexists; repeat apply conj
                         | apply interp_reify_and_let_binds
                         | apply UnderLets.reify_and_let_binds_base_interp_related
                         | match goal with
                           | [ H : _ |- _ ] => eapply H; clear H; solve [ t ]
                           | [ |- ?f ?x = ?f ?y ] => is_evar x; reflexivity
                           | [ |- ?x = ?x ] => reflexivity
                           end ].

          Lemma interp_rewrite_bottomup {t e v}
                (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
            : value_interp_related (@rewrite_bottomup var rewrite_head t e) v.
          Proof using interp_rewrite_head try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
            induction e; cbn [rewrite_bottomup value_interp_related expr.interp_related_gen] in *; auto.
            all: t.
          Qed.
        End with_rewrite_head.

        Local Notation nbe := (@rewrite_bottomup var (fun t idc => reflect (expr.Ident idc))).

        Lemma interp_nbe {t e v}
              (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
          : value_interp_related (@nbe t e) v.
        Proof using try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
          eapply interp_rewrite_bottomup; try eassumption.
          intros; apply reflect_interp_related; cbv [expr.interp_related]; cbn [expr.interp_related_gen]; assumption.
        Qed.

        Lemma interp_repeat_rewrite
              {rewrite_head fuel t e v}
              (retT := value_interp_related (@repeat_rewrite _ rewrite_head fuel t e) v)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall t e v,
                            expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v
                            -> UnderLets.interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (do_again t e) v)
                        t idc v,
                  ident_interp _ idc == v
                  -> value_interp_related (@rewrite_head do_again t idc) v)
              (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
          : retT.
        Proof using try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
          subst retT.
          revert rewrite_head t e v Hrewrite_head He.
          induction fuel as [|fuel IH]; cbn [repeat_rewrite]; intros;
            apply interp_rewrite_bottomup; auto; intros;
              apply Hrewrite_head; auto; intros.
          { refine (@interp_nbe (type.base _) _ _ _); assumption. }
          { refine (IH _ (type.base _) _ _ _ _); auto. }
        Qed.

        Lemma interp_related_rewrite
              {rewrite_head fuel t e v}
              (retT := expr.interp_related (@ident_interp) (@rewrite _ rewrite_head fuel t e) v)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall t e v,
                            expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v
                            -> UnderLets.interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (do_again t e) v)
                        t idc v,
                  ident_interp _ idc == v
                  -> value_interp_related (@rewrite_head do_again t idc) v)
              (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
          : retT.
        Proof using try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
          subst retT; cbv [rewrite].
          apply reify_interp_related, interp_repeat_rewrite; auto.
        Qed.

        Lemma interp_rewrite
              {rewrite_head fuel G t e1 e2}
              (retT := expr.interp (@ident_interp) (@rewrite _ rewrite_head fuel t e1) == expr.interp (@ident_interp) e2)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall t e v,
                            expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v
                            -> UnderLets.interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (do_again t e) v)
                        t idc v,
                  ident_interp _ idc == v
                  -> value_interp_related (@rewrite_head do_again t idc) v)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value_interp_related v1 v2)
              (Hwf : expr.wf G e1 e2)
          : retT.
        Proof using try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
          apply expr.eqv_of_interp_related, interp_related_rewrite; try assumption; [].
          eapply expr.interp_related_gen_of_wf; eassumption.
        Qed.

        Lemma InterpRewrite
              {rewrite_head fuel t e}
              (retT := expr.Interp (@ident_interp) (@Rewrite rewrite_head fuel t e) == expr.Interp (@ident_interp) e)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall t e v,
                            expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v
                            -> UnderLets.interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (do_again t e) v)
                        t idc v,
                  ident_interp _ idc == v
                  -> value_interp_related (@rewrite_head _ do_again t idc) v)
              (Hwf : expr.Wf e)
          : retT.
        Proof using try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect.
          clear -Hrewrite_head Hwf try_make_transport_base_cps_correct ident_interp_Proper buildInvertIdentCorrect buildInterpIdentCorrect type_base base'.
          subst retT; cbv [Rewrite expr.Interp].
          eapply interp_rewrite; eauto; cbn [List.In]; tauto.
        Qed.
      End full.
    End Compile.
  End RewriteRules.
End Compilers.
