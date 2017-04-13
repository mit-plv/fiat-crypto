Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.

Ltac fin_t_step :=
  solve [ reflexivity ].
Ltac fin_t_late_step :=
  solve [ tauto
        | congruence
        | eauto
        | exfalso; unfold not in *; eauto ].
Ltac inversion_step :=
  first [ progress subst
        | match goal with
          | [ H := _ |- _ ] => subst H
          | [ H : ?x = ?y |- _ ] => subst x || subst y
          end
        | progress inversion_option
        | progress inversion_sigma
        | progress inversion_prod
        | progress destruct_head' and
        | progress eliminate_hprop_eq
        | match goal with
          | [ H : ?T, H' : ?T |- _ ] => clear H'
          | [ H : ?x = ?x |- _ ] => clear H
          end
        | progress split_and ].
Ltac rewrite_lookupb_extendb_step :=
  first [ rewrite lookupb_extendb_different by congruence
        | rewrite lookupb_extendb_same
        | rewrite lookupb_extendb_wrong_type by assumption
        | rewrite lookupb_removeb by congruence ].
Ltac specializer_t_step :=
  match goal with
  | _ => progress specialize_by_assumption
  | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
  | [ H : ?T, H' : ?T |- _ ] => clear H'
  | [ H : forall v, Some _ = Some v -> _ |- _ ]
    => specialize (H _ eq_refl)
  | [ H : forall v, Some v = Some _ -> _ |- _ ]
    => specialize (H _ eq_refl)
  end.
Ltac misc_t_step :=
  first [ progress intros
        | progress simpl in * ].
Ltac break_t_step :=
  first [ progress break_innermost_match_step
        | progress unfold cast_if_eq in *
        | match goal with
          | [ H : context[match _ with _ => _ end] |- _ ]
            => revert H; progress break_innermost_match_step
          | [ |- _ /\ _ ] => split
          | [ |- _ <-> _ ] => split
          | [ |- ~ _ ] => intro
          end
        | progress destruct_head' ex
        | progress destruct_head' or ].
Ltac refolder_t_step :=
  let myfold_in_star c :=
      (let c' := (eval cbv [interp_flat_type] in c) in
       change c' with c in * ) in
  first [ match goal with
          | [ var : ?base_type_code -> Type |- _ ]
            => progress myfold_in_star (@interp_flat_type base_type_code var)
          | [ base_type_code : Type, Name : Type |- _ ]
            => progress myfold_in_star (@interp_flat_type base_type_code (fun _ => Name))

          end ].
Ltac rewriter_t_step :=
  first [ match goal with
          | [ H : _ |- _ ] => rewrite H by (assumption || congruence)
          | [ H : _ |- _ ] => etransitivity; [ | rewrite H by (assumption || congruence); reflexivity ]
          | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
          | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
          | [ H : ?x = ?a :> option _, H' : ?x = ?b :> option _ |- _ ]
            => assert (a = b)
              by (transitivity x; [ symmetry | ]; assumption);
               clear H'
          | _ => progress autorewrite with ctx_db in *
          end ].
Ltac t_step :=
  first [ fin_t_step
        | inversion_step
        | rewrite_lookupb_extendb_step
        | specializer_t_step
        | misc_t_step
        | break_t_step
        | refolder_t_step
        | rewriter_t_step
        | fin_t_late_step ].
Ltac t := repeat t_step.
