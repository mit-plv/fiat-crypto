(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.ContextProperties.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          {base_type_dec : DecidableRel (@eq base_type_code)}
          {Name_dec : DecidableRel (@eq Name)}
          {Context : @Context base_type_code Name interp_base_type}
          {ContextOk : ContextOk Context}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation wff := (@wff base_type_code op (fun _ => Name) interp_base_type).
  Local Notation wf := (@wf base_type_code op (fun _ => Name) interp_base_type).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).
  Local Notation ocompilef := (@ocompilef base_type_code op Name).
  Local Notation ocompile := (@ocompile base_type_code op Name).
  Local Notation compilef := (@compilef base_type_code op Name).
  Local Notation compile := (@compile base_type_code op Name).

  Lemma interpf_ocompilef (ctx : Context) {t} (e : exprf t) e' (ls : list (option Name))
        G
        (Hwf : wff G e e')
        (HG : forall t n x, List.In (existT _ t (n, x)%core) G -> lookupb ctx n t = Some x)
        v
        (H : ocompilef e ls = Some v)
    : Named.interpf (interp_op:=interp_op) (ctx:=ctx) v
      = Some (interpf interp_op e').
  Proof.
    revert dependent ctx; revert dependent ls; induction Hwf;
      repeat first [ progress intros
                   | progress subst
                   | progress inversion_option
                   | apply (f_equal (@Some _))
                   | apply (f_equal (@interp_op _ _ _))
                   | solve [ eauto ]
                   | progress simpl in *
                   | progress unfold option_map, LetIn.Let_In in *
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | progress destruct_head' or
                   | match goal with
                     | [ IH : forall v ls, ocompilef ?e ls = Some v -> _, H : ocompilef ?e ?ls' = Some ?v' |- _ ]
                       => specialize (IH _ _ H)
                     | [ IH : forall x1 x2 v ls, ocompilef (?e x1) ls = Some v -> _, H : ocompilef (?e ?x1') ?ls' = Some ?v' |- _ ]
                       => specialize (fun x2 => IH _ x2 _ _ H)
                     | [ H : context[List.In _ (_ ++ _)] |- _ ]
                       => rewrite List.in_app_iff in H
                     | [ H : forall ctx, _ -> Named.interpf ?e = Some _, H' : context[Named.interpf ?e] |- _ ]
                       => rewrite H in H' by assumption
                     | [ H : forall x2 ctx, _ -> Named.interpf ?e = Some _ |- Named.interpf ?e = Some _ ]
                       => apply H; clear H
                     end ].
    { repeat match goal with
             | _ => erewrite lookupb_extend by assumption
             | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
               => lazymatch default with None => fail | _ => idtac end;
                    rewrite (find_Name_and_val_split tdec ndec (default:=default))
             | [ H : _ |- _ ] => erewrite H by eassumption
             | _ => progress unfold dec in *
             | _ => progress break_innermost_match_step
             | _ => progress subst
             | _ => congruence
             end.
      Focus 2.
  Admitted.
  (*
  Fixpoint ocompilef {t} (e : exprf t) (ls : list (option Name)) {struct e}
    : option (nexprf t)
    := match e in @Syntax.exprf _ _ _ t return option (nexprf t) with
       | TT => Some Named.TT
       | Var _ x => Some (Named.Var x)
       | Op _ _ op args => option_map (Named.Op op) (@ocompilef _ args ls)
       | LetIn tx ex _ eC
         => match @ocompilef _ ex nil, split_onames tx ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn tx n x C) (@ocompilef _ (eC n) ls')
            | _, _ => None
            end
       | Pair _ ex _ ey => match @ocompilef _ ex nil, @ocompilef _ ey nil with
                           | Some x, Some y => Some (Named.Pair x y)
                           | _, _ => None
                           end
       end.

  Definition ocompile {t} (e : expr t) (ls : list (option Name))
    : option (nexpr t)
    := match e in @Syntax.expr _ _ _ t return option (nexpr t) with
       | Abs src _ f
         => match split_onames src ls with
            | (Some n, ls')%core
              => option_map (Named.Abs n) (@ocompilef _ (f n) ls')
            | _ => None
            end
       end.

  Definition compilef {t} (e : exprf t) (ls : list Name) := @ocompilef t e (List.map (@Some _) ls).
  Definition compile {t} (e : expr t) (ls : list Name) := @ocompile t e (List.map (@Some _) ls).*)
End language.
