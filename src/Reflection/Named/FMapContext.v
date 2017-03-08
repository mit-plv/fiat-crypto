Require Import Coq.Bool.Sumbool.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Equality.

Module FMapContextFun (E : DecidableType) (W : WSfun E).
  Module Import Properties := WProperties_fun E W.
  Import F.
  Section ctx.
    Context (E_eq_l : forall x y, E.eq x y -> x = y)
            base_type_code (var : base_type_code -> Type)
            (base_type_code_beq : base_type_code -> base_type_code -> bool)
            (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
            (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true).

    Definition var_cast {a b} (x : var a) : option (var b)
      := match Sumbool.sumbool_of_bool (base_type_code_beq a b), Sumbool.sumbool_of_bool (base_type_code_beq b b) with
         | left pf, left pf' => match eq_trans (base_type_code_bl_transparent _ _ pf) (eq_sym (base_type_code_bl_transparent _ _ pf')) with
                                | eq_refl => Some x
                                end
         | right _, _ | _, right _ => None
         end.
    Definition FMapContext : @Context base_type_code W.key var
      := {| ContextT := W.t { t : _ & var t };
            lookupb ctx n t
            := match W.find n ctx with
               | Some (existT t' v)
                 => var_cast v
               | None => None
               end;
            extendb ctx n t v
            := W.add n (existT _ t v) ctx;
            removeb ctx n t
            := W.remove n ctx;
            empty := W.empty _ |}.
    Lemma FMapContextOk : @ContextOk base_type_code W.key var FMapContext.
    Proof.
      split;
        repeat first [ reflexivity
                     | progress simpl in *
                     | progress intros
                     | rewrite add_eq_o by reflexivity
                     | progress rewrite ?add_neq_o, ?remove_neq_o in * by intuition
                     | progress rewrite empty_o in *
                     | progress unfold var_cast
                     | progress break_innermost_match_step
                     | rewrite concat_pV
                     | congruence
                     | rewrite base_type_code_lb in * by reflexivity ].
    Qed.
  End ctx.

  Section ctx_nd.
    Context {base_type_code var : Type}.

    Definition FMapContext_nd : @Context base_type_code W.key (fun _ => var)
      := {| ContextT := W.t var;
            lookupb ctx n t := W.find n ctx;
            extendb ctx n t v := W.add n v ctx;
            removeb ctx n t := W.remove n ctx;
            empty := W.empty _ |}.
  End ctx_nd.
End FMapContextFun.

Module FMapContext (W : WS) := FMapContextFun W.E W.
