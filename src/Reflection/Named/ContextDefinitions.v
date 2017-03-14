Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Logic.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var)
          (base_type_code_dec : forall x y : base_type_code, {x = y} + {x <> y})
          (Name_dec : forall x y : Name, {x = y} + {x <> y}).

  Fixpoint find_Name n
           {T : flat_type base_type_code}
    : interp_flat_type (fun _ => Name) T -> option base_type_code
    := match T with
       | Tbase t' => fun n' : Name => if Name_dec n n' then Some t' else None
       | Unit => fun _ => None
       | Prod A B
         => fun ab : interp_flat_type _ A * interp_flat_type _ B
            => match @find_Name n B (snd ab), @find_Name n A (fst ab) with
               | Some tb, _ => Some tb
               | None, Some ta => Some ta
               | None, None => None
               end
       end.

  Definition cast_if_eq {var'} t t' (v : var' t) : option (var' t')
    := match base_type_code_dec t t', base_type_code_dec t' t' with
       | left pf, left pf' => Some (eq_rect _ var' v _ (eq_trans pf (eq_sym pf')))
       | _, right pf' => match pf' eq_refl with end
       | right pf, _ => None
       end.

  Lemma cast_if_eq_refl {var'} t v : @cast_if_eq var' t t v = Some v.
  Proof.
    compute; clear; break_match; reflexivity.
  Qed.

  Fixpoint find_Name_and_val {var'} t n
           {T : flat_type base_type_code}
    : interp_flat_type (fun _ => Name) T -> interp_flat_type var' T -> option (var' t) -> option (var' t)
    := match T with
       | Tbase t' => fun n' v default => if Name_dec n n'
                                         then cast_if_eq t' t v
                                         else default
       | Unit => fun _ _ default => default
       | Prod A B
         => fun (ab : interp_flat_type _ A * interp_flat_type _ B)
                (a'b' : interp_flat_type _ A * interp_flat_type _ B)
                default
            => @find_Name_and_val
                 var' t n B (snd ab) (snd a'b')
                 (@find_Name_and_val
                    var' t n A (fst ab) (fst a'b')
                    default)
       end.

  Class ContextOk :=
    { lookupb_extendb_same
      : forall (ctx : Context) n t v, lookupb (extendb ctx n (t:=t) v) n t = Some v;
      lookupb_extendb_different
      : forall (ctx : Context) n n' t t' v, n <> n' -> lookupb (extendb ctx n (t:=t) v) n' t'
                                                                                 = lookupb ctx n' t';
      lookupb_extendb_wrong_type
      : forall (ctx : Context) n t t' v, t <> t' -> lookupb (extendb ctx n (t:=t) v) n t' = None;
      lookupb_removeb
      : forall (ctx : Context) n n' t t', n <> n' -> lookupb (removeb ctx n t) n' t'
                                                                     = lookupb ctx n' t';
      lookupb_empty
      : forall n t, lookupb (@empty _ _ _ Context) n t = None }.
End with_context.
