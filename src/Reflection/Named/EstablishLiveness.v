(** * Compute a list of liveness values for each binding *)
Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Util.ListUtil.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Delimit Scope nexpr_scope with nexpr.

Inductive liveness := live | dead.
Fixpoint merge_liveness (ls1 ls2 : list liveness) :=
  match ls1, ls2 with
  | cons x xs, cons y ys
    => cons match x, y with
            | live, _
            | _, live
              => live
            | dead, dead
              => dead
            end
            (@merge_liveness xs ys)
  | nil, ls
  | ls, nil
    => ls
  end.

Section language.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).

  Section internal.
    Context (Name : Type)
            (OutName : Type)
            {Context : Context Name (fun _ : base_type_code => list liveness)}.

    Definition compute_livenessf_step
               (compute_livenessf : forall (ctx : Context) {t} (e : exprf Name t) (prefix : list liveness), list liveness)
               (ctx : Context)
               {t} (e : exprf Name t) (prefix : list liveness)
      : list liveness
      := match e with
         | Const _ x => prefix
         | Var t' name => match lookup ctx t' name with
                          | Some ls => ls
                          | _ => nil
                          end
         | Op _ _ op args
           => @compute_livenessf ctx _ args prefix
         | LetIn tx n ex _ eC
           => let lx := @compute_livenessf ctx _ ex prefix in
              let lx := merge_liveness lx (prefix ++ repeat live (count_pairs tx)) in
              let ctx := extend ctx n (SmartVal _ (fun _ => lx) tx) in
              @compute_livenessf ctx _ eC (prefix ++ repeat dead (count_pairs tx))
         | Pair _ ex _ ey
           => merge_liveness (@compute_livenessf ctx _ ex prefix)
                             (@compute_livenessf ctx _ ey prefix)
         end.

    Fixpoint compute_livenessf ctx {t} e prefix
      := @compute_livenessf_step (@compute_livenessf) ctx t e prefix.

    Fixpoint compute_liveness (ctx : Context)
             {t} (e : expr Name t) (prefix : list liveness)
      : list liveness
      := match e with
         | Return _ x => compute_livenessf ctx x prefix
         | Abs src _ n f
           => let prefix := prefix ++ (live::nil) in
              let ctx := extendb (t:=src) ctx n prefix in
              @compute_liveness ctx _ f prefix
         end.

    Section insert_dead.
      Context (default_out : option OutName).

      Fixpoint insert_dead_names_gen (ls : list liveness) (lsn : list OutName)
        : list (option OutName)
        := match ls with
           | nil => nil
           | cons live xs
             => match lsn with
                | cons n lsn' => Some n :: @insert_dead_names_gen xs lsn'
                | nil => default_out :: @insert_dead_names_gen xs nil
                end
           | cons dead xs
             => None :: @insert_dead_names_gen xs lsn
           end.
      Definition insert_dead_names {t} (e : expr Name t)
        := insert_dead_names_gen (compute_liveness empty e nil).
    End insert_dead.
  End internal.
End language.

Global Arguments compute_livenessf {_ _ _ _ _} ctx {t} e prefix.
Global Arguments compute_liveness {_ _ _ _ _} ctx {t} e prefix.
Global Arguments insert_dead_names {_ _ _ _ _ _} default_out {t} e lsn.
