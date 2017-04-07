(** * Definition of the output type of the post-Wf pipeline *)
(** Do not change these definitions unless you're hacking on the
    entire reflective pipeline tactic automation. *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.

Section with_round_up_list.
  Context {allowable_lgsz : list nat}.

  Local Notation pick_typeb := (@Bounds.bounds_to_base_type (Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Record ProcessedReflectivePackage
    := { InputType : _;
         input_expr : Expr base_type op InputType;
         input_bounds : interp_flat_type Bounds.interp_base_type (domain InputType);
         output_bounds :> interp_flat_type Bounds.interp_base_type (codomain InputType);
         output_expr :> Expr base_type op (Arrow (pick_type input_bounds) (pick_type output_bounds)) }.

  Definition Build_ProcessedReflectivePackage_from_option_sigma
             {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
             (result : option { output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)
                                                & Expr base_type op (Arrow (pick_type input_bounds) (pick_type output_bounds)) })
    : option ProcessedReflectivePackage
    := option_map
         (fun be
          => let 'existT b e' := be in
             {| InputType := t ; input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e' |})
         result.

  Definition ProcessedReflectivePackage_to_sigT (x : ProcessedReflectivePackage)
    : { InputType : _
                    & Expr base_type op InputType
                      * { bounds : interp_flat_type Bounds.interp_base_type (domain InputType)
                                   * interp_flat_type Bounds.interp_base_type (codomain InputType)
                                   & Expr base_type op (Arrow (pick_type (fst bounds)) (pick_type (snd bounds))) } }%type
    := let (a, b, c, d, e) := x in
       existT _ a (b, (existT _ (c, d) e)).
End with_round_up_list.

Ltac inversion_ProcessedReflectivePackage :=
  repeat match goal with
         | [ H : _ = _ :> ProcessedReflectivePackage |- _ ]
           => apply (f_equal ProcessedReflectivePackage_to_sigT) in H;
              cbv [ProcessedReflectivePackage_to_sigT] in H
         end;
  inversion_sigma; inversion_prod.
