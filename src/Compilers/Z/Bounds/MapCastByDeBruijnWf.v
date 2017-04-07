Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Z.MapCastByDeBruijnWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.IsBoundedBy.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.PullCast.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijn.

Definition Wf_MapCast
           {round_up}
           {t} (e : Expr base_type op t)
           (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
           {b} e' (He' : MapCast round_up e input_bounds = Some (existT _ b e'))
           (Hwf : Wf e)
  : Wf e'
  := @Wf_MapCast
       (@Bounds.interp_base_type) (@Bounds.interp_op)
       (@Bounds.bounds_to_base_type round_up)
       (fun _ _ opc _ => @genericize_op _ _ _ opc _ _ _)
       t e input_bounds b e' He' Hwf.

Definition Wf_MapCast_arrow
           {round_up}
           {s d} (e : Expr base_type op (Arrow s d))
           (input_bounds : interp_flat_type Bounds.interp_base_type s)
           {b} e' (He' : MapCast round_up e input_bounds = Some (existT _ b e'))
           (Hwf : Wf e)
  : Wf e'
  := @Wf_MapCast_arrow
       (@Bounds.interp_base_type) (@Bounds.interp_op)
       (@Bounds.bounds_to_base_type round_up)
       (fun _ _ opc _ => @genericize_op _ _ _ opc _ _ _)
       s d e input_bounds b e' He' Hwf.

Hint Extern 1 (Wf ?e')
=> match goal with
   | [ He : MapCast _ _ _ = Some (existT _ _ e') |- _ ]
     => first [ refine (@Wf_MapCast _ _ _ _ _ _ He _)
              | refine (@Wf_MapCast_arrow _ _ _ _ _ _ _ He _) ]
   end : wf.
