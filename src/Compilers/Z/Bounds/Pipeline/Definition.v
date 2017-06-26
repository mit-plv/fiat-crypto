(** * Reflective Pipeline: Main Pipeline Definition *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.OutputType.
(** This file contains the definitions of the assembling of the
    various transformations that are used in the pipeline.  There are
    two stages to the reflective pipeline, with different
    requirements.

    The pre-Wf stage is intended to consist of transformations that
    make the term smaller, and, importantly, should only consist of
    transformations whose interpretation-correctness proofs do not
    require well-founded hypotheses.  Generally this is the case for
    transformations whose input and output [var] types match.  The
    correctness condition for this stage is that the interpretation of
    the transformed term must equal the interpretation of the original
    term, with no side-conditions.

    The post-Wf stage is the rest of the pipeline; its correctness
    condition must have the shape of the correctness condition for
    word-size selection.  We define a record to hold the transformed
    term, so that we can get bounds and similar out of it, without
    running into issues with slowness of conversion. *)

(** ** Pre-Wf Stage *)
(** *** Pre-Wf Pipeline Imports *)
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.Z.ArithmeticSimplifier.
Require Import Crypto.Compilers.Z.ArithmeticSimplifierInterp.

(** *** Definition of the Pre-Wf Pipeline *)
(** Do not change the name or the type of this definition *)
Definition PreWfPipeline {t} (e : Expr base_type op t) : Expr base_type op _
  := ExprEta (SimplifyArith false (Linearize e)).

(** *** Correctness proof of the Pre-Wf Pipeline *)
(** Do not change the statement of this lemma.  You shouldn't need to
    change it's proof, either; all of the relevant lemmas should be in
    the [reflective_interp] rewrite database.  If they're not, you
    should find the file where they are defined and add them. *)
Lemma InterpPreWfPipeline {t} (e : Expr base_type op t)
  : forall x, Interp interp_op (PreWfPipeline e) x = Interp interp_op e x.
Proof.
  unfold PreWfPipeline; intro.
  repeat autorewrite with reflective_interp.
  reflexivity.
Qed.



(** ** Post-Wf Stage *)
(** *** Post-Wf Pipeline Imports *)
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.EtaWf.
Require Import Crypto.Compilers.Z.Inline.
Require Import Crypto.Compilers.Z.InlineInterp.
Require Import Crypto.Compilers.Z.InlineWf.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.LinearizeWf.
(*Require Import Crypto.Compilers.Z.CommonSubexpressionElimination.
Require Import Crypto.Compilers.Z.CommonSubexpressionEliminationInterp.
Require Import Crypto.Compilers.Z.CommonSubexpressionEliminationWf.*)
Require Import Crypto.Compilers.Z.ArithmeticSimplifierWf.
Require Import Crypto.Compilers.Z.RewriteAddToAdc.
Require Import Crypto.Compilers.Z.RewriteAddToAdcWf.
Require Import Crypto.Compilers.Z.RewriteAddToAdcInterp.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijn.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijnInterp.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijnWf.
Require Import Crypto.Util.Sigma.MapProjections.

(** *** Definition of the Post-Wf Pipeline *)
(** We define the record that holds various options to customize the
    pipeline. *)
Record PipelineOptions := { anf : bool ; adc_fusion : bool }.
Definition default_PipelineOptions :=
  {| anf := false ;
     adc_fusion := true |}.
(** Do not change the name or the type of these two definitions *)
(** The definition [PostWfPreBoundsPipeline] is for the part of the
    pipeline that comes before [MapCast]; it must preserve the type of
    the expression. *)
Definition PostWfPreBoundsPipeline
           (opts : PipelineOptions)
           {t} (e : Expr base_type op t)
  : Expr base_type op t
  := let e := InlineConst e in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := if opts.(anf) then InlineConst (ANormal e) else e in
     let e := if opts.(adc_fusion) then RewriteAdc e else e in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := if opts.(anf) then InlineConstAndOpp (ANormal e) else e in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     (*let e := CSE false e in*)
     e.
(** The definition [PostWfBoundsPipeline] is for the part of the
    pipeline that begins with [MapCast]. *)
Definition PostWfBoundsPipeline
           round_up
           (opts : PipelineOptions)
           {t} (e0 : Expr base_type op t)
           (e : Expr base_type op t)
           (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
  : option (@ProcessedReflectivePackage round_up)
  := Build_ProcessedReflectivePackage_from_option_sigma
       e0 input_bounds
       (let e := MapCast _ e input_bounds in
        option_map
          (projT2_map
             (fun b e'
              => let e' := InlineConst e' in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := InlineConst (Linearize (SimplifyArith false e')) in
                 let e' := if opts.(anf) then InlineConst (ANormal e') else e' in
                 let e' := ExprEta e' in
                 e'))
          e).

(** *** Correctness proof of the Post-Wf Pipeline *)
(** Do not change the statement of this lemma. *)
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.InterpSideConditions.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.PointedProp.

Section with_round_up_list.
  Context {allowable_lgsz : list nat}.

  Local Notation pick_typeb := (@Bounds.bounds_to_base_type (Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Local Opaque to_prop InterpSideConditions.

  Definition PostWfPipelineCorrect
             opts
             {t}
             (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
             (Hwf : Wf e)
             (e' := PostWfPreBoundsPipeline opts e)
             {b e''} (He' : PostWfBoundsPipeline _ opts e e' input_bounds
                            = Some {| input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e'' |})
             (v : interp_flat_type Syntax.interp_base_type (domain t))
             (v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds))
             (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
             (Hside : to_prop (InterpSideConditions e' v))
    : Bounds.is_bounded_by b (Interp interp_op e v)
      /\ cast_back_flat_const (Interp interp_op e'' v') = Interp interp_op e v.
  Proof using Type.
    (** These first two lines probably shouldn't change much *)
    unfold PostWfBoundsPipeline, PostWfPreBoundsPipeline, Build_ProcessedReflectivePackage_from_option_sigma, option_map, projT2_map in *; subst e'.
    repeat (break_match_hyps || inversion_option || inversion_ProcessedReflectivePackage
            || inversion_sigma || eliminate_hprop_eq || inversion_prod
            || simpl in * || subst).
    (** Now handle all the transformations that come after the word-size selection *)
    all:autorewrite with reflective_interp.
    (** Now handle word-size selection *)
    all:(eapply MapCastCorrect_eq; [ | eassumption | eassumption | assumption | .. ];
         [ solve_wf_side_condition | reflexivity | ]).
    (** Now handle all the transformations that come before the word-size selection *)
    all:repeat autorewrite with reflective_interp; reflexivity.
  Qed.
End with_round_up_list.

(** ** Constant Simplification and Unfolding *)
(** The reflective pipeline may introduce constants that you want to
    unfold before instantiating the refined term; you can control that
    here.  A number of reflection-specific constants are always
    unfolded (in ReflectiveTactics.v).  Currently, we also reduce
    expressions of the form [wordToZ (ZToWord Z_literal)], as
    specified here. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.FixedWordSizes.
Require Import Bedrock.Word.

Module Export Exports. (* export unfolding strategy *)
  (* iota is probably (hopefully?) the cheapest reduction.
     Unfortunately, we can't say no-op here.  This is meant to be
     extended. *)
  Declare Reduction extra_interp_red := cbv iota.

  (** Overload this to change reduction behavior of constants of the
      form [wordToZ (ZToWord Z_literal)].  You might want to set this
      to false if your term is very large, to speed things up. *)
  Ltac do_constant_simplification := constr:(true).

  Global Arguments ZToWord !_ !_ / .
  Global Arguments wordToZ !_ !_ / .
  Global Arguments word_case_dep _ !_ _ _ _ _ / .
  Global Arguments ZToWord32 !_ / .
  Global Arguments ZToWord64 !_ / .
  Global Arguments ZToWord128 !_ / .
  Global Arguments ZToWord_gen !_ !_ / .
  Global Arguments word32ToZ !_ / .
  Global Arguments word64ToZ !_ / .
  Global Arguments word128ToZ !_ / .
  Global Arguments wordToZ_gen !_ !_ / .
  Global Arguments Z.to_N !_ / .
  Global Arguments Z.of_N !_ / .
  Global Arguments Word.NToWord !_ !_ / .
  Global Arguments Word.wordToN !_ !_ / .
  Global Arguments Word.posToWord !_ !_ / .
  Global Arguments N.succ_double !_ / .
  Global Arguments Word.wzero' !_ / .
  Global Arguments N.double !_ .
  Global Arguments Nat.pow !_ !_ / .
  Global Arguments Nat.mul !_ !_ / .
  Global Arguments Nat.add !_ !_ / .

  Declare Reduction constant_simplification := cbn [FixedWordSizes.wordToZ FixedWordSizes.ZToWord word_case_dep ZToWord32 ZToWord64 ZToWord128 ZToWord_gen word32ToZ word64ToZ word128ToZ wordToZ_gen Word.NToWord Word.wordToN Word.posToWord Word.wzero' Z.to_N Z.of_N N.succ_double N.double Nat.pow Nat.mul Nat.add].
End Exports.
