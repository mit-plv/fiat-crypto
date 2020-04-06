(** * BoundsPipeline *)
(** This file assembles the various compiler stages together into a
    composed pipeline.  It is the final interface for the compiler,
    right before integration with Arithmetic. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Rewriter.Language.Language.
Require Crypto.Language.API.
Require Rewriter.Language.UnderLets.
Require Crypto.AbstractInterpretation.AbstractInterpretation.
Require Rewriter.Rewriter.Rewriter.
Require Crypto.MiscCompilerPasses.
Require Crypto.Stringification.Language.
Require Rewriter.Language.Wf.
Require Crypto.Language.WfExtra.
Require Rewriter.Language.UnderLetsProofs.
Require Crypto.Language.UnderLetsProofsExtra.
Require Crypto.MiscCompilerPassesProofs.
Require Crypto.MiscCompilerPassesProofsExtra.
Require Crypto.Rewriter.All.
Require Crypto.AbstractInterpretation.Wf.
Require Crypto.AbstractInterpretation.WfExtra.
Require Crypto.AbstractInterpretation.Proofs.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import
  Rewriter.Language.Wf
  Crypto.Language.WfExtra
  Rewriter.Language.UnderLetsProofs
  Crypto.Language.UnderLetsProofsExtra
  Crypto.MiscCompilerPassesProofs
  Crypto.MiscCompilerPassesProofsExtra
  Crypto.Rewriter.All
  Crypto.AbstractInterpretation.Wf
  Crypto.AbstractInterpretation.WfExtra
  Crypto.AbstractInterpretation.Proofs
  Rewriter.Language.Language
  Crypto.Language.API
  Rewriter.Language.UnderLets
  Crypto.AbstractInterpretation.AbstractInterpretation
  Rewriter.Rewriter.Rewriter
  Crypto.MiscCompilerPasses
  Crypto.Stringification.Language.

Import
  Language.Wf.Compilers
  Language.WfExtra.Compilers
  UnderLetsProofs.Compilers
  UnderLetsProofsExtra.Compilers
  MiscCompilerPassesProofs.Compilers
  MiscCompilerPassesProofsExtra.Compilers
  Rewriter.All.Compilers
  AbstractInterpretation.Wf.Compilers
  AbstractInterpretation.WfExtra.Compilers
  AbstractInterpretation.Proofs.Compilers
  Language.Compilers
  Language.API.Compilers
  UnderLets.Compilers
  AbstractInterpretation.Compilers
  Rewriter.Compilers
  MiscCompilerPasses.Compilers
  Stringification.Language.Compilers.

Import
  ProofsCommon.Compilers.RewriteRules.GoalType
  ProofsCommon.Compilers.RewriteRules.GoalType.DefaultOptionType.

Export Stringification.Language.Compilers.Options.

Import Compilers.API.

Definition relax_zrange_gen_ranges (possible_ranges : list zrange)
  : zrange -> option zrange
  := fun r
     => List.fold_right
          (fun r' default
           => if (r <=? r')%zrange then Some r' else default)
          None
          possible_ranges.

Inductive kind_of_range := signed | unsigned.

Definition ranges_of_bitwidths (bws : list (Z * kind_of_range))
  : list zrange
  := List.map (fun '(bw, k)
               => match k with
                  | unsigned => r[0~>2^bw-1]
                  | signed => r[-2^(bw-1) ~> 2^(bw-1)-1]
                  end%zrange)
              bws.

Definition relax_zrange_gen (only_signed : bool) (possible_values : list Z)
  : zrange -> option zrange
  := relax_zrange_gen_ranges
       (ranges_of_bitwidths
          (List.flat_map
             (fun k => List.map (fun bw => (bw, k)) possible_values)
             (if only_signed
              then [signed]
              else [unsigned; signed] (* put [unsigned] first so we prefer unsigned ranges to signed ranges *)))).

Lemma relax_zrange_gen_ranges_good
      (possible_ranges : list zrange)
  : forall r r' z : zrange,
    is_true (z <=? r)%zrange -> relax_zrange_gen_ranges possible_ranges r = Some r' -> is_true (z <=? r')%zrange.
Proof.
  intros r r' z Hzr.
  cbv [relax_zrange_gen_ranges].
  induction possible_ranges as [|R Rs IHRs]; cbn [List.fold_right]; [ congruence | ].
  intros; break_innermost_match_hyps; inversion_option; subst.
  { etransitivity; eassumption. }
  { eauto. }
Qed.

Lemma relax_zrange_gen_good
      (only_signed : bool)
      (possible_values : list Z)
  : forall r r' z : zrange,
    (z <=? r)%zrange = true -> relax_zrange_gen only_signed possible_values r = Some r' -> (z <=? r')%zrange = true.
Proof. apply relax_zrange_gen_ranges_good. Qed.

(** Which of the rewriter methods do we use? *)
(** Note that we don't currently generate a precomputed naive method, because it eats too much RAM to do so. *)
Inductive low_level_rewriter_method_opt :=
  precomputed_decision_tree | unreduced_decision_tree | unreduced_naive.
Existing Class low_level_rewriter_method_opt.
(** We make this an instance later *)
Definition default_low_level_rewriter_method : low_level_rewriter_method_opt
  := precomputed_decision_tree.
(** Prefix function definitions with static/non-public? *)
Class static_opt := static : bool.
Typeclasses Opaque static_opt.
(** Prefix internal function definitions with static/non-public? *)
Class internal_static_opt := internal_static : bool.
Typeclasses Opaque internal_static_opt.
(** Use the alternate cmovznz implementation using mul? *)
Class use_mul_for_cmovznz_opt := use_mul_for_cmovznz : bool.
Typeclasses Opaque use_mul_for_cmovznz_opt.
(** Emit the primitive operations? *)
Class emit_primitives_opt := emit_primitives : bool.
Typeclasses Opaque emit_primitives_opt.
(** Only allow signed integers in the output *)
Class only_signed_opt := only_signed : bool.
Typeclasses Opaque only_signed_opt.
(** Split apart multiplications? *)
Class should_split_mul_opt := should_split_mul : bool.
Typeclasses Opaque should_split_mul_opt.
(** If [None], don't split apart multiplications; if [Some (w, wc)], split apart multiplications to use wordsize [w] and widen carries to width [wc] *)
Class split_mul_to_opt := split_mul_to : option (Z * Z).
Typeclasses Opaque split_mul_to_opt.
(** Split apart multi-return functions? *)
Class should_split_multiret_opt := should_split_multiret : bool.
Typeclasses Opaque should_split_multiret_opt.
(** If [None], don't split apart multi-return functions; if [Some (w, wc)], split apart multi-return functions to use wordsize [w] and widen carries to width [wc] *)
Class split_multiret_to_opt := split_multiret_to : option (Z * Z).
Typeclasses Opaque split_multiret_to_opt.
(** Widen carries to the machine wordsize? *)
Class widen_carry_opt := widen_carry : bool.
Typeclasses Opaque widen_carry_opt.
(** Widen uint8 / bytes types to machine wordsize? *)
Class widen_bytes_opt := widen_bytes : bool.
Typeclasses Opaque widen_bytes_opt.
Notation split_mul_to_of_should_split_mul machine_wordsize possible_bitwidths
  := (if should_split_mul return split_mul_to_opt
      then Some (machine_wordsize, fold_right Z.min machine_wordsize (filter (fun x => (1 <=? x)%Z) possible_bitwidths))
      else None) (only parsing).
Notation split_multiret_to_of_should_split_multiret machine_wordsize possible_bitwidths
  := (if should_split_multiret return split_multiret_to_opt
      then Some (machine_wordsize, fold_right Z.min machine_wordsize (filter (fun x => (1 <=? x)%Z) possible_bitwidths))
      else None) (only parsing).
(* We include [0], so that even after bounds relaxation, we can
   notice where the constant 0s are, and remove them. *)
Notation prefix_with_carry bitwidths :=
  ((if widen_carry then (0::bitwidths) else (0::1::bitwidths))%Z)
    (only parsing).
Notation prefix_with_carry_bytes bitwidths :=
  (prefix_with_carry (match bitwidths return _ with bw => if widen_bytes then bw else 8::bw end)%Z) (* master and 8.9 are incompatible about scoping of multiple occurrences of an argument *)
    (only parsing).

Module Pipeline.
  Import GeneralizeVar.
  Inductive ErrorMessage :=
  | Computed_bounds_are_not_tight_enough
      {t} (computed_bounds expected_bounds : ZRange.type.base.option.interp (type.final_codomain t))
      (syntax_tree : Expr t) (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
  | No_modular_inverse (descr : string) (v : Z) (m : Z)
  | Value_not_leZ (descr : string) (lhs rhs : Z)
  | Value_not_leQ (descr : string) (lhs rhs : Q)
  | Value_not_ltZ (descr : string) (lhs rhs : Z)
  | Value_not_lt_listZ (descr : string) (lhs rhs : list Z)
  | Value_not_le_listZ (descr : string) (lhs rhs : list Z)
  | Values_not_provably_distinctZ (descr : string) (lhs rhs : Z)
  | Values_not_provably_equalZ (descr : string) (lhs rhs : Z)
  | Values_not_provably_equal_listZ (descr : string) (lhs rhs : list Z)
  | Unsupported_casts_in_input {t} (e : Expr t) (ls : list { t : _ & @expr (fun _ => string) t })
  | Stringification_failed {t} (e : Expr t) (err : string)
  | Invalid_argument (msg : string).

  Notation ErrorT := (ErrorT ErrorMessage).

  Section show.
    Context {output_api : ToString.OutputLanguageAPI}.
    Local Open Scope string_scope.
    Global Instance show_low_level_rewriter_method_opt : Show low_level_rewriter_method_opt
      := fun _ v => match v with
                    | precomputed_decision_tree => "precomputed_decision_tree"
                    | unreduced_decision_tree => "unreduced_decision_tree"
                    | unreduced_naive => "unreduced_naive"
                    end.
    Fixpoint find_too_loose_base_bounds {t}
      : ZRange.type.base.option.interp t -> ZRange.type.base.option.interp t-> bool * list (nat * nat) * list (zrange * zrange)
      := match t return ZRange.type.base.option.interp t -> ZRange.type.option.interp t-> bool * list (nat * nat) * list (zrange * zrange) with
         | base.type.unit
           => fun 'tt 'tt => (false, nil, nil)
         | base.type.type_base base.type.nat
         | base.type.type_base base.type.bool
         | base.type.type_base base.type.zrange
           => fun _ _ => (false, nil, nil)
         | base.type.type_base base.type.Z
           => fun a b
              => match a, b with
                 | None, None => (false, nil, nil)
                 | Some _, None => (false, nil, nil)
                 | None, Some _ => (true, nil, nil)
                 | Some a, Some b
                   => if is_tighter_than_bool a b
                      then (false, nil, nil)
                      else (false, nil, ((a, b)::nil))
                 end
         | base.type.option A
           => fun a b
              => match a, b with
                 | None, None => (false, nil, nil)
                 | Some _, None => (false, nil, nil)
                 | None, Some _ => (true, nil, nil)
                 | Some None, Some None
                 | Some (Some _), Some None
                 | Some None, Some (Some _)
                   => (false, nil, nil)
                 | Some (Some a), Some (Some b)
                   => @find_too_loose_base_bounds A a b
                 end
         | base.type.prod A B
           => fun '(ra, rb) '(ra', rb')
              => let '(b1, lens1, ls1) := @find_too_loose_base_bounds A ra ra' in
                 let '(b2, lens2, ls2) := @find_too_loose_base_bounds B rb rb' in
                 (orb b1 b2, lens1 ++ lens2, ls1 ++ ls2)%list
         | base.type.list A
           => fun ls1 ls2
              => match ls1, ls2 with
                 | None, None
                 | Some _, None
                   => (false, nil, nil)
                 | None, Some _
                   => (true, nil, nil)
                 | Some ls1, Some ls2
                   => List.fold_right
                        (fun '(b, len, err) '(bs, lens, errs)
                         => (orb b bs, len ++ lens, err ++ errs)%list)
                        (false,
                         (if (List.length ls1 =? List.length ls2)%nat
                          then nil
                          else ((List.length ls1, List.length ls2)::nil)),
                         nil)
                        (List.map
                           (fun '(a, b) => @find_too_loose_base_bounds A a b)
                           (List.combine ls1 ls2))
                 end
         end.

    Definition find_too_loose_bounds {t}
      : ZRange.type.option.interp t -> ZRange.type.option.interp t-> bool * list (nat * nat) * list (zrange * zrange)
      := match t with
         | type.arrow s d => fun _ _ => (false, nil, nil)
         | type.base t => @find_too_loose_base_bounds t
         end.
    Definition explain_too_loose_bounds {t} (b1 b2 : ZRange.type.option.interp t)
      : string
      := let '(none_some, lens, bs) := find_too_loose_bounds b1 b2 in
         String.concat
           String.NewLine
           ((if none_some then "Found None where Some was expected"::nil else nil)
              ++ (List.map
                    (A:=nat*nat)
                    (fun '(l1, l2) => "Found a list of length " ++ show false l1 ++ " where a list of length " ++ show false l2 ++ " was expected.")
                    lens)
              ++ (List.map
                    (A:=zrange*zrange)
                    (fun '(b1, b2) => "The bounds " ++ show false b1 ++ " are looser than the expected bounds " ++ show false b2)
                    bs)).

    Global Instance show_lines_ErrorMessage : ShowLines ErrorMessage
      := fun parens e
         => maybe_wrap_parens_lines
              parens
              match e with
              | Computed_bounds_are_not_tight_enough t computed_bounds expected_bounds syntax_tree arg_bounds
                => ((["Computed bounds " ++ show true computed_bounds ++ " are not tight enough (expected bounds not looser than " ++ show true expected_bounds ++ ")."]%string)
                      ++ [explain_too_loose_bounds (t:=type.base _) computed_bounds expected_bounds]
                      ++ match ToString.ToFunctionLines
                                 (relax_zrange := fun r => r)
                                 false (* do extra bounds check *) false (* static *) "" "f" syntax_tree (fun _ _ => nil) None arg_bounds ZRange.type.base.option.None with
                         | inl (E_lines, types_used)
                           => ["When doing bounds analysis on the syntax tree:"]
                                ++ E_lines ++ [""]
                                ++ ["with input bounds " ++ show true arg_bounds ++ "." ++ String.NewLine]%string
                         | inr errs
                           => (["(Unprintible syntax tree used in bounds analysis)" ++ String.NewLine]%string)
                               ++ ["Stringification failed on the syntax tree:"] ++ show_lines false syntax_tree ++ [errs]
                         end)%list
              | No_modular_inverse descr v m
                => ["Could not compute a modular inverse (" ++ descr ++ ") for " ++ show false v ++ " mod " ++ show false m]
              | Value_not_leZ descr lhs rhs
                => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show false lhs ++ " ≤ " ++ show false rhs]
              | Value_not_leQ descr lhs rhs
                => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show false lhs ++ " ≤ " ++ show false rhs]
              | Value_not_ltZ descr lhs rhs
                => ["Value not < (" ++ descr ++ ") : expected " ++ show false lhs ++ " < " ++ show false rhs]
              | Value_not_lt_listZ descr lhs rhs
                => ["Value not < (" ++ descr ++ ") : expected " ++ show false lhs ++ " < " ++ show false rhs]
              | Value_not_le_listZ descr lhs rhs
                => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show false lhs ++ " ≤ " ++ show false rhs]
              | Values_not_provably_distinctZ descr lhs rhs
                => ["Values not provably distinct (" ++ descr ++ ") : expected " ++ show true lhs ++ " ≠ " ++ show true rhs]
              | Values_not_provably_equalZ descr lhs rhs
              | Values_not_provably_equal_listZ descr lhs rhs
                => ["Values not provably equal (" ++ descr ++ ") : expected " ++ show true lhs ++ " = " ++ show true rhs]
              | Unsupported_casts_in_input t e ls
                => ["Unsupported casts in input syntax tree:"]
                     ++ show_lines false e
                     ++ ["Unsupported casts: " ++ @show_list _ (fun p v => show p (projT2 v)) false ls]
              | Stringification_failed t e err => ["Stringification failed on the syntax tree:"] ++ show_lines false e ++ [err]
              | Invalid_argument msg
                => ["Invalid argument: " ++ msg]%string
              end.
    Local Instance show_ErrorMessage : Show ErrorMessage
      := fun parens err => String.concat String.NewLine (show_lines parens err).
  End show.

  Definition invert_result {T} (v : ErrorT T)
    := match v return match v with Success _ => T | _ => ErrorMessage end with
       | Success v => v
       | Error msg => msg
       end.

  Local Set Primitive Projections.
  Record to_fancy_args := { invert_low : Z (*log2wordmax*) -> Z -> option Z ; invert_high : Z (*log2wordmax*) -> Z -> option Z ; value_range : zrange ; flag_range : zrange }.

  Definition RewriteAndEliminateDeadAndInline {t}
             (DoRewrite : Expr t -> Expr t)
             (with_dead_code_elimination : bool)
             (with_subst01 : bool)
             (E : Expr t)
    : Expr t
    := let E := DoRewrite E in
       (* Note that DCE evaluates the expr with two different [var]
          arguments, and so results in a pipeline that is 2x slower
          unless we pass through a uniformly concrete [var] type
          first *)
       dlet_nd e := ToFlat E in
       let E := FromFlat e in
       let E := if with_subst01 then Subst01.Subst01 E
                else if with_dead_code_elimination then DeadCodeElimination.EliminateDead E
                     else E in
       let E := UnderLets.LetBindReturn (@ident.is_var_like) E in
       let E := DoRewrite E in (* after inlining, see if any new rewrite redexes are available *)
       dlet_nd e := ToFlat E in
       let E := FromFlat e in
       let E := if with_dead_code_elimination then DeadCodeElimination.EliminateDead E else E in
       E.

  Definition opts_of_method
             {low_level_rewriter_method : low_level_rewriter_method_opt}
    := {| use_decision_tree
          := match low_level_rewriter_method with
             | precomputed_decision_tree => true
             | unreduced_decision_tree => true
             | unreduced_naive => false
             end;
          use_precomputed_functions
          := match low_level_rewriter_method with
             | precomputed_decision_tree => true
             | unreduced_decision_tree => false
             | unreduced_naive => false
             end; |}.

  Definition BoundsPipeline
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {only_signed : only_signed_opt}
             {split_mul_to : split_mul_to_opt}
             {split_multiret_to : split_multiret_to_opt}
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             (relax_zrange := relax_zrange_gen only_signed possible_values)
             ((** convert adc/sbb which generates no carry to add/sub iff we're not fancy *)
               adc_no_carry_to_add := match translate_to_fancy with Some _ => false | None => true end)
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
  : ErrorT (Expr t)
    := (*let E := expr.Uncurry E in*)
      let opts := opts_of_method in
      let E := PartialEvaluateWithListInfoFromBounds E arg_bounds in
      let E := PartialEvaluate opts E in
      let E := RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArith 0 opts) with_dead_code_elimination with_subst01 E in
      let E := RewriteRules.RewriteArith (2^8) opts E in (* reassociate small consts *)
      let E := match translate_to_fancy with
               | Some {| invert_low := invert_low ; invert_high := invert_high |} => RewriteRules.RewriteToFancy invert_low invert_high opts E
               | None => E
               end in
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      (** We first do bounds analysis with no relaxation so that we
          can do rewriting with casts, and then once that's out of the
          way, we do bounds analysis again to relax the bounds. *)
      let E' := CheckedPartialEvaluateWithBounds (fun _ => None) false E arg_bounds out_bounds in
      let E'
          := match E' with
             | inl E
               => let E := RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArithWithCasts adc_no_carry_to_add opts) with_dead_code_elimination with_subst01 E in
                  dlet_nd e := ToFlat E in
                  let E := FromFlat e in
                  let E' := CheckedPartialEvaluateWithBounds relax_zrange true (* strip pre-existing casts *) E arg_bounds out_bounds in
                  E'
             | inr v => inr v
             end in
      match E' with
      | inl E
        => let E := match split_mul_to with
                    | Some (max_bitwidth, lgcarrymax)
                      => RewriteRules.RewriteMulSplit max_bitwidth lgcarrymax opts E
                    | None => E
                    end in
           let E := match split_multiret_to with
                    | Some (max_bitwidth, lgcarrymax)
                      => RewriteAndEliminateDeadAndInline (RewriteRules.RewriteMultiRetSplit max_bitwidth lgcarrymax opts) with_dead_code_elimination with_subst01 E
                    | None => E
                    end in
           let rewrote_E_so_should_rewrite_arith_again
               := match split_mul_to, split_multiret_to with
                  | Some _, _ | _, Some _ => true
                  | None, None => false
                  end in
           let E := if rewrote_E_so_should_rewrite_arith_again
                    then RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArithWithCasts adc_no_carry_to_add opts) with_dead_code_elimination with_subst01 E
                    else E in

           let E := match translate_to_fancy with
                    | Some {| invert_low := invert_low ; invert_high := invert_high ; value_range := value_range ; flag_range := flag_range |}
                      => RewriteRules.RewriteToFancyWithCasts invert_low invert_high value_range flag_range opts E
                    | None => E
                    end in
           let E := RewriteRules.RewriteStripLiteralCasts opts E in
           Success E
      | inr (inl (b, E))
        => Error (Computed_bounds_are_not_tight_enough b out_bounds E arg_bounds)
      | inr (inr unsupported_casts)
        => Error (Unsupported_casts_in_input E (@List.map { _ & forall var, _ } _ (fun '(existT t e) => existT _ t (e _)) unsupported_casts))
      end.

  Definition BoundsPipelineToStrings
             {output_language_api : ToString.OutputLanguageAPI}
             {static : static_opt}
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {only_signed : only_signed_opt}
             {split_mul_to : split_mul_to_opt}
             {split_multiret_to : split_multiret_to_opt}
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             (relax_zrangef : relax_zrange_opt
              := fun r => Option.value (relax_zrange_gen only_signed possible_values r) r)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
    : ErrorT (list string * ToString.ident_infos)
    := let E := BoundsPipeline
                  (*with_dead_code_elimination*)
                  with_subst01
                  translate_to_fancy
                  possible_values
                  E arg_bounds out_bounds in
       match E with
       | Success E' => let E := ToString.ToFunctionLines
                                  true static type_prefix name E' comment None arg_bounds out_bounds in
                      match E with
                      | inl E => Success E
                      | inr err => Error (Stringification_failed E' err)
                      end
       | Error err => Error err
       end.

  Definition BoundsPipelineToString
             {output_language_api : ToString.OutputLanguageAPI}
             {static : static_opt}
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {only_signed : only_signed_opt}
             {split_mul_to : split_mul_to_opt}
             {split_multiret_to : split_multiret_to_opt}
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
    : ErrorT (string * ToString.ident_infos)
    := let E := BoundsPipelineToStrings
                  type_prefix name
                  (*with_dead_code_elimination*)
                  with_subst01
                  translate_to_fancy
                  possible_values
                  E comment arg_bounds out_bounds in
       match E with
       | Success (E, types_used) => Success (ToString.LinesToString E, types_used)
       | Error err => Error err
       end.

  Local Notation arg_bounds_of_pipeline result
    := ((fun a b c d e f possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e f possible_values t E arg_bounds out_bounds = result') => arg_bounds) _ _ _ _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Local Notation out_bounds_of_pipeline result
    := ((fun a b c d e f possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e f possible_values t E arg_bounds out_bounds = result') => out_bounds) _ _ _ _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Local Notation possible_values_of_pipeline result
    := ((fun a b c d e f possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e f possible_values t E arg_bounds out_bounds = result') => possible_values) _ _ _ _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).

  Notation FromPipelineToString_gen is_internal prefix name result
    := (fun comment
        => ((prefix ++ name)%string,
            match result with
            | Success E'
              => let E := ToString.ToFunctionLines
                            (relax_zrange
                             := fun r => Option.value (relax_zrange_gen (_ : only_signed_opt) (possible_values_of_pipeline result) r) r)
                            true match is_internal return bool with
                                 | true => orb (_ : static_opt) (_ : internal_static_opt)
                                 | false => _ : static_opt
                                 end
                            prefix (prefix ++ name)%string
                            E'
                            (comment (prefix ++ name)%string)
                            None
                            (arg_bounds_of_pipeline result)
                            (out_bounds_of_pipeline result) in
                 match E with
                 | inl E => Success E
                 | inr err => Error (Pipeline.Stringification_failed E' err)
                 end
            | Error err => Error err
            end)).

  Notation FromPipelineToString prefix name result
    := (FromPipelineToString_gen false prefix name result).
  Notation FromPipelineToInternalString prefix name result
    := (FromPipelineToString_gen true prefix name result).

  Local Ltac wf_interp_t_step :=
    first [ progress destruct_head'_and
          | progress cbv [Classes.base Classes.ident Classes.ident_interp Classes.base_interp Classes.exprInfo] in *
          | progress rewrite_strat repeat topdown hints interp
          | solve [ typeclasses eauto with nocore interp_extra wf_extra ]
          | solve [ typeclasses eauto ]
          | break_innermost_match_step
          | solve [ typeclasses eauto 100 with nocore wf_extra ]
          | progress intros ].

  Local Ltac wf_interp_t := repeat wf_interp_t_step.

  Class bounds_goodT {t} bounds
    := bounds_good :
         Proper (type.and_for_each_lhs_of_arrow (t:=t) (@partial.abstract_domain_R base.type ZRange.type.base.option.interp (fun _ => eq)))
                bounds.

  Class type_goodT (t : type.type base.type)
    := type_good : type.andb_each_lhs_of_arrow type.is_base t = true.

  Hint Extern 1 (type_goodT _) => vm_compute; reflexivity : typeclass_instances.

  Lemma Wf_RewriteAndEliminateDeadAndInline {t} DoRewrite with_dead_code_elimination with_subst01
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Wf (@RewriteAndEliminateDeadAndInline t DoRewrite with_dead_code_elimination with_subst01 E).
  Proof. cbv [RewriteAndEliminateDeadAndInline Let_In]; wf_interp_t. Qed.

  Global Hint Resolve @Wf_RewriteAndEliminateDeadAndInline : wf wf_extra.
  Global Hint Opaque RewriteAndEliminateDeadAndInline : wf wf_extra.

  Lemma Interp_RewriteAndEliminateDeadAndInline {t} DoRewrite with_dead_code_elimination with_subst01
        (Interp_DoRewrite : forall E, Wf E -> Interp (DoRewrite E) == Interp E)
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Interp (@RewriteAndEliminateDeadAndInline t DoRewrite with_dead_code_elimination with_subst01 E)
      == Interp E.
  Proof.
    cbv [RewriteAndEliminateDeadAndInline Let_In];
      repeat (wf_interp_t || rewrite !Interp_DoRewrite).
  Qed.

  Hint Rewrite @Interp_RewriteAndEliminateDeadAndInline : interp interp_extra.

  Local Notation interp_correctT V1 V2 arg_bounds
    := (forall arg1 arg2
               (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
               (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
           type.app_curried V1 arg1 = type.app_curried V2 arg2)
         (only parsing).

  Local Lemma interp_correctT_trans {t} (arg_bounds : type.for_each_lhs_of_arrow _ t)
    : Transitive (fun x y => interp_correctT x y arg_bounds).
  Proof using Type.
    intros V1 V2 V3 H1 H2; intros arg1 arg2 Harg12 Harg1; etransitivity; [ eapply H1 | eapply H2 ]; clear H1 H2; try eassumption.
    { etransitivity; (idtac + symmetry); eassumption. }
    { rewrite <- Harg12; assumption. }
  Qed.

  Local Lemma correct_of_final_iff_correct_of_initial {t} {rv intermediate e : Expr t} {arg_bounds out_bounds}
        (Hintermediate : interp_correctT (Interp intermediate) (Interp e) arg_bounds)
        (Hwf : Wf e)
    : ((forall arg1 arg2
               (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
               (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
           ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp rv) arg1) = true
           /\ type.app_curried (Interp rv) arg1 = type.app_curried (Interp intermediate) arg2)
       /\ Wf rv)
      <-> ((forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
               ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp e) arg1) = true
               /\ type.app_curried (Interp rv) arg1 = type.app_curried (Interp e) arg2)
           /\ Wf rv).
  Proof using Type.
    split; intros [H1 H2]; (split; [ | exact H2 ]);
      repeat (let x := fresh in intro x; specialize (H1 x));
      destruct H1 as [H1' H2']; (split; [ rewrite <- H1', ?H2'; apply f_equal | ]);
        rewrite ?H2';
        try (erewrite ?Hintermediate; [ | (idtac + symmetry); eassumption | ]);
        try reflexivity.
    all: repeat match goal with
                | [ |- type.app_curried ?f ?x = type.app_curried ?f ?y ]
                  => apply type.app_curried_Proper; [ now apply expr.Wf_Interp_Proper | (idtac + symmetry); assumption ]
                | [ H' : ?R ?y ?x |- type.andb_bool_for_each_lhs_of_arrow _ _ ?x = true ]
                  => rewrite <- H'; assumption
                end.
  Qed.

  (** It would be nice if [eauto] were faster, cf
      COQBUG(https://github.com/coq/coq/issues/12052).  It doesn't
      share subterms, though, so we carefully build the proof term
      with forward reasoning *)
  Local Ltac fwd Hrv Hwf Hinterp :=
    cbv beta iota in Hrv;
    lazymatch type of Hrv with
    | Success ?x = Success ?y
      => let H' := fresh in
         assert (H : x = y) by (clear -Hrv; congruence);
         clear Hrv; rename H into Hrv
    | context G[(let x : ?T := ?v in @?F x) ?y]
      => let G' := context G[let x : T := v in F x y] in
         let G' := (eval cbv beta in G') in
         change G' in Hrv;
         fwd Hrv Hwf Hinterp
    | (let x := @inl ?A ?B ?v in ?F) = Success ?rv
      => let x' := fresh in
         change ((let x' := v in match @inl A B x' with x => F end) = Success rv) in Hrv;
         fwd Hrv Hwf Hinterp
    | (let x := @inr ?A ?B ?v in ?F) = Success ?rv
      => let x' := fresh in
         change ((let x' := v in match @inr A B x' with x => F end) = Success rv) in Hrv;
         fwd Hrv Hwf Hinterp
    | (let x := let y := ?v in ?F1 in @?F2 x) = ?rhs
      => change ((let y := v in let x := F1 in F2 x) = rhs) in Hrv;
         fwd Hrv Hwf Hinterp
    | (let x : Expr _ := ?v in ?F) = Success ?rv
      => let e' := fresh "e" in
         pose v as e';
         change (match e' with x => F end = Success rv) in Hrv;
         let e := lazymatch type of Hwf with Wf ?e => e | ?T => constr_fail_with ltac:(fun _ => fail 1 "Expected Wf, got" T) end in
         let Hwf' := fresh "Hwf" in
         let Hinterp' := fresh "Hinterp" in
         lazymatch type of Hinterp with
         | interp_correctT _ ?rhs ?arg_bounds
           => assert (Hwf' : Wf e');
              [ | assert (Hinterp' : interp_correctT (Interp e') rhs arg_bounds) ];
              [ clear Hrv; subst e' ..
              | lazymatch type of Hrv with
                | context[e] => idtac (* keep interp and wf *)
                | _ => clear Hwf Hinterp; try clear e
                end;
                fwd Hrv Hwf' Hinterp' ]
         | ?T => constr_fail_with ltac:(fun _ => fail 1 "Expected related, got" T)
         end
    | (let x : Expr _ + _ := ?v in ?F) = Success ?rv
      => let H := fresh in
         let e' := fresh "e" in
         destruct v as [e'|e'] eqn:H;
         cbv beta iota in Hrv;
         [ apply CheckedPartialEvaluateWithBounds_Correct in H;
           [ let Hwf' := fresh "Hwf" in
             rewrite (correct_of_final_iff_correct_of_initial Hinterp) in H by assumption;
             destruct H as [? Hwf']; split_and;
             lazymatch type of Hinterp with
             | interp_correctT _ ?rhs ?arg_bounds
               => let Hinterp' := fresh "Hinterp" in
                  assert (Hinterp' : interp_correctT (Interp e') rhs arg_bounds) by assumption;
                  fwd Hrv Hwf' Hinterp'
             end
           | clear H; try solve [ assumption | congruence | apply relax_zrange_gen_good ] .. ]
         | cbv beta iota zeta in Hrv;
           try (clear -Hrv; break_innermost_match_hyps; discriminate) ]
    | (let x : ?T := ?v in ?F) = Success ?rv
      => let rec good_ty T
             := lazymatch T with
                | bool => idtac
                | zrange => idtac
                | RewriterOptions => idtac
                | Flat.expr _ => idtac
                | ?A -> ?B => good_ty A; good_ty B
                | option ?A => good_ty A
                | (?A * ?B)%type => good_ty A; good_ty B
                | _ => fail 0 "Unrecognized type" T "in" v
                end in
         tryif good_ty T
         then (change (match v with x => F end = Success rv) in Hrv;
               fwd Hrv Hwf Hinterp)
         else (let T := type of Hrv in idtac T)
    | ?T => idtac T
    end.
  Local Ltac fwd_side_condition_step :=
    first [ assumption
          | progress intros
          | solve [ auto with nocore wf wf_extra ]
          | progress (rewrite_strat repeat topdown hints interp_extra)
          | match goal with
            | [ |- ?x = ?x ] => reflexivity
            | [ |- context[match ?x with Some _ => _ | _ => _ end] ] => destruct x
            | [ |- context[match ?x with (a, b) => _ end] ] => destruct x
            | [ |- type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds _ _)) _ = _ ]
              => erewrite Interp_PartialEvaluateWithListInfoFromBounds by eassumption
            end
          | progress cbv beta zeta in *
          | progress destruct_head'_and ].

  Lemma BoundsPipeline_correct
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {only_signed : only_signed_opt}
             {split_mul_to : split_mul_to_opt}
             {split_multiret_to : split_multiret_to_opt}
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             {t}
             (e : Expr t)
             arg_bounds
             out_bounds
             {type_good : type_goodT t}
             rv
             (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 translate_to_fancy possible_values e arg_bounds out_bounds = Success rv)
             (Hwf : Wf e)
             (Hfancy : match translate_to_fancy with
                       | Some {| invert_low := il ; invert_high := ih |}
                         => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
                           /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
                       | None => True
                       end)
    : (forall arg1 arg2
              (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
              (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
          ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp rv) arg1) = true
          /\ type.app_curried (Interp rv) arg1 = type.app_curried (Interp e) arg2)
      /\ Wf rv.
  Proof.
    assert (Hbounds_Proper : bounds_goodT arg_bounds) by (apply type.and_eqv_for_each_lhs_of_arrow_not_higher_order, type_good).
    assert (Hinterp : interp_correctT (Interp e) (Interp e) arg_bounds)
      by (intros; apply type.app_curried_Proper; [ now apply expr.Wf_Interp_Proper | assumption ]).
    (* talk about initial interp rather than final one *)
    rewrite (correct_of_final_iff_correct_of_initial Hinterp) by assumption.
    pose proof Hwf as Hwf'. (* keep an extra copy so it's not cleared *)
    cbv beta delta [BoundsPipeline Let_In] in Hrv.
    fwd Hrv Hwf Hinterp; [ repeat fwd_side_condition_step .. | subst ].
    solve [ eauto using conj with nocore ].
  Qed.

  Definition BoundsPipeline_correct_transT
             {t}
             arg_bounds
             out_bounds
             (InterpE : type.interp base.interp t)
             (rv : Expr t)
    := (forall arg1 arg2
               (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
               (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
           ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp rv) arg1) = true
           /\ type.app_curried (Interp rv) arg1 = type.app_curried InterpE arg2)
       /\ Wf rv.

  Lemma BoundsPipeline_correct_trans
        {low_level_rewriter_method : low_level_rewriter_method_opt}
        {only_signed : only_signed_opt}
        {split_mul_to : split_mul_to_opt}
        {split_multiret_to : split_multiret_to_opt}
        (with_dead_code_elimination : bool := true)
        (with_subst01 : bool)
        (translate_to_fancy : option to_fancy_args)
        (Hfancy : match translate_to_fancy with
                  | Some {| invert_low := il ; invert_high := ih |}
                    => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
                      /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
                  | None => True
                  end)
        (possible_values : list Z)
        {t}
        (e : Expr t)
        arg_bounds out_bounds
        {type_good : type_goodT t}
        (InterpE : type.interp base.interp t)
        (InterpE_correct_and_Wf
         : (forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
               type.app_curried (Interp e) arg1 = type.app_curried InterpE arg2)
           /\ Wf e)
        rv
        (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 translate_to_fancy possible_values e arg_bounds out_bounds = Success rv)
    : BoundsPipeline_correct_transT arg_bounds out_bounds InterpE rv.
  Proof.
    destruct InterpE_correct_and_Wf as [InterpE_correct Hwf].
    split; [ intros arg1 arg2 Harg12 Harg1; erewrite <- InterpE_correct | ]; try eapply @BoundsPipeline_correct;
      lazymatch goal with
      | [ |- type.andb_bool_for_each_lhs_of_arrow _ _ _ = true ] => eassumption
      | _ => try assumption
      end; try eassumption.
    etransitivity; try eassumption; symmetry; assumption.
  Qed.

  Ltac solve_bounds_good :=
    repeat first [ progress cbv [bounds_goodT Proper partial.abstract_domain_R type_base] in *
                 | progress cbn [type.and_for_each_lhs_of_arrow type.for_each_lhs_of_arrow partial.abstract_domain type.interp ZRange.type.base.option.interp type.related] in *
                 | exact I
                 | apply conj
                 | exact eq_refl ].

  Module Export Instances.
    (*Global Existing Instance default_low_level_rewriter_method.*)

    Global Instance bounds0_good {t : base.type} {bounds} : @bounds_goodT t bounds.
    Proof. solve_bounds_good. Qed.

    Global Instance bounds1_good {s d : base.type} {bounds} : @bounds_goodT (s -> d) bounds.
    Proof. solve_bounds_good. Qed.

    Global Instance bounds2_good {a b D : base.type} {bounds} : @bounds_goodT (a -> b -> D) bounds.
    Proof. solve_bounds_good. Qed.

    Global Instance bounds3_good {a b c D : base.type} {bounds} : @bounds_goodT (a -> b -> c -> D) bounds.
    Proof. solve_bounds_good. Qed.
  End Instances.
End Pipeline.

Module Export Hints.
  Export Pipeline.Instances.
  Hint Extern 1 (@Pipeline.bounds_goodT _ _) => solve [ Pipeline.solve_bounds_good ] : typeclass_instances.
  Global Strategy -100 [type.interp ZRange.type.option.interp ZRange.type.base.option.interp GallinaReify.Reify_as GallinaReify.reify type_base].
  Global Strategy -10 [type.app_curried type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow type.related type.interp Language.Compilers.base.interp base.base_interp type.andb_bool_for_each_lhs_of_arrow fst snd ZRange.type.option.is_bounded_by].
End Hints.

Module PipelineTactics.
  Export Hints.

  Ltac solve_side_conditions_of_BoundsPipeline_correct :=
    repeat first [ progress cbn [fst snd] in *
                 | match goal with
                   | [ |- ?x = ?x ] => reflexivity
                   | [ |- unit ] => constructor
                   | [ |- True ] => constructor
                   | [ |- context[andb _ _ = true] ] => rewrite Bool.andb_true_iff
                   | [ |- and _ _ ] => apply conj
                   | [ |- ?x = ?y ] => is_evar y; reflexivity
                   | [ |- ZRange.type.base.option.is_bounded_by _ _ = true ] => assumption
                   end ].

  Ltac do_unfolding :=
    cbv [type.interp ZRange.type.option.interp ZRange.type.base.option.interp GallinaReify.Reify_as GallinaReify.reify type_base] in *;
    cbn [type.app_curried type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow type.related type.interp Language.Compilers.base.interp base.base_interp type.andb_bool_for_each_lhs_of_arrow fst snd ZRange.type.option.is_bounded_by] in *.

  Ltac curry_args lem :=
    let T := type of lem in
    lazymatch (eval cbn [fst snd] in T) with
    | forall x : ?A * ?B, _
      => let a := fresh in
         let b := fresh in
         curry_args (fun (a : A) (b : B) => lem (a, b))
    | forall x : unit, _
      => curry_args (lem tt)
    | forall x : True, _
      => curry_args (lem I)
    | forall x : ?A /\ ?B, _
      => let a := fresh in
         let b := fresh in
         curry_args (fun (a : A) (b : B) => lem (conj a b))
    | forall x : ?A, _
      => constr:(fun x : A => ltac:(let v := curry_args (lem x) in exact v))
    | ?T
      => let T' := (eval cbn [fst snd] in T) in
         constr:(lem : T')
    end.

  Create HintDb relax_zrange_gen_good discriminated.
  Hint Resolve relax_zrange_gen_good : relax_zrange_gen_good.

  Ltac use_compilers_correctness Hres :=
    eapply Pipeline.BoundsPipeline_correct in Hres;
    [ | try typeclasses eauto with core relax_zrange_gen_good typeclass_instances.. ];
    [ do_unfolding;
      let Hres' := fresh in
      destruct Hres as [Hres' _] (* remove Wf conjunct *);
      let lem' := curry_args Hres' in
      pose proof lem' as Hres; clear Hres';
      let H1 := fresh in
      let H2 := fresh in
      edestruct Hres as [H1 H2]; revgoals;
      [ first [ ((* first try to be smart about which side of the lemma we use *)
                  lazymatch goal with
                  | [ |- _ = true ] => eapply H1
                  | [ |- _ = _ ] => erewrite H2
                  | [ |- ?list_Z_bounded_by _ _ ] => eapply H1
                  end)
                  (* but if that doesn't work, try both ways *)
              | eapply H1
              | erewrite H2 ];
        clear H1 H2 Hres
      | .. ];
      solve_side_conditions_of_BoundsPipeline_correct
    | match goal with
      | [ |- Wf _ ]
        => repeat apply expr.Wf_APP; try typeclasses eauto with nocore wf_extra wf_gen_cache; try typeclasses eauto with nocore wf wf_gen_cache
      end ].
End PipelineTactics.
