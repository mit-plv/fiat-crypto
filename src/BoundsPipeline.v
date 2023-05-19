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
Require Import Crypto.Util.ErrorT.Show.
Require Import Crypto.Util.DynList.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.AllInstances.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.DebugMonad.
Require Rewriter.Language.Language.
Require Crypto.Language.API.
Require Rewriter.Language.UnderLets.
Require Crypto.AbstractInterpretation.AbstractInterpretation.
Require Crypto.AbstractInterpretation.ZRange.
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
Require Crypto.Assembly.Parse.
Require Crypto.Assembly.Equivalence.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List. Import ListNotations. Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Primitive Projections.
Local Set Keyed Unification.

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
  AbstractInterpretation.ZRange
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
  AbstractInterpretation.ZRange.Compilers
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

(** Instantiate this class with typedefs for various bounds *)
Module typedef.
  Class typedef {t} (bounds : ZRange.type.base.option.interp t) := { name : string ; description : string -> string }.
  Global Arguments name {_ _ _}.
  Global Arguments description {_ _ _} _.
End typedef.
Notation typedef := typedef.typedef (only parsing).
Export ZRange.Settings.
(** Which of the rewriter methods do we use? *)
(** Note that we don't currently generate a precomputed naive method, because it eats too much RAM to do so. *)
Inductive low_level_rewriter_method_opt :=
  precomputed_decision_tree | unreduced_decision_tree | unreduced_naive.
Existing Class low_level_rewriter_method_opt.
(** We make this an instance later *)
Definition default_low_level_rewriter_method : low_level_rewriter_method_opt
  := precomputed_decision_tree.
(** What's the bitwidth? *)
Class machine_wordsize_opt := machine_wordsize : Z.
#[global]
Typeclasses Opaque machine_wordsize_opt.
(** Prefix function definitions with static/non-public? *)
Class static_opt := static : bool.
#[global]
Typeclasses Opaque static_opt.
(** Prefix internal/helper function definitions with inline? *)
Class inline_internal_opt := inline_internal : bool.
#[global]
Typeclasses Opaque inline_internal_opt.
(** Prefix all function definitions with inline? *)
Class inline_opt := inline : bool.
#[global]
Typeclasses Opaque inline_opt.
(** Prefix internal function definitions with static/non-public? *)
Class internal_static_opt := internal_static : bool.
#[global]
Typeclasses Opaque internal_static_opt.
(** Use the alternate cmovznz implementation using mul? *)
Class use_mul_for_cmovznz_opt := use_mul_for_cmovznz : bool.
#[global]
Typeclasses Opaque use_mul_for_cmovznz_opt.
(** Emit the primitive operations? *)
Class emit_primitives_opt := emit_primitives : bool.
#[global]
Typeclasses Opaque emit_primitives_opt.
(** Only allow signed integers in the output *)
Class only_signed_opt := only_signed : bool.
#[global]
Typeclasses Opaque only_signed_opt.
(** Rewrite zselect into expressions that don't require cmov? *)
Class no_select_opt := no_select : bool.
#[global]
Typeclasses Opaque no_select_opt.
(** If [None], don't rewrite zselects. If [Some w], rewrite zselects assuming w-bit words *)
Class no_select_size_opt := no_select_size : option Z.
#[global]
Typeclasses Opaque no_select_size_opt.
(** Split apart multiplications? *)
Class should_split_mul_opt := should_split_mul : bool.
#[global]
Typeclasses Opaque should_split_mul_opt.
(** If [None], don't split apart multiplications; if [Some (w, wc)], split apart multiplications to use wordsize [w] and widen carries to width [wc] *)
Class split_mul_to_opt := split_mul_to : option (Z * Z).
#[global]
Typeclasses Opaque split_mul_to_opt.
(** Split apart multi-return functions? *)
Class should_split_multiret_opt := should_split_multiret : bool.
#[global]
Typeclasses Opaque should_split_multiret_opt.
(** If [None], don't split apart multi-return functions; if [Some (w, wc)], split apart multi-return functions to use wordsize [w] and widen carries to width [wc] *)
Class split_multiret_to_opt := split_multiret_to : option (Z * Z).
#[global]
Typeclasses Opaque split_multiret_to_opt.
(** Widen carries to the machine wordsize? *)
Class widen_carry_opt := widen_carry : bool.
#[global]
Typeclasses Opaque widen_carry_opt.
(** Widen uint8 / bytes types to machine wordsize? *)
Class widen_bytes_opt := widen_bytes : bool.
#[global]
Typeclasses Opaque widen_bytes_opt.
(** Display rewriting pass information *)
Class debug_rewriting_opt := debug_rewriting : bool.
#[global]
 Typeclasses Opaque debug_rewriting_opt.
(** Display rewriting pass information on success *)
Class debug_rewriting_on_success_opt := debug_rewriting_on_success : bool.
#[global]
 Typeclasses Opaque debug_rewriting_on_success_opt.
(** Display rewriting pass information on failure *)
Class debug_rewriting_on_failure_opt := debug_rewriting_on_failure : bool.
#[global]
 Typeclasses Opaque debug_rewriting_on_failure_opt.
(** Fancy Output *)
Record to_fancy_args := { invert_low : Z (*log2wordmax*) -> Z -> option Z ; invert_high : Z (*log2wordmax*) -> Z -> option Z ; value_range : zrange ; flag_range : zrange }.
Class translate_to_fancy_opt := translate_to_fancy : option to_fancy_args.
#[global]
Typeclasses Opaque translate_to_fancy_opt.
Definition default_translate_to_fancy : translate_to_fancy_opt := None.
Class translate_to_fancy_opt_correct {translate_to_fancy : translate_to_fancy_opt}
  := translate_to_fancy_correct
    : match translate_to_fancy with
      | Some {| invert_low := il ; invert_high := ih |}
        => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
           /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
      | None => True
      end.
Global Arguments translate_to_fancy_opt_correct {_}, _.
#[global]
Typeclasses Opaque translate_to_fancy_opt_correct.
#[global]
Hint Mode translate_to_fancy_opt_correct + : typeclass_instances.
Global Instance default_translate_to_fancy_correct : translate_to_fancy_opt_correct default_translate_to_fancy := I.
(** Unfold value_barrier *)
Class unfold_value_barrier_opt := unfold_value_barrier : bool.
#[global]
Typeclasses Opaque unfold_value_barrier_opt.
(** Lines of assembly code (implicitly separated by \n) *)
Class assembly_hints_lines_opt := assembly_hints_lines : list (string (* file name *) * list string).
#[global]
Typeclasses Opaque assembly_hints_lines_opt.
(** Error if there are un-requested assembly functions *)
Class error_on_unused_assembly_functions_opt := error_on_unused_assembly_functions : bool.
#[global]
Typeclasses Opaque error_on_unused_assembly_functions_opt.
(** Ignore function-name mismatch errors when there's only one assembly function and only one actual function requested *)
Class ignore_unique_asm_names_opt := ignore_unique_asm_names : bool.
#[global]
Typeclasses Opaque ignore_unique_asm_names_opt.
Inductive synthesis_output_kind := normal_output | assembly_output.
Notation no_select_size_of_no_select machine_wordsize
  := (if no_select return no_select_size_opt
      then Some machine_wordsize
      else None) (only parsing).
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

Definition typedef_info_of_typedef {relax_zrange : relax_zrange_opt} {t bounds} (td : @typedef t bounds)
  : ToString.typedef_info
  := (typedef.name,
      typedef.description,
      ToString.int.option.interp.to_union (ToString.int.option.interp.of_zrange_relaxed (ZRange.type.base.option.map_ranges relax_zrange bounds)),
       existT _ t bounds).

#[global]
 Declare Scope pipelineM_scope.
#[global]
 Delimit Scope pipelineM_scope with pipelineM.
Module Pipeline.
  Import GeneralizeVar.

  Class BoundsPipelineOptions :=
    { AbstractInterpretation_opts : AbstractInterpretation.Options
    ; low_level_rewriter_method : low_level_rewriter_method_opt
    ; only_signed : only_signed_opt
    ; no_select_size : no_select_size_opt
    ; split_mul_to : split_mul_to_opt
    ; split_multiret_to : split_multiret_to_opt
    ; unfold_value_barrier : unfold_value_barrier_opt
    ; relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt
    ; translate_to_fancy : translate_to_fancy_opt
    ; debug_rewriting : debug_rewriting_opt
    ; with_dead_code_elimination : bool := true
    ; with_let_bind_return : bool := true
    (** convert adc/sbb which generates no carry to add/sub iff we're not fancy *)
    ; adc_no_carry_to_add := match translate_to_fancy with Some _ => false | None => true end
    }.
  Definition default_BoundsPipelineOptions : BoundsPipelineOptions :=
    {| AbstractInterpretation_opts := AbstractInterpretation.default_Options
    ; low_level_rewriter_method := default_low_level_rewriter_method
    ; only_signed := false
    ; no_select_size := None
    ; split_mul_to := None
    ; split_multiret_to := None
    ; unfold_value_barrier := true
    ; relax_adc_sbb_return_carry_to_bitwidth := []
    ; translate_to_fancy := default_translate_to_fancy
    ; debug_rewriting := false
    |}.

  Global Existing Instances
         Build_BoundsPipelineOptions
         AbstractInterpretation_opts
         low_level_rewriter_method
         only_signed
         no_select_size
         split_mul_to
         split_multiret_to
         unfold_value_barrier
         relax_adc_sbb_return_carry_to_bitwidth
         translate_to_fancy
         debug_rewriting
  .
  #[global]
   Hint Cut [
      ( _ * )
        (AbstractInterpretation_opts
        | low_level_rewriter_method
        | only_signed
        | no_select_size
        | split_mul_to
        | split_multiret_to
        | unfold_value_barrier
        | relax_adc_sbb_return_carry_to_bitwidth
        | translate_to_fancy
        | debug_rewriting
        ) ( _ * )
        (Build_BoundsPipelineOptions
        )
    ] : typeclass_instances.

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
  | Invalid_argument (msg : string)
  | Assembly_parsing_error (fname : string) (msg : Assembly.Parse.ParseValidatedError)
  | Assembly_without_any_global_labels (fnames : list string)
  | Unused_global_assembly_labels (fname_labels : list (string * list string)) (valid_requests : list string)
  | Equivalence_checking_failure_pre_asm
      {t} (e : Expr t) (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
      (msg : Assembly.Equivalence.EquivalenceCheckingError)
  | Equivalence_checking_failure
      {t} (e : Expr t) (asm_fname : string) (asm : Assembly.Syntax.Lines) (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
      (msg : Assembly.Equivalence.EquivalenceCheckingError)
  .

  Notation DebugM := (@DebugM string) (only parsing).
  Notation ErrorT := (ErrorT ErrorMessage).
  Notation M T := (DebugM (ErrorT T)).

  Module M.
    Definition bind {A B} (x : M A) (k : A -> M B) : M B
      := (x <- x;
          match x with
          | Success x => k x
          | Error err => Debug.ret (Error err)
          end)%debugM.
    Global Arguments bind {A B}%type_scope (x k)%pipelineM_scope.
    Notation sequence x y := (@bind unit _ x%pipelineM (fun 'tt => y%pipelineM)).
    Notation ret x := (@Debug.ret string _ (@Success ErrorMessage _ x)).
    Notation err msg := (@Debug.ret string _ (@Error ErrorMessage _ msg)).
    Notation debug msg := (Debug.sequence (Debug.debug msg) (ret tt)).
    Module Export Notations.
      Notation "x <- y ; f" := (bind y%pipelineM (fun x => f%pipelineM)) : pipelineM_scope.
      Notation "f ;; g" := (sequence f%pipelineM g%pipelineM) : pipelineM_scope.
    End Notations.
  End M.
  Export M.Notations.

  Record ExtendedSynthesisResult t :=
    { lines : list string
      ; ident_infos : ToString.ident_infos
      ; arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t
      ; out_bounds : ZRange.type.base.option.interp (type.final_codomain t)
      ; arg_typedefs : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_typedef_data t
      ; out_typedefs : ToString.OfPHOAS.base_var_typedef_data (type.final_codomain t)
      ; expr : Expr t
    }.

  Section show.
    Context {machine_wordsize : machine_wordsize_opt}
            {output_api : ToString.OutputLanguageAPI}.
    Local Open Scope string_scope.
    Global Instance show_low_level_rewriter_method_opt : Show low_level_rewriter_method_opt
      := fun v => match v with
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
         | base.type.type_base base.type.string
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
                    (fun '(l1, l2) => "Found a list of length " ++ show l1 ++ " where a list of length " ++ show l2 ++ " was expected.")
                    lens)
              ++ (List.map
                    (A:=zrange*zrange)
                    (fun '(b1, b2) => "The bounds " ++ show b1 ++ " are looser than the expected bounds " ++ show b2)
                    bs)).

    Definition show_lines_Expr {t} (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t) (include_input_bounds : bool)
      : ShowLines (Expr t)
      := fun syntax_tree
         => let _ := default_language_naming_conventions in
            let _ := default_documentation_options in
            let _ := default_output_options in
            let _ := AbstractInterpretation.default_Options in
            match ToString.ToFunctionLines
                    (relax_zrange := fun r => r)
                    machine_wordsize
                    false (* do extra bounds check *) false (* internal static *) false (* static *) false (* all static *) false (* inline *) "" "f" syntax_tree (fun _ _ => nil) None arg_bounds ZRange.type.base.option.None (type.forall_each_lhs_of_arrow (@ToString.OfPHOAS.var_typedef_data_None)) ToString.OfPHOAS.base_var_typedef_data_None with
            | inl (E_lines, types_used)
              => ["The syntax tree:"]
                   ++ show_lines syntax_tree
                   ++ [""; "which can be pretty-printed as:"]
                   ++ E_lines ++ [""]
                   ++ (if include_input_bounds then ["with input bounds " ++ show_lvl arg_bounds 0 ++ "." ++ String.NewLine]%string else [])
            | inr errs
              => (["(Unprintible syntax tree used in bounds analysis)" ++ String.NewLine]%string)
                   ++ ["Stringification failed on the syntax tree:"] ++ show_lines syntax_tree ++ [errs]
            end%list.

    Global Instance show_lines_ErrorMessage : ShowLines ErrorMessage
      := fun e
         => let _ := default_language_naming_conventions in
            let _ := default_documentation_options in
            match e with
            | Computed_bounds_are_not_tight_enough t computed_bounds expected_bounds syntax_tree arg_bounds
              => ((["Computed bounds " ++ show_lvl computed_bounds 0 ++ " are not tight enough (expected bounds not looser than " ++ show_lvl expected_bounds 0 ++ ")."]%string)
                    ++ [explain_too_loose_bounds (t:=type.base _) computed_bounds expected_bounds]
                    ++ show_lines_Expr arg_bounds true (* re-print the input bounds at the end; they're very relevant *) syntax_tree)%list
            | No_modular_inverse descr v m
              => ["Could not compute a modular inverse (" ++ descr ++ ") for " ++ show v ++ " mod " ++ show m]%string
            | Value_not_leZ descr lhs rhs
              => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show lhs ++ " ≤ " ++ show rhs]%string
            | Value_not_leQ descr lhs rhs
              => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show lhs ++ " ≤ " ++ show rhs]%string
            | Value_not_ltZ descr lhs rhs
              => ["Value not < (" ++ descr ++ ") : expected " ++ show lhs ++ " < " ++ show rhs]%string
            | Value_not_lt_listZ descr lhs rhs
              => ["Value not < (" ++ descr ++ ") : expected " ++ show lhs ++ " < " ++ show rhs]%string
            | Value_not_le_listZ descr lhs rhs
              => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show lhs ++ " ≤ " ++ show rhs]%string
            | Values_not_provably_distinctZ descr lhs rhs
              => ["Values not provably distinct (" ++ descr ++ ") : expected " ++ show lhs ++ " ≠ " ++ show rhs]%string
            | Values_not_provably_equalZ descr lhs rhs
            | Values_not_provably_equal_listZ descr lhs rhs
              => ["Values not provably equal (" ++ descr ++ ") : expected " ++ show lhs ++ " = " ++ show rhs]%string
            | Unsupported_casts_in_input t e ls
              => ["Unsupported casts in input syntax tree:"]
                   ++ show_lines e
                   ++ ["Unsupported casts: " ++ @show_list _ (fun v => show (projT2 v)) ls]%string
            | Stringification_failed t e err
              => ["Stringification failed on the syntax tree:"]
                   ++ (let _ : PHOAS.with_all_casts := true in show_lines e)
                   ++ ["Which with some casts elided is:"]
                   ++ (let _ : PHOAS.with_all_casts := false in show_lines e)
                   ++ [err]
            | Invalid_argument msg
              => ["Invalid argument: " ++ msg]%string
            | Assembly_parsing_error fname msgs
              => (["In assembly file " ++ fname ++ ":"]%string)
                   ++ show_lines msgs
            | Assembly_without_any_global_labels []
              => ["Internal error: Assembly_without_any_global_labels []"]
            | Assembly_without_any_global_labels fnames
              => ["There are no global labels in " ++ String.concat ", " fnames ++ "."]%string
            | Unused_global_assembly_labels fname_labels valid_requests
              => ["The following global functions are present in the hints file but do not correspond to any requested function: " ++ String.concat ", " (List.map (fun '(fname, labels) => String.concat ", " labels ++ " (in " ++ fname ++ ")") fname_labels) ++ " (expected one of: " ++ String.concat ", " valid_requests ++ ")"]%string
            | Equivalence_checking_failure_pre_asm _ e arg_bounds err
              => (["Error while preparing to check for equivalence of syntax tree and assembly:"]
                    ++ show_lines_Expr arg_bounds false (* don't re-print input bounds; they're not relevant *) e
                    ++ [""; "(no assembly)"]%string
                    ++ [""; "Equivalence checking error:"]
                    ++ show_lines err)
            | Equivalence_checking_failure _ e asm_fname asm arg_bounds err
              => (["Error while checking for equivalence of syntax tree and assembly:"]
                    ++ show_lines_Expr arg_bounds false (* don't re-print input bounds; they're not relevant *) e
                    ++ [""; "Assembly (in " ++ asm_fname ++ "):"]%string
                    ++ match Equivalence.symbolic_state_of_EquivalenceCheckingError err with
                       | Some s => Equivalence.show_lines_AnnotatedLines (asm, s)
                       | None => show_lines asm
                       end
                    ++ [""; "Equivalence checking error:"]
                    ++ show_lines err)
            end%list.
    Local Instance show_ErrorMessage : Show ErrorMessage
      := fun err => String.concat String.NewLine (show_lines err).
  End show.

  Definition debug_after_rewrite {debug_rewriting : debug_rewriting_opt} {t}
             (descr : string)
             (E : Expr t)
    : DebugM unit
    := if debug_rewriting
       then Debug.debug ((["After rewriting " ++ descr ++ ":"]%string)
                           ++ (let _ : PHOAS.with_all_casts := true in show_lines E))
       else Debug.ret tt.

  Definition wrap_debug_rewrite {debug_rewriting : debug_rewriting_opt} {t}
             (descr : string)
             (DoRewrite : Expr t -> Expr t)
             (E : Expr t)
    : DebugM (Expr t)
    := (let E := DoRewrite E in
        debug_after_rewrite descr E;;
        Debug.ret E).

  (* version where the rewriter is already wrapped with debug info *)
  Definition RewriteAndEliminateDeadAndInline_gen {debug_rewriting : debug_rewriting_opt} {t}
             (descr : string)
             (DoRewrite : Expr t -> DebugM (Expr t))
             (with_dead_code_elimination : bool)
             (with_subst01 : bool)
             (with_let_bind_return : bool)
             (E : Expr t)
    : DebugM (Expr t)
    := (E <- DoRewrite E;
        (* Note that DCE evaluates the expr with two different [var]
           arguments, and so results in a pipeline that is 2x slower
           unless we pass through a uniformly concrete [var] type
           first *)
        dlet_nd e := ToFlat E in
        let E := FromFlat e in
        E <- if with_subst01 return DebugM (Expr t)
             then wrap_debug_rewrite ("subst01 for " ++ descr) (Subst01.Subst01 ident.is_comment) E
             else if with_dead_code_elimination return DebugM (Expr t)
                  then wrap_debug_rewrite ("DCE for " ++ descr) (DeadCodeElimination.EliminateDead ident.is_comment) E
                  else Debug.ret E;
        E <- if with_let_bind_return
             then wrap_debug_rewrite ("LetBindReturn for " ++ descr) (UnderLets.LetBindReturn (@ident.is_var_like)) E
             else Debug.ret E;
        E <- DoRewrite E; (* after inlining, see if any new rewrite redexes are available *)
        dlet_nd e := ToFlat E in
        let E := FromFlat e in
        E <- if with_dead_code_elimination
             then wrap_debug_rewrite ("DCE after " ++ descr) (DeadCodeElimination.EliminateDead ident.is_comment) E
             else Debug.ret E;
        Debug.ret E)%debugM.

  Definition RewriteAndEliminateDeadAndInline {debug_rewriting : debug_rewriting_opt} {t}
             (descr : string)
             (DoRewrite : Expr t -> Expr t)
             (with_dead_code_elimination : bool)
             (with_subst01 : bool)
             (with_let_bind_return : bool)
             (E : Expr t)
    : DebugM (Expr t)
    := RewriteAndEliminateDeadAndInline_gen descr (wrap_debug_rewrite descr DoRewrite) with_dead_code_elimination with_subst01 with_let_bind_return E.

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

  Definition PreBoundsPipeline
             {opts : AbstractInterpretation.Options}
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {only_signed : only_signed_opt}
             {unfold_value_barrier : unfold_value_barrier_opt}
             {translate_to_fancy : translate_to_fancy_opt}
             {debug_rewriting : debug_rewriting_opt}
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (with_let_bind_return : bool)
             {t}
             (E : Expr t)
             (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
  : DebugM (Expr t)
    := ((*let E := expr.Uncurry E in*)
      let opts := opts_of_method in
      let E := PartialEvaluateWithListInfoFromBounds E arg_bounds in
      E <- wrap_debug_rewrite "PartialEvaluate" (PartialEvaluate opts) E;
      E <- if unfold_value_barrier
           then wrap_debug_rewrite "RewriteUnfoldValueBarrier" (RewriteRules.RewriteUnfoldValueBarrier opts) E
           else Debug.ret E;
      E <- RewriteAndEliminateDeadAndInline "RewriteArith_0" (RewriteRules.RewriteArith 0 opts) with_dead_code_elimination with_subst01 with_let_bind_return E;
      E <- wrap_debug_rewrite "RewriteArith_2⁸" (RewriteRules.RewriteArith (2^8) opts) E; (* reassociate small consts *)
      E <- match translate_to_fancy with
           | Some {| invert_low := invert_low ; invert_high := invert_high |}
             => wrap_debug_rewrite "RewriteToFancy" (RewriteRules.RewriteToFancy invert_low invert_high opts) E
           | None => Debug.ret E
           end;
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      Debug.ret E)%debugM.

  (** Useful for rewriting to a prettier form sometimes *)
  Definition RepeatRewriteAddAssocLeftAndFlattenThunkedRectsWithDebug
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {debug_rewriting : debug_rewriting_opt}
             (n : nat)
             {t}
             (E : DebugM (Expr t))
    : DebugM (Expr t)
    := (let opts := Pipeline.opts_of_method in
        E <- E;
        E <- wrap_debug_rewrite "RewriteFlattenThunkedRects" (RewriteRules.RewriteFlattenThunkedRects opts) E;
        E <- wrap_debug_rewrite ("repeat " ++ show n ++ " RewriteAddAssocLeft") (fun E => List.fold_right (fun f v => f v) E (List.repeat (RewriteRules.RewriteAddAssocLeft opts) n)) E;
        Debug.ret E)%debugM.

  Definition RepeatRewriteAddAssocLeftAndFlattenThunkedRects
             {low_level_rewriter_method : low_level_rewriter_method_opt}
             {debug_rewriting : debug_rewriting_opt}
             (n : nat)
             {t}
             (E : DebugM (Expr t))
    : Expr t
    := Debug.eval_result (RepeatRewriteAddAssocLeftAndFlattenThunkedRectsWithDebug n E).

  Definition BoundsPipelineWithDebug
             {opts : BoundsPipelineOptions}
             (with_subst01 : bool)
             (possible_values : list Z)
             (relax_zrange := relax_zrange_gen only_signed possible_values)
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
  : M (Expr t)
    := ((*let E := expr.Uncurry E in*)
      let assume_cast_truncates := false in
      let opts := opts_of_method in
      E <- PreBoundsPipeline (* with_dead_code_elimination *) with_subst01 with_let_bind_return E arg_bounds;
      (** We first do bounds analysis with no relaxation so that we
          can do rewriting with casts, and then once that's out of the
          way, we do bounds analysis again to relax the bounds. *)
      (** To get better error messages, we don't check bounds until
          after doing some extra rewriting *)
      let E' := CheckedPartialEvaluateWithBounds (fun _ => None) assume_cast_truncates (@ident.is_comment) false E arg_bounds ZRange.type.base.option.None in
      E' <- match E' with
            | inl E
              => (debug_after_rewrite "CheckedPartialEvaluateWithBounds" E;;
                  E <- RewriteAndEliminateDeadAndInline "RewriteArithWithCasts" (RewriteRules.RewriteArithWithCasts adc_no_carry_to_add opts) with_dead_code_elimination with_subst01 with_let_bind_return E;
                  dlet_nd e := ToFlat E in
                  let E := FromFlat e in
                  (** to give good error messages, we first look at
                      the version of the syntax tree annotated with
                      unrelaxed ranges *)
                  let E' := CheckedPartialEvaluateWithBounds (fun _ => None) assume_cast_truncates (@ident.is_comment) true (* strip pre-existing casts *) E arg_bounds out_bounds in
                  match E' with
                    | inl E
                      => debug_after_rewrite "CheckedPartialEvaluateWithBounds 2" E;;
                         dlet_nd e := ToFlat E in
                         let E := FromFlat e in
                         let E' := CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates (@ident.is_comment) true (* strip pre-existing casts *) E arg_bounds out_bounds in
                         match E' with
                         | inl E
                           => debug_after_rewrite "CheckedPartialEvaluateWithBounds 3" E;;
                              Debug.ret (inl E)
                         | inr E
                           => Debug.ret (inr E)
                         end
                    | inr v => Debug.ret (inr v)
                    end)
            | inr v => Debug.ret (inr v)
            end;
      match E' with
      | inl E
        => (E <- match split_mul_to with
                 | Some (max_bitwidth, lgcarrymax)
                   => wrap_debug_rewrite "RewriteMulSplit" (RewriteRules.RewriteMulSplit max_bitwidth lgcarrymax opts) E
                 | None => Debug.ret E
                 end;
            E <- match split_multiret_to with
                 | Some (max_bitwidth, lgcarrymax)
                   => RewriteAndEliminateDeadAndInline "RewriteMultiRetSplit" (RewriteRules.RewriteMultiRetSplit max_bitwidth lgcarrymax opts) with_dead_code_elimination with_subst01 with_let_bind_return E
                 | None => Debug.ret E
                 end;
            let rewrote_E_so_should_rewrite_arith_again
              := match split_mul_to, split_multiret_to with
                 | Some _, _ | _, Some _ => true
                 | None, None => false
                 end in
            E <- if rewrote_E_so_should_rewrite_arith_again
                 then RewriteAndEliminateDeadAndInline "RewriteArithWithCasts" (RewriteRules.RewriteArithWithCasts adc_no_carry_to_add opts) with_dead_code_elimination with_subst01 with_let_bind_return E
                 else Debug.ret E;
            E <- match relax_adc_sbb_return_carry_to_bitwidth with
                 | [] => Debug.ret E
                 | _ => wrap_debug_rewrite "RewriteRelaxBitwidthAdcSbb" (RewriteRules.RewriteRelaxBitwidthAdcSbb relax_adc_sbb_return_carry_to_bitwidth opts) E
                 end;

            E <- match translate_to_fancy with
                 | Some {| invert_low := invert_low ; invert_high := invert_high ; value_range := value_range ; flag_range := flag_range |}
                   => wrap_debug_rewrite "RewriteToFancyWithCasts" (RewriteRules.RewriteToFancyWithCasts invert_low invert_high value_range flag_range opts) E
                 | None => Debug.ret E
                 end;
            E <- match no_select_size with
                 | Some bitwidth
                   => wrap_debug_rewrite "RewriteNoSelect" (RewriteRules.RewriteNoSelect bitwidth opts) E
                 | None => Debug.ret E
                 end;
            E <- wrap_debug_rewrite "RewriteArithWithRelaxedCasts" (RewriteRules.RewriteArithWithRelaxedCasts opts) E;
            E <- wrap_debug_rewrite "RewriteStripLiteralCasts" (RewriteRules.RewriteStripLiteralCasts opts) E;
            M.ret E)
      | inr (inl (b, E))
        => M.err (Computed_bounds_are_not_tight_enough b out_bounds E arg_bounds)
      | inr (inr unsupported_casts)
        => M.err (Unsupported_casts_in_input E (@List.map { _ & forall var, _ } _ (fun '(existT t e) => existT _ t (e _)) unsupported_casts))
      end)%debugM.

  Definition BoundsPipeline
             {opts : BoundsPipelineOptions}
             (with_subst01 : bool)
             (possible_values : list Z)
             (relax_zrange := relax_zrange_gen only_signed possible_values)
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
    : ErrorT (Expr t)
    := Debug.eval_result (BoundsPipelineWithDebug with_subst01 possible_values E arg_bounds out_bounds).

  Definition BoundsPipelineToExtendedResult
             {opts : BoundsPipelineOptions}
             {output_language_api : ToString.OutputLanguageAPI}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             {internal_static : internal_static_opt}
             {static : static_opt}
             {all_static : static_opt}
             (type_prefix : string)
             (name : string)
             (with_subst01 : bool)
             (inline : bool)
             (possible_values : list Z)
             (relax_zrangef : relax_zrange_opt
              := fun r => Option.value (relax_zrange_gen only_signed possible_values r) r)
             (machine_wordsize : Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
             (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
             (arg_typedefs : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_typedef_data t)
             (out_typedefs : ToString.OfPHOAS.base_var_typedef_data (type.final_codomain t))
    : M (ExtendedSynthesisResult t)
    := (E' <- BoundsPipelineWithDebug
                with_subst01
                possible_values
                E arg_bounds out_bounds;
        let E := ToString.ToFunctionLines
                   machine_wordsize true (orb internal_static static) static all_static inline type_prefix name E' comment None arg_bounds out_bounds arg_typedefs out_typedefs in
        match E with
        | inl (lines, infos)
          => M.ret {| lines := lines; ident_infos := infos; arg_bounds := arg_bounds; out_bounds := out_bounds; arg_typedefs := arg_typedefs ; out_typedefs := out_typedefs ; expr := E' |}
        | inr err => M.err (Stringification_failed E' err)
        end)%pipelineM.

  Definition BoundsPipelineToStringsWithDebug
             {opts : BoundsPipelineOptions}
             {output_language_api : ToString.OutputLanguageAPI}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             {internal_static : internal_static_opt}
             {static : static_opt}
             {all_static : static_opt}
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (inline : bool)
             (possible_values : list Z)
             (relax_zrangef : relax_zrange_opt
              := fun r => Option.value (relax_zrange_gen only_signed possible_values r) r)
             (machine_wordsize : Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
             arg_typedefs
             out_typedefs
    : M (list string * ToString.ident_infos)
    := (v <- BoundsPipelineToExtendedResult
               (static:=static) (all_static:=all_static)
               type_prefix name
               with_subst01
               inline
               possible_values
               machine_wordsize
               E comment arg_bounds out_bounds arg_typedefs out_typedefs;
        M.ret (v.(lines), v.(ident_infos)))%pipelineM.

  Definition BoundsPipelineToStrings
             {opts : BoundsPipelineOptions}
             {output_language_api : ToString.OutputLanguageAPI}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             {internal_static : internal_static_opt}
             {static : static_opt}
             {all_static : static_opt}
             (type_prefix : string)
             (name : string)
             (with_subst01 : bool)
             (inline : bool)
             (possible_values : list Z)
             (relax_zrangef : relax_zrange_opt
              := fun r => Option.value (relax_zrange_gen only_signed possible_values r) r)
             (machine_wordsize : Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
             arg_typedefs
             out_typedefs
    : ErrorT (list string * ToString.ident_infos)
    := Debug.eval_result (BoundsPipelineToStringsWithDebug (static:=static) (all_static:=all_static) type_prefix name with_subst01 inline possible_values machine_wordsize E comment arg_bounds out_bounds arg_typedefs out_typedefs).

  Definition BoundsPipelineToStringWithDebug
             {opts : BoundsPipelineOptions}
             {output_language_api : ToString.OutputLanguageAPI}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             {internal_static : internal_static_opt}
             {static : static_opt}
             {all_static : static_opt}
             (type_prefix : string)
             (name : string)
             (with_subst01 : bool)
             (inline : bool)
             (possible_values : list Z)
             (machine_wordsize : Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
             arg_typedefs
             out_typedefs
    : M (string * ToString.ident_infos)
    := (E <- BoundsPipelineToStringsWithDebug
               (static:=static) (all_static:=all_static)
               type_prefix name
               with_subst01
               inline
               possible_values
               machine_wordsize
               E comment arg_bounds out_bounds arg_typedefs out_typedefs;
        let '(E, types_used) := E in
        M.ret (ToString.LinesToString E, types_used))%pipelineM.

  Definition BoundsPipelineToString
             {opts : BoundsPipelineOptions}
             {output_language_api : ToString.OutputLanguageAPI}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             {internal_static : internal_static_opt}
             {static : static_opt}
             {all_static : static_opt}
             (type_prefix : string)
             (name : string)
             (with_subst01 : bool)
             (inline : bool)
             (possible_values : list Z)
             (machine_wordsize : Z)
             {t}
             (E : Expr t)
             (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t -> ToString.OfPHOAS.var_data (type.final_codomain t) -> list string)
             arg_bounds
             out_bounds
             arg_typedefs
             out_typedefs
    : ErrorT (string * ToString.ident_infos)
    := Debug.eval_result (BoundsPipelineToStringWithDebug (static:=static) (all_static:=all_static) type_prefix name with_subst01 inline possible_values machine_wordsize E comment arg_bounds out_bounds arg_typedefs out_typedefs).

  Ltac typedef_var_data_of_bounds t bounds :=
    let t := (eval cbv [type.interp type.for_each_lhs_of_arrow ZRange.type.option.interp type.final_codomain] in t) in
    let do_prod a b
        := lazymatch (eval hnf in bounds) with
           | (?b1, ?b2) => let td1 := typedef_var_data_of_bounds a b1 in
                           let td2 := typedef_var_data_of_bounds b b2 in
                           uconstr:((td1, td2))
           | ?bounds => fail 1 "Unsupported" "non-literal-pair" "bounds" bounds "for" "type" t
           end in
    match constr:(Set) with
    | _ => let td := constr:(_ : @typedef t bounds) in
           constr:(Some (@typedef.name t bounds td))
    | _
      => lazymatch t with
         | ZRange.type.base.option.interp ?t => typedef_var_data_of_bounds t bounds
         | type.base ?t => typedef_var_data_of_bounds t bounds
         | type.arrow ?s ?d => fail 1 "Unsupported" "arrow" "in" "typedef_var_data_of_bounds" t
         | ?s -> ?d => fail 1 "Unsupported" "arrow" "in" "typedef_var_data_of_bounds" t
         | prod ?a ?b => do_prod a b
         | base.type.prod ?a ?b => do_prod a b
         | unit => constr:(tt)
         | base.type.unit => constr:(tt)
         | base.type.option _ => constr:(tt)
         | base.type.list _ => constr:(@None string)
         | base.type.type_base base.type.Z => constr:(@None string)
         | base.type.type_base _ => constr:(tt)
         | ?t => fail 1 "Unsupported" "type" "in" "typedef_var_data_of_bounds" t
         end
    end.

  Notation type_of_pipeline result
    := ((fun a b possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b possible_values t E arg_bounds out_bounds = result') => t) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Notation arg_bounds_of_pipeline result
    := ((fun a b possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b possible_values t E arg_bounds out_bounds = result') => arg_bounds) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Notation out_bounds_of_pipeline result
    := ((fun a b possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b possible_values t E arg_bounds out_bounds = result') => out_bounds) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Notation possible_values_of_pipeline result
    := ((fun a b possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b possible_values t E arg_bounds out_bounds = result') => possible_values) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Notation arg_typedefs_via_tc_of_pipeline result
    := (match type_of_pipeline result, arg_bounds_of_pipeline result return _ with
        | t, arg_bounds
          => ltac:(let t := (eval cbv in t) in
                   let arg_bounds := (eval cbv [arg_bounds] in arg_bounds) in
                   let v := typedef_var_data_of_bounds (type.for_each_lhs_of_arrow ZRange.type.option.interp t) arg_bounds in
                   let v := (eval cbv in v) in
                   exact v)
        end) (only parsing).
  Notation out_typedefs_via_tc_of_pipeline result
    := (match type_of_pipeline result, out_bounds_of_pipeline result return _ with
        | t, out_bounds
          => ltac:(let t := (eval cbv in t) in
                   let out_bounds := (eval cbv [out_bounds] in out_bounds) in
                   let v := typedef_var_data_of_bounds (ZRange.type.base.option.interp (type.final_codomain t)) out_bounds in
                   let v := (eval cbv in v) in
                   exact v)
        end) (only parsing).
  Notation extend_pipeline_with_debug_info result
    := ((fun a b possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b possible_values t E arg_bounds out_bounds = result') => @Pipeline.BoundsPipelineWithDebug a b possible_values t E arg_bounds out_bounds) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).

  Notation FromPipelineToString_gen machine_wordsize is_internal prefix name result
    := (fun comment
        => ((prefix ++ name)%string,
             Debug.bind
               (extend_pipeline_with_debug_info result)
               (fun E'
                => match E' with
                   | Success E'
                     => let static : static_opt := _ in
                        let internal_static : internal_static_opt := _ in
                        let internal_static := orb static internal_static in
                        let is_internal' := match is_internal return bool with
                                            | true => internal_static
                                            | false => static
                                            end in
                        let inline : inline_opt := _ in
                        let inline_internal : inline_internal_opt := _ in
                        let inline_internal := orb inline_internal inline in
                        let inline' := match is_internal return bool with
                                       | true => inline_internal
                                       | false => inline
                                       end in
                        let adjust_name := convert_to_naming_convention (if is_internal' then private_function_naming_convention else public_function_naming_convention) in
                        let arg_bounds := arg_bounds_of_pipeline result in
                        let out_bounds := out_bounds_of_pipeline result in
                        let arg_typedefs := arg_typedefs_via_tc_of_pipeline result in
                        let out_typedefs := out_typedefs_via_tc_of_pipeline result in
                        let E := ToString.ToFunctionLines
                                   (relax_zrange
                                    := fun r => Option.value (relax_zrange_gen (_ : only_signed_opt) (possible_values_of_pipeline result) r) r)
                                   machine_wordsize
                                   true internal_static is_internal' static inline'
                                   prefix (adjust_name (prefix ++ name)%string)
                                   E'
                                   (comment (adjust_name (prefix ++ name)%string))
                                   None
                                   arg_bounds
                                   out_bounds arg_typedefs out_typedefs in
                        match E with
                        | inl (lines, infos)
                          => Debug.ret (Success {| lines := lines; ident_infos := infos; arg_bounds := arg_bounds; out_bounds := out_bounds; arg_typedefs := arg_typedefs ; out_typedefs := out_typedefs ; expr := E' |})
                        | inr err => Debug.ret (Error (Pipeline.Stringification_failed E' err))
                        end
                   | Error err => Debug.ret (Error err)
                   end)))
         (only parsing).

  Notation FromPipelineToString machine_wordsize prefix name result
    := (FromPipelineToString_gen machine_wordsize false prefix name result) (only parsing).
  Notation FromPipelineToInternalString machine_wordsize prefix name result
    := (FromPipelineToString_gen machine_wordsize true prefix name result) (only parsing).

  Ltac get_all_typedefs _ :=
    let all_typedefs := all_instances_of_family (@typedef) in
    let res := DynList.map_homogenous ltac:(fun td => constr:(typedef_info_of_typedef td)) all_typedefs in
    (* typecheck as a list (to infer the right argument for nil), then strip the cast *)
    match constr:(res : list ToString.typedef_info) with ?res => res end.
  Notation all_typedefs := (ltac:(let v := get_all_typedefs () in exact v)) (only parsing).

  Local Ltac wf_interp_t_step :=
    first [ progress destruct_head'_and
          | progress cbv [Classes.base Classes.ident Classes.ident_interp Classes.base_interp Classes.exprInfo] in *
          | progress intros
          | progress rewrite_strat repeat topdown hints interp
          | solve [ typeclasses eauto with nocore interp_extra wf_extra ]
          | solve [ typeclasses eauto ]
          | break_innermost_match_step
          | solve [ typeclasses eauto 100 with nocore wf_extra ] ].

  Local Ltac wf_interp_t := repeat wf_interp_t_step.

  Class bounds_goodT {t} bounds
    := bounds_good :
         Proper (type.and_for_each_lhs_of_arrow (t:=t) (@partial.abstract_domain_R base.type ZRange.type.base.option.interp (fun _ => eq)))
                bounds.

  Class type_goodT (t : type.type base.type)
    := type_good : type.andb_each_lhs_of_arrow type.is_base t = true.

  #[global]
   Hint Extern 1 (type_goodT _) => vm_compute; reflexivity : typeclass_instances.

  Local Ltac handle_debug_step_t :=
    first [ progress cbv [Debug.bind Debug.ret wrap_debug_rewrite Debug.sequence fst snd] in *
          | progress cbn [Debug.eval_result fst snd] in *
          | match goal with
            | [ H : ?x = (?y, tt) :> DebugM unit |- _ ]
              => clear H y
            | [ H : ?x = (?y, ?z) :> DebugM _ |- _ ]
              => assert (Debug.eval_result x = z) by (now rewrite H);
                 clear H; subst z; clear y
            end ].
  Local Ltac handle_debug_t := repeat handle_debug_step_t.

  Lemma Wf_wrap_debug_rewrite {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Wf (Debug.eval_result (@wrap_debug_rewrite debug_rewriting t descr DoRewrite E)).
  Proof. cbv [wrap_debug_rewrite Let_In] in *; repeat (wf_interp_t; handle_debug_t). Qed.

  Global Hint Resolve @Wf_wrap_debug_rewrite : wf wf_extra.
  Global Hint Opaque wrap_debug_rewrite : wf wf_extra.

  Lemma Interp_wrap_debug_rewrite {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite
        (Interp_DoRewrite : forall E, Wf E -> Interp (DoRewrite E) == Interp E)
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Interp (Debug.eval_result (@wrap_debug_rewrite debug_rewriting t descr DoRewrite E))
      == Interp E.
  Proof.
    cbv [wrap_debug_rewrite Let_In];
      repeat (wf_interp_t || rewrite !Interp_DoRewrite || handle_debug_t).
  Qed.

  #[global]
   Hint Rewrite @Interp_wrap_debug_rewrite : interp interp_extra.

  Lemma Wf_RewriteAndEliminateDeadAndInline_gen {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return
        (Wf_DoRewrite : forall E, Wf E -> Wf (Debug.eval_result (DoRewrite E)))
        E
        (Hwf : Wf E)
    : Wf (Debug.eval_result (@RewriteAndEliminateDeadAndInline_gen debug_rewriting t descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return E)).
  Proof. cbv [RewriteAndEliminateDeadAndInline_gen Let_In] in *; repeat (wf_interp_t; handle_debug_t). Qed.

  Global Hint Resolve @Wf_RewriteAndEliminateDeadAndInline_gen : wf wf_extra.
  Global Hint Opaque RewriteAndEliminateDeadAndInline_gen : wf wf_extra.

  Lemma Interp_RewriteAndEliminateDeadAndInline_gen {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return
        (Interp_DoRewrite : forall E, Wf E -> Interp (Debug.eval_result (DoRewrite E)) == Interp E)
        (Wf_DoRewrite : forall E, Wf E -> Wf (Debug.eval_result (DoRewrite E)))
        E
        (Hwf : Wf E)
    : Interp (Debug.eval_result (@RewriteAndEliminateDeadAndInline_gen debug_rewriting t descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return E))
      == Interp E.
  Proof.
    cbv [RewriteAndEliminateDeadAndInline_gen Let_In];
      repeat (wf_interp_t || rewrite !Interp_DoRewrite || handle_debug_t).
  Qed.

  #[global]
   Hint Rewrite @Interp_RewriteAndEliminateDeadAndInline_gen : interp interp_extra.

  Lemma Wf_RewriteAndEliminateDeadAndInline {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Wf (Debug.eval_result (@RewriteAndEliminateDeadAndInline debug_rewriting t descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return E)).
  Proof. cbv [RewriteAndEliminateDeadAndInline Let_In]; wf_interp_t. Qed.

  Global Hint Resolve @Wf_RewriteAndEliminateDeadAndInline : wf wf_extra.
  Global Hint Opaque RewriteAndEliminateDeadAndInline : wf wf_extra.

  Lemma Interp_RewriteAndEliminateDeadAndInline {debug_rewriting : debug_rewriting_opt} {t} descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return
        (Interp_DoRewrite : forall E, Wf E -> Interp (DoRewrite E) == Interp E)
        (Wf_DoRewrite : forall E, Wf E -> Wf (DoRewrite E))
        E
        (Hwf : Wf E)
    : Interp (Debug.eval_result (@RewriteAndEliminateDeadAndInline debug_rewriting t descr DoRewrite with_dead_code_elimination with_subst01 with_let_bind_return E))
      == Interp E.
  Proof.
    cbv [RewriteAndEliminateDeadAndInline Let_In];
      repeat (wf_interp_t || rewrite !Interp_DoRewrite).
  Qed.

  #[global]
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
    cbv beta iota delta [Debug.sequence] in Hrv;
    (*let t := type of Hrv in idtac t;*)
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
    | context G[Debug.eval_result (let x := ?y in @?F x)]
      => let G' := context G[let x := y in Debug.eval_result (F x)] in
         let G' := (eval cbv beta in G') in
         change G' in Hrv;
         fwd Hrv Hwf Hinterp
    | context G[Debug.eval_result (Debug.ret ?v)]
      => let G' := context G[v] in
         change G' in Hrv;
         fwd Hrv Hwf Hinterp
    | Debug.eval_result (@Debug.bind ?dbg ?A ?B ?x ?y) = _
      => rewrite (@Debug.eval_result_bind dbg A B x y) in Hrv;
         fwd Hrv Hwf Hinterp
    | (let z := Debug.eval_result (@Debug.bind ?dbg ?A ?B ?x ?y) in _) = _
      => rewrite (@Debug.eval_result_bind dbg A B x y) in Hrv;
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
      => (tryif is_var v
           then (change (match v with x => F end = Success rv) in Hrv;
                 fwd Hrv Hwf Hinterp)
           else
             (let e' := fresh "e" in
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
              end))
    | (let x : Expr _ + _ := ?v in ?F) = Success ?rv
      => (tryif is_var v
           then (change (match v with x => F end = Success rv) in Hrv;
                 fwd Hrv Hwf Hinterp)
           else
             (let H := fresh in
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
                first [ clear -Hrv;
                        repeat (rewrite ?Debug.eval_result_bind in Hrv; cbv [Debug.ret] in Hrv; cbn [fst snd Debug.eval_result] in Hrv);
                        break_innermost_match_hyps;
                        discriminate
                      | let T := type of Hrv in
                        idtac "WARNING: Could not discriminate on" T ] ]))
    | (let x : unit := ?v in ?F) = Success ?rv
      => (tryif unify v tt then idtac else destruct v);
         change (match tt with x => F end = Success rv) in Hrv;
         fwd Hrv Hwf Hinterp
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
    first [ match goal with
            | [ |- Wf (Debug.eval_result (RewriteAndEliminateDeadAndInline _ _ _ _ _ _))]
              => apply Wf_RewriteAndEliminateDeadAndInline
            | [ |- type.app_curried (expr.Interp _ (Debug.eval_result (RewriteAndEliminateDeadAndInline _ _ _ _ _ _))) _ = _ ]
              => rewrite Interp_RewriteAndEliminateDeadAndInline
            end
          | assumption
          | progress intros
          | solve [ auto with nocore wf wf_extra ]
          | progress (rewrite_strat repeat topdown hints interp_extra)
          | match goal with
            | [ |- ?x = ?x ] => reflexivity
            | [ |- context[match ?x with Some _ => _ | _ => _ end] ] => destruct x
            | [ |- context[match ?x with (a, b) => _ end] ] => destruct x
            | [ |- context[match ?x with [] => _ | _ => _ end] ] => destruct x
            | [ |- context[match ?x with true => _ | _ => _ end] ] => destruct x
            | [ |- type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds _ _)) _ = _ ]
              => erewrite Interp_PartialEvaluateWithListInfoFromBounds by eassumption
            end
          | progress cbv beta zeta in *
          | progress destruct_head'_and ].

  Local Strategy -100 [Debug.eval_result Debug.bind Debug.sequence fst snd Debug.map Debug.ret].
  Lemma BoundsPipeline_correct
             {opts : BoundsPipelineOptions}
             {translate_to_fancy_correct : translate_to_fancy_opt_correct}
             (with_subst01 : bool)
             (possible_values : list Z)
             {t}
             (e : Expr t)
             arg_bounds
             out_bounds
             {type_good : type_goodT t}
             rv
             (Hrv : BoundsPipeline with_subst01 possible_values e arg_bounds out_bounds = Success rv)
             (Hwf : Wf e)
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
    cbv [translate_to_fancy_opt_correct] in *.
    cbv beta iota delta [BoundsPipeline BoundsPipelineWithDebug PreBoundsPipeline Let_In] in Hrv.
    cbv beta iota delta [Debug.sequence] in Hrv.
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
        {opts : BoundsPipelineOptions}
        {translate_to_fancy_correct : translate_to_fancy_opt_correct}
        (with_subst01 : bool)
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
        (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 possible_values e arg_bounds out_bounds = Success rv)
    : BoundsPipeline_correct_transT arg_bounds out_bounds InterpE rv.
  Proof.
    destruct InterpE_correct_and_Wf as [InterpE_correct Hwf].
    split; [ intros arg1 arg2 Harg12 Harg1; erewrite <- InterpE_correct | ]; try eapply @BoundsPipeline_correct;
      lazymatch goal with
      | [ |- type.andb_bool_for_each_lhs_of_arrow _ _ _ = true ] => eassumption
      | [ |- _ = Success _ ] => eassumption
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
Export Pipeline.M.Notations.

Module Export Hints.
  (* for storing the results of prove_pipeline_wf *)
  Create HintDb wf_op_cache discriminated.

  Export Pipeline.Instances.
#[global]
  Hint Extern 1 (@Pipeline.bounds_goodT _ _) => solve [ Pipeline.solve_bounds_good ] : typeclass_instances.
  Global Strategy -100 [type.interp ZRange.type.option.interp ZRange.type.base.option.interp GallinaReify.Reify_as GallinaReify.reify type_base].
  Global Strategy -10 [type.app_curried type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow type.related type.interp Language.Compilers.base.interp base.base_interp type.andb_bool_for_each_lhs_of_arrow fst snd ZRange.type.option.is_bounded_by].
  Global Strategy 1000 [Pipeline.BoundsPipeline].
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
#[global]
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
              | erewrite H2
              | print_context_and_goal ();
                let G := match goal with |- ?G => G end in
                fail 1 "Could not figure out how to prove" G ];
        clear H1 H2 Hres
      | .. ];
      solve_side_conditions_of_BoundsPipeline_correct
    | lazymatch goal with |- Wf _ => idtac end;
      repeat match goal with
             | [ |- Wf (expr.APP _ _) ] => apply expr.Wf_APP
             end;
      try typeclasses eauto with nocore wf_extra wf_gen_cache;
      try typeclasses eauto with nocore wf wf_gen_cache ].

  Ltac prove_pipeline_wf _ :=
    lazymatch goal with
    | [ Hres : _ = Success _ |- Wf _ ]
      => eapply Pipeline.BoundsPipeline_correct
    end;
    repeat first [ match goal with
                   | [ Hres : _ = Success ?res |- _ = Success ?res ] => refine Hres (* eassumption is too slow *)
                   | [ |- Wf (expr.APP _ _) ] => apply expr.Wf_APP
                   | [ |- Wf (GallinaReify.Reify_as _ _) ] => apply expr.Wf_Reify_as
                   end
                 | exact I
                 | exact _
                 | solve [ auto with wf_gen_cache ] ].
End PipelineTactics.
