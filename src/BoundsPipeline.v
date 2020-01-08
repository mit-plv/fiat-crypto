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
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
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

Export Stringification.Language.Compilers.Options.

Import Compilers.API.

Definition round_up_bitwidth_gen (possible_values : list Z) (bitwidth : Z) : option Z
  := List.fold_right
       (fun allowed cur
        => if bitwidth <=? allowed
           then Some allowed
           else cur)
       None
       possible_values.

Lemma round_up_bitwidth_gen_le possible_values bitwidth v
  : round_up_bitwidth_gen possible_values bitwidth = Some v
    -> bitwidth <= v.
Proof.
  cbv [round_up_bitwidth_gen].
  induction possible_values as [|x xs IHxs]; cbn; intros; inversion_option.
  break_innermost_match_hyps; Z.ltb_to_lt; inversion_option; subst; trivial.
  specialize_by_assumption; omega.
Qed.

Definition relax_zrange_gen (possible_values : list Z) : zrange -> option zrange
  := (fun '(r[ l ~> u ])
      => if (0 <=? l)%Z
         then option_map (fun u => r[0~>2^u-1])
                         (round_up_bitwidth_gen possible_values (Z.log2_up (u+1)))
        else None)%zrange.

Lemma relax_zrange_gen_good
      (possible_values : list Z)
  : forall r r' z : zrange,
    (z <=? r)%zrange = true -> relax_zrange_gen possible_values r = Some r' -> (z <=? r')%zrange = true.
Proof.
  cbv [is_tighter_than_bool relax_zrange_gen]; intros *.
  pose proof (Z.log2_up_nonneg (upper r + 1)).
  rewrite !Bool.andb_true_iff; destruct_head' zrange; cbn [ZRange.lower ZRange.upper] in *.
  cbv [List.fold_right option_map].
  break_innermost_match; intros; destruct_head'_and;
    try match goal with
        | [ H : _ |- _ ] => apply round_up_bitwidth_gen_le in H
        end;
    inversion_option; inversion_zrange;
      subst;
      repeat apply conj;
      Z.ltb_to_lt; try omega;
        try (rewrite <- Z.log2_up_le_pow2_full in *; omega).
Qed.

(** Prefix function definitions with static/non-public? *)
Class static_opt := static : bool.
Typeclasses Opaque static_opt.
(** Use the alternate cmovznz implementation using mul? *)
Class use_mul_for_cmovznz_opt := use_mul_for_cmovznz : bool.
Typeclasses Opaque use_mul_for_cmovznz_opt.
(** Emit the primitive operations? *)
Class emit_primitives_opt := emit_primitives : bool.
Typeclasses Opaque emit_primitives_opt.
(** Split apart multiplications? *)
Class should_split_mul_opt := should_split_mul : bool.
Typeclasses Opaque should_split_mul_opt.
(** If [None], don't split apart multiplications; if [Some (w, wc)], split apart multiplications to use wordsize [w] and widen carries to width [wc] *)
Class split_mul_to_opt := split_mul_to : option (Z * Z).
Typeclasses Opaque split_mul_to_opt.
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
                => ["Invalid argument:" ++ msg]%string
              end.
    Local Instance show_ErrorMessage : Show ErrorMessage
      := fun parens err => String.concat String.NewLine (show_lines parens err).
  End show.

  Definition invert_result {T} (v : ErrorT T)
    := match v return match v with Success _ => T | _ => ErrorMessage end with
       | Success v => v
       | Error msg => msg
       end.

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

  Definition BoundsPipeline
             {split_mul_to : split_mul_to_opt}
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             (relax_zrange := relax_zrange_gen possible_values)
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
  : ErrorT (Expr t)
    := (*let E := expr.Uncurry E in*)
      let E := PartialEvaluateWithListInfoFromBounds E arg_bounds in
      let E := PartialEvaluate E in
      let E := RewriteAndEliminateDeadAndInline (RewriteRules.RewriteArith 0) with_dead_code_elimination with_subst01 E in
      let E := RewriteRules.RewriteArith (2^8) E in (* reassociate small consts *)
      let E := match translate_to_fancy with
               | Some {| invert_low := invert_low ; invert_high := invert_high |} => RewriteRules.RewriteToFancy invert_low invert_high E
               | None => E
               end in
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      let E' := CheckedPartialEvaluateWithBounds relax_zrange E arg_bounds out_bounds in
      match E' with
      | inl E
        => let E := RewriteAndEliminateDeadAndInline RewriteRules.RewriteArithWithCasts with_dead_code_elimination with_subst01 E in
           let E := match split_mul_to with
                    | Some (max_bitwidth, lgcarrymax)
                      => RewriteRules.RewriteMulSplit max_bitwidth lgcarrymax E
                    | None => E
                    end in
           let E := match translate_to_fancy with
                    | Some {| invert_low := invert_low ; invert_high := invert_high ; value_range := value_range ; flag_range := flag_range |}
                      => RewriteRules.RewriteToFancyWithCasts invert_low invert_high value_range flag_range E
                    | None => E
                    end in
           let E := RewriteRules.RewriteStripLiteralCasts E in
           Success E
      | inr (inl (b, E))
        => Error (Computed_bounds_are_not_tight_enough b out_bounds E arg_bounds)
      | inr (inr unsupported_casts)
        => Error (Unsupported_casts_in_input E (@List.map { _ & forall var, _ } _ (fun '(existT t e) => existT _ t (e _)) unsupported_casts))
      end.

  Definition BoundsPipelineToStrings
             {output_language_api : ToString.OutputLanguageAPI}
             {static : static_opt}
             {split_mul_to : split_mul_to_opt}
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             (possible_values : list Z)
             (relax_zrangef : relax_zrange_opt
              := fun r => Option.value (relax_zrange_gen possible_values r) r)
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
             {split_mul_to : split_mul_to_opt}
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
    := ((fun a b c possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c possible_values t E arg_bounds out_bounds = result') => arg_bounds) _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Local Notation out_bounds_of_pipeline result
    := ((fun a b c possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c possible_values t E arg_bounds out_bounds = result') => out_bounds) _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Local Notation possible_values_of_pipeline result
    := ((fun a b c possible_values t E arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c possible_values t E arg_bounds out_bounds = result') => possible_values) _ _ _ _ _ _ _ _ result eq_refl)
         (only parsing).

  Notation FromPipelineToString prefix name result
    := (fun comment
        => ((prefix ++ name)%string,
            match result with
            | Success E'
              => let E := ToString.ToFunctionLines
                            (relax_zrange
                             := fun r => Option.value (relax_zrange_gen (possible_values_of_pipeline result) r) r)
                            true (_ : static_opt) prefix (prefix ++ name)%string
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

  Local Ltac wf_interp_t :=
    repeat first [ progress destruct_head'_and
                 | progress cbv [Classes.base Classes.ident Classes.ident_interp Classes.base_interp Classes.exprInfo] in *
                 | progress autorewrite with interp
                 | solve [ eauto with nocore interp_extra wf_extra ]
                 | solve [ typeclasses eauto ]
                 | break_innermost_match_step
                 | solve [ eauto 100 with nocore wf_extra ]
                 | progress intros ].

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

  Local Opaque RewriteAndEliminateDeadAndInline.
  Local Opaque RewriteRules.RewriteStripLiteralCasts.
  Local Opaque RewriteRules.RewriteToFancyWithCasts.
  Local Opaque RewriteRules.RewriteToFancy.
  Local Opaque RewriteRules.RewriteArith.
  Local Opaque RewriteRules.RewriteMulSplit.
  Local Opaque CheckedPartialEvaluateWithBounds.
  Local Opaque FromFlat ToFlat.
  Lemma BoundsPipeline_correct
             {split_mul_to : split_mul_to_opt}
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
    cbv [BoundsPipeline Let_In bounds_goodT] in *;
      repeat match goal with
             | [ H : match ?x with _ => _ end = Success _ |- _ ]
               => destruct x eqn:?; cbv beta iota in H; [ | break_innermost_match_hyps; congruence ];
                    let H' := fresh in
                    inversion H as [H']; clear H; rename H' into H
             end.
    { intros;
        match goal with
        | [ H : _ = _ |- _ ]
          => let H' := fresh in
             pose proof H as H';
               eapply CheckedPartialEvaluateWithBounds_Correct in H';
               [ destruct H' as [H01 Hwf'] | .. ]
        end;
        [
        | lazymatch goal with
          | [ |- Wf _ ] => idtac
          | _ => eassumption || reflexivity || apply relax_zrange_gen_good
          end.. ].
      { subst; split; [ | solve [ wf_interp_t ] ].
        split_and; simpl in *.
        split; [ solve [ wf_interp_t; eauto with nocore ] | ].
        intros; break_innermost_match; autorewrite with interp_extra; try solve [ wf_interp_t ].
        all: match goal with H : context[type.app_curried _ _ = _] |- _ => erewrite H; clear H end; eauto.
        all: transitivity (type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds e arg_bounds)) arg1);
          [ | apply Interp_PartialEvaluateWithListInfoFromBounds; auto ].
        all: apply type.app_curried_Proper; [ | symmetry; eassumption ].
        all: clear dependent arg1; clear dependent arg2; clear dependent out_bounds.
        all: wf_interp_t. }
      { wf_interp_t. } }
  Qed.
  Local Transparent RewriteAndEliminateDeadAndInline.
  Local Transparent RewriteRules.RewriteStripLiteralCasts.
  Local Transparent RewriteRules.RewriteToFancyWithCasts.
  Local Transparent RewriteRules.RewriteToFancy.
  Local Transparent RewriteRules.RewriteArith.
  Local Transparent RewriteRules.RewriteMulSplit.
  Local Transparent CheckedPartialEvaluateWithBounds.
  Local Transparent FromFlat ToFlat.

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
        {split_mul_to : split_mul_to_opt}
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

  Global Instance bounds0_good {t : base.type} {bounds} : @bounds_goodT t bounds.
  Proof. solve_bounds_good. Qed.

  Global Instance bounds1_good {s d : base.type} {bounds} : @bounds_goodT (s -> d) bounds.
  Proof. solve_bounds_good. Qed.

  Global Instance bounds2_good {a b D : base.type} {bounds} : @bounds_goodT (a -> b -> D) bounds.
  Proof. solve_bounds_good. Qed.

  Global Instance bounds3_good {a b c D : base.type} {bounds} : @bounds_goodT (a -> b -> c -> D) bounds.
  Proof. solve_bounds_good. Qed.
End Pipeline.

Module Export Hints.
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

  Ltac use_compilers_correctness Hres :=
    eapply Pipeline.BoundsPipeline_correct in Hres;
    [ | eauto using relax_zrange_gen_good with typeclass_instances.. ];
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
        => repeat apply expr.Wf_APP; eauto with nocore wf_extra wf_gen_cache; eauto with nocore wf wf_gen_cache
      end ].
End PipelineTactics.
