Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.SubsetoidRing.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.GetGoal.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Experiments.NewPipeline.Arithmetic.
Require Crypto.Experiments.NewPipeline.Language.
Require Crypto.Experiments.NewPipeline.UnderLets.
Require Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Crypto.Experiments.NewPipeline.AbstractInterpretationProofs.
Require Crypto.Experiments.NewPipeline.Rewriter.
Require Crypto.Experiments.NewPipeline.MiscCompilerPasses.
Require Crypto.Experiments.NewPipeline.CStringification.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(** NOTE: Module Ring SHOULD NOT depend on any compilers things *)
Module Ring.
  Local Notation is_bounded_by0 r v
    := ((lower r <=? v) && (v <=? upper r)).
  Local Notation is_bounded_by0o r
    := (match r with Some r' => fun v' => is_bounded_by0 r' v' | None => fun _ => true end).
  Local Notation is_bounded_by bounds ls
    := (fold_andb_map (fun r v'' => is_bounded_by0o r v'') bounds ls).
  Local Notation is_bounded_by1 bounds ls
    := (andb (is_bounded_by bounds (@fst _ unit ls)) true).
  Local Notation is_bounded_by2 bounds ls
    := (andb (is_bounded_by bounds (fst ls)) (is_bounded_by1 bounds (snd ls))).

  Lemma length_is_bounded_by bounds ls
    : is_bounded_by bounds ls = true -> length ls = length bounds.
  Proof.
    intro H.
    apply fold_andb_map_length in H; congruence.
  Qed.

  Section ring_goal.
    Context (limbwidth_num limbwidth_den : Z)
            (n : nat)
            (s : Z)
            (c : list (Z * Z))
            (tight_bounds : list (option zrange))
            (length_tight_bounds : length tight_bounds = n)
            (loose_bounds : list (option zrange))
            (length_loose_bounds : length loose_bounds = n).
    Local Notation weight := (weight limbwidth_num limbwidth_den).
    Local Notation eval := (Positional.eval weight n).
    Let prime_bound : zrange
      := r[0~>(s - Associational.eval c - 1)]%zrange.
    Let m := Z.to_pos (s - Associational.eval c).
    Context (m_eq : Z.pos m = s - Associational.eval c)
            (sc_pos : 0 < s - Associational.eval c)
            (Interp_rrelaxv : list Z -> list Z)
            (HInterp_rrelaxv : forall arg,
                is_bounded_by1 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_rrelaxv (fst arg)) = true
                   /\ Interp_rrelaxv (fst arg) = id (fst arg))
            (carry_mulmod : list Z -> list Z -> list Z)
            (Hcarry_mulmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (carry_mulmod f g)) mod (s - Associational.eval c)
                = (eval f * eval g) mod (s - Associational.eval c))
            (Interp_rcarry_mulv : list Z -> list Z -> list Z)
            (HInterp_rcarry_mulv : forall arg,
                is_bounded_by2 loose_bounds arg = true
                -> is_bounded_by tight_bounds (Interp_rcarry_mulv (fst arg) (fst (snd arg))) = true
                   /\ Interp_rcarry_mulv (fst arg) (fst (snd arg)) = carry_mulmod (fst arg) (fst (snd arg)))
            (carrymod : list Z -> list Z)
            (Hcarrymod
             : forall f,
                length f = n ->
                (eval (carrymod f)) mod (s - Associational.eval c)
                = (eval f) mod (s - Associational.eval c))
            (Interp_rcarryv : list Z -> list Z)
            (HInterp_rcarryv : forall arg,
                is_bounded_by1 loose_bounds arg = true
                -> is_bounded_by tight_bounds (Interp_rcarryv (fst arg)) = true
                   /\ Interp_rcarryv (fst arg) = carrymod (fst arg))
            (addmod : list Z -> list Z -> list Z)
            (Haddmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (addmod f g)) mod (s - Associational.eval c)
                = (eval f + eval g) mod (s - Associational.eval c))
            (Interp_raddv : list Z -> list Z -> list Z)
            (HInterp_raddv : forall arg,
                is_bounded_by2 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_raddv (fst arg) (fst (snd arg))) = true
                   /\ Interp_raddv (fst arg) (fst (snd arg)) = addmod (fst arg) (fst (snd arg)))
            (submod : list Z -> list Z -> list Z)
            (Hsubmod
             : forall f g,
                length f = n -> length g = n ->
                (eval (submod f g)) mod (s - Associational.eval c)
                = (eval f - eval g) mod (s - Associational.eval c))
            (Interp_rsubv : list Z -> list Z -> list Z)
            (HInterp_rsubv : forall arg,
                is_bounded_by2 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_rsubv (fst arg) (fst (snd arg))) = true
                   /\ Interp_rsubv (fst arg) (fst (snd arg)) = submod (fst arg) (fst (snd arg)))
            (oppmod : list Z -> list Z)
            (Hoppmod
             : forall f,
                length f = n ->
                (eval (oppmod f)) mod (s - Associational.eval c)
                = (- eval f) mod (s - Associational.eval c))
            (Interp_roppv : list Z -> list Z)
            (HInterp_roppv : forall arg,
                is_bounded_by1 tight_bounds arg = true
                -> is_bounded_by loose_bounds (Interp_roppv (fst arg)) = true
                   /\ Interp_roppv (fst arg) = oppmod (fst arg))
            (zeromod : list Z)
            (Hzeromod
             : (eval zeromod) mod (s - Associational.eval c)
                = 0 mod (s - Associational.eval c))
            (Interp_rzerov : list Z)
            (HInterp_rzerov : is_bounded_by tight_bounds Interp_rzerov = true
                              /\ Interp_rzerov = zeromod)
            (onemod : list Z)
            (Honemod
             : (eval onemod) mod (s - Associational.eval c)
                = 1 mod (s - Associational.eval c))
            (Interp_ronev : list Z)
            (HInterp_ronev : is_bounded_by tight_bounds Interp_ronev = true
                              /\ Interp_ronev = onemod)
            (encodemod : Z -> list Z)
            (Hencodemod
             : forall f,
                (eval (encodemod f)) mod (s - Associational.eval c)
                = f mod (s - Associational.eval c))
            (Interp_rencodev : Z -> list Z)
            (HInterp_rencodev : forall arg,
                is_bounded_by0 prime_bound (@fst _ unit arg) && true = true
                -> is_bounded_by tight_bounds (Interp_rencodev (fst arg)) = true
                   /\ Interp_rencodev (fst arg) = encodemod (fst arg)).

    Local Notation T := (list Z) (only parsing).
    Local Notation encoded_ok ls
      := (is_bounded_by tight_bounds ls = true) (only parsing).
    Local Notation encoded_okf := (fun ls => encoded_ok ls) (only parsing).

    Definition Fdecode (v : T) : F m
      := F.of_Z m (Positional.eval weight n v).
    Definition T_eq (x y : T)
      := Fdecode x = Fdecode y.

    Definition encodedT := sig encoded_okf.

    Definition ring_mul (x y : T) : T
      := Interp_rcarry_mulv (Interp_rrelaxv x) (Interp_rrelaxv y).
    Definition ring_add (x y : T) : T := Interp_rcarryv (Interp_raddv x y).
    Definition ring_sub (x y : T) : T := Interp_rcarryv (Interp_rsubv x y).
    Definition ring_opp (x : T) : T := Interp_rcarryv (Interp_roppv x).
    Definition ring_encode (x : F m) : T := Interp_rencodev (F.to_Z x).

    Definition GoodT : Prop
      := @subsetoid_ring
           (list Z) encoded_okf T_eq
           Interp_rzerov Interp_ronev ring_opp ring_add ring_sub ring_mul
         /\ @is_subsetoid_homomorphism
              (F m) (fun _ => True) eq 1%F F.add F.mul
              (list Z) encoded_okf T_eq Interp_ronev ring_add ring_mul ring_encode
         /\ @is_subsetoid_homomorphism
              (list Z) encoded_okf T_eq Interp_ronev ring_add ring_mul
              (F m) (fun _ => True) eq 1%F F.add F.mul
              Fdecode.

    Hint Rewrite ->@F.to_Z_add : push_FtoZ.
    Hint Rewrite ->@F.to_Z_mul : push_FtoZ.
    Hint Rewrite ->@F.to_Z_opp : push_FtoZ.
    Hint Rewrite ->@F.to_Z_of_Z : push_FtoZ.

    Lemma Fm_bounded_alt (x : F m)
      : (0 <=? F.to_Z x) && (F.to_Z x <=? Z.pos m - 1) = true.
    Proof using m_eq.
      clear -m_eq.
      destruct x as [x H]; cbn [F.to_Z proj1_sig].
      pose proof (Z.mod_pos_bound x (Z.pos m)).
      rewrite andb_true_iff; split; Z.ltb_to_lt; lia.
    Qed.

    Lemma Good : GoodT.
    Proof.
      split_and.
      repeat match goal with
             | [ H : context[andb _ true] |- _ ] => setoid_rewrite andb_true_r in H
             end.
      eapply subsetoid_ring_by_ring_isomorphism;
        cbv [ring_opp ring_add ring_sub ring_mul ring_encode F.sub] in *;
        repeat match goal with
               | [ H : forall arg : _ * unit, _ |- _ ] => specialize (fun arg => H (arg, tt))
               | [ H : forall arg : _ * (_ * unit), _ |- _ ] => specialize (fun a b => H (a, (b, tt)))
               | _ => progress cbn [fst snd] in *
               | _ => solve [ auto using andb_true_intro, conj with nocore ]
               | _ => progress intros
               | [ H : _ |- is_bounded_by _ _ = true ] => apply H
               | [ |- _ <-> _ ] => reflexivity
               | [ |- ?x = ?x ] => reflexivity
               | [ |- _ = _ :> Z ] => first [ reflexivity | rewrite <- m_eq; reflexivity ]
               | [ H : context[?x] |- Fdecode ?x = _ ] => rewrite H
               | [ H : context[?x _] |- Fdecode (?x _) = _ ] => rewrite H
               | [ H : context[?x _ _] |- Fdecode (?x _ _) = _ ] => rewrite H
               | _ => progress cbv [Fdecode]
               | [ |- _ = _ :> F _ ] => apply F.eq_to_Z_iff
               | _ => progress autorewrite with push_FtoZ
               | _ => rewrite m_eq
               | [ H : context[?x _ _] |- context[eval (?x _ _)] ] => rewrite H
               | [ H : context[?x _] |- context[eval (?x _)] ] => rewrite H
               | [ H : context[?x] |- context[eval ?x] ] => rewrite H
               | [ |- context[List.length ?x] ]
                 => erewrite (length_is_bounded_by _ x)
                   by eauto using andb_true_intro, conj with nocore
               | [ |- _ = _ :> Z ]
                 => push_Zmod; reflexivity
               | _ => pull_Zmod; rewrite Z.add_opp_r
               | _ => rewrite expanding_id_id
               | [ |- context[F.to_Z _ mod (_ - _)] ]
                 => rewrite <- m_eq, F.mod_to_Z
               | _ => rewrite <- m_eq; apply Fm_bounded_alt
               | [ |- context[andb _ true] ] => rewrite andb_true_r
               end.
    Qed.
  End ring_goal.
End Ring.

Import Associational Positional.

Import
  Crypto.Experiments.NewPipeline.Language
  Crypto.Experiments.NewPipeline.UnderLets
  Crypto.Experiments.NewPipeline.AbstractInterpretation
  Crypto.Experiments.NewPipeline.AbstractInterpretationProofs
  Crypto.Experiments.NewPipeline.Rewriter
  Crypto.Experiments.NewPipeline.MiscCompilerPasses
  Crypto.Experiments.NewPipeline.CStringification.

Import
  Language.Compilers
  UnderLets.Compilers
  AbstractInterpretation.Compilers
  AbstractInterpretationProofs.Compilers
  Rewriter.Compilers
  MiscCompilerPasses.Compilers
  CStringification.Compilers.

Import Compilers.defaults.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Notation "x" := (expr.Var x) (only printing, at level 9) : expr_scope.

Axiom admit_pf : False.
Notation admit := (match admit_pf with end).

Module Pipeline.
  Import GeneralizeVar.
  Inductive ErrorMessage :=
  | Computed_bounds_are_not_tight_enough
      {t} (computed_bounds expected_bounds : ZRange.type.base.option.interp (type.final_codomain t))
      (syntax_tree : Expr t) (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
  | Bounds_analysis_failed
  | Type_too_complicated_for_cps (t : type)
  | Value_not_leZ (descr : string) (lhs rhs : Z)
  | Value_not_leQ (descr : string) (lhs rhs : Q)
  | Value_not_ltZ (descr : string) (lhs rhs : Z)
  | Values_not_provably_distinctZ (descr : string) (lhs rhs : Z)
  | Values_not_provably_equalZ (descr : string) (lhs rhs : Z)
  | Values_not_provably_equal_listZ (descr : string) (lhs rhs : list Z)
  | Stringification_failed {t} (e : @Compilers.defaults.Expr t) (err : string).

  Notation ErrorT := (ErrorT ErrorMessage).

  Section show.
    Local Open Scope string_scope.
    Fixpoint find_too_loose_base_bounds {t}
      : ZRange.type.base.option.interp t -> ZRange.type.base.option.interp t-> bool * list (nat * nat) * list (zrange * zrange)
      := match t return ZRange.type.base.option.interp t -> ZRange.type.option.interp t-> bool * list (nat * nat) * list (zrange * zrange) with
         | base.type.unit
           => fun 'tt 'tt => (false, nil, nil)
         | base.type.nat
         | base.type.bool
           => fun _ _ => (false, nil, nil)
         | base.type.Z
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
                      ++ match ToString.C.ToFunctionLines
                                 false (* static *) "" "f" syntax_tree None arg_bounds ZRange.type.base.option.None with
                         | inl (E_lines, types_used)
                           => ["When doing bounds analysis on the syntax tree:"]
                                ++ E_lines ++ [""]
                                ++ ["with input bounds " ++ show true arg_bounds ++ "." ++ String.NewLine]%string
                         | inr errs
                           => (["(Unprintible syntax tree used in bounds analysis)" ++ String.NewLine]%string)
                               ++ ["Stringification failed on the syntax tree:"] ++ show_lines false syntax_tree ++ [errs]
                         end)%list
              | Bounds_analysis_failed => ["Bounds analysis failed."]
              | Type_too_complicated_for_cps t
                => ["Type too complicated for cps: " ++ show false t]
              | Value_not_leZ descr lhs rhs
                => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show false lhs ++ " ≤ " ++ show false rhs]
              | Value_not_leQ descr lhs rhs
                => ["Value not ≤ (" ++ descr ++ ") : expected " ++ show false lhs ++ " ≤ " ++ show false rhs]
              | Value_not_ltZ descr lhs rhs
                => ["Value not < (" ++ descr ++ ") : expected " ++ show false lhs ++ " < " ++ show false rhs]
              | Values_not_provably_distinctZ descr lhs rhs
                => ["Values not provably distinct (" ++ descr ++ ") : expected " ++ show true lhs ++ " ≠ " ++ show true rhs]
              | Values_not_provably_equalZ descr lhs rhs
              | Values_not_provably_equal_listZ descr lhs rhs
                => ["Values not provably equal (" ++ descr ++ ") : expected " ++ show true lhs ++ " = " ++ show true rhs]
              | Stringification_failed t e err => ["Stringification failed on the syntax tree:"] ++ show_lines false e ++ [err]
              end.
    Local Instance show_ErrorMessage : Show ErrorMessage
      := fun parens err => String.concat String.NewLine (show_lines parens err).
  End show.

  Definition invert_result {T} (v : ErrorT T)
    := match v return match v with Success _ => T | _ => ErrorMessage end with
       | Success v => v
       | Error msg => msg
       end.

  Record to_fancy_args := { invert_low : Z (*log2wordmax*) -> Z -> option Z ; invert_high : Z (*log2wordmax*) -> Z -> option Z }.

  Definition BoundsPipeline
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             relax_zrange
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
  : ErrorT (Expr t)
    := (*let E := expr.Uncurry E in*)
      let E := PartialEvaluateWithListInfoFromBounds E arg_bounds in
      let E := PartialEvaluate E in
      (* Note that DCE evaluates the expr with two different [var]
         arguments, and so results in a pipeline that is 2x slower
         unless we pass through a uniformly concrete [var] type
         first *)
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      let E := if with_dead_code_elimination then DeadCodeElimination.EliminateDead E else E in
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      let E := if with_subst01 then Subst01.Subst01 E else E in
      let E := UnderLets.LetBindReturn E in
      let E := PartialEvaluate E in (* after inlining, see if any new rewrite redexes are available *)
      let E := ReassociateSmallConstants.Reassociate (2^8) E in
      let E := match translate_to_fancy with
               | Some {| invert_low := invert_low ; invert_high := invert_high |} => RewriteRules.RewriteToFancy invert_low invert_high E
               | None => E
               end in
      dlet_nd e := ToFlat E in
      let E := FromFlat e in
      let E := CheckedPartialEvaluateWithBounds relax_zrange E arg_bounds out_bounds in
      match E with
      | inl E => Success E
      | inr (b, E)
        => Error (Computed_bounds_are_not_tight_enough b out_bounds E arg_bounds)
      end.

  Definition BoundsPipelineToStrings
             (static : bool)
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             relax_zrange
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
    : ErrorT (list string * ToString.C.ident_infos)
    := let E := BoundsPipeline
                  (*with_dead_code_elimination*)
                  with_subst01
                  translate_to_fancy
                  relax_zrange
                  E arg_bounds out_bounds in
       match E with
       | Success E' => let E := ToString.C.ToFunctionLines
                                  static type_prefix name E' None arg_bounds out_bounds in
                      match E with
                      | inl E => Success E
                      | inr err => Error (Stringification_failed E' err)
                      end
       | Error err => Error err
       end.

  Definition BoundsPipelineToString
             (static : bool)
             (type_prefix : string)
             (name : string)
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             relax_zrange
             {t}
             (E : Expr t)
             arg_bounds
             out_bounds
    : ErrorT (string * ToString.C.ident_infos)
    := let E := BoundsPipelineToStrings
                  static type_prefix name
                  (*with_dead_code_elimination*)
                  with_subst01
                  translate_to_fancy
                  relax_zrange
                  E arg_bounds out_bounds in
       match E with
       | Success (E, types_used) => Success (ToString.C.LinesToString E, types_used)
       | Error err => Error err
       end.

  Lemma BoundsPipeline_correct
             (with_dead_code_elimination : bool := true)
             (with_subst01 : bool)
             (translate_to_fancy : option to_fancy_args)
             relax_zrange
             (Hrelax : forall r r' z : zrange,
                 (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
             {t}
             (e : Expr t)
             arg_bounds
             out_bounds
             rv
             (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 translate_to_fancy relax_zrange e arg_bounds out_bounds = Success rv)
    : forall arg
             (Harg : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg = true),
      ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp rv) arg) = true
      /\ forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rv) arg
                                 = type.app_curried (Interp e) arg.
  Proof.
    cbv [BoundsPipeline Let_In] in *;
      repeat match goal with
             | [ H : match ?x with _ => _ end = Success _ |- _ ]
               => destruct x eqn:?; cbv beta iota in H; [ | destruct_head'_prod; congruence ];
                    let H' := fresh in
                    inversion H as [H']; clear H; rename H' into H
             end.
    { intros;
        match goal with
        | [ H : _ = _ |- _ ]
          => eapply CheckedPartialEvaluateWithBounds_Correct in H;
              [ destruct H as [H0 H1] | .. ]
        end;
        [
        | eassumption || (try reflexivity).. ].
      subst.
      split; [ assumption | ].
      { intros; rewrite H1.
        exact admit. (* interp correctness *) } }
  Qed.

  Definition BoundsPipeline_correct_transT
             {t}
             arg_bounds
             out_bounds
             (InterpE : type.interp base.interp t)
             (rv : Expr t)
    := forall arg
              (Harg : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg = true),
      ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (Interp rv) arg) = true
      /\ forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rv) arg
                                 = type.app_curried InterpE arg.

  Lemma BoundsPipeline_correct_trans
        (with_dead_code_elimination : bool := true)
        (with_subst01 : bool)
        (translate_to_fancy : option to_fancy_args)
        relax_zrange
        (Hrelax
         : forall r r' z : zrange,
            (z <=? r)%zrange = true -> relax_zrange r = Some r' -> (z <=? r')%zrange = true)
        {t}
        (e : Expr t)
        arg_bounds out_bounds
        (InterpE : type.interp base.interp t)
        (InterpE_correct
         : forall arg
                  (Harg : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg = true),
            type.app_curried (Interp e) arg = type.app_curried InterpE arg)
        rv
        (Hrv : BoundsPipeline (*with_dead_code_elimination*) with_subst01 translate_to_fancy relax_zrange e arg_bounds out_bounds = Success rv)
    : BoundsPipeline_correct_transT arg_bounds out_bounds InterpE rv.
  Proof.
    intros arg Harg; rewrite <- InterpE_correct by assumption.
    eapply @BoundsPipeline_correct; eassumption.
  Qed.
End Pipeline.

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
  cbv [fold_right option_map].
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

Ltac cache_reify _ :=
  intros;
  etransitivity;
  [
  | repeat match goal with |- _ = ?f' ?x => is_var x; apply (f_equal (fun f => f _)) end;
    Reify_rhs ();
    reflexivity ];
  subst_evars;
  reflexivity.

Create HintDb reify_gen_cache.

Derive carry_mul_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f g : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (idxs : list nat),
                    Interp (t:=reify_type_of carry_mulmod)
                           carry_mul_gen limbwidth_num limbwidth_den s c n idxs f g
                    = carry_mulmod limbwidth_num limbwidth_den s c n idxs f g)
       As carry_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = carry_mulmod _ _ _ _ _ _ _ _) => simple apply carry_mul_gen_correct : reify_gen_cache.

Derive carry_square_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (idxs : list nat),
                    Interp (t:=reify_type_of carry_squaremod)
                           carry_square_gen limbwidth_num limbwidth_den s c n idxs f
                    = carry_squaremod limbwidth_num limbwidth_den s c n idxs f)
       As carry_square_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = carry_squaremod _ _ _ _ _ _ _) => simple apply carry_square_gen_correct : reify_gen_cache.

Derive carry_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f : list Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (idxs : list nat),
                    Interp (t:=reify_type_of carrymod)
                           carry_gen limbwidth_num limbwidth_den s c n idxs f
                    = carrymod limbwidth_num limbwidth_den s c n idxs f)
       As carry_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = carrymod _ _ _ _ _ _ _) => simple apply carry_gen_correct : reify_gen_cache.

Derive encode_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (v : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z)),
                    Interp (t:=reify_type_of encodemod)
                           encode_gen limbwidth_num limbwidth_den s c n v
                    = encodemod limbwidth_num limbwidth_den s c n v)
       As encode_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = encodemod _ _ _ _ _ _) => simple apply encode_gen_correct : reify_gen_cache.

Derive add_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (f g : list Z)
                        (n : nat),
                    Interp (t:=reify_type_of addmod)
                           add_gen limbwidth_num limbwidth_den n f g
                    = addmod limbwidth_num limbwidth_den n f g)
       As add_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = addmod _ _ _ _ _) => simple apply add_gen_correct : reify_gen_cache.

Derive sub_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (coef : Z)
                        (f g : list Z),
                    Interp (t:=reify_type_of submod)
                           sub_gen limbwidth_num limbwidth_den s c n coef f g
                    = submod limbwidth_num limbwidth_den s c n coef f g)
       As sub_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = submod _ _ _ _ _ _ _ _) => simple apply sub_gen_correct : reify_gen_cache.
Derive opp_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z))
                        (coef : Z)
                        (f : list Z),
                    Interp (t:=reify_type_of oppmod)
                           opp_gen limbwidth_num limbwidth_den s c n coef f
                    = oppmod limbwidth_num limbwidth_den s c n coef f)
       As opp_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = oppmod _ _ _ _ _ _ _) => simple apply opp_gen_correct : reify_gen_cache.
Definition zeromod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 0.
Definition onemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 1.
Definition primemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n (s - Associational.eval c).
Derive zero_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z)),
                    Interp (t:=reify_type_of zeromod)
                           zero_gen limbwidth_num limbwidth_den s c n
                    = zeromod limbwidth_num limbwidth_den s c n)
       As zero_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = zeromod _ _ _ _ _) => simple apply zero_gen_correct : reify_gen_cache.

Derive one_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z)),
                    Interp (t:=reify_type_of onemod)
                           one_gen limbwidth_num limbwidth_den s c n
                    = onemod limbwidth_num limbwidth_den s c n)
       As one_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = onemod _ _ _ _ _) => simple apply one_gen_correct : reify_gen_cache.

Derive prime_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (s : Z)
                        (c : list (Z * Z)),
                    Interp (t:=reify_type_of primemod)
                           prime_gen limbwidth_num limbwidth_den s c n
                    = primemod limbwidth_num limbwidth_den s c n)
       As prime_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = primemod _ _ _ _ _) => simple apply prime_gen_correct : reify_gen_cache.

Derive id_gen
       SuchThat (forall (ls : list Z),
                    Interp (t:=reify_type_of (@id (list Z)))
                           id_gen ls
                    = id ls)
       As id_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = id _) => simple apply id_gen_correct : reify_gen_cache.

Derive to_bytes_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (bitwidth : Z)
                        (m_enc : list Z)
                        (f : list Z),
                    Interp (t:=reify_type_of to_bytesmod)
                           to_bytes_gen limbwidth_num limbwidth_den n bitwidth m_enc f
                    = to_bytesmod limbwidth_num limbwidth_den n bitwidth m_enc f)
       As to_bytes_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = to_bytesmod _ _ _ _ _ _) => simple apply to_bytes_gen_correct : reify_gen_cache.

Derive from_bytes_gen
       SuchThat (forall (limbwidth_num limbwidth_den : Z)
                        (n : nat)
                        (f : list Z),
                    Interp (t:=reify_type_of from_bytesmod)
                           from_bytes_gen limbwidth_num limbwidth_den n f
                    = from_bytesmod limbwidth_num limbwidth_den n f)
       As from_bytes_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = from_bytesmod _ _ _ _) => simple apply from_bytes_gen_correct : reify_gen_cache.

Derive mulx_gen
       SuchThat (forall (s x y : Z),
                    Interp (t:=reify_type_of mulx)
                           mulx_gen s x y
                    = mulx s x y)
       As mulx_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = mulx _ _ _) => simple apply mulx_gen_correct : reify_gen_cache.

Derive addcarryx_gen
       SuchThat (forall (s c x y : Z),
                    Interp (t:=reify_type_of addcarryx)
                           addcarryx_gen s c x y
                    = addcarryx s c x y)
       As addcarryx_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = addcarryx _ _ _ _) => simple apply addcarryx_gen_correct : reify_gen_cache.

Derive subborrowx_gen
       SuchThat (forall (s c x y : Z),
                    Interp (t:=reify_type_of subborrowx)
                           subborrowx_gen s c x y
                    = subborrowx s c x y)
       As subborrowx_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = subborrowx _ _ _ _) => simple apply subborrowx_gen_correct : reify_gen_cache.

Derive cmovznz_gen
       SuchThat (forall (bitwidth cond z nz : Z),
                    Interp (t:=reify_type_of cmovznz)
                           cmovznz_gen bitwidth cond z nz
                    = cmovznz bitwidth cond z nz)
       As cmovznz_gen_correct.
Proof. cache_reify (). Qed.
Hint Extern 1 (_ = cmovznz _ _ _ _) => simple apply cmovznz_gen_correct : reify_gen_cache.


(** XXX TODO: Translate Jade's python script *)
Module Import UnsaturatedSolinas.
  Section rcarry_mul.
    Context (n : nat)
            (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (seq 0 n ++ [0; 1])%list%nat.
    Let coef := 2.
    Let n_bytes := bytes_n (Qnum limbwidth) (Qden limbwidth) n.
    Let prime_upperbound_list : list Z
      := encode (weight (Qnum limbwidth) (Qden limbwidth)) n s c (s-1).
    Let prime_bytes_upperbound_list : list Z
      := encode (weight 8 1) n_bytes s c (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition prime_bound : ZRange.type.option.interp (base.type.Z)
      := Some r[0~>(s - Associational.eval c - 1)]%zrange.
    Definition prime_bytes_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
      := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list).

    Definition m_enc : list Z
      := encode (weight (Qnum limbwidth) (Qden limbwidth)) n s c (s-Associational.eval c).

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [machine_wordsize; 2 * machine_wordsize]%Z.

    Definition relax_zrange_of_machine_wordsize_with_bytes
      := relax_zrange_gen [1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

    Let relax_zrange := relax_zrange_of_machine_wordsize.
    Let relax_zrange_with_bytes := relax_zrange_of_machine_wordsize_with_bytes.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


    (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := fold_right
           (fun '(b, e) k => if b:bool then Error e else k)
           res
           [(negb (Qle_bool 1 limbwidth)%Q, Pipeline.Value_not_leQ "limbwidth < 1" 1%Q limbwidth);
              ((negb (0 <? Associational.eval c))%Z, Pipeline.Value_not_ltZ "Associational.eval c ≤ 0" 0 (Associational.eval c));
              ((negb (Associational.eval c <? s))%Z, Pipeline.Value_not_ltZ "s ≤ Associational.eval c" (Associational.eval c) s);
              ((s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s = 0" s 0);
              ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat);
              ((negb (0 <? machine_wordsize)), Pipeline.Value_not_ltZ "machine_wordsize ≤ 0" 0 machine_wordsize);
              (let v1 := s in
               let v2 := weight (Qnum limbwidth) (QDen limbwidth) n in
               (negb (v1 =? v2), Pipeline.Values_not_provably_equalZ "s ≠ weight n (needed for to_bytes)" v1 v2));
              (let v1 := (map (Z.land (Z.ones machine_wordsize)) m_enc) in
               let v2 := m_enc in
               (negb (list_beq _ Z.eqb v1 v2), Pipeline.Values_not_provably_equal_listZ "map mask m_enc ≠ m_enc (needed for to_bytes)" v1 v2));
              (let v1 := eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc in
               let v2 := s - Associational.eval c in
               (negb (v1 =? v2)%Z, Pipeline.Values_not_provably_equalZ "eval m_enc ≠ s - Associational.eval c (needed for to_bytes)" v1 v2))].

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).

    Notation BoundsPipelineToStrings prefix name rop in_bounds out_bounds
      := ((prefix ++ name)%string,
          Pipeline.BoundsPipelineToStrings
            true (* static *) prefix (prefix ++ name)%string
            (*false*) true None
            relax_zrange
            rop%Expr in_bounds out_bounds).

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               (*false*) true None
               relax_zrange
               (relax_zrange_gen_good _)
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Notation BoundsPipelineToStrings_no_subst01 prefix name rop in_bounds out_bounds
      := ((prefix ++ name)%string,
          Pipeline.BoundsPipelineToStrings
            true (* static *) prefix (prefix ++ name)%string
            (*false*) false None
            relax_zrange
            rop%Expr in_bounds out_bounds).

    Notation BoundsPipeline_no_subst01_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               (*false*) false None
               relax_zrange
               (relax_zrange_gen_good _)
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Notation BoundsPipelineToStrings_with_bytes_no_subst01 prefix name rop in_bounds out_bounds
      := ((prefix ++ name)%string,
          Pipeline.BoundsPipelineToStrings
            true (* static *) prefix (prefix ++ name)%string
            (*false*) false None
            relax_zrange_with_bytes
            rop%Expr in_bounds out_bounds).

    Notation BoundsPipeline_with_bytes_no_subst01_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               (*false*) false None
               relax_zrange_with_bytes
               (relax_zrange_gen_good _)
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    (* N.B. We only need [rcarry_mul] if we want to extract the Pipeline; otherwise we can just use [rcarry_mul_correct] *)
    Definition srcarry_mul prefix
      := BoundsPipelineToStrings
           prefix "carry_mul"
           (carry_mul_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
           (Some loose_bounds, (Some loose_bounds, tt))
           (Some tight_bounds).

    Definition rcarry_mul_correct
      := BoundsPipeline_correct
           (Some loose_bounds, (Some loose_bounds, tt))
           (Some tight_bounds)
           (carry_mulmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n idxs).

    Definition srcarry_square prefix
      := BoundsPipelineToStrings_no_subst01
           prefix "carry_square"
           (carry_square_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
           (Some loose_bounds, tt)
           (Some tight_bounds).

    Definition rcarry_square_correct
      := BoundsPipeline_no_subst01_correct
           (Some loose_bounds, tt)
           (Some tight_bounds)
           (carry_squaremod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n idxs).

    Definition srcarry prefix
      := BoundsPipelineToStrings
           prefix "carry"
           (carry_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
           (Some loose_bounds, tt)
           (Some tight_bounds).

    Definition rcarry_correct
      := BoundsPipeline_correct
           (Some loose_bounds, tt)
           (Some tight_bounds)
           (carrymod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n idxs).

    Definition srrelax prefix
      := BoundsPipelineToStrings
           prefix "relax"
           id_gen
           (Some tight_bounds, tt)
           (Some loose_bounds).

    Definition rrelax_correct
      := BoundsPipeline_correct
           (Some tight_bounds, tt)
           (Some loose_bounds)
           (@id (list Z)).

    Definition sradd prefix
      := BoundsPipelineToStrings
           prefix "add"
           (add_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n)
           (Some tight_bounds, (Some tight_bounds, tt))
           (Some loose_bounds).

    Definition radd_correct
      := BoundsPipeline_correct
           (Some tight_bounds, (Some tight_bounds, tt))
           (Some loose_bounds)
           (addmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n).

    Definition srsub prefix
      := BoundsPipelineToStrings
           prefix "sub"
           (sub_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify coef)
           (Some tight_bounds, (Some tight_bounds, tt))
           (Some loose_bounds).

    Definition rsub_correct
      := BoundsPipeline_correct
           (Some tight_bounds, (Some tight_bounds, tt))
           (Some loose_bounds)
           (submod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n coef).

    Definition sropp prefix
      := BoundsPipelineToStrings
           prefix "opp"
           (opp_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify coef)
           (Some tight_bounds, tt)
           (Some loose_bounds).

    Definition ropp_correct
      := BoundsPipeline_correct
           (Some tight_bounds, tt)
           (Some loose_bounds)
           (oppmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n coef).

    Definition srto_bytes prefix
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix "to_bytes"
           (to_bytes_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify m_enc)
           (Some tight_bounds, tt)
           prime_bytes_bounds.

    Definition rto_bytes_correct
      := BoundsPipeline_with_bytes_no_subst01_correct
           (Some tight_bounds, tt)
           prime_bytes_bounds
           (to_bytesmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n machine_wordsize m_enc).

    Definition srfrom_bytes prefix
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix "from_bytes"
           (from_bytes_gen
              @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n)
           (prime_bytes_bounds, tt)
           (Some tight_bounds).

    Definition rfrom_bytes_correct
      := BoundsPipeline_with_bytes_no_subst01_correct
           (prime_bytes_bounds, tt)
           (Some tight_bounds)
           (from_bytesmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n).

    Definition rencode_correct
      := BoundsPipeline_correct
           (prime_bound, tt)
           (Some tight_bounds)
           (encodemod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n).

    Definition rzero_correct
      := BoundsPipeline_correct
           tt
           (Some tight_bounds)
           (zeromod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n).

    Definition rone_correct
      := BoundsPipeline_correct
           tt
           (Some tight_bounds)
           (onemod (Qnum limbwidth) (Z.pos (Qden limbwidth)) s c n).

    Definition srmulx prefix (s : Z)
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix ("mulx_u" ++ decimal_string_of_Z s)
           (mulx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt))%zrange
           (Some r[0~>2^s-1], Some r[0~>2^s-1])%zrange.

    Definition srmulx_correct (s : Z)
      := BoundsPipeline_with_bytes_no_subst01_correct
           (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt))%zrange
           (Some r[0~>2^s-1], Some r[0~>2^s-1])%zrange
           (mulx s).

    Definition sraddcarryx prefix (s : Z)
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix ("addcarryx_u" ++ decimal_string_of_Z s)
           (addcarryx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange.

    Definition sraddcarryx_correct (s : Z)
      := BoundsPipeline_with_bytes_no_subst01_correct
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange
           (addcarryx s).

    Definition srsubborrowx prefix (s : Z)
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix ("subborrowx_u" ++ decimal_string_of_Z s)
           (subborrowx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange.

    Definition srsubborrowx_correct (s : Z)
      := BoundsPipeline_with_bytes_no_subst01_correct
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange
           (subborrowx s).

    Definition srcmovznz prefix (s : Z)
      := BoundsPipelineToStrings_with_bytes_no_subst01
           prefix ("cmovznz_u" ++ decimal_string_of_Z s)
           (cmovznz_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1])%zrange.

    Definition srcmovznz_correct (s : Z)
      := BoundsPipeline_with_bytes_no_subst01_correct
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1])%zrange
           (cmovznz s).

    (* we need to strip off [Hrv : ... = Pipeline.Success rv] and related arguments *)
    Definition rcarry_mul_correctT rv : Prop
      := type_of_strip_3arrow (@rcarry_mul_correct rv).
    Definition rcarry_correctT rv : Prop
      := type_of_strip_3arrow (@rcarry_correct rv).
    Definition rrelax_correctT rv : Prop
      := type_of_strip_3arrow (@rrelax_correct rv).
    Definition radd_correctT rv : Prop
      := type_of_strip_3arrow (@radd_correct rv).
    Definition rsub_correctT rv : Prop
      := type_of_strip_3arrow (@rsub_correct rv).
    Definition ropp_correctT rv : Prop
      := type_of_strip_3arrow (@ropp_correct rv).
    Definition rto_bytes_correctT rv : Prop
      := type_of_strip_3arrow (@rto_bytes_correct rv).
    Definition rfrom_bytes_correctT rv : Prop
      := type_of_strip_3arrow (@rfrom_bytes_correct rv).
    Definition rencode_correctT rv : Prop
      := type_of_strip_3arrow (@rencode_correct rv).
    Definition rzero_correctT rv : Prop
      := type_of_strip_3arrow (@rzero_correct rv).
    Definition rone_correctT rv : Prop
      := type_of_strip_3arrow (@rone_correct rv).

    Section make_ring.
      Let m : positive := Z.to_pos (s - Associational.eval c).
      Context (curve_good : check_args (Success tt) = Success tt)
              {rcarry_mulv} (Hrmulv : rcarry_mul_correctT rcarry_mulv)
              {rcarryv} (Hrcarryv : rcarry_correctT rcarryv)
              {rrelaxv} (Hrrelaxv : rrelax_correctT rrelaxv)
              {raddv} (Hraddv : radd_correctT raddv)
              {rsubv} (Hrsubv : rsub_correctT rsubv)
              {roppv} (Hroppv : ropp_correctT roppv)
              {rzerov} (Hrzerov : rzero_correctT rzerov)
              {ronev} (Hronev : rone_correctT ronev)
              {rencodev} (Hrencodev : rencode_correctT rencodev)
              {rto_bytesv} (Hto_bytesv : rto_bytes_correctT rto_bytesv)
              {rfrom_bytesv} (Hfrom_bytesv : rfrom_bytes_correctT rfrom_bytesv).

      Local Ltac use_curve_good_t :=
        repeat first [ assumption
                     | progress rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                     | reflexivity
                     | lia
                     | rewrite interp_reify_list, ?map_map
                     | rewrite map_ext with (g:=id), map_id
                     | progress distr_length
                     | progress cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *
                     | progress cbv [Qle] in *
                     | progress cbn -[reify_list] in *
                     | progress intros
                     | solve [ auto ] ].

      Lemma use_curve_good
        : Z.pos m = s - Associational.eval c
          /\ Z.pos m <> 0
          /\ s - Associational.eval c <> 0
          /\ s <> 0
          /\ 0 < machine_wordsize
          /\ n <> 0%nat
          /\ List.length tight_bounds = n
          /\ List.length loose_bounds = n
          /\ 0 < Qden limbwidth <= Qnum limbwidth
          /\ s = weight (Qnum limbwidth) (QDen limbwidth) n
          /\ map (Z.land (Z.ones machine_wordsize)) m_enc = m_enc
          /\ eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc = s - Associational.eval c
          /\ Datatypes.length m_enc = n
          /\ 0 < Associational.eval c < s.
      Proof.
        clear -curve_good.
        cbv [check_args fold_right] in curve_good.
        cbv [tight_bounds loose_bounds prime_bound m_enc] in *.
        break_innermost_match_hyps; try discriminate.
        rewrite negb_false_iff in *.
        Z.ltb_to_lt.
        rewrite Qle_bool_iff in *.
        rewrite NPeano.Nat.eqb_neq in *.
        intros.
        cbv [Qnum Qden limbwidth Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
        rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *.
        specialize_by lia.
        repeat match goal with H := _ |- _ => subst H end.
        repeat match goal with
               | [ H : list_beq _ _ _ _ = true |- _ ] => apply internal_list_dec_bl in H; [ | intros; Z.ltb_to_lt; omega.. ]
               end.
        repeat apply conj.
        { destruct (s - Associational.eval c) eqn:?; cbn; lia. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
        { use_curve_good_t. }
      Qed.

      (** TODO: Find a better place to put the spec for [to_bytes] *)
      Definition GoodT : Prop
        := @Ring.GoodT
             (Qnum limbwidth)
             (Z.pos (Qden limbwidth))
             n s c
             tight_bounds
             (Interp rrelaxv)
             (Interp rcarry_mulv)
             (Interp rcarryv)
             (Interp raddv)
             (Interp rsubv)
             (Interp roppv)
             (Interp rzerov)
             (Interp ronev)
             (Interp rencodev)
           /\ (let to_bytesT := (base.type.list base.type.Z -> base.type.list base.type.Z)%etype in
              forall f
                (Hf : type.andb_bool_for_each_lhs_of_arrow (t:=to_bytesT) (@ZRange.type.option.is_bounded_by) (Some tight_bounds, tt) f = true),
                 ((ZRange.type.base.option.is_bounded_by prime_bytes_bounds (type.app_curried (Interp rto_bytesv) f) = true
                   /\ (forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rto_bytesv) f
                                               = type.app_curried (t:=to_bytesT) (to_bytesmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n machine_wordsize m_enc) f))
                  /\ (Positional.eval (weight 8 1) n_bytes (type.app_curried (t:=to_bytesT) (to_bytesmod (Qnum limbwidth) (Z.pos (Qden limbwidth)) n machine_wordsize m_enc) f)) = (Positional.eval (weight (Qnum limbwidth) (Z.pos (Qden limbwidth))) n (fst f) mod m))).

      Theorem Good : GoodT.
      Proof.
        pose proof use_curve_good; destruct_head'_and; destruct_head_hnf' ex.
        split.
        { eapply Ring.Good;
            lazymatch goal with
            | [ H : ?P ?rop |- context[expr.Interp _ ?rop] ]
              => intros;
                  let H1 := fresh in
                  let H2 := fresh in
                  unshelve edestruct H as [H1 H2]; [ .. | solve [ split; [ eapply H1 | eapply H2 ] ] ];
                    solve [ exact tt | eassumption | reflexivity ]
            | _ => idtac
            end;
            repeat first [ assumption
                         | intros; apply eval_carry_mulmod
                         | intros; apply eval_carrymod
                         | intros; apply eval_addmod
                         | intros; apply eval_submod
                         | intros; apply eval_oppmod
                         | intros; apply eval_encodemod
                         | apply conj ]. }
        { cbv zeta; intros f Hf; split.
          { apply Hto_bytesv; assumption. }
          { cbn [type.for_each_lhs_of_arrow type_base type.andb_bool_for_each_lhs_of_arrow ZRange.type.option.is_bounded_by fst snd] in *.
            rewrite Bool.andb_true_iff in *; split_and'.
            etransitivity; [ apply eval_to_bytesmod | f_equal; (eassumption || (symmetry; eassumption)) ];
              auto; try omega.
            { erewrite Ring.length_is_bounded_by by eassumption; assumption. }
            { lazymatch goal with
              | [ H : eval _ _ _ = ?x |- _ <= _ < 2 * ?x ] => rewrite <- H
              end.
              cbv [m_enc tight_bounds tight_upperbounds prime_upperbound_list] in H15 |- *.
              Lemma fold_andb_map_snoc A B f x xs y ys
                : @fold_andb_map A B f (xs ++ [x]) (ys ++ [y]) = @fold_andb_map A B f xs ys && f x y.
              Proof.
                clear.
                revert ys; induction xs as [|x' xs'], ys as [|y' ys']; cbn;
                  rewrite ?Bool.andb_true_r, ?Bool.andb_false_r;
                  try (destruct ys'; cbn; rewrite Bool.andb_false_r);
                  try (destruct xs'; cbn; rewrite Bool.andb_false_r);
                  try reflexivity.
                rewrite IHxs', Bool.andb_assoc; reflexivity.
              Qed.
              Lemma eval_is_bounded_by wt n' bounds bounds' f
                    (H : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) bounds f = true)
                    (Hb : bounds = Some (List.map (@Some _) bounds'))
                    (Hblen : length bounds' = n')
                    (Hwt : forall i, List.In i (seq 0 n') -> 0 <= wt i)
                : eval wt n' (List.map lower bounds') <= eval wt n' f <= eval wt n' (List.map upper bounds').
              Proof.
                clear -H Hb Hblen Hwt.
                setoid_rewrite in_seq in Hwt.
                subst bounds.
                pose proof H as H'; apply fold_andb_map_length in H'.
                revert dependent bounds'; intro bounds'.
                revert dependent f; intro f.
                rewrite <- (List.rev_involutive bounds'), <- (List.rev_involutive f);
                  generalize (List.rev bounds') (List.rev f); clear bounds' f; intros bounds f; revert bounds f.
                induction n' as [|n IHn], bounds as [|b bounds], f as [|f fs]; intros;
                  cbn [length rev map] in *; distr_length.
                { rewrite !map_app in *; cbn [map] in *.
                  erewrite !eval_snoc by (distr_length; eauto).
                  cbn [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by] in *.
                  specialize_by (intros; auto with omega).
                  specialize (Hwt n); specialize_by omega.
                  repeat first [ progress Bool.split_andb
                               | rewrite Nat.add_1_r in *
                               | rewrite fold_andb_map_snoc in *
                               | rewrite Nat.succ_inj_wd in *
                               | progress Z.ltb_to_lt
                               | progress cbn [In seq] in *
                               | match goal with
                                 | [ H : length _ = ?v |- _ ] => rewrite H in *
                                 | [ H : ?v = length _ |- _ ] => rewrite <- H in *
                                 end ].
                  split; apply Z.add_le_mono; try apply IHn; auto; distr_length; nia. }
              Qed.
              eapply eval_is_bounded_by with (wt:=weight (Qnum limbwidth) (QDen limbwidth)) in H15.
              2:rewrite <- (map_map _ (@Some _)); reflexivity.
              2:distr_length; reflexivity.
              rewrite ?map_map in *.
              cbn [lower upper] in *.
              split.
              { etransitivity; [ erewrite <- eval_zeros; [ | apply weight_0, wprops ] | apply H15 ].
                apply Z.eq_le_incl; f_equal.
                admit.
                omega. }
              { eapply Z.le_lt_trans; [ apply H15 | ].
                assert (Hlen : length (encode (weight (Qnum limbwidth) (QDen limbwidth)) n s c (s - 1)) = n) by distr_length.
                revert Hlen.
                generalize ((encode (weight (Qnum limbwidth) (QDen limbwidth)) n s c (s - 1))).
                intro ls.
                clear.
                revert ls.
                clearbody limbwidth.
                induction n as [|n' IHn'], ls as [|l ls]; cbn [length]; intros; try omega.
                admit.
                cbn [map].
                admit. }
              admit. }
      Admitted.
    End make_ring.

    Section for_stringification.
      Definition aggregate_infos {A B C} (ls : list (A * ErrorT B (C * ToString.C.ident_infos))) : ToString.C.ident_infos
        := fold_right
             ToString.C.ident_info_union
             ToString.C.ident_info_empty
             (List.map
                (fun '(_, res) => match res with
                               | Success (_, infos) => infos
                               | Error _ => ToString.C.ident_info_empty
                               end)
                ls).

      Definition extra_synthesis (function_name_prefix : string) (infos : ToString.C.ident_infos)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t
        := let ls_addcarryx := List.flat_map
                                 (fun lg_split:positive => [sraddcarryx function_name_prefix lg_split; srsubborrowx function_name_prefix lg_split])
                                 (PositiveSet.elements (ToString.C.addcarryx_lg_splits infos)) in
           let ls_mulx := List.map
                            (fun lg_split:positive => srmulx function_name_prefix lg_split)
                            (PositiveSet.elements (ToString.C.mulx_lg_splits infos)) in
           let ls_cmov := List.map
                            (fun bitwidth:positive => srcmovznz function_name_prefix bitwidth)
                            (PositiveSet.elements (ToString.C.cmovznz_bitwidths infos)) in
           let ls := ls_addcarryx ++ ls_mulx ++ ls_cmov in
           let infos := aggregate_infos ls in
           (List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            ToString.C.bitwidths_used infos).

      (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
      Definition Synthesize (function_name_prefix : string) : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := let ls := List.map (fun sr => sr function_name_prefix) [srcarry_mul; srcarry_square; srcarry; sradd; srsub; sropp; srto_bytes; srfrom_bytes] in
           let infos := aggregate_infos ls in
           let '(extra_ls, extra_bit_widths) := extra_synthesis function_name_prefix infos in
           (extra_ls ++ List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            PositiveSet.union extra_bit_widths (ToString.C.bitwidths_used infos)).
    End for_stringification.
  End rcarry_mul.
End UnsaturatedSolinas.

Ltac peel_interp_app _ :=
  lazymatch goal with
  | [ |- ?R' (?InterpE ?arg) (?f ?arg) ]
    => apply fg_equal_rel; [ | reflexivity ];
       try peel_interp_app ()
  | [ |- ?R' (Interp ?ev) (?f ?x) ]
    => let sv := type of x in
       let fx := constr:(f x) in
       let dv := type of fx in
       let rs := reify_type sv in
       let rd := reify_type dv in
       etransitivity;
       [ apply @expr.Interp_APP_rel_reflexive with (s:=rs) (d:=rd) (R:=R');
         typeclasses eauto
       | apply fg_equal_rel;
         [ try peel_interp_app ()
         | try lazymatch goal with
               | [ |- ?R (Interp ?ev) (Interp _) ]
                 => reflexivity
               | [ |- ?R (Interp ?ev) ?c ]
                 => let rc := constr:(GallinaReify.Reify c) in
                    unify ev rc; reflexivity
               end ] ]
  end.
Ltac pre_cache_reify _ :=
  cbv [type.app_curried];
  let arg := fresh "arg" in
  intros arg _;
  peel_interp_app ();
  [ lazymatch goal with
    | [ |- ?R (Interp ?ev) _ ]
      => (tryif is_evar ev
           then let ev' := fresh "ev" in set (ev' := ev)
           else idtac)
    end;
    cbv [pointwise_relation]; intros; clear
  | .. ].
Ltac do_inline_cache_reify do_if_not_cached :=
  pre_cache_reify ();
  [ try solve [
          repeat match goal with H := ?e |- _ => is_evar e; subst H end;
          eauto with nocore reify_gen_cache;
          do_if_not_cached ()
        ];
    cache_reify ()
  | .. ].

(* TODO: MOVE ME *)
Ltac vm_compute_lhs_reflexivity :=
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let x := (eval vm_compute in LHS) in
       (* we cannot use the unify tactic, which just gives "not
          unifiable" as the error message, because we want to see the
          terms that were not unifable.  See also
          COQBUG(https://github.com/coq/coq/issues/7291) *)
       let _unify := constr:(ltac:(reflexivity) : RHS = x) in
       vm_cast_no_check (eq_refl x)
  end.

Ltac solve_rop' rop_correct do_if_not_cached machine_wordsizev :=
  eapply rop_correct with (machine_wordsize:=machine_wordsizev);
  [ do_inline_cache_reify do_if_not_cached
  | subst_evars; vm_compute_lhs_reflexivity (* lazy; reflexivity *) ].
Ltac solve_rop_nocache rop_correct :=
  solve_rop' rop_correct ltac:(fun _ => idtac).
Ltac solve_rop rop_correct :=
  solve_rop'
    rop_correct
    ltac:(fun _ => let G := get_goal in fail 2 "Could not find a solution in reify_gen_cache for" G).
Ltac solve_rcarry_mul := solve_rop rcarry_mul_correct.
Ltac solve_rcarry_mul_nocache := solve_rop_nocache rcarry_mul_correct.
Ltac solve_rcarry := solve_rop rcarry_correct.
Ltac solve_radd := solve_rop radd_correct.
Ltac solve_rsub := solve_rop rsub_correct.
Ltac solve_ropp := solve_rop ropp_correct.
Ltac solve_rto_bytes := solve_rop rto_bytes_correct.
Ltac solve_rfrom_bytes := solve_rop rfrom_bytes_correct.
Ltac solve_rencode := solve_rop rencode_correct.
Ltac solve_rrelax := solve_rop rrelax_correct.
Ltac solve_rzero := solve_rop rzero_correct.
Ltac solve_rone := solve_rop rone_correct.

Module PrintingNotations.
  Export ident.
  (*Global Set Printing Width 100000.*)
  Open Scope zrange_scope.
  Notation "'uint256'"
    := (r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%zrange) : zrange_scope.
  Notation "'uint128'"
    := (r[0 ~> 340282366920938463463374607431768211455]%zrange) : zrange_scope.
  Notation "'uint64'"
    := (r[0 ~> 18446744073709551615]) : zrange_scope.
  Notation "'uint32'"
    := (r[0 ~> 4294967295]) : zrange_scope.
  Notation "'bool'"
    := (r[0 ~> 1]%zrange) : zrange_scope.
  Notation "( range )( ls [[ n ]] )"
    := ((#(ident.Z_cast range) @ (ls [[ n ]]))%expr)
         (format "( range )( ls [[ n ]] )") : expr_scope.
  (*Notation "( range )( v )" := (ident.Z_cast range @@ v)%expr : expr_scope.*)
  Notation "x *₂₅₆ y"
    := (#(ident.Z_cast uint256) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x +₂₅₆ y"
    := (#(ident.Z_cast uint256) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "( out_t )( v >> count )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_shiftr @ v @ count))%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v << count )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_shiftl @ v @ count))%expr)
         (format "( out_t )( v  <<  count )") : expr_scope.
  Notation "( range )( v )"
    := ((#(ident.Z_cast range) @ $v)%expr)
         (format "( range )( v )") : expr_scope.
  Notation "( mask & ( out_t )( v ) )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_land @ #(ident.Literal (t:=base.type.Z) mask) @ v))%expr)
         (format "( mask  &  ( out_t )( v ) )")
       : expr_scope.
  Notation "( ( out_t )( v ) & mask )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_land @ v @ #(ident.Literal (t:=base.type.Z) mask)))%expr)
         (format "( ( out_t )( v )  &  mask )")
       : expr_scope.

  Notation "x" := (#(ident.Z_cast _) @ $x)%expr (only printing, at level 9) : expr_scope.
  Notation "x" := (#(ident.Z_cast2 _) @ $x)%expr (only printing, at level 9) : expr_scope.
  Notation "v ₁" := (#ident.fst @ $v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#ident.snd @ $v)%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (#(ident.Z_cast _) @ (#ident.fst @ $v))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#(ident.Z_cast _) @ (#ident.snd @ $v))%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (#(ident.Z_cast _) @ (#ident.fst @ (#(ident.Z_cast2 _) @ $v)))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#(ident.Z_cast _) @ (#ident.snd @ (#(ident.Z_cast2 _) @ $v)))%expr (at level 10, format "v ₂") : expr_scope.
  Notation "x" := (#(ident.Literal x%Z))%expr (only printing) : expr_scope.

  (*Notation "ls [[ n ]]" := (List.nth_default_concrete _ n @@ ls)%expr : expr_scope.
  Notation "( range )( v )" := (ident.Z_cast range @@ v)%expr : expr_scope.
  Notation "x *₁₂₈ y"
    := (ident.Z_cast uint128 @@ (ident.Z.mul (x, y)))%expr (at level 40) : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z_cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z_cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "v ₁" := (ident.fst @@ v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.snd @@ v)%expr (at level 10, format "v ₂") : expr_scope.*)
  (*
  Notation "'ℤ'"
    := BoundsAnalysis.type.Z : zrange_scope.
  Notation "ls [[ n ]]" := (List.nth n @@ ls)%nexpr : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₁₂₈ y"
    := (mul uint64 uint64 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₆₄ y"
    := (mul uint64 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₃₂ y"
    := (mul uint32 uint32 uint32 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₁₂₈₋₁₂₈ y"
    := (mul uint32 uint128 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₆₄₋₆₄ y"
    := (mul uint32 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₆₄ y"
    := (mul uint32 uint32 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x +₁₂₈ y"
    := (add uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄₋₁₂₈₋₁₂₈ y"
    := (add uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂₋₆₄₋₆₄ y"
    := (add uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄ y"
    := (add uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂ y"
    := (add uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₁₂₈ y"
    := (sub uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄₋₁₂₈₋₁₂₈ y"
    := (sub uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂₋₆₄₋₆₄ y"
    := (sub uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄ y"
    := (sub uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂ y"
    := (sub uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x" := ({| BoundsAnalysis.type.value := x |}) (only printing) : nexpr_scope.
  Notation "( out_t )( v >> count )"
    := ((shiftr _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  >>  count )")
       : nexpr_scope.
  Notation "( out_t )( v << count )"
    := ((shiftl _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  <<  count )")
       : nexpr_scope.
  Notation "( ( out_t ) v & mask )"
    := ((land _ out_t mask @@ v)%nexpr)
         (format "( ( out_t ) v  &  mask )")
       : nexpr_scope.
*)
  (* TODO: come up with a better notation for arithmetic with carries
  that still distinguishes it from arithmetic without carries? *)
  Local Notation "'TwoPow256'" := 115792089237316195423570985008687907853269984665640564039457584007913129639936 (only parsing).
  Notation "'ADD_256' ( x ,  y )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'ADD_128' ( x ,  y )" := (#(ident.Z_cast2 (uint128, bool)%core) @ (#ident.Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'ADDC_256' ( x ,  y ,  z )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'ADDC_128' ( x ,  y ,  z )" := (#(ident.Z_cast2 (uint128, bool)%core) @ (#ident.Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'SUB_256' ( x ,  y )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_sub_get_borrow @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'SUBB_256' ( x ,  y , z )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_sub_with_get_borrow @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'ADDM' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (#ident.Z_add_modulo @ x @ y @ z))%expr : expr_scope.
  Notation "'RSHI' ( x ,  y ,  z )" := (#(ident.Z_cast _) @ (#ident.Z_rshi @ _ @ x @ y @ z))%expr : expr_scope.
  Notation "'SELC' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (ident.Z_zselect @ x @ y @ z))%expr : expr_scope.
  Notation "'SELM' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (ident.Z_zselect @ (#(Z_cast bool) @ (#Z_cc_m @ _) @ x) @ y @ z))%expr : expr_scope.
  Notation "'SELL' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (#ident.Z_zselect @ (#(Z_cast bool) @ (#Z_land @ #(ident.Literal (t:=base.type.Z 1)) @ x)) @ y @ z))%expr : expr_scope.
End PrintingNotations.

(*
Notation "a ∈ b" := (ZRange.type.is_bounded_by b%zrange a = true) (at level 10) : type_scope.
Notation Interp := (expr.Interp _).
Notation "'ℤ'" := (type.type_primitive type.Z).
Set Printing Width 70.
Goal False.
  let rop' := Reify (fun v1v2 : Z * Z => fst v1v2 + snd v1v2) in
  pose rop' as rop.
  pose (@Pipeline.BoundsPipeline_full
          false (fun v => Some v) (type.Z * type.Z) type.Z
          rop
          (r[0~>10], r[0~>10])%zrange
          r[0~>20]%zrange
       ) as E.
  simple refine (let Ev := _ in
                 let compiler_outputs_Ev : E = Pipeline.Success Ev := _ in
                 _); [ shelve | .. ]; revgoals.
  clearbody compiler_outputs_Ev.
  refine (let H' :=
              (fun H'' =>
                 @Pipeline.BoundsPipeline_full_correct
                   _ _
                   H'' _ _ _ _ _ _ compiler_outputs_Ev) _
          in _);
    clearbody H'.
  Focus 2.
  { cbv [Pipeline.BoundsPipeline_full] in E.
    remember (Pipeline.PrePipeline rop) as cache eqn:Hcache in (value of E).
    lazy in Hcache.
    subst cache.
    lazy in E.
    subst E Ev; reflexivity.
  } Unfocus.
  cbv [rop] in H'; cbn [expr.Interp expr.interp for_reification.ident.interp] in H'.
(*
  H' : forall arg : type.interp (ℤ * ℤ),
       arg ∈ (r[0 ~> 10], r[0 ~> 10]) ->
       (Interp Ev arg) ∈ r[0 ~> 20] /\
       Interp Ev arg = fst arg + snd arg
*)
Abort.
*)

Module SaturatedSolinas.
  Section MulMod.
    Context (s : Z) (c : list (Z * Z))
            (s_nz : s <> 0) (modulus_nz : s - Associational.eval c <> 0).
    Context (log2base : Z) (log2base_pos : 0 < log2base)
            (n nreductions : nat) (n_nz : n <> 0%nat).

    Let weight := weight log2base 1.
    Let props : @weight_properties weight := wprops log2base 1 ltac:(omega).
    Local Lemma base_nz : 2 ^ log2base <> 0. Proof. auto with zarith. Qed.

    Derive mulmod
           SuchThat (forall (f g : list Z)
                            (Hf : length f = n)
                            (Hg : length g = n),
                        (eval weight n (fst (mulmod f g)) + weight n * (snd (mulmod f g))) mod (s - Associational.eval c)
                        = (eval weight n f * eval weight n g) mod (s - Associational.eval c))
           As eval_mulmod.
    Proof.
      intros.
      rewrite <-Rows.eval_mulmod with (base:=2^log2base) (s:=s) (c:=c) (nreductions:=nreductions) by auto using base_nz.
      eapply f_equal2; [|trivial].
      (* expand_lists (). *) (* uncommenting this line removes some unused multiplications but also inlines a bunch of carry stuff at the end *)
      subst mulmod. reflexivity.
    Qed.
    Definition mulmod' := fun x y => fst (mulmod x y).
  End MulMod.

  Derive mulmod_gen
         SuchThat (forall (log2base s : Z) (c : list (Z * Z)) (n nreductions : nat)
                          (f g : list Z),
                      Interp (t:=reify_type_of mulmod')
                             mulmod_gen s c log2base n nreductions f g
                      = mulmod' s c log2base n nreductions f g)
         As mulmod_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = mulmod' _ _ _ _ _ _ _) => simple apply mulmod_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rmulmod.
    Context (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [1; machine_wordsize]%Z.

    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i). So, to go from
         the n extra limbs we have post-multiplication down to 0, we
         need ceil (n / (n - i)) reductions. *)
    Let nreductions : nat :=
      let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
      Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i))).
    Let relax_zrange := relax_zrange_of_machine_wordsize.
    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

    (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := if (negb (0 <? s - Associational.eval c))%Z
         then Error (Pipeline.Value_not_ltZ "s - Associational.eval c ≤ 0" 0 (s - Associational.eval c))
         else if (s =? 0)%Z
              then Error (Pipeline.Values_not_provably_distinctZ "s ≠ 0" s 0)
              else if (n =? 0)%nat
                   then Error (Pipeline.Values_not_provably_distinctZ "n ≠ 0" n 0)
                   else if (negb (0 <? machine_wordsize))
                        then Error (Pipeline.Value_not_ltZ "0 < machine_wordsize" 0 machine_wordsize)
                        else res.

  Notation BoundsPipelineToStrings prefix name rop in_bounds out_bounds
    := ((prefix ++ name)%string,
        Pipeline.BoundsPipelineToStrings
          true (* static *) prefix (prefix ++ name)%string
          (*false*) false None
          relax_zrange
          rop%Expr in_bounds out_bounds).

  Notation BoundsPipeline_correct in_bounds out_bounds op
    := (fun rv (rop : Expr (reify_type_of op)) Hrop
        => @Pipeline.BoundsPipeline_correct_trans
             (*false*) false None
             relax_zrange
             (relax_zrange_gen_good _)
             _
             rop
             in_bounds
             out_bounds
             op
             Hrop rv)
         (only parsing).

  Definition rmulmod_correct
    := BoundsPipeline_correct
         (Some boundsn, (Some boundsn, tt))
         (Some boundsn)
         (mulmod' s c machine_wordsize n nreductions).

  Definition srmulmod prefix
    := BoundsPipelineToStrings
         prefix "mulmod"
         (mulmod_gen @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify nreductions)
         (Some boundsn, (Some boundsn, tt))
         (Some boundsn).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rmulmod_correctT rv : Prop
      := type_of_strip_3arrow (@rmulmod_correct rv).

    Section for_stringification.
      Definition aggregate_infos {A B C} (ls : list (A * ErrorT B (C * ToString.C.ident_infos))) : ToString.C.ident_infos
        := fold_right
             ToString.C.ident_info_union
             ToString.C.ident_info_empty
             (List.map
                (fun '(_, res) => match res with
                               | Success (_, infos) => infos
                               | Error _ => ToString.C.ident_info_empty
                               end)
                ls).

      Definition extra_synthesis (function_name_prefix : string) (infos : ToString.C.ident_infos)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t
        := let ls_addcarryx := List.flat_map
                                 (fun lg_split:positive => [sraddcarryx machine_wordsize function_name_prefix lg_split; srsubborrowx machine_wordsize function_name_prefix lg_split])
                                 (PositiveSet.elements (ToString.C.addcarryx_lg_splits infos)) in
           let ls_mulx := List.map
                            (fun lg_split:positive => srmulx machine_wordsize function_name_prefix lg_split)
                            (PositiveSet.elements (ToString.C.mulx_lg_splits infos)) in
           let ls_cmov := List.map
                            (fun bitwidth:positive => srcmovznz machine_wordsize function_name_prefix bitwidth)
                            (PositiveSet.elements (ToString.C.cmovznz_bitwidths infos)) in
           let ls := ls_addcarryx ++ ls_mulx ++ ls_cmov in
           let infos := aggregate_infos ls in
           (List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            ToString.C.bitwidths_used infos).

      (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
      Definition Synthesize (function_name_prefix : string) : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := let ls := List.map (fun sr => sr function_name_prefix) [srmulmod] in
           let infos := aggregate_infos ls in
           let '(extra_ls, extra_bit_widths) := extra_synthesis function_name_prefix infos in
           (extra_ls ++ List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            PositiveSet.union extra_bit_widths (ToString.C.bitwidths_used infos)).
    End for_stringification.
  End rmulmod.
End SaturatedSolinas.

Ltac solve_rmulmod := solve_rop SaturatedSolinas.rmulmod_correct.
Ltac solve_rmulmod_nocache := solve_rop_nocache SaturatedSolinas.rmulmod_correct.

Module Import InvertHighLow.
  Section with_wordmax.
    Context (log2wordmax : Z) (consts : list Z).
    Let wordmax := 2 ^ log2wordmax.
    Let half_bits := log2wordmax / 2.
    Let wordmax_half_bits := 2 ^ half_bits.

    Inductive kind_of_constant := upper_half (c : BinInt.Z) | lower_half (c : BinInt.Z).

    Definition constant_to_scalar_single (const x : BinInt.Z) : option kind_of_constant :=
      if x =? (BinInt.Z.shiftr const half_bits)
      then Some (upper_half const)
      else if x =? (BinInt.Z.land const (wordmax_half_bits - 1))
           then Some (lower_half const)
           else None.

    Definition constant_to_scalar (x : BinInt.Z)
      : option kind_of_constant :=
      fold_right (fun c res => match res with
                            | Some s => Some s
                            | None => constant_to_scalar_single c x
                            end) None consts.

    Definition invert_low (v : BinInt.Z) : option BinInt.Z
      := match constant_to_scalar v with
         | Some (lower_half v) => Some v
         | _ => None
         end.

    Definition invert_high (v : BinInt.Z) : option BinInt.Z
      := match constant_to_scalar v with
         | Some (upper_half v) => Some v
         | _ => None
         end.
  End with_wordmax.
End InvertHighLow.

Module BarrettReduction.
  (* TODO : generalize to multi-word and operate on (list Z) instead of T; maybe stop taking ops as context variables *)
  Section Generic.
    Context {T} (rep : T -> Z -> Prop)
            (k : Z) (k_pos : 0 < k)
            (low : T -> Z)
            (low_correct : forall a x, rep a x -> low a = x mod 2 ^ k)
            (shiftr : T -> Z -> T)
            (shiftr_correct : forall a x n,
                rep a x ->
                0 <= n <= k ->
                rep (shiftr a n) (x / 2 ^ n))
            (mul_high : T -> T -> Z -> T)
            (mul_high_correct : forall a b x y x0y1,
                rep a x ->
                rep b y ->
                2 ^ k <= x < 2^(k+1) ->
                0 <= y < 2^(k+1) ->
                x0y1 = x mod 2 ^ k * (y / 2 ^ k) ->
                rep (mul_high a b x0y1) (x * y / 2 ^ k))
            (mul : Z -> Z -> T)
            (mul_correct : forall x y,
                0 <= x < 2^k ->
                0 <= y < 2^k ->
                rep (mul x y) (x * y))
            (sub : T -> T -> T)
            (sub_correct : forall a b x y,
                rep a x ->
                rep b y ->
                0 <= x - y < 2^k * 2^k ->
                rep (sub a b) (x - y))
            (cond_sub1 : T -> Z -> Z)
            (cond_sub1_correct : forall a x y,
                rep a x ->
                0 <= x < 2 * y ->
                0 <= y < 2 ^ k ->
                cond_sub1 a y = if (x <? 2 ^ k) then x else x - y)
            (cond_sub2 : Z -> Z -> Z)
            (cond_sub2_correct : forall x y, cond_sub2 x y = if (x <? y) then x else x - y).
    Context (xt mut : T) (M muSelect: Z).

    Let mu := 2 ^ (2 * k) / M.
    Context x (mu_rep : rep mut mu) (x_rep : rep xt x).
    Context (M_nz : 0 < M)
            (x_range : 0 <= x < M * 2 ^ k)
            (M_range : 2 ^ (k - 1) < M < 2 ^ k)
            (M_good : 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu)
            (muSelect_correct: muSelect = mu mod 2 ^ k * (x / 2 ^ (k - 1) / 2 ^ k)).

    Definition qt :=
      dlet_nd muSelect := muSelect in (* makes sure muSelect is not inlined in the output *)
      dlet_nd q1 := shiftr xt (k - 1) in
      dlet_nd twoq := mul_high mut q1 muSelect in
      shiftr twoq 1.
    Definition reduce  :=
      dlet_nd qt := qt in
      dlet_nd r2 := mul (low qt) M in
      dlet_nd r := sub xt r2 in
      let q3 := cond_sub1 r M in
      cond_sub2 q3 M.

    Lemma looser_bound : M * 2 ^ k < 2 ^ (2*k).
    Proof. clear -M_range M_nz x_range k_pos; rewrite <-Z.add_diag, Z.pow_add_r; nia. Qed.

    Lemma pow_2k_eq : 2 ^ (2*k) = 2 ^ (k - 1) * 2 ^ (k + 1).
    Proof. clear -k_pos; rewrite <-Z.pow_add_r by omega. f_equal; ring. Qed.

    Lemma mu_bounds : 2 ^ k <= mu < 2^(k+1).
    Proof.
      pose proof looser_bound.
      subst mu. split.
      { apply Z.div_le_lower_bound; omega. }
      { apply Z.div_lt_upper_bound; try omega.
        rewrite pow_2k_eq; apply Z.mul_lt_mono_pos_r; auto with zarith. }
    Qed.

    Lemma shiftr_x_bounds : 0 <= x / 2 ^ (k - 1) < 2^(k+1).
    Proof.
      pose proof looser_bound.
      split; [ solve [Z.zero_bounds] | ].
      apply Z.div_lt_upper_bound; auto with zarith.
      rewrite <-pow_2k_eq. omega.
    Qed.
    Hint Resolve shiftr_x_bounds.

    Ltac solve_rep := eauto using shiftr_correct, mul_high_correct, mul_correct, sub_correct with omega.

    Let q := mu * (x / 2 ^ (k - 1)) / 2 ^ (k + 1).

    Lemma q_correct : rep qt q .
    Proof.
      pose proof mu_bounds. cbv [qt]; subst q.
      rewrite Z.pow_add_r, <-Z.div_div by Z.zero_bounds.
      solve_rep.
    Qed.
    Hint Resolve q_correct.

    Lemma x_mod_small : x mod 2 ^ (k - 1) <= M.
    Proof. transitivity (2 ^ (k - 1)); auto with zarith. Qed.
    Hint Resolve x_mod_small.

    Lemma q_bounds : 0 <= q < 2 ^ k.
    Proof.
      pose proof looser_bound. pose proof x_mod_small. pose proof mu_bounds.
      split; subst q; [ solve [Z.zero_bounds] | ].
      edestruct q_nice_strong with (n:=M) as [? Hqnice];
        try rewrite Hqnice; auto; try omega; [ ].
      apply Z.le_lt_trans with (m:= x / M).
      { break_match; omega. }
      { apply Z.div_lt_upper_bound; omega. }
    Qed.

    Lemma two_conditional_subtracts :
      forall a x,
      rep a x ->
      0 <= x < 2 * M ->
      cond_sub2 (cond_sub1 a M) M = cond_sub2 (cond_sub2 x M) M.
    Proof.
      intros.
      erewrite !cond_sub2_correct, !cond_sub1_correct by (eassumption || omega).
      break_match; Z.ltb_to_lt; try lia; discriminate.
    Qed.

    Lemma r_bounds : 0 <= x - q * M < 2 * M.
    Proof.
      pose proof looser_bound. pose proof q_bounds. pose proof x_mod_small.
      subst q mu; split.
      { Z.zero_bounds. apply qn_small; omega. }
      { apply r_small_strong; rewrite ?Z.pow_1_r; auto; omega. }
    Qed.

    Lemma reduce_correct : reduce = x mod M.
    Proof.
      pose proof looser_bound. pose proof r_bounds. pose proof q_bounds.
      assert (2 * M < 2^k * 2^k) by nia.
      rewrite barrett_reduction_small with (k:=k) (m:=mu) (offset:=1) (b:=2) by (auto; omega).
      cbv [reduce Let_In].
      erewrite low_correct by eauto. Z.rewrite_mod_small.
      erewrite two_conditional_subtracts by solve_rep.
      rewrite !cond_sub2_correct.
      subst q; reflexivity.
    Qed.
  End Generic.

  Section BarrettReduction.
    Context (k : Z) (k_bound : 2 <= k).
    Context (M muLow : Z).
    Context (M_pos : 0 < M)
            (muLow_eq : muLow + 2^k = 2^(2*k) / M)
            (muLow_bounds : 0 <= muLow < 2^k)
            (M_bound1 : 2 ^ (k - 1) < M < 2^k)
            (M_bound2: 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - (muLow + 2^k)).

    Context (n:nat) (Hn_nz: n <> 0%nat) (n_le_k : Z.of_nat n <= k).
    Context (nout : nat) (Hnout : nout = 2%nat).
    Let w := weight k 1.
    Local Lemma k_range : 0 < 1 <= k. Proof. omega. Qed.
    Let props : @weight_properties w := wprops k 1 k_range.

    Hint Rewrite Positional.eval_nil Positional.eval_snoc : push_eval.

    Definition low (t : list Z) : Z := nth_default 0 t 0.
    Definition high (t : list Z) : Z := nth_default 0 t 1.
    Definition represents (t : list Z) (x : Z) :=
      t = [x mod 2^k; x / 2^k] /\ 0 <= x < 2^k * 2^k.

    Lemma represents_eq t x :
      represents t x -> t = [x mod 2^k; x / 2^k].
    Proof. cbv [represents]; tauto. Qed.

    Lemma represents_length t x : represents t x -> length t = 2%nat.
    Proof. cbv [represents]; intuition. subst t; reflexivity. Qed.

    Lemma represents_low t x :
      represents t x -> low t = x mod 2^k.
    Proof. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_high t x :
      represents t x -> high t = x / 2^k.
    Proof. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_low_range t x :
      represents t x -> 0 <= x mod 2^k < 2^k.
    Proof. auto with zarith. Qed.

    Lemma represents_high_range t x :
      represents t x -> 0 <= x / 2^k < 2^k.
    Proof.
      destruct 1 as [? [? ?] ]; intros.
      auto using Z.div_lt_upper_bound with zarith.
    Qed.
    Hint Resolve represents_length represents_low_range represents_high_range.

    Lemma represents_range t x :
      represents t x -> 0 <= x < 2^k*2^k.
    Proof. cbv [represents]; tauto. Qed.

    Lemma represents_id x :
      0 <= x < 2^k * 2^k ->
      represents [x mod 2^k; x / 2^k] x.
    Proof.
      intros; cbv [represents]; autorewrite with cancel_pair.
      Z.rewrite_mod_small; tauto.
    Qed.

    Local Ltac push_rep :=
      repeat match goal with
             | H : represents ?t ?x |- _ => unique pose proof (represents_low_range _ _ H)
             | H : represents ?t ?x |- _ => unique pose proof (represents_high_range _ _ H)
             | H : represents ?t ?x |- _ => rewrite (represents_low t x) in * by assumption
             | H : represents ?t ?x |- _ => rewrite (represents_high t x) in * by assumption
             end.

    Definition shiftr (t : list Z) (n : Z) : list Z :=
      [Z.rshi (2^k) (high t) (low t) n; Z.rshi (2^k) 0 (high t) n].

    Lemma shiftr_represents a i x :
      represents a x ->
      0 <= i <= k ->
      represents (shiftr a i) (x / 2 ^ i).
    Proof.
      cbv [shiftr]; intros; push_rep.
      match goal with H : _ |- _ => pose proof (represents_range _ _ H) end.
      assert (0 < 2 ^ i) by auto with zarith.
      assert (x < 2 ^ i * 2 ^ k * 2 ^ k) by nia.
      assert (0 <= x / 2 ^ k / 2 ^ i < 2 ^ k) by
          (split; Z.zero_bounds; auto using Z.div_lt_upper_bound with zarith).
      repeat match goal with
             | _ => rewrite Z.rshi_correct by auto with zarith
             | _ => rewrite <-Z.div_mod''' by auto with zarith
             | _ => progress autorewrite with zsimplify_fast
             | _ => progress Z.rewrite_mod_small
             | |- context [represents [(?a / ?c) mod ?b; ?a / ?b / ?c] ] =>
               rewrite (Z.div_div_comm a b c) by auto with zarith
             | _ => solve [auto using represents_id, Z.div_lt_upper_bound with zarith lia]
             end.
    Qed.

    Context (Hw : forall i, w i = (2 ^ k) ^ Z.of_nat i).
    Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r.

    Definition wideadd t1 t2 := fst (Rows.add w 2 t1 t2).
    (* TODO: use this definition once issue #352 is resolved *)
    (* Definition widesub t1 t2 := fst (Rows.sub w 2 t1 t2). *)
    Definition widesub (t1 t2 : list Z) :=
      let t1_0 := hd 0 t1 in
      let t1_1 := hd 0 (tl t1) in
      let t2_0 := hd 0 t2 in
      let t2_1 := hd 0 (tl t2) in
      dlet_nd x0 := Z.sub_get_borrow_full (2^k) t1_0 t2_0 in
      dlet_nd x1 := Z.sub_with_get_borrow_full (2^k) (snd x0) t1_1 t2_1 in
      [fst x0; fst x1].
    Definition widemul := BaseConversion.widemul_inlined k n nout.

    Lemma partition_represents x :
      0 <= x < 2^k*2^k ->
      represents (Rows.partition w 2 x) x.
    Proof.
      intros; cbn. change_weight.
      Z.rewrite_mod_small.
      autorewrite with zsimplify_fast.
      auto using represents_id.
    Qed.

    Lemma eval_represents t x :
      represents t x -> eval w 2 t = x.
    Proof.
      intros; rewrite (represents_eq t x) by assumption.
      cbn. change_weight; push_rep.
      autorewrite with zsimplify. reflexivity.
    Qed.

    Ltac wide_op partitions_pf :=
      repeat match goal with
             | _ => rewrite partitions_pf by eauto
             | _ => rewrite partitions_pf by auto with zarith
             | _ => erewrite eval_represents by eauto
             | _ => solve [auto using partition_represents, represents_id]
             end.

    Lemma wideadd_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x + y < 2^k*2^k ->
      represents (wideadd t1 t2) (x + y).
    Proof. intros; cbv [wideadd]. wide_op Rows.add_partitions. Qed.

    Lemma widesub_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x - y < 2^k*2^k ->
      represents (widesub t1 t2) (x - y).
    Proof.
      intros; cbv [widesub Let_In].
      rewrite (represents_eq t1 x) by assumption.
      rewrite (represents_eq t2 y) by assumption.
      cbn [hd tl].
      autorewrite with to_div_mod.
      pull_Zmod.
      match goal with |- represents [?m; ?d] ?x =>
                      replace d with (x / 2 ^ k); [solve [auto using represents_id] |] end.
      rewrite <-(Z.mod_small ((x - y) / 2^k) (2^k)) by (split; try apply Z.div_lt_upper_bound; Z.zero_bounds).
      f_equal.
      transitivity ((x mod 2^k - y mod 2^k + 2^k * (x / 2 ^ k) - 2^k * (y / 2^k)) / 2^k). {
        rewrite (Z.div_mod x (2^k)) at 1 by auto using Z.pow_nonzero with omega.
        rewrite (Z.div_mod y (2^k)) at 1 by auto using Z.pow_nonzero with omega.
        f_equal. ring. }
      autorewrite with zsimplify.
      ring.
    Qed.
    (* Works with Rows.sub-based widesub definition
    Proof. intros; cbv [widesub]. wide_op Rows.sub_partitions. Qed.
    *)

    Lemma widemul_represents x y :
      0 <= x < 2^k ->
      0 <= y < 2^k ->
      represents (widemul x y) (x * y).
    Proof.
      intros; cbv [widemul].
      assert (0 <= x * y < 2^k*2^k) by auto with zarith.
      wide_op BaseConversion.widemul_correct.
    Qed.

    Definition mul_high (a b : list Z) a0b1 : list Z :=
      dlet_nd a0b0 := widemul (low a) (low b) in
      dlet_nd ab := wideadd [high a0b0; high b] [low b; 0] in
      wideadd ab [a0b1; 0].

    Lemma mul_high_idea d a b a0 a1 b0 b1 :
      d <> 0 ->
      a = d * a1 + a0 ->
      b = d * b1 + b0 ->
      (a * b) / d = a0 * b0 / d + d * a1 * b1 + a1 * b0 + a0 * b1.
    Proof.
      intros. subst a b. autorewrite with push_Zmul.
      ring_simplify_subterms. rewrite Z.pow_2_r.
      rewrite Z.div_add_exact by (push_Zmod; autorewrite with zsimplify; omega).
      repeat match goal with
             | |- context [d * ?a * ?b * ?c] =>
               replace (d * a * b * c) with (a * b * c * d) by ring
             | |- context [d * ?a * ?b] =>
               replace (d * a * b) with (a * b * d) by ring
             end.
      rewrite !Z.div_add by omega.
      autorewrite with zsimplify.
      rewrite (Z.mul_comm a0 b0).
      ring_simplify. ring.
    Qed.

    Lemma represents_trans t x y:
      represents t y -> y = x ->
      represents t x.
    Proof. congruence. Qed.

    Lemma represents_add x y :
      0 <= x < 2 ^ k ->
      0 <= y < 2 ^ k ->
      represents [x;y] (x + 2^k*y).
    Proof.
      intros; cbv [represents]; autorewrite with zsimplify.
      repeat split; (reflexivity || nia).
    Qed.

    Lemma represents_small x :
      0 <= x < 2^k ->
      represents [x; 0] x.
    Proof.
      intros.
      eapply represents_trans.
      { eauto using represents_add with zarith. }
      { ring. }
    Qed.

    Lemma mul_high_represents a b x y a0b1 :
      represents a x ->
      represents b y ->
      2^k <= x < 2^(k+1) ->
      0 <= y < 2^(k+1) ->
      a0b1 = x mod 2^k * (y / 2^k) ->
      represents (mul_high a b a0b1) ((x * y) / 2^k).
    Proof.
      cbv [mul_high Let_In]; rewrite Z.pow_add_r, Z.pow_1_r by omega; intros.
      assert (4 <= 2 ^ k) by (transitivity (Z.pow 2 2); auto with zarith).
      assert (0 <= x * y / 2^k < 2^k*2^k) by (Z.div_mod_to_quot_rem; nia).

      rewrite mul_high_idea with (a:=x) (b:=y) (a0 := low a) (a1 := high a) (b0 := low b) (b1 := high b) in *
        by (push_rep; Z.div_mod_to_quot_rem; lia).

      push_rep. subst a0b1.
      assert (y / 2 ^ k < 2) by (apply Z.div_lt_upper_bound; omega).
      replace (x / 2 ^ k) with 1 in * by (rewrite Z.div_between_1; lia).
      autorewrite with zsimplify_fast in *.

      eapply represents_trans.
      { repeat (apply wideadd_represents;
                [ | apply represents_small; Z.div_mod_to_quot_rem; nia| ]).
        erewrite represents_high; [ | apply widemul_represents; solve [ auto with zarith ] ].
        { apply represents_add; try reflexivity; solve [auto with zarith]. }
        { match goal with H : 0 <= ?x + ?y < ?z |- 0 <= ?x < ?z =>
                          split; [ solve [Z.zero_bounds] | ];
                            eapply Z.le_lt_trans with (m:= x + y); nia
          end. }
        { omega. } }
      { ring. }
    Qed.

    Definition cond_sub1 (a : list Z) y : Z :=
      dlet_nd maybe_y := Z.zselect (Z.cc_l (high a)) 0 y in
      dlet_nd diff := Z.sub_get_borrow_full (2^k) (low a) maybe_y in
      fst diff.

    Lemma cc_l_only_bit : forall x s, 0 <= x < 2 * s -> Z.cc_l (x / s) = 0 <-> x < s.
    Proof.
      cbv [Z.cc_l]; intros.
      rewrite Z.div_between_0_if by omega.
      break_match; Z.ltb_to_lt; Z.rewrite_mod_small; omega.
    Qed.

    Lemma cond_sub1_correct a x y :
      represents a x ->
      0 <= x < 2 * y ->
      0 <= y < 2 ^ k ->
      cond_sub1 a y = if (x <? 2 ^ k) then x else x - y.
    Proof.
      intros; cbv [cond_sub1 Let_In]. rewrite Z.zselect_correct. push_rep.
      break_match; Z.ltb_to_lt; rewrite cc_l_only_bit in *; try omega;
        autorewrite with zsimplify_fast to_div_mod pull_Zmod; auto with zarith.
    Qed.

    Definition cond_sub2 x y := Z.add_modulo x 0 y.
    Lemma cond_sub2_correct x y :
      cond_sub2 x y = if (x <? y) then x else x - y.
    Proof.
      cbv [cond_sub2]. rewrite Z.add_modulo_correct.
      autorewrite with zsimplify_fast. break_match; Z.ltb_to_lt; omega.
    Qed.

    Section Defn.
      Context (xLow xHigh : Z) (xLow_bounds : 0 <= xLow < 2^k) (xHigh_bounds : 0 <= xHigh < M).
      Let xt := [xLow; xHigh].
      Let x := xLow + 2^k * xHigh.

      Lemma x_rep : represents xt x.
      Proof. cbv [represents]; subst xt x; autorewrite with cancel_pair zsimplify; repeat split; nia. Qed.

      Lemma x_bounds : 0 <= x < M * 2 ^ k.
      Proof. subst x; nia. Qed.

      Definition muSelect := Z.zselect (Z.cc_m (2 ^ k) xHigh) 0 muLow.

      Local Hint Resolve Z.div_nonneg Z.div_lt_upper_bound.
      Local Hint Resolve shiftr_represents mul_high_represents widemul_represents widesub_represents
            cond_sub1_correct cond_sub2_correct represents_low represents_add.

      Lemma muSelect_correct :
        muSelect = (2 ^ (2 * k) / M) mod 2 ^ k * ((x / 2 ^ (k - 1)) / 2 ^ k).
      Proof.
        (* assertions to help arith tactics *)
        pose proof x_bounds.
        assert (2^k * M < 2 ^ (2*k)) by (rewrite <-Z.add_diag, Z.pow_add_r; nia).
        assert (0 <= x / (2 ^ k * (2 ^ k / 2)) < 2) by (Z.div_mod_to_quot_rem; auto with nia).
        assert (0 < 2 ^ k / 2) by Z.zero_bounds.
        assert (2 ^ (k - 1) <> 0) by auto with zarith.
        assert (2 < 2 ^ k) by (eapply Z.le_lt_trans with (m:=2 ^ 1); auto with zarith).

        cbv [muSelect]. rewrite <-muLow_eq.
        rewrite Z.zselect_correct, Z.cc_m_eq by auto with zarith.
        replace xHigh with (x / 2^k) by (subst x; autorewrite with zsimplify; lia).
        autorewrite with pull_Zdiv push_Zpow.
        rewrite (Z.mul_comm (2 ^ k / 2)).
        break_match; [ ring | ].
        match goal with H : 0 <= ?x < 2, H' : ?x <> 0 |- _ => replace x with 1 by omega end.
        autorewrite with zsimplify; reflexivity.
      Qed.

      Lemma mu_rep : represents [muLow; 1] (2 ^ (2 * k) / M).
      Proof. rewrite <-muLow_eq. eapply represents_trans; auto with zarith. Qed.

      Derive barrett_reduce
             SuchThat (barrett_reduce = x mod M)
             As barrett_reduce_correct.
      Proof.
        erewrite <-reduce_correct with (rep:=represents) (muSelect:=muSelect) (k0:=k) (mut:=[muLow;1]) (xt0:=xt)
          by (auto using x_bounds, muSelect_correct, x_rep, mu_rep; omega).
        subst barrett_reduce. reflexivity.
      Qed.
    End Defn.
  End BarrettReduction.

  (* all the list operations from for_reification.ident *)
  Strategy 100 [length seq repeat combine map flat_map partition app rev fold_right update_nth nth_default ].
  Strategy -10 [barrett_reduce reduce].

  Derive barrett_red_gen
         SuchThat (forall (k M muLow : Z)
                          (n nout: nat)
                          (xLow xHigh : Z),
                      Interp (t:=reify_type_of barrett_reduce)
                             barrett_red_gen k M muLow n nout xLow xHigh
                      = barrett_reduce k M muLow n nout xLow xHigh)
         As barrett_red_gen_correct.
  Proof. Time cache_reify (). Time Qed. (* Now only takes ~5-10 s, because we set up [Strategy] commands correctly *)
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = barrett_reduce _ _ _ _ _ _ _) => simple apply barrett_red_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rbarrett_red.
    Context (M : Z)
            (machine_wordsize : Z).

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
    Let mu := (2 ^ (2 * machine_wordsize)) / M.
    Let muLow := mu mod (2 ^ machine_wordsize).
    Let consts_list := [M; muLow].

    Definition relax_zrange_of_machine_wordsize'
      := relax_zrange_gen [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    (* TODO: This is a special-case hack to let the prefancy pass have enough bounds information. *)
    Definition relax_zrange_of_machine_wordsize r : option zrange :=
      if (lower r =? 0) && (upper r =? 2)
      then Some r
      else relax_zrange_of_machine_wordsize' r.

    Lemma relax_zrange_good (r r' z : zrange) :
      (z <=? r)%zrange = true ->
      relax_zrange_of_machine_wordsize r = Some r' -> (z <=? r')%zrange = true.
    Proof.
      cbv [relax_zrange_of_machine_wordsize]; break_match; [congruence|].
      eauto using relax_zrange_gen_good.
    Qed.

    Local Arguments relax_zrange_of_machine_wordsize / .

    Let relax_zrange := relax_zrange_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := if (mu / (2 ^ machine_wordsize) =? 0)
         then Error (Pipeline.Values_not_provably_distinctZ "mu / 2 ^ k ≠ 0" (mu / 2 ^ machine_wordsize) 0)
         else if (machine_wordsize <? 2)
              then Error (Pipeline.Value_not_leZ "~ (2 <=k)" 2 machine_wordsize)
              else if (negb (Z.log2 M + 1 =? machine_wordsize))
                   then Error
                          (Pipeline.Values_not_provably_equalZ "log2(M)+1 != k" (Z.log2 M + 1) machine_wordsize)
                   else if (2 ^ (machine_wordsize + 1) - mu <? 2 * (2 ^ (2 * machine_wordsize) mod M))
                        then Error
                               (Pipeline.Value_not_leZ "~ (2 * (2 ^ (2*k) mod M) <= 2^(k + 1) - mu)"
                                                       (2 * (2 ^ (2*machine_wordsize) mod M))
                                                       (2^(machine_wordsize + 1) - mu))
                        else res.

    Let fancy_args
      := (Some {| Pipeline.invert_low log2wordsize := invert_low log2wordsize consts_list;
                  Pipeline.invert_high log2wordsize := invert_high log2wordsize consts_list |}).

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *) fancy_args
               relax_zrange
               relax_zrange_good
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Definition rbarrett_red_correct
      := BoundsPipeline_correct
           (bound, (bound, tt))
           bound
           (barrett_reduce machine_wordsize M muLow 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rbarrett_red_correctT rv : Prop
      := type_of_strip_3arrow (@rbarrett_red_correct rv).
  End rbarrett_red.
End BarrettReduction.

Ltac solve_rbarrett_red := solve_rop BarrettReduction.rbarrett_red_correct.
Ltac solve_rbarrett_red_nocache := solve_rop_nocache BarrettReduction.rbarrett_red_correct.

Module MontgomeryReduction.
  Section MontRed'.
    Context (N R N' R' : Z).
    Context (HN_range : 0 <= N < R) (HN'_range : 0 <= N' < R) (HN_nz : N <> 0) (R_gt_1 : R > 1)
            (N'_good : Z.equiv_modulo R (N*N') (-1)) (R'_good: Z.equiv_modulo N (R*R') 1).

    Context (Zlog2R : Z) .
    Let w : nat -> Z := weight Zlog2R 1.
    Context (n:nat) (Hn_nz: n <> 0%nat) (n_good : Zlog2R mod Z.of_nat n = 0).
    Context (R_big_enough : n <= Zlog2R)
            (R_two_pow : 2^Zlog2R = R).
    Let w_mul : nat -> Z := weight (Zlog2R / n) 1.
    Context (nout : nat) (Hnout : nout = 2%nat).

    Definition montred' (lo_hi : (Z * Z)) :=
      dlet_nd y := nth_default 0 (BaseConversion.widemul_inlined Zlog2R n nout (fst lo_hi) N') 0  in
      dlet_nd t1_t2 := (BaseConversion.widemul_inlined_reverse Zlog2R n nout N y) in
      dlet_nd sum_carry := Rows.add (weight Zlog2R 1) 2 [fst lo_hi; snd lo_hi] t1_t2 in
      dlet_nd y' := Z.zselect (snd sum_carry) 0 N in
      dlet_nd lo''_carry := Z.sub_get_borrow_full R (nth_default 0 (fst sum_carry) 1) y' in
      Z.add_modulo (fst lo''_carry) 0 N.

    Local Lemma Hw : forall i, w i = R ^ Z.of_nat i.
    Proof.
      clear -R_big_enough R_two_pow; cbv [w weight]; intro.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, R_two_pow by omega; reflexivity.
    Qed.

    Local Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r, ?Z.pow_1_l in *.
    Local Ltac solve_range :=
      repeat match goal with
             | _ => progress change_weight
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(omega))
             | |- 0 <= _ => progress Z.zero_bounds
             | |- 0 <= _ * _ < _ * _ =>
               split; [ solve [Z.zero_bounds] | apply Z.mul_lt_mono_nonneg; omega ]
             | _ => solve [auto]
             | _ => omega
             end.

    Local Lemma eval2 x y : eval w 2 [x;y] = x + R * y.
    Proof. cbn. change_weight. ring. Qed.

    Hint Rewrite BaseConversion.widemul_inlined_reverse_correct BaseConversion.widemul_inlined_correct
         using (autorewrite with widemul push_nth_default; solve [solve_range]) : widemul.

    Lemma montred'_eq lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R):
      montred' lo_hi = reduce_via_partial N R N' T.
    Proof.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi.
      assert (0 <= (T mod R) * N' < w 2) by  (solve_range).

      autorewrite with widemul.
      rewrite Rows.add_partitions, Rows.add_div by (distr_length; apply wprops; omega).
      rewrite R_two_pow.
      cbv [Rows.partition seq]. rewrite !eval2.
      autorewrite with push_nth_default push_map.
      autorewrite with to_div_mod. rewrite ?Z.zselect_correct, ?Z.add_modulo_correct.
      change_weight.

      (* pull out value before last modular reduction *)
      match goal with |- (if (?n <=? ?x)%Z then ?x - ?n else ?x) = (if (?n <=? ?y) then ?y - ?n else ?y)%Z =>
                      let P := fresh "H" in assert (x = y) as P; [|rewrite P; reflexivity] end.

      autorewrite with zsimplify.
      rewrite (Z.mul_comm (((T mod R) * N') mod R) N) in *.
      break_match; try reflexivity; Z.ltb_to_lt; rewrite Z.div_small_iff in * by omega;
        repeat match goal with
               | _ => progress autorewrite with zsimplify_fast
               | |- context [?x mod (R * R)] =>
                 unique pose proof (Z.mod_pos_bound x (R * R));
                   try rewrite (Z.mod_small x (R * R)) in * by Z.rewrite_mod_small_solver
               | _ => omega
               | _ => progress Z.rewrite_mod_small
               end.
    Qed.

    Lemma montred'_correct lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R): montred' lo_hi = (T * R') mod N.
    Proof.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; omega).
      apply reduce_via_partial_in_range; omega.
    Qed.
  End MontRed'.

  Derive montred_gen
         SuchThat (forall (N R N' : Z)
                          (Zlog2R : Z)
                          (n nout: nat)
                          (lo_hi : Z * Z),
                      Interp (t:=reify_type_of montred')
                             montred_gen N R N' Zlog2R n nout lo_hi
                      = montred' N R N' Zlog2R n nout lo_hi)
         As montred_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Module Export ReifyHints.
    Global Hint Extern 1 (_ = montred' _ _ _ _ _ _ _) => simple apply montred_gen_correct : reify_gen_cache.
  End ReifyHints.

  Section rmontred.
    Context (N R N' : Z)
            (machine_wordsize : Z).

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
    Let consts_list := [N; N'].

    Definition relax_zrange_of_machine_wordsize
      := relax_zrange_gen [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    Local Arguments relax_zrange_of_machine_wordsize / .

    Let relax_zrange := relax_zrange_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := res. (* TODO: this should actually check stuff that corresponds with preconditions of montred'_correct *)

    Let fancy_args
      := (Some {| Pipeline.invert_low log2wordsize := invert_low log2wordsize consts_list;
                  Pipeline.invert_high log2wordsize := invert_high log2wordsize consts_list |}).

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *) fancy_args
               relax_zrange
               (relax_zrange_gen_good _)
               _
               rop
               in_bounds
               out_bounds
               op
               Hrop rv)
           (only parsing).

    Definition rmontred_correct
      := BoundsPipeline_correct
           ((bound, bound), tt)
           bound
           (montred' N R N' (Z.log2 R) 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rmontred_correctT rv : Prop
      := type_of_strip_3arrow (@rmontred_correct rv).
  End rmontred.
End MontgomeryReduction.

Ltac solve_rmontred := solve_rop MontgomeryReduction.rmontred_correct.
Ltac solve_rmontred_nocache := solve_rop_nocache MontgomeryReduction.rmontred_correct.


Time Compute
     (Pipeline.BoundsPipeline
        true None (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Time Compute
     (Pipeline.BoundsPipeline
        true None (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (scmul (weight 51 1) 5) in
              exact r)
               (None, (Some (repeat (@None _) 5), tt))
               ZRange.type.base.option.None).

Compute
     (Pipeline.BoundsPipeline
        true None (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (fun f => carry_mulmod 51 1 (2^255) [(1,19)] 5 (seq 0 5 ++ [0; 1])%list%nat f f) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_mulx_u64"
        true None (relax_zrange_gen [64; 128])
        ltac:(let r := Reify (mulx 64) in
              exact r)
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u64"
        true None (relax_zrange_gen [1; 64; 128])
        ltac:(let r := Reify (addcarryx 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u51"
        true None (relax_zrange_gen [1; 64; 128])
        ltac:(let r := Reify (addcarryx 51) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u64"
        true None (relax_zrange_gen [1; 64; 128])
        ltac:(let r := Reify (subborrowx 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).
Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u51"
        true None (relax_zrange_gen [1; 64; 128])
        ltac:(let r := Reify (subborrowx 51) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_cmovznz64"
        true None (relax_zrange_gen [1; 64; 128])
        ltac:(let r := Reify (cmovznz 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange).
