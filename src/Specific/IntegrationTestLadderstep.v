Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Curves.Montgomery.XZ.
Import ListNotations.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.xzladderstep (F m) F.add F.sub F.mul.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists (@M.xzladderstep _ (proj1_sig add_sig) (proj1_sig sub_sig) (fun x y => proj1_sig carry_sig (proj1_sig mul_sig x y))).
    intros.
    cbv [FMxzladderstep M.xzladderstep].
    destruct Q, Q'; cbv [map map' fst snd Let_In eval].
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.

  Definition adjust_tuple2_tuple2_sig {A P Q}
             (v : { a : { a : tuple (tuple A 2) 2 | (P (fst (fst a)) /\ P (snd (fst a))) /\ (P (fst (snd a)) /\ P (snd (snd a))) }
                  | Q (exist _ _ (proj1 (proj1 (proj2_sig a))),
                       exist _ _ (proj2 (proj1 (proj2_sig a))),
                       (exist _ _ (proj1 (proj2 (proj2_sig a))),
                        exist _ _ (proj2 (proj2 (proj2_sig a))))) })
    : { a : tuple (tuple (@sig A P) 2) 2 | Q a }.
  Proof.
    eexists.
    exact (proj2_sig v).
  Defined.

  (** TODO MOVE ME *)
  (** The [eexists_sig_etransitivity] tactic takes a goal of the form
      [{ a | f a = b }], and splits it into two goals, [?b' = b] and
      [{ a | f a = ?b' }], where [?b'] is a fresh evar. *)
  Definition sig_eq_trans_exist1 {A B} (f : A -> B)
             (b b' : B)
             (pf : b' = b)
             (y : { a : A | f a = b' })
    : { a : A | f a = b }
    := let 'exist a p := y in exist _ a (eq_trans p pf).
  Ltac eexists_sig_etransitivity :=
    lazymatch goal with
    | [ |- { a : ?A | @?f a = ?b } ]
      => let lem := open_constr:(@sig_eq_trans_exist1 A _ f b _) in
         simple refine (lem _ _)
    end.
  Definition sig_eq_trans_rewrite_fun_exist1 {A B} (f f' : A -> B)
             (b : B)
             (pf : forall a, f' a = f a)
             (y : { a : A | f' a = b })
    : { a : A | f a = b }
    := let 'exist a p := y in exist _ a (eq_trans (eq_sym (pf a)) p).
  Ltac eexists_sig_etransitivity_for_rewrite_fun :=
    lazymatch goal with
    | [ |- { a : ?A | @?f a = ?b } ]
      => let lem := open_constr:(@sig_eq_trans_rewrite_fun_exist1 A _ f _ b) in
         simple refine (lem _ _); cbv beta
    end.

  (** TODO MOVE ME *)
  (* TODO : change this to field once field isomorphism happens *)
  Definition xzladderstep :
    { xzladderstep : feBW -> feBW -> feBW * feBW -> feBW * feBW -> feBW * feBW * (feBW * feBW)
    | forall a24 x1 Q Q', Tuple.map (n:=2) (Tuple.map (n:=2) phi) (xzladderstep a24 x1 Q Q') = FMxzladderstep (phi a24) (phi x1) (Tuple.map (n:=2) phi Q) (Tuple.map (n:=2) phi Q') }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b c d, ?phi (f a b c d) = @?rhs a b c d } ]
      => apply lift4_sig with (P:=fun a b c d f => phi f = rhs a b c d)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- !(Tuple.map_map (B.Positional.Fdecode wt) (BoundedWordToZ sz bitwidth bounds)).
    rewrite <- (proj2_sig Mxzladderstep_sig).
    apply f_equal.
    cbv [proj1_sig]; cbv [Mxzladderstep_sig].
    context_to_dlet_in_rhs (@M.xzladderstep _ _ _ _).
    set (k := @M.xzladderstep _ _ _ _); context_to_dlet_in_rhs k; subst k.
    cbv [M.xzladderstep].
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b carry_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b carry_sig)
    end.
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b mul_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b mul_sig)
    end.
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b add_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b add_sig)
    end.
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b sub_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b sub_sig)
    end.
    cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig carry_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz].
    reflexivity.
    eexists_sig_etransitivity_for_rewrite_fun.
    { intro; cbv beta.
      subst feBW.
      set_evars.
      do 2 lazymatch goal with
           | [ |- context[Tuple.map (n:=?n) (fun x => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=n) f g : pointwise_relation _ eq _ _)
           end.
      subst_evars.
      reflexivity. }
    cbv beta.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    apply adjust_tuple2_tuple2_sig.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*
    Time Glue.refine_to_reflective_glue.
    Time ReflectiveTactics.refine_with_pipeline_correct.
    { Time ReflectiveTactics.do_reify. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
    { Time SubstLet.subst_let; clear; abstract vm_cast_no_check (eq_refl true). }
    { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
    { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
     *)
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

Time End BoundedField25p5.
