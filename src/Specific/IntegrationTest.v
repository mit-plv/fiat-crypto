Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Import ListNotations.

Require Import Crypto.Reflection.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
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

  Let feZ : Type := tuple Z 10.
  Let feW : Type := tuple word32 10.
  Let feBW : Type := BoundedWord 10 32 bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

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

  (** TODO MOVE ME *)
  (** This tactic moves to the context any [dlet x := y in ...] on the
      rhs of a goal of the form [{ a | lhs = rhs }]. *)
  Ltac sig_dlet_in_rhs_to_context :=
    repeat lazymatch goal with
           | [ |- { a | _ = @Let_In ?A ?B ?x ?P } ]
             => let v := fresh "x" in
                pose x as v;
                replace (@Let_In A B x P) with (P v) by (clear; abstract (subst v; cbv [Let_In]; reflexivity));
                cbv beta
           end.
  (** This tactic creates a [dlet x := f in rhs] in the rhs of a goal
      of the form [lhs = rhs]. *)
  Ltac context_to_dlet_in_rhs f :=
    lazymatch goal with
    | [ |- ?LHS = ?RHS ]
      => let RHS' := lazymatch (eval pattern f in RHS) with
                     | ?RHS _ => RHS
                     end in
         let x := fresh "x" in
         transitivity (dlet x := f in RHS' x);
         [ | clear; abstract (cbv [Let_In]; reflexivity) ]
    end.
  (* TODO : change this to field once field isomorphism happens *)
  Definition mul :
    { mul : feBW -> feBW -> feBW
    | forall a b, phi (mul a b) = F.mul (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- (proj2_sig mul_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_mulZ := fun a b => proj1_sig carry_sig (proj1_sig mul_sig a b)).
    change (proj1_sig carry_sig (proj1_sig mul_sig ?a ?b)) with (carry_mulZ a b).
    context_to_dlet_in_rhs carry_mulZ.
    cbv beta iota delta [carry_mulZ proj1_sig mul_sig carry_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz].
    reflexivity.
    sig_dlet_in_rhs_to_context.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    (* jgross start here! *)
    (*Set Ltac Profiling.*)
    Time refine_reflectively. (* Finished transaction in 19.348 secs (19.284u,0.036s) (successful) *)
    (*Show Ltac Profile.*)
    (* total time:     19.632s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
─ReflectiveTactics.do_reflective_pipelin  -0.0%  96.2%       1   18.884s
─ReflectiveTactics.solve_side_conditions   1.2%  96.1%       1   18.860s
─ReflectiveTactics.do_reify ------------  27.7%  44.0%       1    8.640s
─ReflectiveTactics.abstract_vm_compute_r  12.3%  13.9%       2    2.024s
─ReflectiveTactics.abstract_vm_compute_r   8.9%  12.2%       2    1.576s
─Reify_rhs_gen -------------------------   0.8%  11.7%       1    2.300s
─ReflectiveTactics.renamify_rhs --------  10.4%  11.5%       1    2.260s
─ReflectiveTactics.abstract_rhs --------   4.6%   5.8%       1    1.148s
─clear (var_list) ----------------------   5.2%   5.2%      57    0.184s
─eexact --------------------------------   4.1%   4.1%      68    0.028s
─prove_interp_compile_correct ----------   0.0%   3.4%       1    0.664s
─ReflectiveTactics.abstract_cbv_interp_r   2.7%   3.3%       1    0.648s
─unify (constr) (constr) ---------------   3.2%   3.2%       6    0.248s
─rewrite ?EtaInterp.InterpExprEta ------   3.1%   3.1%       1    0.612s
─ReflectiveTactics.abstract_cbv_rhs ----   2.0%   2.7%       1    0.532s
─Glue.refine_to_reflective_glue --------   0.0%   2.2%       1    0.436s
─rewrite H -----------------------------   2.1%   2.1%       1    0.420s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
 ├─ReflectiveTactics.do_reflective_pipel  -0.0%  96.2%       1   18.884s
 │└ReflectiveTactics.solve_side_conditio   1.2%  96.1%       1   18.860s
 │ ├─ReflectiveTactics.do_reify --------  27.7%  44.0%       1    8.640s
 │ │ ├─Reify_rhs_gen -------------------   0.8%  11.7%       1    2.300s
 │ │ │ ├─prove_interp_compile_correct --   0.0%   3.4%       1    0.664s
 │ │ │ │└rewrite ?EtaInterp.InterpExprEt   3.1%   3.1%       1    0.612s
 │ │ │ └─rewrite H ---------------------   2.1%   2.1%       1    0.420s
 │ │ └─eexact --------------------------   4.1%   4.1%      68    0.028s
 │ ├─ReflectiveTactics.abstract_vm_compu  12.3%  13.9%       2    2.024s
 │ ├─ReflectiveTactics.abstract_vm_compu   8.9%  12.2%       2    1.576s
 │ ├─ReflectiveTactics.renamify_rhs ----  10.4%  11.5%       1    2.260s
 │ ├─ReflectiveTactics.abstract_rhs ----   4.6%   5.8%       1    1.148s
 │ ├─ReflectiveTactics.abstract_cbv_inte   2.7%   3.3%       1    0.648s
 │ └─ReflectiveTactics.abstract_cbv_rhs    2.0%   2.7%       1    0.532s
 └─Glue.refine_to_reflective_glue ------   0.0%   2.2%       1    0.436s
*)
  Time Defined. (* Finished transaction in 10.167 secs (10.123u,0.023s) (successful) *)

End BoundedField25p5.
