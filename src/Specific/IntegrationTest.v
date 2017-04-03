Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
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

  Ltac eexists_sig_etransitivity :=
    lazymatch goal with
    | [ |- { a : ?A | @?f a = ?b } ]
      => let k := fresh in
         let k' := fresh in
         simple refine (let k : { a | a = b } := _ in
                        let k' : { a : A | f a = let (p1, _) := k in p1 } := _ in
                        exist _ (proj1_sig k') (eq_trans (proj2_sig k') (proj2_sig k)));
         [ eexists | subst k ];
         cbv beta iota
    end.

  (** TODO MOVE ME *)
  Ltac save_state_and_back_to_sig :=
    [> reflexivity
    | lazymatch goal with
      | [ |- { c | _ = ?f ?x } ]
        => let rexpr := head x in
           let rexprZ := fresh "rexprZ" in
           set (rexprZ := rexpr)
      end ].
  (** TODO: Move me *)
  Definition sig_f_equal {T A B} (f : A -> B) {x y : T -> A}
             (p : { t : T | x t = y t })
    : { t : T | f (x t) = f (y t) }
    := exist _ (proj1_sig p) (f_equal f (proj2_sig p)).
  (* TODO : change this to field once field isomorphism happens *)
  Definition add :
    { add : feBW -> feBW -> feBW
    | forall a b, phi (add a b) = F.add (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    cbv beta iota delta [proj1_sig add_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ.
    cbn beta iota delta [fst snd] in carry_addZ.
    reflexivity.

    Require Import AdmitAxiom.
    all:exfalso; clear; admit. Grab Existential Variables. all:exfalso; clear; admit. Notation "!!!!!!!!" := (False_rect _ _). Notation "!!!!!!!!" := (False_ind _ _). Show Proof. Time Defined.

    apply sig_f_equal.
    (* jgross start here! *)
    Definition sig_sig_assoc {A} {P : A -> Prop} {Q}
      : { a : A | P a /\ Q a } -> { ap : { a : A | P a } | Q (proj1_sig ap) }
      := fun apq => exist _ (exist _ (proj1_sig apq) (proj1 (proj2_sig apq))) (proj2 (proj2_sig apq)).
    Ltac sig_sig_assoc :=
      lazymatch goal with
      | [ |- { a : ?A | ?P } ]
        => let P'' := fresh a in
           let P' := fresh P'' in
           let term := constr:(fun a : A => match P with
                                            | P' => ltac:(let v := (eval cbv [P'] in P') in
                                                          lazymatch eval pattern (proj1_sig a) in v with
                                                          | ?P _ => exact P
                                                          end)
                                            end) in
           let Q := lazymatch (eval cbv beta in term) with fun _ => ?term => term end in
           apply (@sig_sig_assoc _ _ Q)
      end.
    Ltac evar_exists :=
      let T := fresh in
      let e := fresh in
      evar (T : Type); evar (e : T); subst T; exists e.
    Ltac reassoc_sig_and_eexists :=
      cbv [BoundedWordToZ]; sig_sig_assoc;
      evar_exists.
    Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Curry.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tuple.

    Ltac do_curry :=
      lazymatch goal with
      | [ |- _ /\ ?BWtoZ ?f_bw = ?f_Z ]
        => let f_bw := head f_bw in
           let f_Z := head f_Z in
           change_with_curried f_Z;
           change_with_curried f_bw
      end.
    reassoc_sig_and_eexists.
    do_curry.
    Ltac split_BoundedWordToZ :=
      (** first revert the context definition which is an evar named [f]
      in the docs above, so that it becomes evar 1 (for
      [instantiate]), and so that [make_evar_for_first_projection]
      works *)
      lazymatch goal with
      | [ |- _ /\ map wordToZ ?f = _ ]
        => revert f
      end;
      repeat match goal with
             | [ |- context[map wordToZ (proj1_sig ?x)] ]
               => is_var x;
                  first [ clearbody x; fail 1
                        | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                        instantiate (1:=ltac:(destruct x)); destruct x ]
             end;
      cbv beta iota; intro; (* put [f] back in the context so that [cbn] doesn't remove this let-in *)
      cbn [proj1_sig].
    split_BoundedWordToZ.
    Glue.zrange_to_reflective_goal.

      make_evar_for_first_projection.

    Require Import Glue AdmitAxiom.


      := fun x => exist _ (exist _ (proj1_sig x)
    Set Ltac Profiling.
    do_curry.
    check_split_BoundedWordToZ_precondition;
      (** first revert the context definition which is an evar named [f]
      in the docs above, so that it becomes evar 1 (for
      [instantiate]), and so that [make_evar_for_first_projection]
      works *)
      lazymatch goal with
      | [ |- BoundedWordToZ _ _ _ ?f = _ ]
        => revert f
      end;
      repeat match goal with
             | [ |- context[BoundedWordToZ _ _ _ ?x] ]
               => is_var x;
                    first [ clearbody x; fail 1
                          | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                          instantiate (1:=ltac:(destruct x)); destruct x ]
             end;
      cbv beta iota; intro; (* put [f] back in the context so that [cbn] doesn't remove this let-in *)
        unfold BoundedWordToZ; cbn [proj1_sig].

      Require Import Coq.ZArith.ZArith.
      Require Import Crypto.Util.LetIn.
      lazymatch goal with
      | [ |- ?map (@proj1_sig _ ?P ?f) = _ ]
        => let f1 := fresh f in
           let f2 := fresh f in
           let pf := fresh in
           revert f; refine (_ : let f := exist P _ _ in _);
             intro f;
             pose (proj1_sig f) as f1;
             pose (proj2_sig f : P f1) as f2;
             change f with (exist P f1 f2);
             subst f; cbn [proj1_sig proj2_sig] in f1, f2 |- *; revert f2;
               instantiate (1:=ltac:(refine (proj1 _)));
               lazymatch goal with
               | [ |- let f' := ?e in ?B ]
                 => let A := type of e in
                    simple refine (let pf : A /\ B := _ in _);
                      [ | intro f2; let unused := constr:(eq_refl : f2 = proj1 pf) in exact (proj2 pf) ]
               end
      end.
      Show Proof.
      Opaque carry_sig.
      all:exfalso; clear; admit. Grab Existential Variables. all:exfalso; clear; admit. Notation "!!!!!!!!" := (False_rect _ _). Notation "!!!!!!!!" := (False_ind _ _). Show Proof. Time Defined.
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

End BoundedField25p5.
