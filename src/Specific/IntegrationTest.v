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

  (*(** TODO MOVE ME *)
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
    := exist _ (proj1_sig p) (f_equal f (proj2_sig p)).*)
  (* TODO : change this to field once field isomorphism happens *)
  Definition add :
    { add : feBW -> feBW -> feBW
    | forall a b, phi (add a b) = F.add (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros. eexists ?[add]. all:cbv [phi].
    (*eexists_sig_etransitivity. all:cbv [phi].*)
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    let carry_addZ' := (eval cbv beta iota delta [carry_addZ proj1_sig add_sig carry_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ) in
    let carry_addZ'' := fresh carry_addZ in
    rename carry_addZ into carry_addZ'';
      pose carry_addZ' as carry_addZ;
      replace carry_addZ'' with carry_addZ by abstract (cbv beta iota delta [carry_addZ'' proj1_sig add_sig carry_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz]; reflexivity);
      clear carry_addZ''.
    apply f_equal.
    (* jgross start here! *)
    Set Ltac Profiling.
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

End BoundedField25p5.
