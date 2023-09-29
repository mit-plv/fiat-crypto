Require Import Coq.ZArith.ZArith Coq.micromega.Lia. Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Require Import Coq.Lists.List. Local Open Scope list_scope. Import ListNotations.
Require Import Crypto.Util.Tactics.

Require Import Crypto.Arithmetic.WeightStream.
Import WeightStream.Saturated.
Import Crypto.Util.ZUtil.Definitions.
Import Crypto.Util.LetIn.

Definition p256 := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff%Z.
Definition p3 :=   0xffffffff00000001%Z.

Definition n : nat := 4.
Definition bound (_ : nat) : positive := Z.to_pos (2^64).

Definition two_steps_of_p256_montgomery_reduction xs :=
  let x := hd 0 xs in
  let y := hd 0 (tl xs) in
  let (x't, h) := Z.mul_split (2^64) (2^32) x in
  let (x', c) := Z.add_with_get_carry_full (2^64) 0 y x't in
  product_scan_ bound (tl (tl xs)) ([(2^32, x'); (p3, x); (p3, x')] ++ repeat (0,0) (length xs - 5)) h c 0.

Lemma two_steps_of_p256_montgomery_reduction_correct xs :
  let z := eval bound (two_steps_of_p256_montgomery_reduction xs) in
  2^128 * z mod p256 = eval bound xs mod p256 /\ (
    0 <= eval bound xs -> 0 <= hd 0 xs < 2^64 -> 0 <= hd 0 (tl xs) < 2^64  ->
    (eval bound xs <= ( p256+2^129-2^97)*(2^128-1) -> 0 <= z <  p256 + p256) /\
    (eval bound xs <= (2^256+2^129-2^96)*(2^128-1) -> 0 <= z < 2^256 + p256) /\
    (eval bound xs <= p256*p256 -> 0 <= z < 2^128 * p256)).
Proof.
  cbv [Let_In two_steps_of_p256_montgomery_reduction].
  pose proof eval_hd_tl bound xs; pose proof eval_hd_tl bound (tl xs).
  set (hd 0 xs) as x in *; set (hd 0 (tl xs)) as y in *.
  rewrite ?eval_cons in *.
  repeat change (stream.tl ?b) with b in *.
  repeat change (stream.hd _) with (2^64)%positive in *.
  edestruct Z.mul_split as (tl, th) eqn:Et.
  rewrite Z.mul_split_correct in Et; symmetry in Et; Prod.inversion_pair.
  edestruct Z.add_with_get_carry_full as (x', c) eqn:Ex'.
  rewrite Z.add_with_get_carry_full_correct in Ex'; symmetry in Ex'; Prod.inversion_pair; rewrite ?Z.add_0_l in *.
  rewrite eval_product_scan_.
  set (_ + _) as z.
  assert (2 ^ 128 * z = eval bound xs + (x + 2 ^ 64 * x') * p256) as Hz; [|clearbody z].
  { subst z.
    enough (eval bound (map _ _) = 2^32 * x' + 2^64 * p3 * x + 2^128 * p3*x') as ->.
    { cbv [p256 p3]; Z.div_mod_to_equations; nia. }
    rewrite map_app, map_repeat, eval_app, eval_repeat_0.
    cbn [List.length List.map uncurry eval PreExtra.list_rect_fbb_b list_rect].
    change (stream.hd _) with (2^64)%positive.
    Z.div_mod_to_equations; nia. }
  split; intros.
  { symmetry; erewrite <-Z.mod_add with (b := x + 2^64*x') by (cbv; lia); symmetry; f_equal; lia. }
  assert (0 <= 2^128 * z) by (rewrite Hz; cbv [p256]; Z.div_mod_to_equations; lia).
  assert (0 <= 2^384 -2^352 +2^320 + (x + 2^64 * x')*p256 < 2^128*(p256+p256)) by (cbv [p256]; Z.div_mod_to_equations; lia).
  assert (0 <= (2^256+2^129-2^96)*(2^128-1) + (x + 2^64 * x')*p256 < 2^128*(p256+2^256)) by (cbv [p256]; Z.div_mod_to_equations; lia).
  assert (0 <= p256*p256 + (x + 2^64 * x')*p256 < 2^128*2^128*p256) by (cbv [p256]; Z.div_mod_to_equations; lia).
  lia.
Qed.

Definition p256_mul' x y :=
  dlet xlo := firstn 2 x in
  dlet xhi := skipn 2 x in
  dlet a := mul bound (firstn 2 x) y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := add_mul bound a xhi y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := condsub bound a (encode bound 4 p256) in
  firstn 4 a.

Definition p256_mul x y :=
  if negb ((0 <=? eval bound x) && (eval bound x <? 2^256)) then nil else
  if negb ((0 <=? eval bound y) && (eval bound y <? 2^256)) then nil else
  dlet xlo := firstn 2 x in
  dlet xhi := skipn 2 x in
  if negb ((0 <=? eval bound xlo) && (eval bound xlo <? 2^128)) then nil else
  dlet a := mul bound (firstn 2 x) y in
  if negb ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64)) then nil else
  if negb ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64)) then nil else
  dlet a := two_steps_of_p256_montgomery_reduction a in
  if negb ((0 <=? eval bound xhi) && (eval bound xhi <? 2^128)) then nil else
  dlet a := add_mul bound a xhi y in
  if negb ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64)) then nil else
  if negb ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64)) then nil else
  dlet a := two_steps_of_p256_montgomery_reduction a in
  if negb (eval bound a <? (weight bound (Nat.max (Datatypes.length a) (Datatypes.length (encode bound 4 p256))))) then nil else
  dlet a := condsub bound a (encode bound 4 p256) in
  if negb (4 <=? Z.of_nat (Datatypes.length a)) then nil else
  if negb (isbounded bound a) then nil else
  firstn 4 a.

(*
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WeightStream.
Require Crypto.PushButtonSynthesis.Primitives.
Require Crypto.Stringification.C.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.DebugMonad.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Import
  AbstractInterpretation.Compilers
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Existing Instance default_translate_to_fancy.
Local Existing Instances
      Primitives.Options.default_PipelineOptions
      Primitives.Options.default_PipelineToStringOptions
      Primitives.Options.default_SynthesisOptions
| 100.
Local Instance : unfold_value_barrier_opt := true.

Module debugging_scheduled_saturated_arithmetic.
  Section __.
    Import Stringification.C.
    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    (* We split these off to make things a bit easier on typeclass resolution and speed things up. *)
    Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : static_opt := true.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : should_split_mul_opt := false.
    Local Instance : should_split_multiret_opt := false.
    Local Instance : widen_carry_opt := false.
    Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)

    (** ======= these are the changable parameters ====== *)
    Let machine_wordsize := 64.
    (** ================================================= *)
    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    Let n : nat := 4.
    Let boundsn : list (ZRange.type.option.interp base.type.Z) := repeat (Some r[0 ~> (2^machine_wordsize - 1)]%zrange) n.

    Import IdentifiersBasicGENERATED.Compilers.
    Import API.Compilers.
    Import APINotations.Compilers.

    Import WeightStream.Saturated.

Time Redirect "log"
     Compute
     let e :=
       (ltac:(
       let e := constr:(p256_mul) in
       let e := eval cbv delta [two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
       let r := Reify e in
       exact r))
                in
     Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
     (
     Pipeline.BoundsPipelineToString
        "fiat_" "p256_mul"
        false (* subst01 *)
        false (* inline *)
        possible_values
        machine_wordsize
        e
               (fun _ _ => []) (* comment *)
               (Some boundsn, (Some boundsn, tt))
               (Some boundsn)
               (None, (None, tt))
               (None)
      : Pipeline.ErrorT _).
*)

Ltac lift_let :=
  match goal with
  | |- context G [let x := ?v in @?C x] =>
      let x := fresh x in
      set v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g'
  | d := context G [let x := ?v in @?C x] |- _ =>
      let x := fresh x in
      set v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g' in (value of d)
  | H: context G [let x := ?v in @?C x] |- _ =>
      let x := fresh x in
      set v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g' in H
  end.

Require Import AdmitAxiom.
Lemma p256_mul_correct x y
  (Hy : 0 <= eval bound y < p256)
  (Hlx : (2 <= length x)%nat)
  (z := p256_mul x y)
  (Hcompiles : z <> nil) :
  2^256 * eval bound z mod p256 = eval bound x * eval bound y mod p256 /\
  (0 <= eval bound x < p256 -> 0 <= eval bound z < p256).
Proof.
  pose proof firstn_skipn 2 x as H; eapply (f_equal (eval bound)) in H.
  rewrite eval_app, firstn_length_le in H by trivial.

  cbv beta delta [p256_mul Let_In] in *.
  set (skipn 2 x) as xhi in *.
  set (firstn 2 x) as xlo in *.
  change (stream.skipn 2 bound) with bound in *.
  change (Z.pos (weight bound 2)) with (2^128) in *.

  lift_let. lift_let.
  subst y0. subst y1.
  repeat lift_let.

  repeat match goal with
         | x := ?v |- _ =>
             let H := fresh "H" x in
             pose proof eq_refl x : x = v as H;
             move H before x;
             clearbody x
         end.

  eapply (f_equal (eval bound)) in Hy0.
  rewrite (eval_mul (Z.to_pos (2^64))) in Hy0.
  change (fun _ => _) with bound in *.
  
  repeat match goal with
  | H : context G [match ?x with _ => _ end] |- _ =>
      destruct x eqn:? in *; cbn [negb] in H; [congruence|]
  end.
  rewrite Bool.negb_false_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in *.

  pose proof two_steps_of_p256_montgomery_reduction_correct y0 as HH.
  rewrite <-Hy1, Hy0 in HH; clear Hy1; cbv zeta in HH; case HH as [Hy1 HH'1].

  do 3 specialize (HH'1 ltac:(cbv [p256] in *; nia)).
  apply proj1 in HH'1.
  do 1 specialize (HH'1 ltac:(cbv [p256] in *; nia)).

  eapply (f_equal (eval bound)) in Hy2.
  rewrite (eval_add_mul (Z.to_pos (2^64))) in Hy2.
  change (fun _ => _) with bound in *.

  pose proof two_steps_of_p256_montgomery_reduction_correct y2 as HH.
  pose proof Hy3 as Hy3'.
  rewrite <-Hy3, Hy2 in HH; clear Hy3; cbv zeta in HH; case HH as [Hy3 HH'2].

  assert (HH : (2 ^ 256 * eval bound y3) mod p256 =
    ((2^128 * eval bound y1) mod p256 + 2^128 * eval bound xhi * eval bound y) mod p256).
  { clear -Hy3; cbv [p256] in *; Z.div_mod_to_equations; nia. }
  rewrite Hy1 in HH; clear Hy1 Hy3; autorewrite with pull_Zmod in HH.
  replace (eval bound xlo * eval bound y + 2 ^ 128 * eval bound xhi * eval bound y)
    with (eval bound x * eval bound y) in HH by nia.

  eapply (f_equal (eval bound)) in Hy4.
  rewrite eval_condsub, eval_encode, Z.mod_small in Hy4.
  2: { cbv. intuition congruence. }
  2: { trivial. }
  2: { cbv. inversion 1. }
  destruct (isbounded_correct bound y4) in *; [|discriminate].

  do 3 specialize (HH'2 ltac:(cbv [p256] in *; nia)).

  eapply (f_equal (eval bound)) in Hz.
  rewrite <-e, eval_firstn_encode in Hz.
  2: { lia. }
  change (Z.pos (weight bound 4)) with (2^256) in *.
  rewrite Z.mod_small in Hz.
  2: {
    apply proj2, proj1 in HH'2.
    do 1 specialize (HH'2 ltac:(cbv [p256] in *; nia)).
    destruct (Z.leb_spec p256 (eval bound y3)) in *; simpl Z.b2z in *; cbv [p256] in *; lia. }

  rewrite Hz, Hy4.
  split.
  { Modulo.push_Zmod; Modulo.pull_Zmod.
    rewrite Z.mul_0_r, Z.sub_0_r; trivial. }

  intros.
  destruct (Z.leb_spec p256 (eval bound y3)) in *; simpl Z.b2z in *; cbv [p256] in *; nia.
Qed.

(*
Print Assumptions p256_mul_correct.
Closed under the global context
*)

Definition diagonal b (pps : list (Z * Z)) :=
  flat_map (fun '(x, y) =>
    let '(lo, hi) := Z.mul_split b x y in
    [lo; hi]
  ) pps.

Lemma eval_diagonal (b : positive) pps :
  eval (fun _ => b) (diagonal b pps) =
  eval (fun _ => Pos.mul b b) (map (uncurry Z.mul) pps).
Proof.
  induction pps as [|[x y] ]; [trivial|].
  cbn [diagonal flat_map map fst snd uncurry].
  progress change (flat_map _ ?xs) with (diagonal (Z.pos b) xs).
  rewrite Z.mul_split_correct.
  cbn [app]; rewrite ?eval_cons, ?eval_nil; cbn [length].
  progress repeat change (stream.tl ?b) with b.
  progress repeat change (stream.hd ?b) with (b O); cbv beta.
  Z.div_mod_to_equations; nia.
Qed.

Definition sqr4 xs : list Z :=
  let x0 := nth_default 0 xs 0 in
  let x1 := nth_default 0 xs 1 in
  let x2 := nth_default 0 xs 2 in
  let x3 := nth_default 0 xs 3 in
  dlet acc := product_scan_ bound [] [(0,0); (0,0); (0, 0); (x1, x2)] 0 0 0 in
  dlet acc := product_scan_ bound acc [(0, 0); (x0, x1); (x0, x2); (x0, x3); (x1, x3); (x2, x3)] 0 0 0 in
  dlet acc := add_ bound 0 acc acc in
  dlet acc := fst (add bound 0 acc (diagonal (2^64) [(x0,x0); (x1, x1); (x2, x2); (x3, x3)]))
  in acc.

Lemma eval_sqr4' x0 x1 x2 x3 (xs:=[x0;x1;x2;x3]) :
  0 <= eval bound xs < 2^256 -> eval bound (sqr4 xs) = eval bound xs * eval bound xs.
Proof.
  cbv beta delta [sqr4 Let_In].
  repeat (progress change (?f (let x := ?v in @?C x) = ?R) with (let x := v in f (C x) = R); cbv beta; intros).
  cbv in x, x4, x5, x6; subst x x4 x5 x6.
  subst x10.
  rewrite add_correct; cbn [fst]. change (Nat.max _ _) with 8%nat.
  rewrite Z.add_0_l, (eval_diagonal (Z.to_pos (2^64))).
  subst x9.
  rewrite eval_encode, eval_add_, Z.add_0_l, Z.add_diag.
  subst x8.
  rewrite eval_product_scan_.
  subst x7.
  rewrite eval_product_scan_, ?eval_nil, ?Z.add_0_l.
  cbn [map uncurry]; rewrite ?Z.mul_0_l, ?Z.add_0_r.
  subst xs.
  rewrite ?eval_cons, ?eval_nil in *;
  progress repeat change (stream.tl ?b) with b in *;
  progress repeat change (Z.pos (stream.hd bound)) with (2^64) in *;
  progress repeat change (stream.hd ?b) with (b O) in *; cbv beta in *.
  change (Z.pos (weight bound 8)) with (2^512) in *.
  rewrite Z.mod_small; nia.
Qed.

Lemma eval_sqr4 xs :
  length xs = 4%nat ->
  0 <= eval bound xs < 2 ^ 256 ->
  eval bound (sqr4 xs) = eval bound xs * eval bound xs.
Proof. intros H *. do 5 (destruct xs; try inversion H). apply eval_sqr4'. Qed.

Definition p256_sqr' a :=
  dlet a := sqr4 a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := condsub bound a (encode bound 4 p256) in
  dlet a := firstn 4 a in
  a.

Definition p256_sqr a :=
  if negb (4 =? Z.of_nat (Datatypes.length a)) then nil else
  dlet a := sqr4 a in
  if negb ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64)) then nil else
  if negb ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64)) then nil else
  dlet a := two_steps_of_p256_montgomery_reduction a in
  if negb ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64)) then nil else
  if negb ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64)) then nil else
  dlet a := two_steps_of_p256_montgomery_reduction a in
  if negb (eval bound a <? (weight bound (Nat.max (Datatypes.length a) (Datatypes.length (encode bound 4 p256))))) then nil else
  dlet a := condsub bound a (encode bound 4 p256) in
  if negb (4 <=? Z.of_nat (Datatypes.length a)) then nil else
  if negb (isbounded bound a) then nil else
  dlet a := firstn 4 a in
  a.

Lemma p256_sqr_correct x
  (Hy : 0 <= eval bound x < p256)
  (z := p256_sqr x)
  (Hcompiles : z <> nil) :
  2^256 * eval bound z mod p256 = eval bound x * eval bound x mod p256 /\
  (0 <= eval bound x < p256 -> 0 <= eval bound z < p256).
Proof.
  cbv beta delta [p256_sqr Let_In] in *.
  repeat lift_let.

  repeat match reverse goal with
         | x := ?v |- _ =>
             let H := fresh "H" x in
             pose proof eq_refl x : x = v as H;
             move H before x;
             clearbody x
         end.
  clear; exfalso; admit. Qed.
  
  repeat match goal with
  | H : context G [match ?x with _ => _ end] |- _ =>
      destruct x eqn:? in *; cbn [negb] in H; [congruence|]
  end.

  rewrite Bool.negb_false_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in *.

  eapply (f_equal (eval bound)) in Hy0.
  rewrite eval_sqr4 in Hy0 by (cbv [p256] in *; lia).

  pose proof two_steps_of_p256_montgomery_reduction_correct y as HH.
  rewrite <-Hy1, Hy0 in HH; clear Hy1; cbv zeta in HH; case HH as [Hy1 HH'1].
  do 3 specialize (HH'1 ltac:(cbv [p256] in *; nia)).
  apply proj2, proj2 in HH'1.
  do 1 specialize (HH'1 ltac:(cbv [p256] in *; nia)).

  pose proof two_steps_of_p256_montgomery_reduction_correct y0 as HH.
  pose proof Hy2 as Hy2'.
  rewrite <-Hy2 in HH; clear Hy2; cbv zeta in HH; case HH as [Hy2 HH'2].

  do 3 specialize (HH'2 ltac:(cbv [p256] in *; nia)).
  apply proj1 in HH'2.
  do 1 specialize (HH'2 ltac:(cbv [p256] in *; nia)).

  eapply (f_equal (eval bound)) in Hy3.
  rewrite eval_condsub, eval_encode, Z.mod_small in Hy3.
  2: { cbv. intuition congruence. }
  2: { trivial. }
  2: { cbv. inversion 1. }
  destruct (isbounded_correct bound y2) in *; [|discriminate].

  subst y3.
  eapply (f_equal (eval bound)) in Hz.
  rewrite <-e, eval_firstn_encode in Hz.
  2: { lia. }
  change (Z.pos (weight bound 4)) with (2^256) in *.
  rewrite Z.mod_small in Hz.
  2: { destruct (Z.leb_spec p256 (eval bound y1)) in *; simpl Z.b2z in *; cbv [p256] in *; lia. }

  rewrite Hz, Hy3.
  split.
  { Modulo.push_Zmod; Modulo.pull_Zmod.
    rewrite Z.mul_0_r, Z.sub_0_r.
    replace (2 ^ 256 * eval bound y1)
    with (2 ^ 128 * (2 ^ 128 * eval bound y1)) by lia.
    rewrite <-Z.mul_mod_idemp_r by (cbv; lia).
    rewrite Hy2.
    rewrite Z.mul_mod_idemp_r by (cbv; lia).
    trivial.
  }

  intros.
  destruct (Z.leb_spec p256 (eval bound y1)) in *; simpl Z.b2z in *; cbv [p256] in *; nia.
Qed.
