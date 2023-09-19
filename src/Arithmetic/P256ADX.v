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

Lemma eval_repeat_0 n : forall bound, eval bound (repeat 0 n) = 0.
Proof. induction n; trivial; cbn [repeat]; intros; rewrite eval_cons, IHn; lia. Qed.

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
    (eval bound xs <= (2^256+2^129-2^96)*(2^128-1) -> 0 <= z < 2^256 + p256)).
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
  assert (0 <= (p256+2^129-2^97)*(2^128-1) + (x + 2^64 * x')*p256 < 2^128*(p256+p256)) by (cbv [p256]; Z.div_mod_to_equations; lia).
  assert (0 <= (2^256+2^129-2^96)*(2^128-1) + (x + 2^64 * x')*p256 < 2^128*(p256+2^256)) by (cbv [p256]; Z.div_mod_to_equations; lia).
  lia.
Qed.

Definition p256_mul x y :=
  dlet a := mul bound (firstn 2 x) y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := add_mul bound a (skipn 2 x) y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  let a := condsub bound a (encode bound 4 p256) in
  firstn 4 a.

Require Import AdmitAxiom.
Lemma p256_mul_correct x y
  (Hlx : (2 <= length x)%nat) :
  eval bound (p256_mul x y) mod p256 =
  eval bound x * eval bound y mod p256.
Proof.
  pose proof firstn_skipn 2 x as H; eapply (f_equal (eval bound)) in H.
  rewrite eval_app, firstn_length_le in H by trivial.

  cbv beta delta [p256_mul Let_In].
  set (skipn 2 x) as xhi in *.
  set (firstn 2 x) as xlo in *.
  change (stream.skipn 2 bound) with bound in *.
  change (Z.pos (weight bound 2)) with (2^128) in *.

  repeat match goal with
  | |- context G [let x := ?v in @?C x] =>
      let x := fresh x in
      set v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g';
      let H := fresh "H" x in
      pose proof eq_refl : x = v as H; clearbody x
  end.

  eapply (f_equal (eval bound)) in Hy0.
  rewrite (eval_mul (Z.to_pos (2^64))) in Hy0.
  change (fun _ => _) with bound in *.

  pose proof two_steps_of_p256_montgomery_reduction_correct y0 as HH.
  rewrite <-Hy1, Hy0 in HH; clear Hy1; cbv zeta in HH; case HH as [Hy1 HH'].
  clear HH'.
  
  eapply (f_equal (eval bound)) in Hy2.
  rewrite (eval_add_mul (Z.to_pos (2^64))) in Hy2.
  change (fun _ => _) with bound in *.

  pose proof two_steps_of_p256_montgomery_reduction_correct y2 as HH.
  rewrite <-Hy3, Hy2 in HH; clear Hy3; cbv zeta in HH; case HH as [Hy3 HH'].
  clear HH'.

  assert (HH : (2 ^ 256 * eval bound y3) mod p256 =
    ((2^128 * eval bound y1) mod p256 + 2^128 * eval bound xhi * eval bound y) mod p256).
  { clear -Hy3; cbv [p256] in *; Z.div_mod_to_equations; nia. }
  rewrite Hy1 in HH; clear Hy1 Hy3; autorewrite with pull_Zmod in HH.
  replace (eval bound xlo * eval bound y + 2 ^ 128 * eval bound xhi * eval bound y)
    with (eval bound x * eval bound y) in HH by nia.

  rewrite condsub_correct in Ha.
  assert (eval bound a mod p256 = eval bound x * eval bound y mod p256) by admit.
  assert (0 <= eval bound a < p256) by admit.

  pose proof eval_firstn_encode bound 4 4 (eval bound a) ltac:(lia).
  change (Z.pos (weight bound 4)) with (2^256) in *.
  rewrite (Z.mod_small _ (2^256)) in * by (cbv [p256] in *; lia).

  all : admit.
Qed.
Print Assumptions p256_mul_correct.

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

Definition sqr4 xs :=
  let x0 := nth_default 0 xs 0 in
  let x1 := nth_default 0 xs 1 in
  let x2 := nth_default 0 xs 2 in
  let x3 := nth_default 0 xs 3 in
  dlet acc := product_scan_ bound [] [(0,0); (0,0); (0, 0); (x1, x2)] 0 0 0 in
  dlet acc := product_scan_ bound acc [(0, 0); (x0, x1); (x0, x2); (x0, x3); (x1, x3); (x2, x3)] 0 0 0 in
  dlet acc := add_ bound 0 acc acc in
  dlet acc := firstn 8 (add_ bound 0 acc (diagonal (2^64) [(x0,x0); (x1, x1); (x2, x2); (x3, x3)]))
  in acc.

Lemma eval_sqr4' x0 x1 x2 x3 (xs:=[x0;x1;x2;x3]) :
  eval bound (sqr4 xs) mod weight bound 8 =
  eval bound xs * eval bound xs mod 2^512.
Proof.
  cbv beta delta [sqr4 Let_In].
  repeat (progress change (?f (let x := ?v in @?C x) mod ?X = ?R) with (let x := v in f (C x) mod X = R); cbv beta; intros).
  cbv in x, x4, x5, x6; subst x x4 x5 x6.
  subst x10.
  rewrite eval_firstn, eval_add_, Z.add_0_l, (eval_diagonal (Z.to_pos (2^64))).
  f_equal.
  subst x9.
  rewrite eval_add_, Z.add_0_l, Z.add_diag.
  subst x8.
  rewrite eval_product_scan_.
  subst x7.
  rewrite eval_product_scan_, ?eval_nil, ?Z.add_0_l.
  cbn [map uncurry]; rewrite ?Z.mul_0_l, ?Z.add_0_r.
  subst xs.
  rewrite ?eval_cons, ?eval_nil;
  progress repeat change (stream.tl ?b) with b;
  progress repeat change (Z.pos (stream.hd bound)) with (2^64);
  progress repeat change (stream.hd ?b) with (b O); cbv beta.
  nia.
Qed.

Definition p256_sqr a :=
  dlet a := sqr4 a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a' := firstn 4 (condsub bound a (encode bound 4 p256)) in
  a'.
