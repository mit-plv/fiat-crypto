(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Crypto.Algebra.Nsatz.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.Sorting.Mergesort Coq.Structures.Orders.
Require Import Coq.Sorting.Permutation.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition. (* For MontgomeryReduction *)
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs. (* For MontgomeryReduction *)
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Opp.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Sorting.
Require Import Crypto.Util.ZUtil.CC Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Zselect Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.SetEvars.
Import ListNotations. Local Open Scope Z_scope.

Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).

  Lemma eval_nil : eval nil = 0.
  Proof. trivial.                                             Qed.
  Lemma eval_cons p q : eval (p::q) = fst p * snd p + eval q.
  Proof. trivial.                                             Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof. induction p; rewrite <-?List.app_comm_cons;
           rewrite ?eval_nil, ?eval_cons; nsatz.              Qed.

  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof. induction p; push; nsatz.                            Qed.
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; cbv [mul]; push; nsatz.                 Qed.
  Hint Rewrite eval_mul : push_eval.

  Definition square (p:list (Z*Z)) : list (Z*Z) :=
    list_rect
      _
      nil
      (fun t ts acc
       => (dlet two_t2 := 2 * snd t in
               (fst t * fst t, snd t * snd t)
                 :: (map (fun t'
                          => (fst t * fst t', two_t2 * snd t'))
                         ts))
            ++ acc)
      p.
  Lemma eval_square p : eval (square p) = eval p * eval p.
  Proof. induction p; cbv [square list_rect Let_In]; push; nsatz. Qed.
  Hint Rewrite eval_square : push_eval.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, -snd cx)) p.
  Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
  Proof. induction p; cbv [negate_snd]; push; nsatz.          Qed.
  Hint Rewrite eval_negate_snd : push_eval.

  Example base10_2digit_mul (a0:Z) (a1:Z) (b0:Z) (b1:Z) :
    {ab| eval ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)]}.
    eexists ?[ab].
    (* Goal: eval ?ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)] *)
    rewrite <-eval_mul.
    (* Goal: eval ?ab = eval (mul [(10,a1);(1,a0)] [(10,b1);(1,b0)]) *)
    cbv -[Z.mul eval]; cbn -[eval].
    (* Goal: eval ?ab = eval [(100,(a1*b1));(10,a1*b0);(10,a0*b1);(1,a0*b0)]%RT *)
    trivial.                                              Defined.

  Lemma eval_partition f (p:list (Z*Z)) :
    eval (snd (partition f p)) + eval (fst (partition f p)) = eval p.
  Proof. induction p; cbn [partition]; eta_expand; break_match; cbn [fst snd]; push; nsatz. Qed.
  Hint Rewrite eval_partition : push_eval.

  Lemma eval_partition' f (p:list (Z*Z)) :
    eval (fst (partition f p)) + eval (snd (partition f p)) = eval p.
  Proof. rewrite Z.add_comm, eval_partition; reflexivity. Qed.
  Hint Rewrite eval_partition' : push_eval.

  Lemma eval_fst_partition f p : eval (fst (partition f p)) = eval p - eval (snd (partition f p)).
  Proof. rewrite <- (eval_partition f p); nsatz. Qed.
  Lemma eval_snd_partition f p : eval (snd (partition f p)) = eval p - eval (fst (partition f p)).
  Proof. rewrite <- (eval_partition f p); nsatz. Qed.

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Lemma eval_snd_split s p (s_nz:s<>0) :
    s * eval (snd (split s p)) = eval (fst (partition (fun t => fst t mod s =? 0) p)).
  Proof using Type. cbv [split Let_In]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.
  Lemma eval_split s p (s_nz:s<>0) :
    eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
  Proof using Type. rewrite eval_snd_split, eval_fst_partition by assumption; cbv [split Let_In]; cbn [fst snd]; omega. Qed.

  Lemma reduction_rule' b s c (modulus_nz:s-c<>0) :
    (s * b) mod (s - c) = (c * b) mod (s - c).
  Proof using Type. replace (s * b) with ((c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof using Type. apply Z.add_mod_Proper; [ reflexivity | apply reduction_rule', modulus_nz ]. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
  Hint Rewrite eval_reduce : push_eval.

  Lemma eval_reduce_adjusted s c p w c' (s_nz:s<>0) (modulus_nz:s-eval c<>0)
        (w_mod:w mod s = 0) (w_nz:w <> 0) (Hc' : eval c' = (w / s) * eval c) :
    eval (reduce w c' p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    cbv [reduce]; push.
    rewrite Hc', <- (Z.mul_comm (eval c)), <- !Z.mul_assoc, <-reduction_rule by auto.
    autorewrite with zsimplify_const; rewrite !Z.mul_assoc, Z.mul_div_eq_full, w_mod by auto.
    autorewrite with zsimplify_const; rewrite eval_split; trivial.
  Qed.

  (*
  Definition splitQ (s:Q) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => (fst t * Zpos (Qden s)) mod (Qnum s) =? 0) p in
       (snd hi_lo, map (fun t => ((fst t * Zpos (Qden s)) / Qnum s, snd t)) (fst hi_lo)).
  Lemma eval_snd_splitQ s p (s_nz:Qnum s<>0) :
   Qnum s * eval (snd (splitQ s p)) = eval (fst (partition (fun t => (fst t * Zpos (Qden s)) mod (Qnum s) =? 0) p)) * Zpos (Qden s).
  Proof using Type.
    (* Work around https://github.com/mit-plv/fiat-crypto/issues/381 ([nsatz] can't handle [Zpos]) *)
    cbv [splitQ Let_In]; cbn [fst snd]; zify; generalize dependent (Zpos (Qden s)); generalize dependent (Qnum s); clear s; intros.
    induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.
  Lemma eval_splitQ s p (s_nz:Qnum s<>0) :
    eval (fst (splitQ s p)) + (Qnum s * eval (snd (splitQ s p))) / Zpos (Qden s) = eval p.
  Proof using Type. rewrite eval_snd_splitQ, eval_fst_partition by assumption; cbv [splitQ Let_In]; cbn [fst snd]; Z.div_mod_to_quot_rem_in_goal; nia. Qed.
  Lemma eval_splitQ_mul s p (s_nz:Qnum s<>0) :
    eval (fst (splitQ s p)) * Zpos (Qden s) + (Qnum s * eval (snd (splitQ s p))) = eval p * Zpos (Qden s).
  Proof using Type. rewrite eval_snd_splitQ, eval_fst_partition by assumption; cbv [splitQ Let_In]; cbn [fst snd]; nia. Qed.
   *)
  Lemma eval_rev p : eval (rev p) = eval p.
  Proof using Type. induction p; cbn [rev]; push; lia. Qed.
  Hint Rewrite eval_rev : push_eval.
  (*
  Lemma eval_permutation (p q : list (Z * Z)) : Permutation p q -> eval p = eval q.
  Proof using Type. induction 1; push; nsatz.                          Qed.

  Module RevWeightOrder <: TotalLeBool.
    Definition t := (Z * Z)%type.
    Definition leb (x y : t) := Z.leb (fst y) (fst x).
    Infix "<=?" := leb.
    Local Coercion is_true : bool >-> Sortclass.
    Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
    Proof using Type.
      cbv [is_true leb]; intros x y; rewrite !Z.leb_le; pose proof (Z.le_ge_cases (fst x) (fst y)).
      omega.
    Qed.
    Global Instance leb_Transitive : Transitive leb.
    Proof using Type. repeat intro; unfold is_true, leb in *; Z.ltb_to_lt; omega. Qed.
  End RevWeightOrder.

  Module RevWeightSort := Mergesort.Sort RevWeightOrder.

  Lemma eval_sort p : eval (RevWeightSort.sort p) = eval p.
  Proof using Type. symmetry; apply eval_permutation, RevWeightSort.Permuted_sort. Qed.
  Hint Rewrite eval_sort : push_eval.
  *)
  (* rough template (we actually have to do things a bit differently to account for duplicate weights):
[ dlet fi_c := c * fi in
   let (fj_high, fj_low) := split fj at s/fi.weight in
   dlet fi_2 := 2 * fi in
    dlet fi_2_c := 2 * fi_c in
    (if fi.weight^2 >= s then fi_c * fi else fi * fi)
       ++ fi_2_c * fj_high
       ++ fi_2 * fj_low
 | fi <- f , fj := (f weight less than i) ]
   *)
  (** N.B. We take advantage of dead code elimination to allow us to
      let-bind partial products that we don't end up using *)
  (** [v] -> [(v, v*c, v*c*2, v*2)] *)
  Definition let_bind_for_reduce_square (c:list (Z*Z)) (p:list (Z*Z)) : list ((Z*Z) * list(Z*Z) * list(Z*Z) * list(Z*Z)) :=
    let two := [(1,2)] (* (weight, value) *) in
    map (fun t => dlet c_t := mul [t] c in dlet two_c_t := mul c_t two in dlet two_t := mul [t] two in (t, c_t, two_c_t, two_t)) p.
  Definition reduce_square (s:Z) (c:list (Z*Z)) (p:list (Z*Z)) : list (Z*Z) :=
    let p := let_bind_for_reduce_square c p in
    let div_s := map (fun t => (fst t / s, snd t)) in
    list_rect
      _
      nil
      (fun t ts acc
       => (let '(t, c_t, two_c_t, two_t) := t in
           (if ((fst t * fst t) mod s =? 0)
            then div_s (mul [t] c_t)
            else mul [t] [t])
             ++ (flat_map
                   (fun '(t', c_t', two_c_t', two_t')
                    => if ((fst t * fst t') mod s =? 0)
                       then div_s
                              (if fst t' <=? fst t
                               then mul [t'] two_c_t
                               else mul [t] two_c_t')
                       else (if fst t' <=? fst t
                             then mul [t'] two_t
                             else mul [t] two_t'))
                   ts))
            ++ acc)
      p.
  Lemma eval_map_div s p (s_nz:s <> 0) (Hmod : forall v, In v p -> fst v mod s = 0)
    : eval (map (fun x => (fst x / s, snd x)) p) = eval p / s.
  Proof using Type.
    assert (Hmod' : forall v, In v p -> (fst v * snd v) mod s = 0).
    { intros; push_Zmod; rewrite Hmod by assumption; autorewrite with zsimplify_const; reflexivity. }
    induction p as [|p ps IHps]; push.
    { autorewrite with zsimplify_const; reflexivity. }
    { cbn [In] in *; rewrite Z.div_add_exact by eauto.
      rewrite !Z.Z_divide_div_mul_exact', IHps by auto using Znumtheory.Zmod_divide.
      nsatz. }
  Qed.
  Lemma eval_map_mul_div s a b c (s_nz:s <> 0) (a_mod : (a*a) mod s = 0)
    : eval (map (fun x => ((a * (a * fst x)) / s, b * (b * snd x))) c) = ((a * a) / s) * (b * b) * eval c.
  Proof using Type.
    rewrite <- eval_map_mul; apply f_equal, map_ext; intro.
    rewrite !Z.mul_assoc.
    rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    f_equal; nia.
  Qed.
  Hint Rewrite eval_map_mul_div using solve [ auto ] : push_eval.

  Lemma eval_map_mul_div' s a b c (s_nz:s <> 0) (a_mod : (a*a) mod s = 0)
    : eval (map (fun x => (((a * a) * fst x) / s, (b * b) * snd x)) c) = ((a * a) / s) * (b * b) * eval c.
  Proof using Type. rewrite <- eval_map_mul_div by assumption; f_equal; apply map_ext; intro; Z.div_mod_to_quot_rem_in_goal; f_equal; nia. Qed.
  Hint Rewrite eval_map_mul_div' using solve [ auto ] : push_eval.

  Lemma eval_flat_map_if A (f : A -> bool) g h p
    : eval (flat_map (fun x => if f x then g x else h x) p)
      = eval (flat_map g (fst (partition f p))) + eval (flat_map h (snd (partition f p))).
  Proof using Type.
    induction p; cbn [flat_map partition fst snd]; eta_expand; break_match; cbn [fst snd]; push;
      nsatz.
  Qed.
  (*Local Hint Rewrite eval_flat_map_if : push_eval.*) (* this should be [Local], but that doesn't work *)

  Lemma eval_if (b : bool) p q : eval (if b then p else q) = if b then eval p else eval q.
  Proof using Type. case b; reflexivity. Qed.
  Hint Rewrite eval_if : push_eval.

  Lemma split_app s p q :
    split s (p ++ q) = (fst (split s p) ++ fst (split s q), snd (split s p) ++ snd (split s q)).
  Proof using Type.
    cbv [split]; rewrite !partition_app; cbn [fst snd].
    rewrite !map_app; reflexivity.
  Qed.
  Lemma fst_split_app s p q :
    fst (split s (p ++ q)) = fst (split s p) ++ fst (split s q).
  Proof using Type. rewrite split_app; reflexivity. Qed.
  Lemma snd_split_app s p q :
    snd (split s (p ++ q)) = snd (split s p) ++ snd (split s q).
  Proof using Type. rewrite split_app; reflexivity. Qed.
  Hint Rewrite fst_split_app snd_split_app : push_eval.

  Lemma eval_reduce_list_rect_app A s c N C p :
    eval (reduce s c (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p))
    = eval (@list_rect A _ (reduce s c N) (fun x xs acc => reduce s c (C x xs) ++ acc) p).
  Proof using Type.
    cbv [reduce]; induction p as [|p ps IHps]; cbn [list_rect]; push; [ nsatz | rewrite <- IHps; clear IHps ].
    push; nsatz.
  Qed.
  Hint Rewrite eval_reduce_list_rect_app : push_eval.

  Lemma eval_list_rect_app A N C p :
    eval (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p)
    = @list_rect A _ (eval N) (fun x xs acc => eval (C x xs) + acc) p.
  Proof using Type. induction p; cbn [list_rect]; push; nsatz. Qed.
  Hint Rewrite eval_list_rect_app : push_eval.

  Local Existing Instances list_rect_Proper pointwise_map flat_map_Proper.
  Local Hint Extern 0 (Proper _ _) => solve_Proper_eq : typeclass_instances.

  Lemma reduce_nil s c : reduce s c nil = nil.
  Proof using Type. cbv [reduce]; induction c; cbn; intuition auto. Qed.
  Hint Rewrite reduce_nil : push_eval.

  Lemma eval_reduce_app s c p q : eval (reduce s c (p ++ q)) = eval (reduce s c p) + eval (reduce s c q).
  Proof using Type. cbv [reduce]; push; nsatz. Qed.
  Hint Rewrite eval_reduce_app : push_eval.

  Lemma eval_reduce_cons s c p q :
    eval (reduce s c (p :: q))
    = (if fst p mod s =? 0 then eval c * ((fst p / s) * snd p) else fst p * snd p)
      + eval (reduce s c q).
  Proof using Type.
    cbv [reduce split]; cbn [partition fst snd]; eta_expand; push.
    break_innermost_match; cbn [fst snd map]; push; nsatz.
  Qed.
  Hint Rewrite eval_reduce_cons : push_eval.

  Lemma mul_cons_l t ts p :
    mul (t::ts) p = map (fun t' => (fst t * fst t', snd t * snd t')) p ++ mul ts p.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_l p : mul nil p = nil.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_r p : mul p nil = nil.
  Proof using Type. cbv [mul]; induction p; cbn; intuition auto. Qed.
  Hint Rewrite mul_nil_l mul_nil_r : push_eval.
  Lemma mul_app_l p p' q :
    mul (p ++ p') q = mul p q ++ mul p' q.
  Proof using Type. cbv [mul]; rewrite flat_map_app; reflexivity. Qed.
  Lemma mul_singleton_l_app_r p q q' :
    mul [p] (q ++ q') = mul [p] q ++ mul [p] q'.
  Proof using Type. cbv [mul flat_map]; rewrite !map_app, !app_nil_r; reflexivity. Qed.
  Hint Rewrite mul_singleton_l_app_r : push_eval.
  Lemma mul_singleton_singleton p q :
    mul [p] [q] = [(fst p * fst q, snd p * snd q)].
  Proof using Type. reflexivity. Qed.

  Lemma eval_reduce_square_step_helper s c t' t v (s_nz:s <> 0) :
    (fst t * fst t') mod s = 0 \/ (fst t' * fst t) mod s = 0 -> In v (mul [t'] (mul (mul [t] c) [(1, 2)])) -> fst v mod s = 0.
  Proof using Type.
    cbv [mul]; cbn [map flat_map fst snd].
    rewrite !app_nil_r, flat_map_singleton, !map_map; cbn [fst snd]; rewrite in_map_iff; intros [H|H] [? [? ?] ]; subst; revert H.
    all:cbn [fst snd]; autorewrite with zsimplify_const; intro H; rewrite Z.mul_assoc, Z.mul_mod_l.
    all:rewrite H || rewrite (Z.mul_comm (fst t')), H; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma eval_reduce_square_step s c t ts (s_nz : s <> 0) :
    eval (flat_map
            (fun t' => if (fst t * fst t') mod s =? 0
                    then map (fun t => (fst t / s, snd t))
                             (if fst t' <=? fst t
                              then mul [t'] (mul (mul [t] c) [(1, 2)])
                              else mul [t] (mul (mul [t'] c) [(1, 2)]))
                    else (if fst t' <=? fst t
                          then mul [t'] (mul [t] [(1, 2)])
                          else mul [t] (mul [t'] [(1, 2)])))
            ts)
    = eval (reduce s c (mul [(1, 2)] (mul [t] ts))).
  Proof using Type.
    induction ts as [|t' ts IHts]; cbn [flat_map]; [ push; nsatz | rewrite eval_app, IHts; clear IHts ].
    change (t'::ts) with ([t'] ++ ts); rewrite !mul_singleton_l_app_r, !mul_singleton_singleton; autorewrite with zsimplify_const; push.
    break_match; Z.ltb_to_lt; push; try nsatz.
    all:rewrite eval_map_div by eauto using eval_reduce_square_step_helper; push; autorewrite with zsimplify_const.
    all:rewrite ?Z.mul_assoc, <- !(Z.mul_comm (fst t')), ?Z.mul_assoc.
    all:rewrite ?Z.mul_assoc, <- !(Z.mul_comm (fst t)), ?Z.mul_assoc.
    all:rewrite <- !Z.mul_assoc, Z.mul_assoc.
    all:rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    all:nsatz.
  Qed.

  Lemma eval_reduce_square_helper s c x y v (s_nz:s <> 0) :
    (fst x * fst y) mod s = 0 \/ (fst y * fst x) mod s = 0 -> In v (mul [x] (mul [y] c)) -> fst v mod s = 0.
  Proof using Type.
    cbv [mul]; cbn [map flat_map fst snd].
    rewrite !app_nil_r, ?flat_map_singleton, !map_map; cbn [fst snd]; rewrite in_map_iff; intros [H|H] [? [? ?] ]; subst; revert H.
    all:cbn [fst snd]; autorewrite with zsimplify_const; intro H; rewrite Z.mul_assoc, Z.mul_mod_l.
    all:rewrite H || rewrite (Z.mul_comm (fst x)), H; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma eval_reduce_square_exact s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0)
    : eval (reduce_square s c p) = eval (reduce s c (square p)).
  Proof using Type.
    cbv [let_bind_for_reduce_square reduce_square square Let_In]; rewrite list_rect_map; push.
    apply list_rect_Proper; [ | repeat intro; subst | reflexivity ]; cbv [split]; push; [ nsatz | ].
    rewrite flat_map_map, eval_reduce_square_step by auto.
    break_match; Z.ltb_to_lt; push.
    1:rewrite eval_map_div by eauto using eval_reduce_square_helper; push.
    all:cbv [mul]; cbn [map flat_map fst snd]; rewrite !app_nil_r, !map_map; cbn [fst snd].
    all:autorewrite with zsimplify_const.
    all:rewrite <- ?Z.mul_assoc, !(Z.mul_comm (fst a)), <- ?Z.mul_assoc.
    all:rewrite ?Z.mul_assoc, <- (Z.mul_assoc _ (fst a) (fst a)), <- !(Z.mul_comm (fst a * fst a)).
    1:rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    all:idtac;
      let LHS := match goal with |- ?LHS = ?RHS => LHS end in
      let RHS := match goal with |- ?LHS = ?RHS => RHS end in
      let f := match LHS with context[eval (reduce _ _ (map ?f _))] => f end in
      let g := match RHS with context[eval (reduce _ _ (map ?f _))] => f end in
      rewrite (map_ext f g) by (intros; f_equal; nsatz).
    all:nsatz.
  Qed.
  Lemma eval_reduce_square s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0)
    : eval (reduce_square s c p) mod (s - eval c)
      = (eval p * eval p) mod (s - eval c).
  Proof using Type. rewrite eval_reduce_square_exact by assumption; push; auto. Qed.
  Hint Rewrite eval_reduce_square : push_eval.

  Definition bind_snd (p : list (Z*Z)) :=
    map (fun t => dlet_nd t2 := snd t in (fst t, t2)) p.

  Lemma bind_snd_correct p : bind_snd p = p.
  Proof using Type.
    cbv [bind_snd]; induction p as [| [? ?] ];
      push; [|rewrite IHp]; reflexivity.
  Qed.

  Section Carries.
    Definition carryterm (w fw:Z) (t:Z * Z) :=
      if (Z.eqb (fst t) w)
      then dlet_nd t2 := snd t in
           dlet_nd d2 := t2 / fw in
           dlet_nd m2 := t2 mod fw in
           [(w * fw, d2);(w,m2)]
      else [t].

    Lemma eval_carryterm w fw (t:Z * Z) (fw_nonzero:fw<>0):
      eval (carryterm w fw t) = eval [t].
    Proof using Type*.
      cbv [carryterm Let_In]; break_match; push; [|trivial].
      pose proof (Z.div_mod (snd t) fw fw_nonzero).
      rewrite Z.eqb_eq in *.
      nsatz.
    Qed. Hint Rewrite eval_carryterm using auto : push_eval.

    Definition carry (w fw:Z) (p:list (Z * Z)):=
      flat_map (carryterm w fw) p.

    Lemma eval_carry w fw p (fw_nonzero:fw<>0):
      eval (carry w fw p) = eval p.
    Proof using Type*. cbv [carry]; induction p; push; nsatz. Qed.
    Hint Rewrite eval_carry using auto : push_eval.
  End Carries.
End Associational.

Module Weight.
  Section Weight.
    Context weight
            (weight_0 : weight 0%nat = 1)
            (weight_positive : forall i, 0 < weight i)
            (weight_multiples : forall i, weight (S i) mod weight i = 0)
            (weight_divides : forall i : nat, 0 < weight (S i) / weight i).

    Local Hint Resolve Z.positive_is_nonzero Z.lt_gt Nat2Z.is_nonneg.

    Lemma weight_multiples_full' j : forall i, weight (i+j) mod weight i = 0.
    Proof using weight_positive weight_multiples.
      induction j; intros;
        repeat match goal with
               | _ => rewrite Nat.add_succ_r
               | _ => rewrite IHj
               | |- context [weight (S ?x) mod weight _] =>
                 rewrite (Z.div_mod (weight (S x)) (weight x)), weight_multiples by auto
               | _ => progress autorewrite with push_Zmod natsimplify zsimplify_fast
               | _ => reflexivity
               end.
    Qed.

    Lemma weight_multiples_full j i : (i <= j)%nat -> weight j mod weight i = 0.
    Proof using weight_positive weight_multiples.
      intros; replace j with (i + (j - i))%nat by omega.
      apply weight_multiples_full'.
    Qed.

    Lemma weight_divides_full j i : (i <= j)%nat -> 0 < weight j / weight i.
    Proof using weight_positive weight_multiples. auto using Z.gt_lt, Z.div_positive_gt_0, weight_multiples_full. Qed.

    Lemma weight_div_mod j i : (i <= j)%nat -> weight j = weight i * (weight j / weight i).
    Proof using weight_positive weight_multiples. intros. apply Z.div_exact; auto using weight_multiples_full. Qed.

    Lemma weight_mod_pull_div n x :
      x mod weight (S n) / weight n =
      (x / weight n) mod (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto
             | _ => rewrite Z.mul_div_eq' by auto
             | _ => rewrite Z.mod_pull_div
             | _ => rewrite weight_multiples by auto
             | _ => solve [auto using Z.lt_le_incl]
             end.
    Qed.

    Lemma weight_div_pull_div n x :
      x / weight (S n) =
      (x / weight n) / (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zdiv_to_mod zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto
             | _ => rewrite Z.mul_div_eq' by auto
             | _ => rewrite Z.div_div by auto
             | _ => rewrite weight_multiples by assumption
             | _ => solve [auto using Z.lt_le_incl]
             end.
    Qed.
  End Weight.
End Weight.

Module Positional.
  Import Weight.
  Section Positional.
  Context (weight : nat -> Z)
          (weight_0 : weight 0%nat = 1)
          (weight_nz : forall i, weight i <> 0).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Lemma eval_to_associational n x :
    Associational.eval (@to_associational n x) = eval n x.
  Proof using Type. trivial.                                             Qed.
  Hint Rewrite @eval_to_associational : push_eval.
  Lemma eval_nil n : eval n [] = 0.
  Proof using Type. cbv [eval to_associational]. rewrite combine_nil_r. reflexivity. Qed.
  Hint Rewrite eval_nil : push_eval.
  Lemma eval0 p : eval 0 p = 0.
  Proof using Type. cbv [eval to_associational]. reflexivity. Qed.
  Hint Rewrite eval0 : push_eval.

  Lemma eval_snoc n m x y : n = length x -> m = S n -> eval m (x ++ [y]) = eval n x + weight n * y.
  Proof using Type.
    cbv [eval to_associational]; intros; subst n m.
    rewrite seq_snoc, map_app.
    rewrite combine_app_samelength by distr_length.
    autorewrite with push_eval. simpl.
    autorewrite with push_eval cancel_pair; ring.
  Qed.

  Lemma eval_snoc_S n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * y.
  Proof using Type. intros; erewrite eval_snoc; eauto. Qed.
  Hint Rewrite eval_snoc_S using (solve [distr_length]) : push_eval.

  (* SKIP over this: zeros, add_to_nth *)
  Local Ltac push := autorewrite with push_eval push_map distr_length
    push_flat_map push_fold_right push_nth_default cancel_pair natsimplify.
  Definition zeros n : list Z := repeat 0 n.
  Lemma length_zeros n : length (zeros n) = n. Proof using Type. clear; cbv [zeros]; distr_length. Qed.
  Hint Rewrite length_zeros : distr_length.
  Lemma eval_combine_zeros ls n : Associational.eval (List.combine ls (zeros n)) = 0.
  Proof using Type.
    clear; cbv [Associational.eval zeros].
    revert n; induction ls, n; simpl; rewrite ?IHls; nsatz.   Qed.
  Lemma eval_zeros n : eval n (zeros n) = 0.
  Proof using Type. apply eval_combine_zeros.                            Qed.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => x + y) ls.
  Lemma length_add_to_nth i x ls : length (add_to_nth i x ls) = length ls.
  Proof using Type. clear; cbv [add_to_nth]; distr_length. Qed.
  Hint Rewrite length_add_to_nth : distr_length.
  Lemma eval_add_to_nth (n:nat) (i:nat) (x:Z) (xs:list Z) (H:(i<length xs)%nat)
        (Hn : length xs = n) (* N.B. We really only need [i < Nat.min n (length xs)] *) :
    eval n (add_to_nth i x xs) = weight i * x + eval n xs.
  Proof using Type.
    subst n.
    cbv [eval to_associational add_to_nth].
    rewrite ListUtil.combine_update_nth_r at 1.
    rewrite <-(update_nth_id i (List.combine _ _)) at 2.
    rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _
      (weight 0, 0)) by (push; lia); cbv [ListUtil.splice_nth id].
    repeat match goal with
           | _ => progress push
           | _ => progress break_match
           | _ => progress (apply Zminus_eq; ring_simplify)
           | _ => rewrite <-ListUtil.map_nth_default_always
           end; lia.                                          Qed.
  Hint Rewrite @eval_add_to_nth eval_zeros eval_combine_zeros : push_eval.

  Lemma zeros_ext_map {A} n (p : list A) : length p = n -> zeros n = map (fun _ => 0) p.
  Proof using Type. cbv [zeros]; intro; subst; induction p; cbn; congruence. Qed.

  Lemma eval_mul_each (n:nat) (a:Z) (p:list Z)
        (Hn : length p = n)
    : eval n (List.map (fun x => a*x) p) = a*eval n p.
  Proof using Type.
    clear -Hn.
    transitivity (Associational.eval (map (fun t => (1 * fst t, a * snd t)) (to_associational n p))).
    { cbv [eval to_associational]; rewrite !combine_map_r.
      f_equal; apply map_ext; intros; f_equal; nsatz. }
    { rewrite Associational.eval_map_mul, eval_to_associational; nsatz. }
  Qed.
  Hint Rewrite eval_mul_each : push_eval.

  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => unit -> (nat * Z)%type)
      (fun _ => (O, fst t * snd t))
      (fun i' place_i' _
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in c * snd t)
          else place_i' tt)
      i
      tt.

  Lemma place_in_range (t:Z*Z) (n:nat) : (fst (place t n) < S n)%nat.
  Proof using Type. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try omega. Qed.
  Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
  Proof using weight_nz weight_0. induction i; cbv [place nat_rect] in *; break_match; push;
    repeat match goal with |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(auto) ltac:(auto))
           end; nsatz.                                        Qed.
  Hint Rewrite weight_place : push_eval.
  Lemma weight_add_mod (weight_mul : forall i, weight (S i) mod weight i = 0) i j
    : weight (i + j) mod weight i = 0.
  Proof using weight_nz.
    rewrite Nat.add_comm.
    induction j as [|[|j] IHj]; cbn [Nat.add] in *;
      eauto using Z_mod_same_full, Z.mod_mod_trans.
  Qed.
  Lemma weight_mul_iff (weight_pos : forall i, 0 < weight i) (weight_mul : forall i, weight (S i) mod weight i = 0) i j
    : weight i mod weight j = 0 <-> ((j < i)%nat \/ forall k, (i <= k <= j)%nat -> weight k = weight j).
  Proof using weight_nz.
    split.
    { destruct (dec (j < i)%nat); [ left; omega | intro H; right; revert H ].
      assert (j = (j - i) + i)%nat by omega.
      generalize dependent (j - i)%nat; intro jmi; intros ? H0.
      subst j.
      destruct jmi as [|j]; [ intros k ?; assert (k = i) by omega; subst; f_equal; omega | ].
      induction j as [|j IH]; cbn [Nat.add] in *.
      { intros k ?; assert (k = i \/ k = S i) by omega; destruct_head'_or; subst;
          eauto using Z.mod_mod_0_0_eq_pos. }
      { specialize_by omega.
        { pose proof (weight_mul (S (j + i))) as H.
          specialize_by eauto using Z.mod_mod_trans with omega.
          intros k H'; destruct (dec (k = S (S (j + i)))); subst;
            try rewrite IH by eauto using Z.mod_mod_trans with omega;
            eauto using Z.mod_mod_trans, Z.mod_mod_0_0_eq_pos with omega.
          rewrite (IH i) in * by omega.
          eauto using Z.mod_mod_trans, Z.mod_mod_0_0_eq_pos with omega. } } }
    { destruct (dec (j < i)%nat) as [H|H]; [ intros _ | intros [H'|H']; try omega ].
      { assert (i = j + (i - j))%nat by omega.
        generalize dependent (i - j)%nat; intro imj; intros.
        subst i.
        apply weight_add_mod; auto. }
      { erewrite H', Z_mod_same_full by omega; omega. } }
  Qed.
  Lemma weight_div_from_pos_mul (weight_pos : forall i, 0 < weight i) (weight_mul : forall i, weight (S i) mod weight i = 0)
    : forall i, 0 < weight (S i) / weight i.
  Proof using weight_nz.
    intro i; generalize (weight_mul i) (weight_mul (S i)).
    Z.div_mod_to_quot_rem; nia.
  Qed.
  Lemma place_weight n (weight_pos : forall i, 0 < weight i) (weight_mul : forall i, weight (S i) mod weight i = 0)
        (weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j)
        i x
    : (place (weight i, x) n) = (Nat.min i n, (weight i / weight (Nat.min i n)) * x).
  Proof using weight_0 weight_nz.
    cbv [place].
    induction n as [|n IHn]; cbn; [ destruct i; cbn; rewrite ?weight_0; autorewrite with zsimplify_const; reflexivity | ].
    destruct (dec (i < S n)%nat);
      break_innermost_match; cbn [fst snd] in *; Z.ltb_to_lt; [ | rewrite IHn | | rewrite IHn ];
        break_innermost_match;
        rewrite ?Min.min_l in * by omega;
        rewrite ?Min.min_r in * by omega;
        eauto with omega.
    { rewrite weight_mul_iff in * by auto.
      destruct_head'_or; try omega.
      assert (S n = i).
      { apply weight_unique; try omega.
        symmetry; eauto with omega. }
      subst; reflexivity. }
    { rewrite weight_mul_iff in * by auto.
      exfalso; intuition eauto with omega. }
  Qed.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      dlet_nd p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational n p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof using weight_0 weight_nz. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational Let_In] in *; push; try
  pose proof place_in_range a (pred n); try omega; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  try omega.                                                  Qed.
  Hint Rewrite @eval_from_associational : push_eval.
  Lemma length_from_associational n p : length (from_associational n p) = n.
  Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
  Hint Rewrite length_from_associational : distr_length.

  Lemma nth_default_from_associational v n p i (n_nz : n <> 0%nat) :
    nth_default v (from_associational n p) i
    = fold_right Z.add (nth_default v (zeros n) i)
                 (map (fun t => dlet p : nat * Z := place t (pred n) in
                           if dec (fst p = i) then snd p else 0) p).
  Proof.
    subst; cbv [from_associational Let_In].
    induction p as [|p ps IHps]; [ reflexivity | ]; cbn [fold_right map]; rewrite <- IHps; clear IHps.
    cbv [add_to_nth].
    match goal with
    | [ |- context[place ?p ?i] ]
      => pose proof (place_in_range p i)
    end.
    rewrite update_nth_nth_default_full; break_match; try omega;
      rewrite nth_default_out_of_bounds by omega; try omega.
    match goal with
    | [ H : context[length (fold_right ?f ?v ?ps)] |- _ ]
      => replace (length (fold_right f v ps)) with (length v) in H
        by (apply fold_right_invariant; intros; distr_length; auto)
    end.
    distr_length; auto.
  Qed.

  Definition extend_to_length (n_in n_out : nat) (p:list Z) : list Z :=
    p ++ zeros (n_out - n_in).
  Lemma eval_extend_to_length n_in n_out p :
    length p = n_in -> (n_in <= n_out)%nat ->
    eval n_out (extend_to_length n_in n_out p) = eval n_in p.
  Proof using Type.
    cbv [eval extend_to_length to_associational]; intros.
    replace (seq 0 n_out) with (seq 0 (n_in + (n_out - n_in))) by (f_equal; omega).
    rewrite seq_add, map_app, combine_app_samelength, Associational.eval_app;
      push; omega.
  Qed.
  Hint Rewrite eval_extend_to_length : push_eval.
  Lemma length_extend_to_length n_in n_out p :
    length p = n_in -> (n_in <= n_out)%nat ->
    length (extend_to_length n_in n_out p) = n_out.
  Proof using Type. clear; cbv [extend_to_length]; intros; distr_length.        Qed.
  Hint Rewrite length_extend_to_length : distr_length.

  Definition drop_high_to_length (n : nat) (p:list Z) : list Z :=
    firstn n p.
  Lemma length_drop_high_to_length n p :
    length (drop_high_to_length n p) = Nat.min n (length p).
  Proof using Type. clear; cbv [drop_high_to_length]; intros; distr_length.        Qed.
  Hint Rewrite length_drop_high_to_length : distr_length.

  Section mulmod.
    Context (s:Z) (s_nz:s <> 0)
            (c:list (Z*Z))
            (m_nz:s - Associational.eval c <> 0).
    Definition mulmod (n:nat) (a b:list Z) : list Z
      := let a_a := to_associational n a in
         let b_a := to_associational n b in
         let ab_a := Associational.mul a_a b_a in
         let abm_a := Associational.reduce s c ab_a in
         from_associational n abm_a.
    Lemma eval_mulmod n (f g:list Z)
          (Hf : length f = n) (Hg : length g = n) :
      eval n (mulmod n f g) mod (s - Associational.eval c)
      = (eval n f * eval n g) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. cbv [mulmod]; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try omega.. ].
    clear; cbv -[Associational.reduce].
    induction c as [|?? IHc]; simpl; trivial.                 Qed.

    Definition squaremod (n:nat) (a:list Z) : list Z
      := let a_a := to_associational n a in
         let aa_a := Associational.reduce_square s c a_a in
         from_associational n aa_a.
    Lemma eval_squaremod n (f:list Z)
          (Hf : length f = n) :
      eval n (squaremod n f) mod (s - Associational.eval c)
      = (eval n f * eval n f) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. cbv [squaremod]; push; trivial.
    destruct f; simpl in *; [ right; subst n; reflexivity | left; try omega.. ]. Qed.
  End mulmod.
  Hint Rewrite @eval_mulmod @eval_squaremod : push_eval.

  Definition add (n:nat) (a b:list Z) : list Z
    := let a_a := to_associational n a in
       let b_a := to_associational n b in
       from_associational n (a_a ++ b_a).
  Lemma eval_add n (f g:list Z)
        (Hf : length f = n) (Hg : length g = n) :
    eval n (add n f g) = (eval n f + eval n g).
  Proof using weight_0 weight_nz. cbv [add]; push; trivial. destruct n; auto.          Qed.
  Hint Rewrite @eval_add : push_eval.
  Lemma length_add n f g
        (Hf : length f = n) (Hg : length g = n) :
    length (add n f g) = n.
  Proof using Type. clear -Hf Hf; cbv [add]; distr_length.               Qed.
  Hint Rewrite @length_add : distr_length.

  Section Carries.
    Definition carry n m (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Lemma length_carry n m index p : length (carry n m index p) = m.
    Proof using Type. cbv [carry]; distr_length. Qed.
    Hint Rewrite length_carry : distr_length.
    Lemma eval_carry n m i p: (n <> 0%nat) -> (m <> 0%nat) ->
                              weight (S i) / weight i <> 0 ->
      eval m (carry n m i p) = eval n p.
    Proof using weight_0 weight_nz.
      cbv [carry]; intros; push; [|tauto].
      rewrite @Associational.eval_carry by eauto.
      apply eval_to_associational.
    Qed. Hint Rewrite @eval_carry : push_eval.

    (** TODO: figure out a way to make this proof shorter and faster *)
    Lemma nth_default_carry upper n m index p
      (weight_mul : forall i, weight (S i) mod weight i = 0)
      (weight_pos : forall i, 0 < weight i)
      (weight_unique : forall i j, (i <= upper)%nat -> (j <= upper)%nat -> weight i = weight j -> i = j)
      (Hn : (n <= upper)%nat)
      (Hm : (0 < m <= upper)%nat)
      (Hnm : (n <= m)%nat)
      (Hidx : (index <= upper)%nat) :
      length p = n ->
      forall i, nth_default 0 (carry n m index p) i
           = if dec (m <= i)%nat
             then 0
             else if dec (i = S index)
                  then nth_default 0 p i + ((nth_default 0 p index) / (weight (S index) / weight index))
                  else if dec (i = index)
                       then if dec (S index <> n \/ n <> m)
                            then ((nth_default 0 p i) mod (weight (S index) / weight index))
                            else nth_default 0 p i
                       else nth_default 0 p i.
    Proof using weight_0 weight_nz.
      assert (weight_unique_iff : forall i j, (i <= upper)%nat -> (j <= upper)%nat -> weight i = weight j <-> i = j)
        by (split; subst; auto).
      pose proof (weight_div_from_pos_mul weight_pos weight_mul) as weight_div_pos.
      assert (weight_div_nz : forall i, weight (S i) / weight i <> 0) by (intro i; specialize (weight_div_pos i); omega).
      intro; subst.
      intro i.
      destruct (dec (m <= i)%nat) as [Hmi|Hmi];
        [ rewrite (@nth_default_out_of_bounds _ i (carry _ _ _ _)) by (distr_length; omega); reflexivity | ].
      cbv [carry to_associational Associational.carry Let_In Associational.carryterm].
      rewrite combine_map_l, flat_map_map; cbn [fst snd].
      rewrite nth_default_from_associational, map_flat_map by omega; cbn [map].
      cbv [zeros]; rewrite nth_default_repeat.
      replace (if (dec (i < m)%nat) then 0 else 0) with 0 by (break_match; reflexivity).
      set (init := 0) at 1.
      lazymatch goal with |- ?LHS = ?RHS => rewrite <- (Z.add_0_l RHS : init + RHS = RHS) end.
      clearbody init.
      revert Hn i init Hmi Hnm Hidx.
      rewrite <- (rev_involutive p); generalize (rev p); clear p; intro p; rewrite rev_length.
      induction p as [|p ps IHps]; cbn [length]; intros Hn i init Hmi Hnm Hidx.
      { cbn; cbv [zeros]; break_innermost_match; cbn;
          rewrite ?nth_default_repeat, ?nth_default_nil; break_innermost_match; autorewrite with zsimplify_const; reflexivity. }
      { specialize_by omega.
        rewrite seq_snoc, rev_cons, combine_app_samelength by distr_length.
        rewrite flat_map_app, fold_right_app, IHps by omega; clear IHps.
        cbn [combine fold_right fst snd flat_map map].
        rewrite Nat.add_0_l.
        cbv [Let_In]; cbn [fst snd].
        rewrite ?nth_default_app; distr_length.
        destruct (dec (i = index)), (dec (i = S index)); try (subst; omega).
        { all:subst; break_innermost_match; Z.ltb_to_lt;
            match goal with
            | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
            end; destruct_head'_or; try (subst; omega).
          all:repeat first [ progress cbn [fst snd app map fold_right]
                           | progress Z.ltb_to_lt
                           | progress subst
                           | progress destruct_head'_or
                           | progress rewrite ?Z.mul_div_eq_full, ?weight_mul, ?Z.sub_0_r by eauto with omega
                           | progress rewrite ?place_weight by eauto with omega
                           | rewrite !Nat.sub_diag
                           | rewrite !Min.min_l by omega
                           | rewrite !nth_default_cons
                           | rewrite Z.div_same by eauto with omega
                           | progress break_innermost_match
                           | progress autorewrite with zsimplify_const
                           | lia
                           | match goal with
                             | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
                             | [ |- context[nth_default ?d ?ls ?i] ] => rewrite (@nth_default_out_of_bounds _ i ls d) by (distr_length; omega)
                             | [ H : ?x = ?x |- _ ] => clear H
                             end
                           | progress handle_min_max_for_omega_case ]. }
        { subst; break_innermost_match; Z.ltb_to_lt;
            match goal with
            | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
            end; destruct_head'_or; try (subst; omega).
          all:repeat first [ progress cbn [fst snd app map fold_right]
                           | progress Z.ltb_to_lt
                           | progress subst
                           | progress destruct_head'_or
                           | progress rewrite ?Z.mul_div_eq_full, ?weight_mul, ?Z.sub_0_r by eauto with omega
                           | progress rewrite ?place_weight by eauto with omega
                           | rewrite !Nat.sub_diag
                           | rewrite !Min.min_l by omega
                           | rewrite !nth_default_cons
                           | rewrite Z.div_same by eauto with omega
                           | progress break_innermost_match
                           | progress autorewrite with zsimplify_const
                           | lia
                           | match goal with
                             | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
                             | [ |- context[nth_default ?d ?ls ?i] ] => rewrite (@nth_default_out_of_bounds _ i ls d) by (distr_length; omega)
                             | [ H : ?x = ?x |- _ ] => clear H
                             end
                           | progress handle_min_max_for_omega_case ]. }
        { subst; break_innermost_match; Z.ltb_to_lt;
            match goal with
            | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
            end; destruct_head'_or; try (subst; omega).
          all:repeat first [ progress cbn [fst snd app map fold_right]
                           | progress Z.ltb_to_lt
                           | progress subst
                           | progress destruct_head'_or
                           | progress rewrite ?Z.mul_div_eq_full, ?weight_mul, ?Z.sub_0_r by eauto with omega
                           | progress rewrite ?place_weight by eauto with omega
                           | rewrite !Nat.sub_diag
                           | rewrite !Min.min_l by omega
                           | rewrite !nth_default_cons
                           | rewrite Z.div_same by eauto with omega
                           | progress break_innermost_match
                           | progress autorewrite with zsimplify_const
                           | lia
                           | match goal with
                             | [ H : context[weight ?x = weight ?y] |- _ ] => rewrite (weight_unique_iff x y) in H by omega
                             | [ |- context[nth_default ?d ?ls ?i] ] => rewrite (@nth_default_out_of_bounds _ i ls d) by (distr_length; omega)
                             | [ H : ?x = ?x |- _ ] => clear H
                             end
                           | progress handle_min_max_for_omega_case ]. } }
    Qed.

    Definition carry_reduce n (s:Z) (c:list (Z * Z))
               (index:nat) (p : list Z) :=
      from_associational
        n (Associational.reduce
             s c (to_associational (S n) (@carry n (S n) index p))).

    Lemma eval_carry_reduce n s c index p :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (weight (S index) / weight index <> 0) ->
      eval n (carry_reduce n s c index p) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof using weight_0 weight_nz. cbv [carry_reduce]; intros; push; auto.            Qed.
    Hint Rewrite @eval_carry_reduce : push_eval.
    Lemma length_carry_reduce n s c index p
      : length p = n -> length (carry_reduce n s c index p) = n.
    Proof using Type. cbv [carry_reduce]; distr_length.                  Qed.
    Hint Rewrite @length_carry_reduce : distr_length.

    (* N.B. It is important to reverse [idxs] here, because fold_right is
      written such that the first terms in the list are actually used
      last in the computation. For example, running:

      `Eval cbv - [Z.add] in (fun a b c d => fold_right Z.add d [a;b;c]).`

      will produce [fun a b c d => (a + (b + (c + d)))].*)
    Definition chained_carries n s c p (idxs : list nat) :=
      fold_right (fun a b => carry_reduce n s c a b) p (rev idxs).

    Lemma eval_chained_carries n s c p idxs :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries n s c p idxs) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof using Type*.
      cbv [chained_carries]; intros; push.
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        destruct n; intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries : push_eval.
    Lemma length_chained_carries n s c p idxs
      : length p = n -> length (@chained_carries n s c p idxs) = n.
    Proof using Type.
      intros; cbv [chained_carries]; induction (rev idxs) as [|x xs IHxs];
        cbn [fold_right]; distr_length.
    Qed. Hint Rewrite @length_chained_carries : distr_length.

    (* carries without modular reduction; useful for converting between bases *)
    Definition chained_carries_no_reduce n p (idxs : list nat) :=
      fold_right (fun a b => carry n n a b) p (rev idxs).
    Lemma eval_chained_carries_no_reduce n p idxs:
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries_no_reduce n p idxs) = eval n p.
    Proof using weight_0 weight_nz.
      cbv [chained_carries_no_reduce]; intros.
      destruct n; [push;reflexivity|].
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries_no_reduce : push_eval.
    Lemma length_chained_carries_no_reduce n p idxs
      : length p = n -> length (@chained_carries_no_reduce n p idxs) = n.
    Proof using Type.
      intros; cbv [chained_carries_no_reduce]; induction (rev idxs) as [|x xs IHxs];
        cbn [fold_right]; distr_length.
    Qed. Hint Rewrite @length_chained_carries_no_reduce : distr_length.
    (** TODO: figure out a way to make this proof shorter and faster *)
    Lemma nth_default_chained_carries_no_reduce_app n m inp1 inp2
          (weight_mul : forall i, weight (S i) mod weight i = 0)
          (weight_pos : forall i, 0 < weight i)
          (weight_div : forall i : nat, 0 < weight (S i) / weight i)
          (weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j) :
      length inp1 = m -> (length inp1 + length inp2 = n)%nat
      -> (List.length inp2 <> 0%nat \/ 0 <= eval m inp1 < weight m)
      -> forall i,
          nth_default 0 (chained_carries_no_reduce n (inp1 ++ inp2) (seq 0 m)) i
          = if dec (i < m)%nat
            then ((eval m inp1) mod weight (S i)) / weight i
            else if dec (i = m)
                 then match inp2 with
                      | nil => 0
                      | cons x xs
                        =>  x + (eval m inp1) / weight m
                      end
                 else nth_default 0 inp2 (i - m).
    Proof using weight_0 weight_nz.
      intro; subst m.
      rewrite <- (rev_involutive inp1); generalize (List.rev inp1); clear inp1; intro inp1; rewrite rev_length.
      revert inp2; induction inp1 as [|x xs IHxs]; intros.
      { destruct inp2; cbn; autorewrite with zsimplify_const; intros; destruct i; reflexivity. }
      destruct (lt_dec i n);
        [
        | break_match; cbn [List.length] in *; try lia;
          rewrite ?nth_default_out_of_bounds by (repeat autorewrite with distr_length; lia);
          reflexivity ].
      cbv [chained_carries_no_reduce] in *.
      repeat first [ progress cbn [List.length List.app List.rev fold_right] in *
                   | reflexivity
                   | assumption
                   | progress intros
                   | rewrite <- List.app_assoc
                   | rewrite seq_snoc
                   | rewrite rev_unit
                   | rewrite Nat.add_0_l
                   | rewrite eval_snoc_S in * by distr_length
                   | rewrite app_length
                   | rewrite rev_length
                   | erewrite nth_default_carry; try eassumption
                   | rewrite !IHxs; clear IHxs
                   | lia
                   | match goal with
                     | [ |- length (fold_right _ ?p (rev ?idxs)) = ?n ]
                       => apply (length_chained_carries_no_reduce n p idxs)
                     | [ |- context[_ mod weight (S ?n) / weight ?n] ]
                       => rewrite (Z.div_mod' (weight (S n)) (weight n)), weight_mul, Z.add_0_r, <- Z.mod_pull_div, ?Z.div_mul, ?Z.div_add', ?Z.mul_div_eq', ?weight_mul, ?Z.sub_0_r
                         by solve [ assumption
                                  | now apply Z.lt_le_incl, weight_div
                                  | now apply Z.lt_gt, weight_pos
                                  | (idtac + symmetry); now apply Z.lt_neq, weight_pos ]
                     | [ |- context[?x + ?y] ]
                       => match goal with
                          | [ |- context[y + x] ]
                            => progress replace (y + x) with (x + y) by lia
                          end
                     end ].
      break_match; try (exfalso; lia).
      all: repeat first [ rewrite nth_default_app
                        | rewrite nth_default_carry
                        | rewrite Nat.sub_diag
                        | rewrite minus_S_diag
                        | rewrite Nat.sub_succ_r
                        | rewrite nth_default_cons
                        | rewrite nth_default_cons_S
                        | progress subst
                        | now apply weight_0
                        | now apply weight_mul
                        | now apply weight_pos
                        | reflexivity
                        | progress intros
                        | (idtac + symmetry); now apply Z.lt_neq, weight_pos
                        | rewrite Z.div_add' by ((idtac + symmetry); now apply Z.lt_neq, weight_pos)
                        | progress destruct_head'_and
                        | progress destruct_head'_or
                        | progress cbn [List.length] in *
                        | match goal with
                          | [ |- context[?x + ?y] ]
                            => match goal with
                               | [ |- context[y + x] ]
                                 => progress replace (y + x) with (x + y) by lia
                               end
                          | [ H : List.length ?x = 0%nat |- _ ] => is_var x; destruct x
                          | [ H : not (or _ _) |- _ ] => apply Decidable.not_or in H
                          | [ H : ?x = ?x |- _ ] => clear H
                          | [ H : not (?x < ?x) |- _ ] => clear H
                          | [ H : not (?x < ?x)%nat |- _ ] => clear H
                          | [ H : not (S ?x < ?x)%nat |- _ ] => clear H
                          | [ H : ~(S ?x + _ <= ?x)%nat |- _ ] => clear H
                          | [ H : (?x < S ?x + _)%nat |- _ ] => clear H
                          | [ H : ?x <> S ?x |- _ ] => clear H
                          | [ H : ?x <> (?x + ?y)%nat |- _ ] => assert (0 < y)%nat by lia; clear H
                          | [ H : (?x < ?x + ?y)%nat |- _ ] => assert (0 < y)%nat by lia; clear H
                          | [ H : ~(?x + ?y <= ?x)%nat |- _ ] => assert (0 < y)%nat by lia; clear H
                          | [ H : ~(?x <> ?y) |- _ ] => assert (x = y) by lia; clear H
                          | [ H : (?x = ?x + ?y)%nat |- _ ] => assert (y = 0%nat) by lia; clear H
                          | [ H : ~(?x <= ?y)%nat |- _ ] => assert (y < x)%nat by lia; clear H
                          | [ H : ~(?x < ?y)%nat |- _ ] => assert (y <= x)%nat by lia; clear H
                          | [ H : (?x <= ?y)%nat, H' : ?x <> ?y |- _ ] => assert (x < y)%nat by lia; clear H H'
                          | [ H : (?x <= ?y)%nat, H' : ?y <> ?x |- _ ] => assert (x < y)%nat by lia; clear H H'
                          | [ H : (?x < ?y)%nat |- context[nth_default _ _ (?y - ?x)] ]
                            => destruct (y - x)%nat eqn:?
                          | [ |- context[nth_default _ (_ :: _) ?n] ] => is_var n; destruct n
                          | [ H : ?T, H' : ?T |- _ ] => clear H'
                          | [ |- (?x + ?y) mod ?z = (?y + ?x) mod ?z ] => apply f_equal2
                          | [ |- ?x + _ = ?x + _ ] => apply f_equal
                          | [ H0 : 0 <= ?e + ?w * ?x, H1 : ?e + ?w * ?x < ?w'
                              |- ?x + ?e / ?w = (?x + ?e / ?w) mod (?w' / ?w) ]
                            => rewrite (Z.mod_small (x + e / w) (w' / w))
                          | [ H : (?i < ?n)%nat |- context[(_ + weight ?n * _) / weight ?i] ]
                            => rewrite (Z.div_mod (weight n) (weight (S i))), weight_multiples_full, Z.add_0_r,
                               (Z.div_mod (weight (S i)) (weight i)), weight_mul, Z.add_0_r,
                               <- !Z.mul_assoc, Z.div_add', ?Z.div_mul', ?Z.mul_div_eq_full, ?weight_mul, ?Z.sub_0_r
                              by solve [ assumption
                                       | now apply Z.lt_le_incl, weight_div
                                       | now apply Z.lt_gt, weight_pos
                                       | now apply Nat.lt_le_incl
                                       | (idtac + symmetry); now apply Z.lt_neq, weight_pos ];
                               push_Zmod; pull_Zmod
                          end
                        | progress autorewrite with distr_length in *
                        | lia
                        | progress autorewrite with zsimplify_const
                        | break_innermost_match_step
                        | match goal with
                          | [ |- context[weight (S ?n) / weight ?n] ]
                            => unique pose proof (@weight_mul n)
                          end
                        | Z.div_mod_to_quot_rem; nia ].
    Qed.

    Lemma nth_default_chained_carries_no_reduce n inp
          (weight_mul : forall i, weight (S i) mod weight i = 0)
          (weight_pos : forall i, 0 < weight i)
          (weight_div : forall i : nat, 0 < weight (S i) / weight i)
          (weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j) :
      length inp = n -> 0 <= eval n inp < weight n
      -> forall i,
          nth_default 0 (chained_carries_no_reduce n inp (seq 0 n)) i
          = ((eval n inp) mod weight (S i)) / weight i.
    Proof using weight_0 weight_nz.
      pose proof (weight_divides_full weight ltac:(assumption) ltac:(assumption)) as weight_div_full.
      pose proof (weight_multiples_full weight ltac:(assumption) ltac:(assumption)) as weight_mul_full.
      assert (weight_le_full : forall j i, (i <= j)%nat -> weight i <= weight j)
        by (intros j i pf; specialize (weight_div_full j i pf); specialize (weight_mul_full j i pf); Z.div_mod_to_quot_rem; nia).
      intros ? ? i.
      pose proof (weight_le_full (S n) n ltac:(lia)).
      pose proof (weight_le_full (S i) i ltac:(lia)).
      pose proof (weight_le_full i n).
      intros; rewrite <- (app_nil_r inp).
      rewrite (@nth_default_chained_carries_no_reduce_app n n inp nil), app_nil_r by (cbn [List.length]; auto with lia).
      break_innermost_match; try reflexivity; rewrite ?nth_default_nil.
      all: rewrite Z.mod_small by lia.
      all: rewrite Z.div_small by lia.
      all: reflexivity.
    Qed.

    Lemma nth_default_chained_carries_no_reduce_pred n inp
          (weight_mul : forall i, weight (S i) mod weight i = 0)
          (weight_pos : forall i, 0 < weight i)
          (weight_div : forall i : nat, 0 < weight (S i) / weight i)
          (weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j) :
      length inp = n -> 0 <= eval n inp < weight n
      -> forall i,
          nth_default 0 (chained_carries_no_reduce n inp (seq 0 (pred n))) i
          = ((eval n inp) mod weight (S i)) / weight i.
    Proof using weight_0 weight_nz.
      pose proof (weight_divides_full weight ltac:(assumption) ltac:(assumption)) as weight_div_full.
      pose proof (weight_multiples_full weight ltac:(assumption) ltac:(assumption)) as weight_mul_full.
      assert (weight_le_full : forall j i, (i <= j)%nat -> weight i <= weight j)
        by (intros j i pf; specialize (weight_div_full j i pf); specialize (weight_mul_full j i pf); Z.div_mod_to_quot_rem; nia).
      destruct n as [|n]; [ now apply nth_default_chained_carries_no_reduce | ].
      intros ? ? i.
      pose proof (weight_le_full (S n) n ltac:(lia)).
      pose proof (weight_le_full (S i) i ltac:(lia)).
      pose proof (weight_le_full i n).
      pose proof (weight_le_full (S i) (S n)).
      pose proof (weight_le_full i (S n)).
      cbn [pred].
      revert dependent inp; intro inp.
      rewrite <- (rev_involutive inp); generalize (rev inp); clear inp; intro inp.
      rewrite rev_length; intros.
      destruct inp as [|x inp]; cbn [List.length List.rev] in *; [ lia | ].
      rewrite (@nth_default_chained_carries_no_reduce_app (S n) n (List.rev inp) (x::nil)) by (cbn [List.length]; autorewrite with distr_length; auto with lia).
      rewrite eval_snoc_S in * by distr_length.
      break_innermost_match; try reflexivity.
      all: repeat first [ progress autorewrite with zsimplify_const
                        | reflexivity
                        | progress Z.rewrite_mod_small
                        | rewrite Z.div_add' by ((idtac + symmetry); now apply Z.lt_neq, weight_pos)
                        | lia
                        | match goal with
                          | [ |- context[_ mod weight (S ?n) / weight ?n] ]
                            => rewrite (Z.div_mod' (weight (S n)) (weight n)), weight_mul, Z.add_0_r, <- Z.mod_pull_div, ?Z.div_mul, ?Z.div_add', ?Z.mul_div_eq', ?weight_mul, ?Z.sub_0_r
                              by solve [ assumption
                                       | now apply Z.lt_le_incl, weight_div
                                       | now apply Z.lt_gt, weight_pos
                                       | (idtac + symmetry); now apply Z.lt_neq, weight_pos ]
                          | [ |- context[(_ + weight ?n * _) / weight ?i] ]
                            => rewrite (Z.div_mod (weight n) (weight (S i))), weight_multiples_full, Z.add_0_r,
                               (Z.div_mod (weight (S i)) (weight i)), weight_mul, Z.add_0_r,
                               <- !Z.mul_assoc, Z.div_add', ?Z.div_mul', ?Z.mul_div_eq_full, ?weight_mul, ?Z.sub_0_r
                              by solve [ assumption
                                       | now apply Z.lt_le_incl, weight_div
                                       | now apply Z.lt_gt, weight_pos
                                       | now apply Nat.lt_le_incl
                                       | (idtac + symmetry); now apply Z.lt_neq, weight_pos ];
                               push_Zmod; pull_Zmod
                          end
                        | rewrite nth_default_cons
                        | rewrite nth_default_cons_S
                        | rewrite nth_default_nil
                        | rewrite Z.div_small by lia
                        | lia
                        | match goal with
                          | [ H : ~(?x < ?y)%nat |- _ ] => assert (y <= x)%nat by lia; clear H
                          | [ H : (?x <= ?y)%nat, H' : ?x <> ?y |- _ ] => assert (x < y)%nat by lia; clear H H'
                          | [ H : (?x <= ?y)%nat, H' : ?y <> ?x |- _ ] => assert (x < y)%nat by lia; clear H H'
                          | [ H : (?x < ?y)%nat |- context[nth_default _ _ (?y - ?x)] ]
                            => destruct (y - x)%nat eqn:?
                          end ].
    Qed.

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying. *)
    Definition encode n s c (x : Z) : list Z :=
      chained_carries n s c (from_associational n [(1,x)]) (seq 0 n).
    Lemma eval_encode n s c x :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
      eval n (encode n s c x) mod (s - Associational.eval c)
      = x mod (s - Associational.eval c).
    Proof using Type*. cbv [encode]; intros; push; auto; f_equal; omega. Qed.
    Lemma length_encode n s c x
      : length (encode n s c x) = n.
    Proof using Type. cbv [encode]; repeat distr_length.                 Qed.

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying, but without reduction. *)
    Definition encode_no_reduce n (x : Z) : list Z :=
      chained_carries_no_reduce n (from_associational n [(1,x)]) (seq 0 n).
    Lemma eval_encode_no_reduce n x :
      (n <> 0%nat) ->
      (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
      eval n (encode_no_reduce n x) = x.
    Proof using Type*. cbv [encode_no_reduce]; intros; push; auto; f_equal; omega. Qed.
    Lemma length_encode_no_reduce n x
      : length (encode_no_reduce n x) = n.
    Proof using Type. cbv [encode_no_reduce]; repeat distr_length.                 Qed.

  End Carries.
  Hint Rewrite @eval_encode @eval_encode_no_reduce @eval_carry @eval_carry_reduce @eval_chained_carries @eval_chained_carries_no_reduce : push_eval.
  Hint Rewrite @length_encode @length_encode_no_reduce @length_carry @length_carry_reduce @length_chained_carries @length_chained_carries_no_reduce : distr_length.

  Section sub.
    Context (n:nat)
            (s:Z) (s_nz:s <> 0)
            (c:list (Z * Z))
            (m_nz:s - Associational.eval c <> 0)
            (coef:Z).

    Definition negate_snd (a:list Z) : list Z
      := let A := to_associational n a in
         let negA := Associational.negate_snd A in
         from_associational n negA.

    Definition scmul (x:Z) (a:list Z) : list Z
      := let A := to_associational n a in
         let R := Associational.mul A [(1, x)] in
         from_associational n R.

    Definition balance : list Z
      := scmul coef (encode n s c (s - Associational.eval c)).

    Definition sub (a b:list Z) : list Z
      := let ca := add n balance a in
         let _b := negate_snd b in
         add n ca _b.

    Lemma eval_sub a b
      : (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        (List.length a = n) -> (List.length b = n) ->
        eval n (sub a b) mod (s - Associational.eval c)
        = (eval n a - eval n b) mod (s - Associational.eval c).
    Proof using s_nz m_nz weight_0 weight_nz.
      destruct (zerop n); subst; try reflexivity.
      intros; cbv [sub balance scmul negate_snd]; push; repeat distr_length;
        eauto with omega.
      push_Zmod; push; pull_Zmod; push_Zmod; pull_Zmod; distr_length; eauto.
    Qed.
    Hint Rewrite eval_sub : push_eval.
    Lemma length_sub a b
      : length a = n -> length b = n ->
        length (sub a b) = n.
    Proof using Type. intros; cbv [sub balance scmul negate_snd]; repeat distr_length. Qed.
    Hint Rewrite length_sub : distr_length.
    Definition opp (a:list Z) : list Z
      := sub (zeros n) a.
    Lemma eval_opp
          (a:list Z)
      : (length a = n) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval n (opp a) mod (s - Associational.eval c)
        = (- eval n a) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. intros; cbv [opp]; push; distr_length; auto.       Qed.
    Lemma length_opp a
      : length a = n -> length (opp a) = n.
    Proof using Type. cbv [opp]; intros; repeat distr_length.            Qed.
  End sub.
  Hint Rewrite @eval_opp @eval_sub : push_eval.
  Hint Rewrite @length_sub @length_opp : distr_length.

  Section select.
    Definition zselect (mask cond:Z) (p:list Z) :=
      dlet t := Z.zselect cond 0 mask in List.map (Z.land t) p.

    Definition select (cond:Z) (if_zero if_nonzero:list Z) :=
      List.map (fun '(p, q) => Z.zselect cond p q) (List.combine if_zero if_nonzero).

    Lemma map_and_0 n (p:list Z) : length p = n -> map (Z.land 0) p = zeros n.
    Proof using Type.
      intro; subst; induction p as [|x xs IHxs]; [reflexivity | ].
      cbn; f_equal; auto.
    Qed.
    Lemma eval_zselect n mask cond p (H:List.map (Z.land mask) p = p) :
      length p = n
      -> eval n (zselect mask cond p) =
         if dec (cond = 0) then 0 else eval n p.
    Proof using Type.
      cbv [zselect Let_In].
      rewrite Z.zselect_correct; break_match.
      { intros; erewrite map_and_0 by eassumption. apply eval_zeros. }
      { rewrite H; reflexivity. }
    Qed.
    Lemma length_zselect mask cond p :
      length (zselect mask cond p) = length p.
    Proof using Type. clear dependent weight. cbv [zselect Let_In]; break_match; intros; distr_length. Qed.

    (** We need an explicit equality proof here, because sometimes it
        matters that we retain the same bounds when selecting.  The
        alternative (weaker) lemma is [eval_select], where we only
        talk about equality under [eval]. *)
    Lemma select_eq cond n : forall p q,
        length p = n -> length q = n ->
        select cond p q = if dec (cond = 0) then p else q.
    Proof using weight.
      cbv [select]; induction n; intros;
        destruct p; distr_length;
          destruct q; distr_length;
        repeat match goal with
               | _ => progress autorewrite with push_combine push_map
               | _ => rewrite IHn by distr_length
               | _ => rewrite Z.zselect_correct
               | _ => break_match; reflexivity
               end.
    Qed.
    Lemma eval_select n cond p q :
      length p = n -> length q = n
      -> eval n (select cond p q) =
         if dec (cond = 0) then eval n p else eval n q.
    Proof using weight.
      intros; erewrite select_eq by eauto.
      break_match; reflexivity.
    Qed.
    Lemma length_select_min cond p q :
      length (select cond p q) = Nat.min (length p) (length q).
    Proof using Type. clear dependent weight. cbv [select Let_In]; distr_length. Qed.
    Hint Rewrite length_select_min : distr_length.
    Lemma length_select n cond p q :
      length p = n -> length q = n ->
      length (select cond p q) = n.
    Proof using Type. clear dependent weight. distr_length; omega **. Qed.
  End select.
End Positional.
(* Hint Rewrite disappears after the end of a section *)
Hint Rewrite length_zeros length_add_to_nth length_from_associational @length_add @length_carry_reduce @length_carry @length_chained_carries @length_chained_carries_no_reduce @length_encode @length_encode_no_reduce @length_sub @length_opp @length_select @length_zselect @length_select_min @length_extend_to_length @length_drop_high_to_length : distr_length.
Hint Rewrite @eval_zeros @eval_nil @eval_snoc_S @eval_select @eval_zselect @eval_extend_to_length using solve [auto; distr_length]: push_eval.
Section Positional_nonuniform.
  Context (weight weight' : nat -> Z).

  Lemma eval_hd_tl n (xs:list Z) :
    length xs = n ->
    eval weight n xs = weight 0%nat * hd 0 xs + eval (fun i => weight (S i)) (pred n) (tl xs).
  Proof using Type.
    intro; subst; destruct xs as [|x xs]; [ cbn; omega | ].
    cbv [eval to_associational Associational.eval] in *; cbn.
    rewrite <- map_S_seq; reflexivity.
  Qed.

  Lemma eval_cons n (x:Z) (xs:list Z) :
    length xs = n ->
    eval weight (S n) (x::xs) = weight 0%nat * x + eval (fun i => weight (S i)) n xs.
  Proof using Type. intro; subst; apply eval_hd_tl; reflexivity. Qed.

  Lemma eval_weight_mul n p k :
    (forall i, In i (seq 0 n) -> weight i = k * weight' i) ->
    eval weight n p = k * eval weight' n p.
  Proof using Type.
    setoid_rewrite List.in_seq.
    revert n weight weight'; induction p as [|x xs IHxs], n as [|n]; intros weight weight' Hwt;
      cbv [eval to_associational Associational.eval] in *; cbn in *; try omega.
    rewrite Hwt, Z.mul_add_distr_l, Z.mul_assoc by omega.
    erewrite <- !map_S_seq, IHxs; [ reflexivity | ]; cbn; eauto with omega.
  Qed.
End Positional_nonuniform.
End Positional.

Record weight_properties {weight : nat -> Z} :=
  {
    weight_0 : weight 0%nat = 1;
    weight_positive : forall i, 0 < weight i;
    weight_multiples : forall i, weight (S i) mod weight i = 0;
    weight_divides : forall i : nat, 0 < weight (S i) / weight i;
  }.
Hint Resolve weight_0 weight_positive weight_multiples weight_divides.

Section mod_ops.
  Import Positional.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).
  Definition weight (i : nat)
    := 2^(-(-(limbwidth_num * i) / limbwidth_den)).

  Local Ltac Q_cbv :=
    cbv [Qceiling inject_Z Qle Qfloor Qdiv Qnum Qden Qmult Qinv Qopp].

  Local Lemma weight_ZQ_correct i
        (limbwidth := (limbwidth_num / limbwidth_den)%Q)
    : weight i = 2^Qceiling(limbwidth*i).
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cbv [limbwidth weight]; Q_cbv.
    destruct limbwidth_num, limbwidth_den, i; try reflexivity;
      repeat rewrite ?Pos.mul_1_l, ?Pos.mul_1_r, ?Z.mul_0_l, ?Zdiv_0_l, ?Zdiv_0_r, ?Z.mul_1_l, ?Z.mul_1_r, <- ?Z.opp_eq_mul_m1, ?Pos2Z.opp_pos;
      try reflexivity; try lia.
  Qed.

  Local Ltac t_weight_with lem :=
    clear -limbwidth_good;
    intros; rewrite !weight_ZQ_correct;
    apply lem;
    try omega; Q_cbv; destruct limbwidth_den; cbn; try lia.

  Definition wprops : @weight_properties weight.
  Proof using limbwidth_good.
    constructor.
    { cbv [weight Z.of_nat]; autorewrite with zsimplify_fast; reflexivity. }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_pos 2). }
    { t_weight_with (@pow_ceil_mul_nat_multiples 2). }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_divide 2). }
  Defined.
  Local Hint Immediate (weight_0 wprops).
  Local Hint Immediate (weight_positive wprops).
  Local Hint Immediate (weight_multiples wprops).
  Local Hint Immediate (weight_divides wprops).
  Local Hint Resolve Z.positive_is_nonzero Z.lt_gt.

  Local Lemma weight_1_gt_1 : weight 1 > 1.
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cut (1 < weight 1); [ lia | ].
    cbv [weight Z.of_nat]; autorewrite with zsimplify_fast.
    apply Z.pow_gt_1; [ omega | ].
    Z.div_mod_to_quot_rem_in_goal; nia.
  Qed.

  Lemma weight_unique_iff : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j <-> i = j.
  Proof using limbwidth_good.
    clear Hn_nz; clear dependent c.
    cbv [weight]; split; intro H'; subst; trivial; [].
    apply (f_equal (fun x => limbwidth_den * (- Z.log2 x))) in H'.
    rewrite !Z.log2_pow2, !Z.opp_involutive in H' by (Z.div_mod_to_quot_rem; nia).
    Z.div_mod_to_quot_rem.
    destruct i as [|i], j as [|j]; autorewrite with zsimplify_const in *; [ reflexivity | exfalso; nia.. | ].
    nia.
  Qed.
  Lemma weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j.
  Proof using limbwidth_good. apply weight_unique_iff. Qed.

  Derive carry_mulmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (carry_mulmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f * eval weight n g) mod (s - Associational.eval c))
         As eval_carry_mulmod.
  Proof.
    intros.
    rewrite <-eval_mulmod with (s:=s) (c:=c) by auto.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_mulmod; reflexivity.
  Qed.

  Derive carry_squaremod
         SuchThat (forall (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carry_squaremod f)) mod (s - Associational.eval c)
                      = (eval weight n f * eval weight n f) mod (s - Associational.eval c))
         As eval_carry_squaremod.
  Proof.
    intros.
    rewrite <-eval_squaremod with (s:=s) (c:=c) by auto.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_squaremod; reflexivity.
  Qed.

  Derive carry_scmulmod
         SuchThat (forall (x : Z) (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carry_scmulmod x f)) mod (s - Associational.eval c)
                      = (x * eval weight n f) mod (s - Associational.eval c))
         As eval_carry_scmulmod.
  Proof.
    intros.
    push_Zmod.
    rewrite <-eval_encode with (s:=s) (c:=c) (x:=x) (weight:=weight) (n:=n) by auto.
    pull_Zmod.
    rewrite<-eval_mulmod with (s:=s) (c:=c) by (auto; distr_length).
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_scmulmod; reflexivity.
  Qed.

  Derive carrymod
         SuchThat (forall (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carrymod f)) mod (s - Associational.eval c)
                      = (eval weight n f) mod (s - Associational.eval c))
         As eval_carrymod.
  Proof.
    intros.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carrymod; reflexivity.
  Qed.

  Derive addmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (addmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f + eval weight n g) mod (s - Associational.eval c))
         As eval_addmod.
  Proof.
    intros.
    rewrite <-eval_add by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst addmod; reflexivity.
  Qed.

  Derive submod
         SuchThat (forall (coef:Z)
                          (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (submod coef f g)) mod (s - Associational.eval c)
                      = (eval weight n f - eval weight n g) mod (s - Associational.eval c))
         As eval_submod.
  Proof.
    intros.
    rewrite <-eval_sub with (coef:=coef) by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst submod; reflexivity.
  Qed.

  Derive oppmod
         SuchThat (forall (coef:Z)
                          (f: list Z)
                          (Hf : length f = n),
                      (eval weight n (oppmod coef f)) mod (s - Associational.eval c)
                      = (- eval weight n f) mod (s - Associational.eval c))
         As eval_oppmod.
  Proof.
    intros.
    rewrite <-eval_opp with (coef:=coef) by auto.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst oppmod; reflexivity.
  Qed.

  Derive encodemod
         SuchThat (forall (f:Z),
                      (eval weight n (encodemod f)) mod (s - Associational.eval c)
                      = f mod (s - Associational.eval c))
         As eval_encodemod.
  Proof.
    intros.
    etransitivity.
    2:rewrite <-@eval_encode with (weight:=weight) (n:=n) by auto; reflexivity.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst encodemod; reflexivity.
  Qed.
End mod_ops.

Module Saturated.
  Module Associational.
    Section Associational.

      Definition sat_multerm s (t t' : (Z * Z)) : list (Z * Z) :=
        dlet_nd xy := Z.mul_split s (snd t) (snd t') in
              [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (fun t' => sat_multerm s t t') q) p.

      Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * Associational.eval q.
      Proof using Type.
        cbv [sat_multerm Let_In]; induction q;
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
                 | _ => progress simpl flat_map
                 | _ => rewrite IHq
                 | _ => rewrite Z.mod_eq by assumption
                 | _ => ring_simplify; omega
                 end.
      Qed.
      Hint Rewrite eval_map_sat_multerm using (omega || assumption) : push_eval.

      Lemma eval_sat_mul s p q (s_nonzero:s<>0):
        Associational.eval (sat_mul s p q) = Associational.eval p * Associational.eval q.
      Proof using Type.
        cbv [sat_mul]; induction p; [reflexivity|].
        repeat match goal with
               | _ => progress (autorewrite with push_flat_map push_eval in * )
               | _ => rewrite IHp
               | _ => ring_simplify; omega
               end.
      Qed.
      Hint Rewrite eval_sat_mul : push_eval.

      Definition sat_multerm_const s (t t' : (Z * Z)) : list (Z * Z) :=
        if snd t =? 1
        then [(fst t * fst t', snd t')]
        else if snd t =? -1
             then [(fst t * fst t', - snd t')]
             else if snd t =? 0
                  then nil
                  else dlet_nd xy := Z.mul_split s (snd t) (snd t') in
              [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul_const s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (fun t' => sat_multerm_const s t t') q) p.

      Lemma eval_map_sat_multerm_const s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm_const s a) q) = fst a * snd a * Associational.eval q.
      Proof using Type.
        cbv [sat_multerm_const Let_In]; induction q;
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
                 | _ => progress simpl flat_map
                 | H : _ = 1 |- _ => rewrite H
                 | H : _ = -1 |- _ => rewrite H
                 | H : _ = 0 |- _ => rewrite H
                 | _ => progress break_match; Z.ltb_to_lt
                 | _ => rewrite IHq
                 | _ => rewrite Z.mod_eq by assumption
                 | _ => ring_simplify; omega
                 end.
      Qed.
      Hint Rewrite eval_map_sat_multerm_const using (omega || assumption) : push_eval.

      Lemma eval_sat_mul_const s p q (s_nonzero:s<>0):
        Associational.eval (sat_mul_const s p q) = Associational.eval p * Associational.eval q.
      Proof using Type.
        cbv [sat_mul_const]; induction p; [reflexivity|].
        repeat match goal with
               | _ => progress (autorewrite with push_flat_map push_eval in * )
               | _ => rewrite IHp
               | _ => ring_simplify; omega
               end.
      Qed.
      Hint Rewrite eval_sat_mul_const : push_eval.
    End Associational.
  End Associational.
End Saturated.

Module Partition.
  Import Weight.
  Section Partition.
    Context weight {wprops : @weight_properties weight}.

    Hint Resolve Z.positive_is_nonzero Z.lt_gt.

    Definition partition n x :=
      map (fun i => (x mod weight (S i)) / weight i) (seq 0 n).

    Lemma partition_step n x :
      partition (S n) x = partition n x ++ [(x mod weight (S n)) / weight n].
    Proof using Type.
      cbv [partition]. rewrite seq_snoc.
      autorewrite with natsimplify push_map. reflexivity.
    Qed.

    Lemma length_partition n x : length (partition n x) = n.
    Proof using Type. cbv [partition]; distr_length. Qed.
    Hint Rewrite length_partition : distr_length.

    Lemma eval_partition n x :
      Positional.eval weight n (partition n x) = x mod (weight n).
    Proof using wprops.
      induction n; intros.
      { cbn. rewrite (weight_0); auto with zarith. }
      { rewrite (Z.div_mod (x mod weight (S n)) (weight n)) by auto.
        rewrite <-Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto).
        rewrite partition_step, Positional.eval_snoc with (n:=n) by distr_length.
        omega. }
    Qed.

    Lemma partition_Proper n :
      Proper (Z.equiv_modulo (weight n) ==> eq) (partition n).
    Proof using wprops.
      cbv [Proper Z.equiv_modulo respectful].
      intros x y Hxy; induction n; intros.
      { reflexivity. }
      { assert (Hxyn : x mod weight n = y mod weight n).
        { erewrite (Znumtheory.Zmod_div_mod _ (weight (S n)) x), (Znumtheory.Zmod_div_mod _ (weight (S n)) y), Hxy
            by (try apply Z.mod_divide; auto);
            reflexivity. }
        rewrite !partition_step, IHn by eauto.
        rewrite (Z.div_mod (x mod weight (S n)) (weight n)), (Z.div_mod (y mod weight (S n)) (weight n)) by auto.
        rewrite <-!Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto).
        rewrite Hxy, Hxyn; reflexivity. }
    Qed.

    (* This is basically a shortcut for:
       apply partition_Proper; [ | cbv [Z.equiv_modulo] *)
    Lemma partition_eq_mod x y n :
      x mod weight n = y mod weight n ->
      partition n x = partition n y.
    Proof. apply partition_Proper. Qed.

    Fixpoint recursive_partition n i x :=
      match n with
      | O => []
      | S n' => x mod (weight (S i) / weight i) :: recursive_partition n' (S i) (x / (weight (S i) / weight i))
      end.

    Lemma recursive_partition_equiv' n : forall x j,
        map (fun i => x mod weight (S i) / weight i) (seq j n) = recursive_partition n j (x / weight j).
    Proof using wprops.
      induction n; [reflexivity|].
      intros; cbn. rewrite IHn.
      pose proof (@weight_positive _ wprops j).
      pose proof (@weight_divides _ wprops j).
      f_equal;
        repeat match goal with
               | _ => rewrite Z.mod_pull_div by auto using Z.lt_le_incl
               | _ => rewrite weight_multiples by auto
               | _ => progress autorewrite with zsimplify_fast zdiv_to_mod pull_Zdiv
               | _ => reflexivity
               end.
    Qed.

    Lemma recursive_partition_equiv n x :
      partition n x = recursive_partition n 0%nat x.
    Proof using wprops.
      cbv [partition]. rewrite recursive_partition_equiv'.
      rewrite weight_0 by auto; autorewrite with zsimplify_fast.
      reflexivity.
    Qed.

    Lemma length_recursive_partition n : forall i x,
      length (recursive_partition n i x) = n.
    Proof using Type.
      induction n; cbn [recursive_partition]; [reflexivity | ].
      intros; distr_length; auto.
    Qed.

    Lemma drop_high_to_length_partition n m x :
      (n <= m)%nat ->
      Positional.drop_high_to_length n (partition m x) = partition n x.
    Proof using Type.
      cbv [Positional.drop_high_to_length partition]; intros.
      autorewrite with push_firstn.
      rewrite Nat.min_l by omega.
      reflexivity.
    Qed.
  End Partition.
  Hint Rewrite length_partition length_recursive_partition : distr_length.
  Hint Rewrite eval_partition using (solve [auto; distr_length]) : push_eval.
End Partition.

Module Columns.
  Import Saturated. Import Partition. Import Weight.
  Section Columns.
    Context weight {wprops : @weight_properties weight}.
    Hint Resolve Z.positive_is_nonzero Z.lt_gt.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof using Type. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof using Type.
      cbv [eval]; intros; subst. rewrite map_app. simpl map.
      apply Positional.eval_snoc; distr_length.
    Qed. Hint Rewrite eval_snoc using (solve [distr_length]) : push_eval.

    Hint Rewrite <- Z.div_add' using omega : pull_Zdiv.

    Ltac cases :=
      match goal with
      | |- _ /\ _ => split
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | _ => progress break_match; try discriminate
      end.

    Section Flatten.
      Section flatten_column.
        Context (fw : Z). (* maximum size of the result *)

        (* Outputs (sum, carry) *)
        Definition flatten_column (digit: list Z) : (Z * Z) :=
          list_rect (fun _ => (Z * Z)%type) (0,0)
                    (fun xx tl flatten_column_tl =>
                       list_case
                         (fun _ => (Z * Z)%type) (xx mod fw, xx / fw)
                         (fun yy tl' =>
                            list_case
                              (fun _ => (Z * Z)%type) (dlet_nd x := xx in dlet_nd y := yy in Z.add_get_carry_full fw x y)
                              (fun _ _ =>
                                 dlet_nd x := xx in
                                   dlet_nd rec := flatten_column_tl in (* recursively get the sum and carry *)
                                   dlet_nd sum_carry := Z.add_get_carry_full fw x (fst rec) in (* add the new value to the sum *)
                                   dlet_nd carry' := snd sum_carry + snd rec in (* add the two carries together *)
                                   (fst sum_carry, carry'))
                              tl')
                         tl)
                    digit.
      End flatten_column.

      Definition flatten_step (digit:list Z) (acc_carry:list Z * Z) : list Z * Z :=
        dlet sum_carry := flatten_column (weight (S (length (fst acc_carry))) / weight (length (fst acc_carry))) (snd acc_carry::digit) in
              (fst acc_carry ++ fst sum_carry :: nil, snd sum_carry).

      Definition flatten (xs : list (list Z)) : list Z * Z :=
        fold_right (fun a b => flatten_step a b) (nil,0) (rev xs).

      Ltac push_fast :=
        repeat match goal with
               | _ => progress cbv [Let_In list_case]
               | |- context [list_rect _ _ _ ?ls] => rewrite single_list_rect_to_match; destruct ls
               | _ => progress (unfold flatten_step in *; fold flatten_step in * )
               | _ => rewrite Nat.add_1_r
               | _ => rewrite Z.mul_div_eq_full by (auto; omega)
               | _ => rewrite weight_multiples
               | _ => reflexivity
               | _ => solve [repeat (f_equal; try ring)]
               | _ => congruence
               | _ => progress cases
               end.
      Ltac push :=
        repeat match goal with
               | _ => progress push_fast
               | _ => progress autorewrite with cancel_pair to_div_mod
               | _ => progress autorewrite with push_sum push_fold_right push_nth_default in *
               | _ => progress autorewrite with pull_Zmod pull_Zdiv zsimplify_fast
               | _ => progress autorewrite with list distr_length push_eval
               end.

      Lemma flatten_column_mod fw (xs : list Z) :
        fst (flatten_column fw xs)  = sum xs mod fw.
      Proof using Type.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_mod : to_div_mod.

      Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
        snd (flatten_column fw xs)  = sum xs / fw.
      Proof using Type.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => rewrite Z.mul_div_eq_full by omega
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_div using auto with zarith : to_div_mod.

      Hint Rewrite Positional.eval_nil : push_eval.
      Hint Resolve Z.gt_lt.

      Lemma length_flatten_step digit state :
        length (fst (flatten_step digit state)) = S (length (fst state)).
      Proof using Type. cbv [flatten_step]; push. Qed.
      Hint Rewrite length_flatten_step : distr_length.
      Lemma length_flatten inp : length (fst (flatten inp)) = length inp.
      Proof using Type. cbv [flatten]. induction inp using rev_ind; push. Qed.
      Hint Rewrite length_flatten : distr_length.

      Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
      Proof using Type. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

      Lemma flatten_correct inp:
        forall n,
          length inp = n ->
          flatten inp = (partition weight n (eval n inp),
                         eval n inp / (weight n)).
      Proof using wprops.
        induction inp using rev_ind; intros;
          destruct n; distr_length; [ reflexivity | ].
        rewrite flatten_snoc.
        rewrite partition_step.
        erewrite IHinp with (n:=n) by distr_length.
        push.
        pose proof (@weight_positive _ wprops n).
        repeat match goal with
               | |- pair _ _ = pair _ _ => f_equal
               | |- _ ++ _ = _ ++ _ => f_equal
               | |- _ :: _ = _ :: _ => f_equal
               | _ => apply (@partition_eq_mod _ wprops)
               | _ => rewrite length_partition
               | _ => rewrite weight_mod_pull_div by auto
               | _ => rewrite weight_div_pull_div by auto
               | _ => f_equal; ring
               | _ => progress autorewrite with zsimplify
               end.
      Qed.

      Lemma flatten_div_mod n inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp))
         = (eval n inp) mod (weight n))
        /\ (snd (flatten inp) = eval n inp / weight n).
      Proof using wprops.
        intros.
        rewrite flatten_correct with (n:=n) by auto.
        cbn [fst snd].
        rewrite eval_partition; auto.
      Qed.

      Lemma flatten_mod {n} inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
      Proof using wprops. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_mod : push_eval.

      Lemma flatten_div {n} inp :
        length inp = n -> snd (flatten inp) = eval n inp / weight n.
      Proof using wprops. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_div : push_eval.
    End Flatten.

    Section FromAssociational.
      (* nils *)
      Definition nils n : list (list Z) := repeat nil n.
      Lemma length_nils n : length (nils n) = n. Proof using Type. cbv [nils]. distr_length. Qed.
      Hint Rewrite length_nils : distr_length.
      Lemma eval_nils n : eval n (nils n) = 0.
      Proof using Type.
        erewrite <-Positional.eval_zeros by eauto.
        cbv [eval nils]; rewrite List.map_repeat; reflexivity.
      Qed. Hint Rewrite eval_nils : push_eval.

      (* cons_to_nth *)
      Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
        ListUtil.update_nth i (fun y => cons x y) xs.
      Lemma length_cons_to_nth i x xs : length (cons_to_nth i x xs) = length xs.
      Proof using Type. cbv [cons_to_nth]. distr_length. Qed.
      Hint Rewrite length_cons_to_nth : distr_length.
      Lemma cons_to_nth_add_to_nth xs : forall i x,
          map sum (cons_to_nth i x xs) = Positional.add_to_nth i x (map sum xs).
      Proof using Type.
        cbv [cons_to_nth]; induction xs as [|? ? IHxs];
          intros i x; destruct i; simpl; rewrite ?IHxs; reflexivity.
      Qed.
      Lemma eval_cons_to_nth n i x xs : (i < length xs)%nat -> length xs = n ->
                                        eval n (cons_to_nth i x xs) = weight i * x + eval n xs.
      Proof using Type.
        cbv [eval]; intros. rewrite cons_to_nth_add_to_nth.
        apply Positional.eval_add_to_nth; distr_length.
      Qed. Hint Rewrite eval_cons_to_nth using (solve [distr_length]) : push_eval.

      Hint Rewrite Positional.eval_zeros : push_eval.
      Hint Rewrite Positional.eval_add_to_nth using (solve [distr_length]): push_eval.

      (* from_associational *)
      Definition from_associational n (p:list (Z*Z)) : list (list Z) :=
        List.fold_right (fun t ls =>
                           dlet_nd p := Positional.place weight t (pred n) in
                           cons_to_nth (fst p) (snd p) ls ) (nils n) p.
      Lemma length_from_associational n p : length (from_associational n p) = n.
      Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
      Hint Rewrite length_from_associational: distr_length.
      Lemma eval_from_associational n p (n_nonzero:n<>0%nat\/p=nil) :
        eval n (from_associational n p) = Associational.eval p.
      Proof using wprops.
        erewrite <-Positional.eval_from_associational by eauto.
        induction p; [ autorewrite with push_eval; solve [auto] |].
        cbv [from_associational Positional.from_associational]; autorewrite with push_fold_right.
        fold (from_associational n p); fold (Positional.from_associational weight n p).
        cbv [Let_In].
        match goal with |- context [Positional.place _ ?x ?n] =>
                        pose proof (Positional.place_in_range weight x n) end.
        repeat match goal with
               | _ => rewrite Nat.succ_pred in * by auto
               | _ => rewrite IHp by auto
               | _ => progress autorewrite with push_eval
               | _ => progress cases
               | _ => congruence
               end.
      Qed.

      Lemma from_associational_step n t p :
        from_associational n (t :: p) =
        cons_to_nth (fst (Positional.place weight t (Nat.pred n)))
                    (snd (Positional.place weight t (Nat.pred n)))
                    (from_associational n p).
      Proof using Type. reflexivity. Qed.
    End FromAssociational.
  End Columns.
End Columns.

Module Rows.
  Import Saturated. Import Partition. Import Weight.
  Section Rows.
    Context weight {wprops : @weight_properties weight}.
    Hint Resolve Z.positive_is_nonzero Z.lt_gt.
    Local Notation rows := (list (list Z)) (only parsing).
    Local Notation cols := (list (list Z)) (only parsing).

    Hint Rewrite Positional.eval_nil Positional.eval0 @Positional.eval_snoc
         Positional.eval_to_associational
         Columns.eval_nil Columns.eval_snoc using (auto; solve [distr_length]) : push_eval.
    Hint Resolve in_eq in_cons.

    Definition eval n (inp : rows) :=
      sum (map (Positional.eval weight n) inp).
    Lemma eval_nil n : eval n nil = 0.
    Proof using Type. cbv [eval]. rewrite map_nil, sum_nil; reflexivity. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval0 x : eval 0 x = 0.
    Proof using Type. cbv [eval]. induction x; autorewrite with push_map push_sum push_eval; omega. Qed.
    Hint Rewrite eval0 : push_eval.
    Lemma eval_cons n r inp : eval n (r :: inp) = Positional.eval weight n r + eval n inp.
    Proof using Type. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
    Hint Rewrite eval_cons : push_eval.
    Lemma eval_app n x y : eval n (x ++ y) = eval n x + eval n y.
    Proof using Type. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
    Hint Rewrite eval_app : push_eval.

    Ltac In_cases :=
      repeat match goal with
             | H: In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H
             | H: In _ (_ :: _) |- _ => apply in_inv in H; destruct H
             | H: In _ nil |- _ => contradiction H
             | H: forall x, In x (?y :: ?ls) -> ?P |- _ =>
               unique pose proof (H y ltac:(apply in_eq));
               unique assert (forall x, In x ls -> P) by auto
             | H: forall x, In x (?ls ++ ?y :: nil) -> ?P |- _ =>
               unique pose proof (H y ltac:(auto using in_or_app, in_eq));
               unique assert (forall x, In x ls -> P) by eauto using in_or_app
             end.

    Section FromAssociational.
      (* extract row *)
      Definition extract_row (inp : cols) : cols * list Z := (map (fun c => tl c) inp, map (fun c => hd 0 c) inp).

      Lemma eval_extract_row (inp : cols): forall n,
          length inp = n ->
          Positional.eval weight n (snd (extract_row inp)) = Columns.eval weight n inp - Columns.eval weight n (fst (extract_row inp)) .
      Proof using Type.
        cbv [extract_row].
        induction inp using rev_ind; [ | destruct n ];
          repeat match goal with
                 | _ => progress intros
                 | _ => progress distr_length
                 | _ => rewrite Positional.eval_snoc with (n:=n) by distr_length
                 | _ => progress autorewrite with cancel_pair push_eval push_map in *
                 | _ => ring
                 end.
        rewrite IHinp by distr_length.
        destruct x; cbn [hd tl]; rewrite ?sum_nil, ?sum_cons; ring.
      Qed. Hint Rewrite eval_extract_row using (solve [distr_length]) : push_eval.

      Lemma length_fst_extract_row (inp : cols) :
        length (fst (extract_row inp)) = length inp.
      Proof using Type. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_fst_extract_row : distr_length.

      Lemma length_snd_extract_row (inp : cols) :
        length (snd (extract_row inp)) = length inp.
      Proof using Type. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_snd_extract_row : distr_length.

      (* max column size *)
      Definition max_column_size (x:cols) := fold_right (fun a b => Nat.max a b) 0%nat (map (fun c => length c) x).

      (* TODO: move to where list is defined *)
      Hint Rewrite @app_nil_l : list.
      Hint Rewrite <-@app_comm_cons: list.

      Lemma max_column_size_nil : max_column_size nil = 0%nat.
      Proof using Type. reflexivity. Qed. Hint Rewrite max_column_size_nil : push_max_column_size.
      Lemma max_column_size_cons col (inp : cols) :
        max_column_size (col :: inp) = Nat.max (length col) (max_column_size inp).
      Proof using Type. reflexivity. Qed. Hint Rewrite max_column_size_cons : push_max_column_size.
      Lemma max_column_size_app (x y : cols) :
        max_column_size (x ++ y) = Nat.max (max_column_size x) (max_column_size y).
      Proof using Type. induction x; autorewrite with list push_max_column_size; lia. Qed.
      Hint Rewrite max_column_size_app : push_max_column_size.
      Lemma max_column_size0 (inp : cols) :
        forall n,
          length inp = n -> (* this is not needed to make the lemma true, but prevents reliance on the implementation of Columns.eval*)
          max_column_size inp = 0%nat -> Columns.eval weight n inp = 0.
      Proof using Type.
        induction inp as [|x inp] using rev_ind; destruct n; try destruct x; intros;
          autorewrite with push_max_column_size push_eval push_sum distr_length in *; try lia.
        rewrite IHinp; distr_length; lia.
      Qed.

      (* from_columns *)
      Definition from_columns' n start_state : cols * rows :=
        fold_right (fun _ (state : cols * rows) =>
                      let cols'_row := extract_row (fst state) in
                      (fst cols'_row, snd state ++ [snd cols'_row])
                   ) start_state (repeat 0 n).

      Definition from_columns (inp : cols) : rows := snd (from_columns' (max_column_size inp) (inp, [])).

      Local Ltac eval_from_columns'_with_length_t :=
        cbv [from_columns'];
        first [ intros; apply fold_right_invariant; intros
              | apply fold_right_invariant ];
        repeat match goal with
               | _ => progress (intros; subst)
               | _ => progress autorewrite with cancel_pair push_eval in *
               | _ => progress In_cases
               | _ => split; try omega
               | H: _ /\ _ |- _ => destruct H
               | _ => progress distr_length
               | _ => solve [auto]
               end.
      Lemma length_from_columns' m st n:
        (length (fst st) = n) ->
        length (fst (from_columns' m st)) = n /\
        ((forall r, In r (snd st) -> length r = n) ->
         forall r, In r (snd (from_columns' m st)) -> length r = n).
      Proof using Type. eval_from_columns'_with_length_t. Qed.
      Lemma eval_from_columns'_with_length m st n:
        (length (fst st) = n) ->
        length (fst (from_columns' m st)) = n /\
        ((forall r, In r (snd st) -> length r = n) ->
         forall r, In r (snd (from_columns' m st)) -> length r = n) /\
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof using Type. eval_from_columns'_with_length_t. Qed.
      Lemma length_fst_from_columns' m st :
        length (fst (from_columns' m st)) = length (fst st).
      Proof using Type. apply length_from_columns'; reflexivity. Qed.
      Hint Rewrite length_fst_from_columns' : distr_length.
      Lemma length_snd_from_columns' m st :
        (forall r, In r (snd st) -> length r = length (fst st)) ->
        forall r, In r (snd (from_columns' m st)) -> length r = length (fst st).
      Proof using Type. apply length_from_columns'; reflexivity. Qed.
      Hint Rewrite length_snd_from_columns' : distr_length.
      Lemma eval_from_columns' m st n :
        (length (fst st) = n) ->
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof using Type. apply eval_from_columns'_with_length. Qed.
      Hint Rewrite eval_from_columns' using (auto; solve [distr_length]) : push_eval.

      Lemma max_column_size_extract_row inp :
        max_column_size (fst (extract_row inp)) = (max_column_size inp - 1)%nat.
      Proof using Type.
        cbv [extract_row]. autorewrite with cancel_pair.
        induction inp; [ reflexivity | ].
        autorewrite with push_max_column_size push_map distr_length.
        rewrite IHinp. auto using Nat.sub_max_distr_r.
      Qed.
      Hint Rewrite max_column_size_extract_row : push_max_column_size.

      Lemma max_column_size_from_columns' m st :
        max_column_size (fst (from_columns' m st)) = (max_column_size (fst st) - m)%nat.
      Proof using Type.
        cbv [from_columns']; induction m; intros; cbn - [max_column_size extract_row];
          autorewrite with push_max_column_size; lia.
      Qed.
      Hint Rewrite max_column_size_from_columns' : push_max_column_size.

      Lemma eval_from_columns (inp : cols) :
        forall n, length inp = n -> eval n (from_columns inp) = Columns.eval weight n inp.
      Proof using Type.
        intros; cbv [from_columns];
          repeat match goal with
                 | _ => progress autorewrite with cancel_pair push_eval push_max_column_size
                 | _ => rewrite max_column_size0 with (inp := fst (from_columns' _ _)) by
                       (autorewrite with push_max_column_size; distr_length)
                 | _ => omega
                 end.
      Qed.
      Hint Rewrite eval_from_columns using (auto; solve [distr_length]) : push_eval.

      Lemma length_from_columns inp:
        forall r, In r (from_columns inp) -> length r = length inp.
      Proof using Type.
        cbv [from_columns]; intros.
        change inp with (fst (inp, @nil (list Z))).
        eapply length_snd_from_columns'; eauto.
        autorewrite with cancel_pair; intros; In_cases.
      Qed.
      Hint Rewrite length_from_columns using eassumption : distr_length.

      (* from associational *)
      Definition from_associational n (p : list (Z * Z)) := from_columns (Columns.from_associational weight n p).

      Lemma eval_from_associational n p: (n <> 0%nat \/ p = nil) ->
                                         eval n (from_associational n p) = Associational.eval p.
      Proof using wprops.
        intros. cbv [from_associational].
        rewrite eval_from_columns by auto using Columns.length_from_associational.
        auto using Columns.eval_from_associational.
      Qed.

      Lemma length_from_associational n p :
        forall r, In r (from_associational n p) -> length r = n.
      Proof using Type.
        cbv [from_associational]; intros.
        match goal with H: _ |- _ => apply length_from_columns in H end.
        rewrite Columns.length_from_associational in *; auto.
      Qed.

      Lemma max_column_size_zero_iff x :
        max_column_size x = 0%nat <-> (forall c, In c x -> c = nil).
      Proof using Type.
        cbv [max_column_size]; induction x; intros; [ cbn; tauto | ].
        autorewrite with push_fold_right push_map.
        rewrite max_0_iff, IHx.
        split; intros; [ | rewrite length_zero_iff_nil; solve [auto] ].
        match goal with H : _ /\ _ |- _ => destruct H end.
        In_cases; subst; auto using length0_nil.
      Qed.

      Lemma max_column_size_Columns_from_associational n p :
        n <> 0%nat -> p <> nil ->
        max_column_size (Columns.from_associational weight n p) <> 0%nat.
      Proof using Type.
        intros.
        rewrite max_column_size_zero_iff.
        intro. destruct p; [congruence | ].
        rewrite Columns.from_associational_step in *.
        cbv [Columns.cons_to_nth] in *.
        match goal with H : forall c, In c (update_nth ?n ?f ?ls) -> _ |- _ =>
                        assert (n < length (update_nth n f ls))%nat;
                          [ | specialize (H (nth n (update_nth n f ls) nil) ltac:(auto using nth_In)) ]
        end.
        { distr_length.
          rewrite Columns.length_from_associational.
          remember (Nat.pred n) as m. replace n with (S m) by omega.
          apply Positional.place_in_range. }
        rewrite <-nth_default_eq in *.
        autorewrite with push_nth_default in *.
        rewrite eq_nat_dec_refl in *.
        congruence.
      Qed.

      Lemma from_associational_nonnil n p :
        n <> 0%nat -> p <> nil ->
        from_associational n p <> nil.
      Proof using Type.
        intros; cbv [from_associational from_columns from_columns'].
        pose proof (max_column_size_Columns_from_associational n p ltac:(auto) ltac:(auto)).
        case_eq (max_column_size (Columns.from_associational weight n p)); [omega|].
        intros; cbn.
        rewrite <-length_zero_iff_nil. distr_length.
      Qed.
    End FromAssociational.

    Section Flatten.
      Local Notation fw := (fun i => weight (S i) / weight i) (only parsing).

      Section SumRows.
        Definition sum_rows' start_state (row1 row2 : list Z) : list Z * Z * nat :=
          fold_right (fun next (state : list Z * Z * nat) =>
                        let i := snd state in
                        let low_high' :=
                            let low_high := fst state in
                            let low := fst low_high in
                            let high := snd low_high in
                          dlet_nd sum_carry := Z.add_with_get_carry_full (fw i) high (fst next) (snd next) in
                          (low ++ [fst sum_carry], snd sum_carry) in
                     (low_high', S i)) start_state (rev (combine row1 row2)).
        Definition sum_rows row1 row2 := fst (sum_rows' (nil, 0, 0%nat) row1 row2).

        Ltac push :=
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbv [Let_In]
                 | _ => rewrite Nat.add_1_r
                 | _ => erewrite Positional.eval_snoc by eauto
                 | H : length _ = _ |- _ => rewrite H
                 | H: 0%nat = _ |- _ => rewrite <-H
                 | [p := _ |- _] => subst p
                 | _ => progress autorewrite with cancel_pair natsimplify push_sum_rows list
                 | _ => progress autorewrite with cancel_pair in *
                 | _ => progress distr_length
                 | _ => progress break_match
                 | _ => ring
                 | _ => solve [ repeat (f_equal; try ring) ]
                 | _ => tauto
                 | _ => solve [eauto]
                 end.

        Lemma sum_rows'_cons state x1 row1 x2 row2 :
          sum_rows' state (x1 :: row1) (x2 :: row2) =
          sum_rows' (fst (fst state) ++ [(snd (fst state) + x1 + x2) mod (fw (snd state))],
                     (snd (fst state) + x1 + x2) / fw (snd state),
                     S (snd state)) row1 row2.
        Proof using Type.
          cbv [sum_rows' Let_In]; autorewrite with push_combine.
          rewrite !fold_left_rev_right. cbn [fold_left].
          autorewrite with cancel_pair to_div_mod. congruence.
        Qed.

        Lemma sum_rows'_nil state :
          sum_rows' state nil nil = state.
        Proof using Type. reflexivity. Qed.

        Hint Rewrite sum_rows'_cons sum_rows'_nil : push_sum_rows.

        Lemma sum_rows'_correct row1 :
          forall start_state nm row2 row1' row2',
            let m := snd start_state in
            let n := length row1 in
            length row2 = n ->
            length row1' = m ->
            length row2' = m ->
            length (fst (fst start_state)) = m ->
            nm = (n + m)%nat ->
            let eval := Positional.eval weight in
            snd (fst start_state) = (eval m row1' + eval m row2') / weight m ->
            (fst (fst start_state) = partition weight m (eval m row1' + eval m row2')) ->
            let sum := eval nm (row1' ++ row1) + eval nm (row2' ++ row2) in
            sum_rows' start_state row1 row2
            = (partition weight nm sum, sum / weight nm, nm) .
        Proof using wprops.
          destruct start_state as [ [acc rem] m].
          cbn [fst snd]. revert acc rem m.
          induction row1 as [|x1 row1];
            destruct row2 as [|x2 row2]; intros;
              subst nm; push; [ congruence | ].
          rewrite (app_cons_app_app _ row1'), (app_cons_app_app _ row2').
          subst rem acc.
          apply IHrow1; clear IHrow1;
            repeat match goal with
                   | _ => rewrite <-(Z.add_assoc _ x1 x2)
                   | _ => rewrite div_step by auto using Z.gt_lt
                   | _ => rewrite Z.mul_div_eq_full by auto
                   | _ => rewrite weight_multiples by auto
                   | _ => rewrite partition_step by auto
                   | _ => rewrite weight_div_pull_div by auto
                   | _ => rewrite weight_mod_pull_div by auto
                   | _ => rewrite <-Z.div_add' by auto
                   | _ => progress push
                   end.
          f_equal; push; [ ].
          apply (@partition_eq_mod _ wprops).
          push_Zmod.
          autorewrite with zsimplify_fast; reflexivity.
        Qed.

        Lemma sum_rows_correct row1: forall row2 n,
            length row1 = n -> length row2 = n ->
            let sum := Positional.eval weight n row1 + Positional.eval weight n row2 in
            sum_rows row1 row2 = (partition weight n sum, sum / weight n).
        Proof using wprops.
          cbv [sum_rows]; intros.
          erewrite sum_rows'_correct with (nm:=n) (row1':=nil) (row2':=nil)by (cbn; distr_length; reflexivity).
          reflexivity.
        Qed.

        Lemma sum_rows_mod n row1 row2 :
          length row1 = n -> length row2 = n ->
          Positional.eval weight n (fst (sum_rows row1 row2))
          = (Positional.eval weight n row1 + Positional.eval weight n row2) mod (weight n).
        Proof using wprops.
          intros; erewrite sum_rows_correct by eauto.
          cbn [fst]. auto using eval_partition.
        Qed.

        Lemma length_sum_rows row1 row2 n:
          length row1 = n -> length row2 = n ->
          length (fst (sum_rows row1 row2)) = n.
        Proof using wprops.
          intros; erewrite sum_rows_correct by eauto.
          cbn [fst]. distr_length.
        Qed. Hint Rewrite length_sum_rows : distr_length.
      End SumRows.
      Hint Resolve length_sum_rows.
      Hint Rewrite sum_rows_mod using (auto; solve [distr_length; auto]) : push_eval.

      Definition flatten' (start_state : list Z * Z) (inp : rows) : list Z * Z :=
        fold_right (fun next_row (state : list Z * Z)=>
                      let out_carry := sum_rows next_row (fst state) in
                      (fst out_carry, snd state + snd out_carry)) start_state inp.

      (* In order for the output to have the right length and bounds,
         we insert rows of zeroes if there are fewer than two rows. *)
      Definition flatten n (inp : rows) : list Z * Z :=
        let default := Positional.zeros n in
        flatten' (hd default inp, 0) (hd default (tl inp) :: tl (tl inp)).

      Lemma flatten'_cons state r inp :
        flatten' state (r :: inp) = (fst (sum_rows r (fst (flatten' state inp))), snd (flatten' state inp) + snd (sum_rows r (fst (flatten' state inp)))).
      Proof using Type. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_snoc state r inp :
        flatten' state (inp ++ r :: nil) = flatten' (fst (sum_rows r (fst state)), snd state + snd (sum_rows r (fst state))) inp.
      Proof using Type. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_nil state : flatten' state [] = state. Proof using Type. reflexivity. Qed.
      Hint Rewrite flatten'_cons flatten'_snoc flatten'_nil : push_flatten.

      Ltac push :=
        repeat match goal with
               | _ => progress intros
               | _ => erewrite sum_rows_correct by (eassumption || distr_length; reflexivity)
               | _ => rewrite eval_partition by auto
               | H: length _ = _ |- _ => rewrite H
               | _ => progress autorewrite with cancel_pair push_flatten push_eval distr_length zsimplify_fast
               | _ => progress In_cases
               | |- _ /\ _ => split
               | |- context [?x mod ?y] => unique pose proof (Z.mul_div_eq_full x y ltac:(auto)); lia
               | _ => apply length_sum_rows
               | _ => solve [repeat (ring_simplify; f_equal; try ring)]
               | _ => congruence
               | _ => solve [eauto]
               end.

      Lemma flatten'_correct n inp : forall start_state,
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        inp <> nil ->
        let sum := Positional.eval weight n (fst start_state) + eval n inp + weight n * snd start_state in
        flatten' start_state inp = (partition weight n sum, sum / weight n).
      Proof using wprops.
        induction inp using rev_ind; push. subst sum.
        destruct (dec (inp = nil)); [ subst inp; cbn | ];
          repeat match goal with
                 | _ => rewrite IHinp by push; clear IHinp
                 | |- pair _ _ = pair _ _ => f_equal
                 | _ => apply (@partition_eq_mod _ wprops)
                 | _ => rewrite <-Z.div_add_l' by auto
                 | _ => rewrite Z.mod_add'_full by omega
                 | _ => rewrite Z.mul_div_eq_full by auto
                 | _ => progress (push_Zmod; pull_Zmod)
                 | _ => progress push
                 end.
      Qed.

      Hint Rewrite (@Positional.length_zeros) : distr_length.
      Hint Rewrite (@Positional.eval_zeros) using auto : push_eval.

      Lemma flatten_correct inp n :
        (forall row, In row inp -> length row = n) ->
        flatten n inp = (partition weight n (eval n inp), eval n inp / weight n).
      Proof using wprops.
        intros; cbv [flatten].
        destruct inp; [|destruct inp]; cbn [hd tl];
          [ | | erewrite ?flatten'_correct ]; push.
      Qed.

      Lemma flatten_mod inp n :
        (forall row, In row inp -> length row = n) ->
        Positional.eval weight n (fst (flatten n inp)) = (eval n inp) mod (weight n).
      Proof using wprops. intros; rewrite flatten_correct; push. Qed.

      Lemma length_flatten n inp :
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten n inp)) = n.
      Proof using wprops. intros; rewrite flatten_correct by assumption; push. Qed.
    End Flatten.
    Hint Rewrite length_flatten : distr_length.

    Section Ops.
      Definition add n p q := flatten n [p; q].

      (* TODO: Although cleaner, using Positional.negate snd inserts
      dlets which prevent add-opp=>sub transformation in partial
      evaluation. Should probably either make partial evaluation
      handle that or remove the dlet in Positional.from_associational.

      NOTE(from jgross): I think partial evaluation now handles that
      fine; we should check this. *)
      Definition sub n p q := flatten n [p; map (fun x => dlet y := x in Z.opp y) q].

      Definition conditional_add n mask cond (p q:list Z) :=
        let qq := Positional.zselect mask cond q in
        add n p qq.

      (* Subtract q if and only if p >= q. *)
      Definition conditional_sub n (p q:list Z) :=
        let '(v, c) := sub n p q in
        Positional.select (-c) v p.

      (* the carry will be 0 unless we underflow--we do the addition only
         in the underflow case *)
      Definition sub_then_maybe_add n mask (p q r:list Z) :=
        let '(p_minus_q, c) := sub n p q in
        let rr := Positional.zselect mask (-c) r in
        let '(res, c') := add n p_minus_q rr in
        (res, c' - c).

      Hint Rewrite eval_cons eval_nil using solve [auto] : push_eval.

      Definition mul base n m (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        flatten m (from_associational m pq_a).

      (* if [s] is not exactly equal to a weight, we must adjust it to
         be a weight, so that rather than dividing by s and
         multiplying by c, we divide by w and multiply by c*(w/s).
         See
         https://github.com/mit-plv/fiat-crypto/issues/326#issuecomment-404135131
         for a bit more discussion *)
      Definition adjust_s fuel s : Z * bool :=
        fold_right
          (fun w_i res
           => let '(v, found_adjustment) := res in
              let res := (v, found_adjustment) in
              if found_adjustment:bool
              then res
              else if w_i mod s =? 0
                   then (w_i, true)
                   else res)
          (s, false)
          (map weight (List.rev (seq 0 fuel))).

      (* TODO : move sat_reduce and repeat_sat_reduce to Saturated.Associational *)
      Definition sat_reduce base s c n (p : list (Z * Z)) :=
        let '(s', _) := adjust_s (S (S n)) s in
        let lo_hi := Associational.split s' p in
        fst lo_hi ++ (Associational.sat_mul_const base [(1, s'/s)] (Associational.sat_mul_const base c (snd lo_hi))).

      Definition repeat_sat_reduce base s c (p : list (Z * Z)) n :=
        fold_right (fun _ q => sat_reduce base s c n q) p (seq 0 n).

      Definition mulmod base s c n nreductions (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        let r_a := repeat_sat_reduce base s c pq_a nreductions in
        flatten n (from_associational n r_a).

      Hint Rewrite Associational.eval_sat_mul_const Associational.eval_sat_mul Associational.eval_split using solve [auto] : push_eval.
      Hint Rewrite eval_from_associational using solve [auto] : push_eval.
      Ltac solver :=
        intros; cbv [sub add mul mulmod sat_reduce];
        rewrite ?flatten_correct by (intros; In_cases; subst; distr_length; eauto using length_from_associational);
        autorewrite with push_eval; ring_simplify_subterms;
        try reflexivity.

      Lemma add_partitions n p q :
        length p = n -> length q = n ->
        fst (add n p q) = partition weight n (Positional.eval weight n p + Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma add_div n p q :
        length p = n -> length q = n ->
        snd (add n p q) = (Positional.eval weight n p + Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma conditional_add_partitions n mask cond p q :
        length p = n -> length q = n -> map (Z.land mask) q = q ->
        fst (conditional_add n mask cond p q)
        = partition weight n (Positional.eval weight n p + if dec (cond = 0) then 0 else Positional.eval weight n q).
      Proof using wprops.
        cbv [conditional_add]; intros; rewrite add_partitions by (distr_length; auto).
        autorewrite with push_eval; reflexivity.
      Qed.

      Lemma conditional_add_div n mask cond p q :
        length p = n -> length q = n -> map (Z.land mask) q = q ->
        snd (conditional_add n mask cond p q) = (Positional.eval weight n p + if dec (cond = 0) then 0 else Positional.eval weight n q) / weight n.
      Proof using wprops.
        cbv [conditional_add]; intros; rewrite add_div by (distr_length; auto).
        autorewrite with push_eval; auto.
      Qed.

      Lemma eval_map_opp q :
        forall n, length q = n ->
                  Positional.eval weight n (map Z.opp q) = - Positional.eval weight n q.
      Proof using Type.
        induction q using rev_ind; intros;
          repeat match goal with
                 | _ => progress autorewrite with push_map push_eval
                 | _ => erewrite !Positional.eval_snoc with (n:=length q) by distr_length
                 | _ => rewrite IHq by auto
                 | _ => ring
                 end.
      Qed. Hint Rewrite eval_map_opp using solve [auto]: push_eval.

      Lemma sub_partitions n p q :
        length p = n -> length q = n ->
        fst (sub n p q) = partition weight n (Positional.eval weight n p - Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma sub_div n p q :
        length p = n -> length q = n ->
        snd (sub n p q) = (Positional.eval weight n p - Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma conditional_sub_partitions n p q
        (Hp : p = partition weight n (Positional.eval weight n p)) :
        length q = n ->
        0 <= Positional.eval weight n q < weight n ->
        conditional_sub n p q = partition weight n (if Positional.eval weight n q <=? Positional.eval weight n p then Positional.eval weight n p - Positional.eval weight n q else Positional.eval weight n p).
      Proof using wprops.
        cbv [conditional_sub]; intros.
        rewrite (surjective_pairing (sub _ _ _)).
        assert (length p = n) by (rewrite Hp; distr_length).
        assert (0 <= Positional.eval weight n p < weight n) by
            (rewrite Hp; autorewrite with push_eval; auto using Z.mod_pos_bound).
        rewrite sub_partitions, sub_div; distr_length.
        erewrite Positional.select_eq by (distr_length; eauto).
        rewrite Z.div_sub_small, Z.ltb_antisym by omega.
        destruct (Positional.eval weight n q <=? Positional.eval weight n p);
          cbn [negb]; autorewrite with zsimplify_fast;
            break_match; congruence.
      Qed.

      Let sub_then_maybe_add_Z a b c :=
        a - b + (if (a - b <? 0) then c else 0).

      Lemma sub_then_maybe_add_partitions n mask p q r :
        length p = n -> length q = n -> length r = n ->
        map (Z.land mask) r = r ->
        0 <= Positional.eval weight n p < weight n ->
        0 <= Positional.eval weight n q < weight n ->
        fst (sub_then_maybe_add n mask p q r) = partition weight n (sub_then_maybe_add_Z (Positional.eval weight n p) (Positional.eval weight n q) (Positional.eval weight n r)).
      Proof using wprops.
        cbv [sub_then_maybe_add]. subst sub_then_maybe_add_Z.
        intros.
        rewrite (surjective_pairing (sub _ _ _)).
        rewrite (surjective_pairing (add _ _ _)).
        cbn [fst snd].
        rewrite sub_partitions, add_partitions, sub_div by distr_length.
        autorewrite with push_eval.
        Z.rewrite_mod_small.
        rewrite Z.div_sub_small by omega.
        break_innermost_match; Z.ltb_to_lt; try omega;
          auto using partition_eq_mod with zarith.
      Qed.

      Lemma mul_partitions base n m p q :
        base <> 0 -> m <> 0%nat -> length p = n -> length q = n ->
        fst (mul base n m p q) = partition weight m (Positional.eval weight n p * Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma mul_div base n m p q :
        base <> 0 -> m <> 0%nat -> length p = n -> length q = n ->
        snd (mul base n m p q) = (Positional.eval weight n p * Positional.eval weight n q) / weight m.
      Proof using wprops. solver. Qed.

      Lemma length_mul base n m p q :
        length p = n -> length q = n ->
        length (fst (mul base n m p q)) = m.
      Proof using wprops. solver; cbn [fst snd]; distr_length. Qed.

      Lemma adjust_s_invariant fuel s (s_nz:s<>0) :
        fst (adjust_s fuel s) mod s = 0
        /\ fst (adjust_s fuel s) <> 0.
      Proof using wprops.
        cbv [adjust_s]; rewrite fold_right_map; generalize (List.rev (seq 0 fuel)); intro ls; induction ls as [|l ls IHls];
          cbn.
        { rewrite Z.mod_same by assumption; auto. }
        { break_match; cbn in *; auto. }
      Qed.

      Lemma eval_sat_reduce base s c n p :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (sat_reduce base s c n p) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof using wprops.
        intros; cbv [sat_reduce].
        lazymatch goal with |- context[adjust_s ?fuel ?s] => destruct (adjust_s_invariant fuel s ltac:(assumption)) as [Hmod ?] end.
        eta_expand; autorewrite with push_eval zsimplify_const; cbn [fst snd].
        rewrite !Z.mul_assoc, <- (Z.mul_comm (Associational.eval c)), <- !Z.mul_assoc, <-Associational.reduction_rule by auto.
        autorewrite with zsimplify_const; rewrite !Z.mul_assoc, Z.mul_div_eq_full, Hmod by auto.
        autorewrite with zsimplify_const push_eval; trivial.
      Qed.
      Hint Rewrite eval_sat_reduce using auto : push_eval.

      Lemma eval_repeat_sat_reduce base s c p n :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (repeat_sat_reduce base s c p n) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof using wprops.
        intros; cbv [repeat_sat_reduce].
        apply fold_right_invariant; intros; autorewrite with push_eval; auto.
      Qed.
      Hint Rewrite eval_repeat_sat_reduce using auto : push_eval.

      Lemma eval_mulmod base s c n nreductions p q :
        base <> 0 -> s <> 0 -> s - Associational.eval c <> 0 ->
        n <> 0%nat -> length p = n -> length q = n ->
        (Positional.eval weight n (fst (mulmod base s c n nreductions p q))
         + weight n * (snd (mulmod base s c n nreductions p q))) mod (s - Associational.eval c)
        = (Positional.eval weight n p * Positional.eval weight n q) mod (s - Associational.eval c).
      Proof using wprops.
        solver. cbn [fst snd].
        rewrite eval_partition by auto.
        rewrite <-Z.div_mod'' by auto.
        autorewrite with push_eval; reflexivity.
      Qed.

      (* returns all-but-lowest-limb and lowest limb *)
      Definition divmod (p : list Z) : list Z * Z
        := (tl p, hd 0 p).
    End Ops.
  End Rows.
  Hint Rewrite length_from_columns using eassumption : distr_length.
  Hint Rewrite length_sum_rows using solve [ reflexivity | eassumption | distr_length; eauto ] : distr_length.
  Hint Rewrite length_fst_extract_row length_snd_extract_row length_flatten length_fst_from_columns' length_snd_from_columns' : distr_length.
End Rows.

Module BaseConversion.
  Import Positional. Import Partition.
  Section BaseConversion.
    Hint Resolve Z.positive_is_nonzero Z.lt_gt Z.gt_lt.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            {swprops : @weight_properties sw}
            {dwprops : @weight_properties dw}.

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p' := Positional.from_associational dw dn (Positional.to_associational sw sn p) in
      chained_carries_no_reduce dw dn p' (seq 0 (pred dn)).

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof using dwprops.
      cbv [convert_bases]; intros.
      rewrite eval_chained_carries_no_reduce by auto.
      rewrite eval_from_associational; auto.
    Qed.

    Lemma length_convert_bases sn dn p
      : length (convert_bases sn dn p) = dn.
    Proof using Type.
      cbv [convert_bases]; now repeat autorewrite with distr_length.
    Qed.
    Hint Rewrite length_convert_bases : distr_length.

    Lemma convert_bases_partitions sn dn p
          (dw_unique : forall i j : nat, (i <= dn)%nat -> (j <= dn)%nat -> dw i = dw j -> i = j)
          (p_bounded : 0 <= eval sw sn p < dw dn)
      : convert_bases sn dn p = partition dw dn (eval sw sn p).
    Proof using dwprops.
      apply list_elementwise_eq; intro i.
      destruct (lt_dec i dn); [ | now rewrite !nth_error_length_error by distr_length ].
      erewrite !(@nth_error_Some_nth_default _ _ 0) by (break_match; distr_length).
      apply f_equal.
      cbv [convert_bases partition].
      unshelve erewrite map_nth_default, nth_default_chained_carries_no_reduce_pred;
        repeat first [ progress autorewrite with distr_length push_eval
                     | rewrite eval_from_associational, eval_to_associational
                     | rewrite nth_default_seq_inbounds
                     | apply dwprops
                     | destruct dwprops; now auto with zarith ].
    Qed.

    Hint Rewrite
         @Rows.eval_from_associational
         @Associational.eval_carry
         @Associational.eval_mul
         @Positional.eval_to_associational
         Associational.eval_carryterm
         @eval_convert_bases using solve [auto using Z.positive_is_nonzero] : push_eval.

    Ltac push_eval := intros; autorewrite with push_eval; auto with zarith.

    (* convert from positional in one weight to the other, then to associational *)
    Definition to_associational n m p : list (Z * Z) :=
      let p' := convert_bases n m p in
      Positional.to_associational dw m p'.

    (* TODO : move to Associational? *)
    Section reorder.
      Definition reordering_carry (w fw : Z) (p : list (Z * Z)) :=
        fold_right (fun t acc =>
                      let r := Associational.carryterm w fw t in
                      if fst t =? w then acc ++ r else r ++ acc) nil p.

      Lemma eval_reordering_carry w fw p (_:fw<>0):
        Associational.eval (reordering_carry w fw p) = Associational.eval p.
      Proof using Type.
        cbv [reordering_carry]. induction p; [reflexivity |].
        autorewrite with push_fold_right. break_match; push_eval.
      Qed.
    End reorder.
    Hint Rewrite eval_reordering_carry using solve [auto using Z.positive_is_nonzero] : push_eval.

    (* carry at specified indices in dw, then use Rows.flatten to convert to Positional with sw *)
    Definition from_associational idxs n (p : list (Z * Z)) : list Z :=
      (* important not to use Positional.carry here; we don't want to accumulate yet *)
      let p' := fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) (Associational.bind_snd p) (rev idxs) in
      fst (Rows.flatten sw n (Rows.from_associational sw n p')).

    Lemma eval_carries p idxs :
      Associational.eval (fold_right (fun i acc => reordering_carry (dw i) (dw (S i) / dw i) acc) p idxs) =
      Associational.eval p.
    Proof using dwprops. apply fold_right_invariant; push_eval. Qed.
    Hint Rewrite eval_carries: push_eval.

    Lemma eval_to_associational n m p :
      m <> 0%nat -> length p = n ->
      Associational.eval (to_associational n m p) = Positional.eval sw n p.
    Proof using dwprops. cbv [to_associational]; push_eval. Qed.
    Hint Rewrite eval_to_associational using solve [push_eval; distr_length] : push_eval.

    Lemma eval_from_associational idxs n p :
      n <> 0%nat -> 0 <= Associational.eval p < sw n ->
      Positional.eval sw n (from_associational idxs n p) = Associational.eval p.
    Proof using dwprops swprops.
      cbv [from_associational]; intros.
      rewrite Rows.flatten_mod by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.
    Hint Rewrite eval_from_associational using solve [push_eval; distr_length] : push_eval.

    Lemma from_associational_partitions n idxs p  (_:n<>0%nat):
      from_associational idxs n p = partition sw n (Associational.eval p).
    Proof using dwprops swprops.
      intros. cbv [from_associational].
      rewrite Rows.flatten_correct with (n:=n) by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.

    Derive from_associational_inlined
           SuchThat (forall idxs n p,
                        from_associational_inlined idxs n p = from_associational idxs n p)
           As from_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [from_associational reordering_carry Associational.carryterm].
      cbv beta iota delta [Let_In]. (* inlines all shifts/lands from carryterm *)
      cbv beta iota delta [from_associational Rows.from_associational Columns.from_associational].
      cbv beta iota delta [Let_In]. (* inlines the shifts from place *)
      subst from_associational_inlined; reflexivity.
    Qed.

    Derive to_associational_inlined
           SuchThat (forall n m p,
                        to_associational_inlined n m p = to_associational n m p)
           As to_associational_inlined_correct.
    Proof.
      intros.
      cbv beta iota delta [ to_associational convert_bases
                                             Positional.to_associational
                                             Positional.from_associational
                                             chained_carries_no_reduce
                                             carry
                                             Associational.carry
                                             Associational.carryterm
                          ].
      cbv beta iota delta [Let_In].
      subst to_associational_inlined; reflexivity.
    Qed.

    (* carry chain that aligns terms in the intermediate weight with the final weight *)
    Definition aligned_carries (log_dw_sw nout : nat)
      := (map (fun i => ((log_dw_sw * (i + 1)) - 1))%nat (seq 0 nout)).

    Section mul_converted.
      Definition mul_converted
              n1 n2 (* lengths in original format *)
              m1 m2 (* lengths in converted format *)
              (n3 : nat) (* final length *)
              (idxs : list nat) (* carries to do -- this helps preemptively line up weights *)
              (p1 p2 : list Z) :=
        let p1_a := to_associational n1 m1 p1 in
        let p2_a := to_associational n2 m2 p2 in
        let p3_a := Associational.mul p1_a p2_a in
        from_associational idxs n3 p3_a.

      Lemma eval_mul_converted n1 n2 m1 m2 n3 idxs p1 p2 (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        0 <= (Positional.eval sw n1 p1 * Positional.eval sw n2 p2) < sw n3 ->
        Positional.eval sw n3 (mul_converted n1 n2 m1 m2 n3 idxs p1 p2) = (Positional.eval sw n1 p1) * (Positional.eval sw n2 p2).
      Proof using dwprops swprops. cbv [mul_converted]; push_eval. Qed.
      Hint Rewrite eval_mul_converted : push_eval.

      Lemma mul_converted_partitions n1 n2 m1 m2 n3 idxs p1 p2  (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        mul_converted n1 n2 m1 m2 n3 idxs p1 p2 = partition sw n3 (Positional.eval sw n1 p1 * Positional.eval sw n2 p2).
      Proof using dwprops swprops.
        intros; cbv [mul_converted].
        rewrite from_associational_partitions by auto. push_eval.
      Qed.
    End mul_converted.
  End BaseConversion.
  Hint Rewrite length_convert_bases : distr_length.

  (* multiply two (n*k)-bit numbers by converting them to n k-bit limbs each, multiplying, then converting back *)
  Section widemul.
    Context (log2base : Z) (log2base_pos : 0 < log2base).
    Context (n : nat) (n_nz : n <> 0%nat) (n_le_log2base : Z.of_nat n <= log2base)
            (nout : nat) (nout_2 : nout = 2%nat). (* nout is always 2, but partial evaluation is overeager if it's a constant *)
    Let dw : nat -> Z := weight (log2base / Z.of_nat n) 1.
    Let sw : nat -> Z := weight log2base 1.

    Local Lemma base_bounds : 0 < 1 <= log2base. Proof using log2base_pos. clear -log2base_pos; auto with zarith. Qed.
    Local Lemma dbase_bounds : 0 < 1 <= log2base / Z.of_nat n. Proof using n_nz n_le_log2base. clear -n_nz n_le_log2base; auto with zarith. Qed.
    Let dwprops : @weight_properties dw := wprops (log2base / Z.of_nat n) 1 dbase_bounds.
    Let swprops : @weight_properties sw := wprops log2base 1 base_bounds.

    Hint Resolve Z.gt_lt Z.positive_is_nonzero Nat2Z.is_nonneg.

    Definition widemul a b := mul_converted sw dw 1 1 n n nout (aligned_carries n nout) [a] [b].

    Lemma widemul_correct a b :
      0 <= a * b < 2^log2base * 2^log2base ->
      widemul a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base].
    Proof using dwprops swprops nout_2.
      cbv [widemul]; intros.
      rewrite mul_converted_partitions by auto with zarith.
      subst nout.
      unfold sw in *; cbv [weight]; cbn.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, Z.pow_2_r by omega.
      Z.rewrite_mod_small. reflexivity.
    Qed.

    Derive widemul_inlined
           SuchThat (forall a b,
                        0 <= a * b < 2^log2base * 2^log2base ->
                        widemul_inlined a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base])
           As widemul_inlined_correct.
    Proof.
      intros.
      rewrite <-widemul_correct by auto.
      cbv beta iota delta [widemul mul_converted].
      rewrite <-to_associational_inlined_correct with (p:=[a]).
      rewrite <-to_associational_inlined_correct with (p:=[b]).
      rewrite <-from_associational_inlined_correct.
      subst widemul_inlined; reflexivity.
    Qed.

    Derive widemul_inlined_reverse
           SuchThat (forall a b,
                        0 <= a * b < 2^log2base * 2^log2base ->
                        widemul_inlined_reverse a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base])
           As widemul_inlined_reverse_correct.
    Proof.
      intros.
      rewrite <-widemul_inlined_correct by assumption.
      cbv [widemul_inlined].
      match goal with |- _ = from_associational_inlined sw dw ?idxs ?n ?p =>
                      transitivity (from_associational_inlined sw dw idxs n (rev p));
                        [ | transitivity (from_associational sw dw idxs n p); [ | reflexivity ] ](* reverse to make addc chains line up *)
      end.
      { subst widemul_inlined_reverse; reflexivity. }
      { rewrite from_associational_inlined_correct by (subst nout; auto).
        cbv [from_associational].
        rewrite !Rows.flatten_correct by eauto using Rows.length_from_associational.
        rewrite !Rows.eval_from_associational by (subst nout; auto).
        f_equal.
        rewrite !eval_carries, !Associational.bind_snd_correct, !Associational.eval_rev by auto.
        reflexivity. }
    Qed.
  End widemul.
End BaseConversion.

(* TODO: rename this module? (Should it be, e.g., [Rows.freeze]?) *)
Module Freeze.
  Section Freeze.
    Context weight {wprops : @weight_properties weight}.

    Definition freeze n mask (m p:list Z) : list Z :=
      let '(p, carry) := Rows.sub weight n p m in
      let '(r, carry) := Rows.conditional_add weight n mask (-carry) p m in
      r.

    Lemma freezeZ m s c y :
      m = s - c ->
      0 < c < s ->
      s <> 0 ->
      0 <= y < 2*m ->
      ((y - m) + (if (dec (-((y - m) / s) = 0)) then 0 else m)) mod s
      = y mod m.
    Proof using Type.
      clear; intros.
      transitivity ((y - m) mod m);
        repeat first [ progress intros
                     | progress subst
                     | rewrite Z.opp_eq_0_iff in *
                     | break_innermost_match_step
                     | progress autorewrite with zsimplify_fast
                     | rewrite Z.div_small_iff in * by auto
                     | progress (Z.rewrite_mod_small; push_Zmod; Z.rewrite_mod_small)
                     | progress destruct_head'_or
                     | omega ].
    Qed.

    Lemma length_freeze n mask m p :
      length m = n -> length p = n -> length (freeze n mask m p) = n.
    Proof using wprops.
      cbv [freeze Rows.conditional_add Rows.add]; eta_expand; intros.
      distr_length; try assumption; cbn; intros; destruct_head'_or; destruct_head' False; subst;
        distr_length.
      erewrite Rows.length_sum_rows by (reflexivity || eassumption || distr_length); distr_length.
    Qed.
    Lemma eval_freeze_eq n mask m p
          (n_nonzero:n<>0%nat)
          (Hmask : List.map (Z.land mask) m = m)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : Positional.eval weight n (@freeze n mask m p)
        = (Positional.eval weight n p - Positional.eval weight n m +
           (if dec (-((Positional.eval weight n p - Positional.eval weight n m) / weight n) = 0) then 0 else Positional.eval weight n m))
            mod weight n.
            (*if dec ((Positional.eval weight n p - Positional.eval weight n m) / weight n = 0)
          then Positional.eval weight n p - Positional.eval weight n m
          else Positional.eval weight n p mod weight n.*)
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      cbv [freeze Z.equiv_modulo]; eta_expand.
      repeat first [ solve [auto]
                   | rewrite Rows.conditional_add_partitions
                   | rewrite Rows.sub_partitions
                   | rewrite Rows.sub_div
                   | rewrite Partition.eval_partition
                   | progress distr_length
                   | progress pull_Zmod (*
                   | progress break_innermost_match_step
                   | progress destruct_head'_or
                   | omega
                   | f_equal; omega
                   | rewrite Z.div_small_iff in * by (auto using (@weight_positive weight ltac:(assumption)))
                   | progress Z.rewrite_mod_small *) ].
    Qed.

    Lemma eval_freeze n c mask m p
          (n_nonzero:n<>0%nat)
          (Hc : 0 < Associational.eval c < weight n)
          (Hmask : List.map (Z.land mask) m = m)
          (modulus:=weight n - Associational.eval c)
          (Hm : Positional.eval weight n m = modulus)
          (Hp : 0 <= Positional.eval weight n p < 2*modulus)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : Positional.eval weight n (@freeze n mask m p)
        = Positional.eval weight n p mod modulus.
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      rewrite eval_freeze_eq by assumption.
      erewrite freezeZ; try eassumption; try omega.
      f_equal; omega.
    Qed.

    Lemma freeze_partitions n c mask m p
          (n_nonzero:n<>0%nat)
          (Hc : 0 < Associational.eval c < weight n)
          (Hmask : List.map (Z.land mask) m = m)
          (modulus:=weight n - Associational.eval c)
          (Hm : Positional.eval weight n m = modulus)
          (Hp : 0 <= Positional.eval weight n p < 2*modulus)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : @freeze n mask m p = Partition.partition weight n (Positional.eval weight n p mod modulus).
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      pose proof (fun v => Z.mod_pos_bound v (weight n) ltac:(lia)).
      pose proof (Z.mod_pos_bound (Positional.eval weight n p) modulus ltac:(lia)).
      subst modulus.
      erewrite <- eval_freeze by eassumption.
      cbv [freeze]; eta_expand.
      rewrite Rows.conditional_add_partitions by (auto; rewrite Rows.sub_partitions; auto; distr_length).
      rewrite !Partition.eval_partition by assumption.
      apply Partition.partition_Proper; [ assumption .. | ].
      cbv [Z.equiv_modulo].
      pull_Zmod; reflexivity.
    Qed.
  End Freeze.
End Freeze.
Hint Rewrite Freeze.length_freeze : distr_length.

Section freeze_mod_ops.
  Import Positional.
  Import Freeze.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (bitwidth : Z)
          (m_enc : list Z)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat).
  Local Notation bytes_weight := (@weight 8 1).
  Local Notation weight := (@weight limbwidth_num limbwidth_den).
  Let m := (s - Associational.eval c).

  Context (Hs : s = weight n).
  Context (c_small : 0 < Associational.eval c < weight n)
          (m_enc_bounded : List.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_enc_correct : Positional.eval weight n m_enc = m)
          (Hm_enc_len : length m_enc = n).

  Definition wprops_bytes := (@wprops 8 1 ltac:(clear; lia)).
  Local Notation wprops := (@wprops limbwidth_num limbwidth_den limbwidth_good).

  Local Notation wunique := (@weight_unique limbwidth_num limbwidth_den limbwidth_good).
  Local Notation wunique_bytes := (@weight_unique 8 1 ltac:(clear; lia)).

  Local Hint Immediate (wprops).
  Local Hint Immediate (wprops_bytes).
  Local Hint Immediate (weight_0 wprops).
  Local Hint Immediate (weight_positive wprops).
  Local Hint Immediate (weight_multiples wprops).
  Local Hint Immediate (weight_divides wprops).
  Local Hint Immediate (weight_0 wprops_bytes).
  Local Hint Immediate (weight_positive wprops_bytes).
  Local Hint Immediate (weight_multiples wprops_bytes).
  Local Hint Immediate (weight_divides wprops_bytes).
  Local Hint Immediate (wunique) (wunique_bytes).
  Local Hint Resolve (wunique) (wunique_bytes).
  Local Hint Resolve Z.positive_is_nonzero Z.lt_gt.

  Definition bytes_n
    := Eval cbv [Qceiling Qdiv inject_Z Qfloor Qmult Qopp Qnum Qden Qinv Pos.mul]
      in Z.to_nat (Qceiling (Z.log2_up (weight n) / 8)).

  Lemma weight_bytes_weight_matches
    : weight n <= bytes_weight bytes_n.
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cbv [weight bytes_n].
    autorewrite with zsimplify_const.
    rewrite Z.log2_up_pow2, !Z2Nat.id, !Z.opp_involutive by (Z.div_mod_to_quot_rem; nia).
    Z.peel_le.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Definition to_bytes (v : list Z)
    := BaseConversion.convert_bases weight bytes_weight n bytes_n v.

  Definition from_bytes (v : list Z)
    := BaseConversion.convert_bases bytes_weight weight bytes_n n v.

  Definition freeze_to_bytesmod (f : list Z) : list Z
    := to_bytes (freeze weight n (Z.ones bitwidth) m_enc f).

  Definition to_bytesmod (f : list Z) : list Z
    := to_bytes f.

  Definition from_bytesmod (f : list Z) : list Z
    := from_bytes f.

  Lemma bytes_nz : bytes_n <> 0%nat.
  Proof using limbwidth_good Hn_nz.
    clear -limbwidth_good Hn_nz.
    cbv [bytes_n].
    cbv [Qceiling Qdiv inject_Z Qfloor Qmult Qopp Qnum Qden Qinv].
    autorewrite with zsimplify_const.
    change (Z.pos (1*8)) with 8.
    cbv [weight].
    rewrite Z.log2_up_pow2 by (Z.div_mod_to_quot_rem; nia).
    autorewrite with zsimplify_fast.
    rewrite <- Z2Nat.inj_0, Z2Nat.inj_iff by (Z.div_mod_to_quot_rem; nia).
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma bytes_n_big : weight n <= bytes_weight bytes_n.
  Proof using limbwidth_good Hn_nz.
    clear -limbwidth_good Hn_nz.
    cbv [bytes_n bytes_weight].
    Z.peel_le.
    rewrite Z.log2_up_pow2 by (Z.div_mod_to_quot_rem; nia).
    autorewrite with zsimplify_fast.
    rewrite Z2Nat.id by (Z.div_mod_to_quot_rem; nia).
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_to_bytes
    : forall (f : list Z)
        (Hf : length f = n),
      eval bytes_weight bytes_n (to_bytes f) = eval weight n f.
  Proof using limbwidth_good Hn_nz.
    generalize wprops wprops_bytes; clear -Hn_nz limbwidth_good.
    intros.
    cbv [to_bytes].
    rewrite BaseConversion.eval_convert_bases
      by (auto using bytes_nz; distr_length; auto using wprops).
    reflexivity.
  Qed.

  Lemma to_bytes_partitions
    : forall (f : list Z)
             (Hf : length f = n)
             (Hf_small : 0 <= eval weight n f < weight n),
      to_bytes f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f).
  Proof using Hn_nz limbwidth_good.
    clear -Hn_nz limbwidth_good.
    intros; cbv [to_bytes].
    pose proof weight_bytes_weight_matches.
    apply BaseConversion.convert_bases_partitions; eauto; lia.
  Qed.

  Lemma eval_to_bytesmod
    : forall (f : list Z)
             (Hf : length f = n)
             (Hf_small : 0 <= eval weight n f < weight n),
      eval bytes_weight bytes_n (to_bytesmod f) = eval weight n f
      /\ to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f).
  Proof using Hn_nz limbwidth_good.
    split; apply eval_to_bytes || apply to_bytes_partitions; assumption.
  Qed.

  Lemma eval_freeze_to_bytesmod_and_partitions
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      (eval bytes_weight bytes_n (freeze_to_bytesmod f)) = (eval weight n f) mod m
      /\ freeze_to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f mod m).
  Proof using m_enc_correct Hs limbwidth_good Hn_nz c_small Hm_enc_len m_enc_bounded.
    clear -m_enc_correct Hs limbwidth_good Hn_nz c_small Hm_enc_len m_enc_bounded.
    intros; subst m s.
    cbv [freeze_to_bytesmod].
    rewrite eval_to_bytes, to_bytes_partitions;
      erewrite ?eval_freeze by eauto using wprops;
      autorewrite with distr_length; eauto.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_freeze_to_bytesmod
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      (eval bytes_weight bytes_n (freeze_to_bytesmod f)) = (eval weight n f) mod m.
  Proof using m_enc_correct Hs limbwidth_good Hn_nz c_small Hm_enc_len m_enc_bounded.
    intros; now apply eval_freeze_to_bytesmod_and_partitions.
  Qed.

  Lemma freeze_to_bytesmod_partitions
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      freeze_to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f mod m).
  Proof using m_enc_correct Hs limbwidth_good Hn_nz c_small Hm_enc_len m_enc_bounded.
    intros; now apply eval_freeze_to_bytesmod_and_partitions.
  Qed.

  Lemma eval_from_bytes
    : forall (f : list Z)
        (Hf : length f = bytes_n),
      eval weight n (from_bytes f) = eval bytes_weight bytes_n f.
  Proof using limbwidth_good Hn_nz.
    generalize wprops wprops_bytes; clear -Hn_nz limbwidth_good.
    intros.
    cbv [from_bytes].
    rewrite BaseConversion.eval_convert_bases
      by (auto using bytes_nz; distr_length; auto using wprops).
    reflexivity.
  Qed.

  Lemma from_bytes_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      from_bytes f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good.
    clear -limbwidth_good.
    intros; cbv [from_bytes].
    pose proof weight_bytes_weight_matches.
    apply BaseConversion.convert_bases_partitions; eauto; lia.
  Qed.

  Lemma eval_from_bytesmod
    : forall (f : list Z)
             (Hf : length f = bytes_n),
      eval weight n (from_bytesmod f) = eval bytes_weight bytes_n f.
  Proof using Hn_nz limbwidth_good. apply eval_from_bytes. Qed.

  Lemma from_bytesmod_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      from_bytesmod f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good. apply from_bytes_partitions. Qed.

  Lemma eval_from_bytesmod_and_partitions
    : forall (f : list Z)
             (Hf : length f = bytes_n)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      eval weight n (from_bytesmod f) = eval bytes_weight bytes_n f
      /\ from_bytesmod f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good Hn_nz.
    now (split; [ apply eval_from_bytesmod | apply from_bytes_partitions ]).
  Qed.
End freeze_mod_ops.
Hint Rewrite eval_freeze_to_bytesmod eval_to_bytes eval_to_bytesmod eval_from_bytes eval_from_bytesmod : push_eval.

Section primitives.
  Definition mulx (bitwidth : Z) := Eval cbv [Z.mul_split_at_bitwidth] in Z.mul_split_at_bitwidth bitwidth.
  Definition addcarryx (bitwidth : Z) := Eval cbv [Z.add_with_get_carry Z.add_with_carry Z.get_carry] in Z.add_with_get_carry bitwidth.
  Definition subborrowx (bitwidth : Z) := Eval cbv [Z.sub_with_get_borrow Z.sub_with_borrow Z.get_borrow Z.get_carry Z.add_with_carry] in Z.sub_with_get_borrow bitwidth.
  Definition cmovznz (bitwidth : Z) (cond : Z) (z nz : Z)
    := dlet t := (0 - Z.bneg (Z.bneg cond)) mod 2^bitwidth in Z.lor (Z.land t nz) (Z.land (Z.lnot_modulo t (2^bitwidth)) z).

  Lemma mulx_correct (bitwidth : Z)
        (x y : Z)
    : mulx bitwidth x y = ((x * y) mod 2^bitwidth, (x * y) / 2^bitwidth).
  Proof using Type.
    change mulx with Z.mul_split_at_bitwidth.
    rewrite <- Z.mul_split_at_bitwidth_div, <- Z.mul_split_at_bitwidth_mod; eta_expand.
    eta_expand; reflexivity.
  Qed.

  Lemma addcarryx_correct (bitwidth : Z)
        (c x y : Z)
    : addcarryx bitwidth c x y = ((c + x + y) mod 2^bitwidth, (c + x + y) / 2^bitwidth).
  Proof using Type.
    cbv [addcarryx Let_In]; reflexivity.
  Qed.

  Lemma subborrowx_correct (bitwidth : Z)
        (b x y : Z)
    : subborrowx bitwidth b x y = ((-b + x + -y) mod 2^bitwidth, -((-b + x + -y) / 2^bitwidth)).
  Proof using Type.
    cbv [subborrowx Let_In]; reflexivity.
  Qed.

  Lemma cmovznz_correct bitwidth cond z nz
    : 0 <= z < 2^bitwidth
      -> 0 <= nz < 2^bitwidth
      -> cmovznz bitwidth cond z nz = Z.zselect cond z nz.
  Proof using Type.
    intros.
    assert (0 < 2^bitwidth) by omega.
    assert (0 <= bitwidth) by auto with zarith.
    assert (0 < bitwidth -> 1 < 2^bitwidth) by auto with zarith.
    pose proof Z.log2_lt_pow2_alt.
    assert (bitwidth = 0 \/ 0 < bitwidth) by omega.
    repeat first [ progress cbv [cmovznz Z.zselect Z.bneg Let_In Z.lnot_modulo]
                 | progress split_iff
                 | progress subst
                 | progress Z.ltb_to_lt
                 | progress destruct_head'_or
                 | congruence
                 | omega
                 | progress break_innermost_match_step
                 | progress break_innermost_match_hyps_step
                 | progress autorewrite with zsimplify_const in *
                 | progress pull_Zmod
                 | progress intros
                 | rewrite !Z.sub_1_r, <- Z.ones_equiv, <- ?Z.sub_1_r
                 | rewrite Z_mod_nz_opp_full by (Z.rewrite_mod_small; omega)
                 | rewrite (Z.land_comm (Z.ones _))
                 | rewrite Z.land_ones_low by auto with omega
                 | progress Z.rewrite_mod_small ].
  Qed.
End primitives.

Module UniformWeight.
  Definition uweight (lgr : Z) : nat -> Z
    := weight lgr 1.
  Definition uwprops lgr (Hr : 0 < lgr) : @weight_properties (uweight lgr).
  Proof using Type. apply wprops; omega. Qed.
  Lemma uweight_eq_alt' lgr n : uweight lgr n = 2^(lgr*Z.of_nat n).
  Proof using Type. now cbv [uweight weight]; autorewrite with zsimplify_fast. Qed.
  Lemma uweight_eq_alt lgr (Hr : 0 <= lgr) n : uweight lgr n = (2^lgr)^Z.of_nat n.
  Proof using Type. now rewrite uweight_eq_alt', Z.pow_mul_r by lia. Qed.
  Lemma uweight_eval_shift lgr (Hr : 0 <= lgr) xs :
    forall n,
    length xs = n ->
    Positional.eval (fun i => uweight lgr (S i)) n xs =
    (uweight lgr 1) * Positional.eval (uweight lgr) n xs.
  Proof using Type.
    induction xs using rev_ind; destruct n; distr_length;
      intros; [cbn; ring | ].
    rewrite !Positional.eval_snoc with (n:=n) by distr_length.
    rewrite IHxs, !uweight_eq_alt by omega.
    autorewrite with push_Zof_nat push_Zpow.
    rewrite !Z.pow_succ_r by auto using Nat2Z.is_nonneg.
    ring.
  Qed.
  Lemma uweight_S lgr (Hr : 0 <= lgr) n : uweight lgr (S n) = 2 ^ lgr * uweight lgr n.
  Proof using Type.
    rewrite !uweight_eq_alt by auto.
    autorewrite with push_Zof_nat.
    rewrite Z.pow_succ_r by auto using Nat2Z.is_nonneg.
    reflexivity.
  Qed.
  Lemma uweight_double_le lgr (Hr : 0 < lgr) n : uweight lgr n + uweight lgr n <= uweight lgr (S n).
  Proof using Type.
    rewrite uweight_S, uweight_eq_alt by omega.
    rewrite Z.add_diag.
    apply Z.mul_le_mono_nonneg_r.
    { auto with zarith. }
    { transitivity (2 ^ 1); [ reflexivity | ].
      apply Z.pow_le_mono_r; omega. }
  Qed.

  Lemma uweight_1 lgr : uweight lgr 1 = 2^lgr.
  Proof using Type.
    cbv [uweight weight].
    f_equal; autorewrite with zsimplify_const; lia.
  Qed.

  (* Because the weight is uniform, we can start partitioning from
  any index and end up with the same result. *)
  Lemma uweight_recursive_partition_change_start lgr (Hr : 0 <= lgr) n :
    forall i j x,
      Partition.recursive_partition (uweight lgr) n i x
      = Partition.recursive_partition (uweight lgr) n j x.
  Proof using Type.
    induction n; intros; [reflexivity | ].
    cbn [Partition.recursive_partition].
    rewrite !uweight_eq_alt by omega.
    autorewrite with push_Zof_nat push_Zpow.
    rewrite <-!Z.pow_sub_r by auto using Z.pow_nonzero with omega.
    rewrite !Z.sub_succ_l.
    autorewrite with zsimplify_fast.
    erewrite IHn. reflexivity.
  Qed.
  Lemma uweight_recursive_partition_equiv lgr (Hr : 0 < lgr) n i x:
    Partition.partition (uweight lgr) n x =
    Partition.recursive_partition (uweight lgr) n i x.
  Proof using Type.
    rewrite Partition.recursive_partition_equiv by auto using uwprops.
    auto using uweight_recursive_partition_change_start with omega.
  Qed.

  Lemma uweight_partition_unique lgr (Hr : 0 < lgr) n ls :
    length ls = n -> (forall x, List.In x ls -> 0 <= x <= 2^lgr - 1) ->
    ls = Partition.partition (uweight lgr) n (Positional.eval (uweight lgr) n ls).
  Proof using Type.
    intro; subst n.
    rewrite uweight_recursive_partition_equiv with (i:=0%nat) by assumption.
    induction ls as [|x xs IHxs]; [ reflexivity | ].
    repeat first [ progress cbn [List.length Partition.recursive_partition List.In] in *
                 | progress intros
                 | assumption
                 | rewrite Positional.eval_cons by reflexivity
                 | rewrite weight_0 by now apply uwprops
                 | rewrite uweight_1
                 | progress specialize_by_assumption
                 | progress split_contravariant_or
                 | rewrite uweight_recursive_partition_change_start with (i:=1%nat) (j:=0%nat) by lia
                 | rewrite uweight_eval_shift by lia
                 | rewrite Z.div_1_r
                 | progress Z.rewrite_mod_small
                 | rewrite Z.div_add' by auto with arith lia
                 | rewrite Z.div_small by lia
                 | match goal with
                   | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
                   | [ |- context[(_ + ?x * _) mod ?x] ]
                     => let k := fresh in
                        set (k := x); push_Zmod; pull_Zmod; subst k;
                        progress autorewrite with zsimplify_const
                   | [ |- ?x :: _ = ?x :: _ ] => apply f_equal
                   end ].
  Qed.
End UniformWeight.

Module WordByWordMontgomery.
  Import Partition.
  Local Hint Resolve Z.positive_is_nonzero Z.lt_gt Nat2Z.is_nonneg.
  Section with_args.
    Context (lgr : Z)
            (m : Z).
    Local Notation weight := (UniformWeight.uweight lgr).
    Let T (n : nat) := list Z.
    Let r := (2^lgr).
    Definition eval {n} : T n -> Z := Positional.eval weight n.
    Let zero {n} : T n := Positional.zeros n.
    Let divmod {n} : T (S n) -> T n * Z := Rows.divmod.
    Let scmul {n} (c : Z) (p : T n) : T (S n) (* uses double-output multiply *)
      := let '(v, c) := Rows.mul weight r n (S n) (Positional.extend_to_length 1 n [c]) p in
         v.
    Let addT {n} (p q : T n) : T (S n) (* joins carry *)
      := let '(v, c) := Rows.add weight n p q in
         v ++ [c].
    Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
      := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
    Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
      := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
    Context (R_numlimbs : nat)
            (N : T R_numlimbs). (* encoding of m *)
    Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
      := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
    Local Opaque T.
    Section Iteration.
      Context (pred_A_numlimbs : nat)
              (B : T R_numlimbs) (k : Z)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs)).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
      Local Definition A_a := dlet p := @divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
      Local Definition S1 := @addT _ S (@scmul _ a B).
      Local Definition s := snd (@divmod _ S1).
      Local Definition q := fst (Z.mul_split r s k).
      Local Definition S2 := @drop_high_addT' _ S1 (@scmul _ q N).
      Local Definition S3' := fst (@divmod _ S2).

      Local Definition A'_S3
        := dlet A_a := @divmod _ A in
           dlet A' := fst A_a in
           dlet a := snd A_a in
           dlet S1 := @addT _ S (@scmul _ a B) in
           dlet s := snd (@divmod _ S1) in
           dlet q := fst (Z.mul_split r s k) in
           dlet S2 := @drop_high_addT' _ S1 (@scmul _ q N) in
           dlet S3 := fst (@divmod _ S2) in
           (A', S3).

      Lemma A'_S3_alt : A'_S3 = (A', S3').
      Proof using Type. cbv [A'_S3 A' S3' Let_In S2 q s S1 A' a A_a]; reflexivity. Qed.
    End Iteration.

    Section loop.
      Context (A_numlimbs : nat)
              (A : T A_numlimbs)
              (B : T R_numlimbs)
              (k : Z)
              (S' : T (S R_numlimbs)).

      Definition redc_body {pred_A_numlimbs} : T (S pred_A_numlimbs) * T (S R_numlimbs)
                                               -> T pred_A_numlimbs * T (S R_numlimbs)
        := fun '(A, S') => A'_S3 _ B k A S'.

      Definition redc_loop (count : nat) : T count * T (S R_numlimbs) -> T O * T (S R_numlimbs)
        := nat_rect
             (fun count => T count * _ -> _)
             (fun A_S => A_S)
             (fun count' redc_loop_count' A_S
              => redc_loop_count' (redc_body A_S))
             count.

      Definition pre_redc : T (S R_numlimbs)
        := snd (redc_loop A_numlimbs (A, @zero (1 + R_numlimbs)%nat)).

      Definition redc : T R_numlimbs
        := conditional_sub pre_redc N.
    End loop.

    Create HintDb word_by_word_montgomery.
    Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.

    Definition add (A B : T R_numlimbs) : T R_numlimbs
      := conditional_sub (@addT _ A B) N.
    Definition sub (A B : T R_numlimbs) : T R_numlimbs
      := sub_then_maybe_add A B.
    Definition opp (A : T R_numlimbs) : T R_numlimbs
      := sub (@zero _) A.
    Definition nonzero (A : list Z) : Z
      := fold_right Z.lor 0 A.

    Context (lgr_big : 0 < lgr)
            (R_numlimbs_nz : R_numlimbs <> 0%nat).
    Let R := (r^Z.of_nat R_numlimbs).
    Transparent T.
    Definition small {n} (v : T n) : Prop
      := v = partition weight n (eval v).
    Context (small_N : small N)
            (N_lt_R : eval N < R)
            (N_nz : 0 < eval N)
            (B : T R_numlimbs)
            (B_bounds : 0 <= eval B < R)
            (small_B : small B)
            ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
            (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

    Local Lemma r_big : r > 1.
    Proof using lgr_big. clear -lgr_big; subst r. auto with zarith. Qed.
    Local Notation wprops := (@UniformWeight.uwprops lgr lgr_big).

    Local Hint Immediate (wprops).
    Local Hint Immediate (weight_0 wprops).
    Local Hint Immediate (weight_positive wprops).
    Local Hint Immediate (weight_multiples wprops).
    Local Hint Immediate (weight_divides wprops).
    Local Hint Immediate r_big.

    Lemma length_small {n v} : @small n v -> length v = n.
    Proof using Type. clear; cbv [small]; intro H; rewrite H; autorewrite with distr_length; reflexivity. Qed.
    Lemma small_bound {n v} : @small n v -> 0 <= eval v < weight n.
    Proof using lgr_big. clear - lgr_big; cbv [small eval]; intro H; rewrite H; autorewrite with push_eval; auto with zarith. Qed.

    Lemma R_plusR_le : R + R <= weight (S R_numlimbs).
    Proof using lgr_big.
      clear - lgr_big.
      etransitivity; [ | apply UniformWeight.uweight_double_le; omega ].
      rewrite UniformWeight.uweight_eq_alt by omega.
      subst r R; omega.
    Qed.

    Lemma mask_r_sub1 n x :
      map (Z.land (r - 1)) (partition weight n x) = partition weight n x.
    Proof using lgr_big.
      clear - lgr_big. cbv [partition].
      rewrite map_map. apply map_ext; intros.
      rewrite UniformWeight.uweight_S by omega.
      rewrite <-Z.mod_pull_div by auto with zarith.
      replace (r - 1) with (Z.ones lgr) by (rewrite Z.ones_equiv; subst r; reflexivity).
      rewrite <-Z.land_comm, Z.land_ones by omega.
      auto with zarith.
    Qed.

    Let partition_Proper := (@partition_Proper _ wprops).
    Local Existing Instance partition_Proper.
    Lemma eval_nonzero n A : @small n A -> nonzero A = 0 <-> @eval n A = 0.
    Proof using lgr_big.
      clear -lgr_big partition_Proper.
      cbv [nonzero eval small]; intro Heq.
      do 2 rewrite Heq.
      rewrite !eval_partition, Z.mod_mod by auto.
      generalize (Positional.eval weight n A); clear Heq A.
      induction n as [|n IHn].
      { cbn; rewrite weight_0 by auto; intros; autorewrite with zsimplify_const; omega. }
      { intro; rewrite partition_step.
        rewrite fold_right_snoc, Z.lor_comm, <- fold_right_push, Z.lor_eq_0_iff by auto using Z.lor_assoc.
        assert (Heq : Z.equiv_modulo (weight n) (z mod weight (S n)) (z mod (weight n))).
        { cbv [Z.equiv_modulo].
          generalize (weight_multiples ltac:(auto) n).
          generalize (weight_positive ltac:(auto) n).
          generalize (weight_positive ltac:(auto) (S n)).
          generalize (weight (S n)) (weight n); clear; intros wsn wn.
          clear; intros.
          Z.div_mod_to_quot_rem; subst.
          autorewrite with zsimplify_const in *.
          Z.linear_substitute_all.
          apply Zminus_eq; ring_simplify.
          rewrite <- !Z.add_opp_r, !Z.mul_opp_comm, <- !Z.mul_opp_r, <- !Z.mul_assoc.
          rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
          nia. }
        rewrite Heq at 1; rewrite IHn.
        rewrite Z.mod_mod by auto.
        generalize (weight_multiples ltac:(auto) n).
        generalize (weight_positive ltac:(auto) n).
        generalize (weight_positive ltac:(auto) (S n)).
        generalize (weight (S n)) (weight n); clear; intros wsn wn; intros.
        Z.div_mod_to_quot_rem.
        repeat (intro || apply conj); destruct_head'_or; try omega; destruct_head'_and; subst; autorewrite with zsimplify_const in *; try nia;
          Z.linear_substitute_all.
        all: apply Zminus_eq; ring_simplify.
        all: rewrite <- ?Z.add_opp_r, ?Z.mul_opp_comm, <- ?Z.mul_opp_r, <- ?Z.mul_assoc.
        all: rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
        all: nia. }
    Qed.

    Local Ltac push_step :=
      first [ progress eta_expand
            | rewrite Rows.mul_partitions
            | rewrite Rows.mul_div
            | rewrite Rows.add_partitions
            | rewrite Rows.add_div
            | progress autorewrite with push_eval distr_length
            | match goal with
              | [ H : ?v = _ |- context[length ?v] ] => erewrite length_small by eassumption
              | [ H : small ?v |- context[length ?v] ] => erewrite length_small by eassumption
              end
            | rewrite Positional.eval_cons by distr_length
            | progress rewrite ?weight_0, ?UniformWeight.uweight_1 by auto;
              autorewrite with zsimplify_fast
            | rewrite (weight_0 wprops)
            | rewrite <- Z.div_mod'' by auto with omega
            | solve [ trivial ] ].
    Local Ltac push := repeat push_step.

    Local Ltac t_step :=
      match goal with
      | [ H := _ |- _ ] => progress cbv [H] in *
      | _ => progress push_step
      | _ => progress autorewrite with zsimplify_const
      | _ => solve [ auto with omega ]
      end.

    Local Hint Unfold eval zero small divmod scmul drop_high_addT' addT R : loc.
    Local Lemma eval_zero : forall n, eval (@zero n) = 0.
    Proof using Type.
      clear; autounfold with loc; intros; autorewrite with push_eval; auto.
    Qed.
    Local Lemma small_zero : forall n, small (@zero n).
    Proof using Type.
      etransitivity; [ eapply Positional.zeros_ext_map | rewrite eval_zero ]; cbv [partition]; cbn; try reflexivity; autorewrite with distr_length; reflexivity.
    Qed.
    Local Hint Immediate small_zero.

    Ltac push_recursive_partition :=
      repeat match goal with
             | _ => progress cbn [recursive_partition]
             | H : small _ |- _ => rewrite H; clear H
             | _ => rewrite recursive_partition_equiv by auto using wprops
             | _ => rewrite UniformWeight.uweight_eval_shift by distr_length
             | _ => progress push
             end.

    Lemma eval_div : forall n v, small v -> eval (fst (@divmod n v)) = eval v / r.
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod fst tl].
      autorewrite with zsimplify; reflexivity.
    Qed.
    Lemma eval_mod : forall n v, small v -> snd (@divmod n v) = eval v mod r.
    Proof using lgr_big.
      clear - lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod snd hd].
      autorewrite with zsimplify; reflexivity.
    Qed.
    Lemma small_div : forall n v, small v -> small (fst (@divmod n v)).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big. intros; autounfold with loc.
      push_recursive_partition. cbn [Rows.divmod fst tl].
      rewrite <-recursive_partition_equiv by auto.
      rewrite <-UniformWeight.uweight_recursive_partition_equiv with (i:=1%nat) by omega.
      push.
      apply Partition.partition_Proper; [ solve [auto] | ].
      cbv [Z.equiv_modulo]. autorewrite with zsimplify.
      reflexivity.
    Qed.

    Definition canon_rep {n} x (v : T n) : Prop :=
      (v = partition weight n x) /\ (0 <= x < weight n).
    Lemma eval_canon_rep n x v : @canon_rep n x v -> eval v = x.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      auto using Z.mod_small.
    Qed.
    Lemma small_canon_rep n x v : @canon_rep n x v -> small v.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval small]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      apply partition_eq_mod; auto; [ ].
      Z.rewrite_mod_small; reflexivity.
    Qed.

    Local Lemma scmul_correct: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> canon_rep (a * eval v) (@scmul n a v).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - lgr_big r_big.
      autounfold with loc; intro n; destruct (zerop n); intros until 0; intro Hsmall; intros.
      { intros; subst; cbn; rewrite Z.add_with_get_carry_full_mod.
        split; cbn; autorewrite with zsimplify_fast; auto with zarith. }
      { rewrite (surjective_pairing (Rows.mul _ _ _ _ _ _)).
        rewrite Rows.mul_partitions by (try rewrite Hsmall; auto using length_partition, Positional.length_extend_to_length with omega).
        autorewrite with push_eval.
        rewrite Positional.eval_cons by reflexivity.
        rewrite weight_0 by auto.
        autorewrite with push_eval zsimplify_fast.
        split; [reflexivity | ].
        rewrite UniformWeight.uweight_S, UniformWeight.uweight_eq_alt by omega.
        subst r; nia. }
    Qed.

    Local Lemma addT_correct : forall n a b, small a -> small b -> canon_rep (eval a + eval b) (@addT n a b).
    Proof using lgr_big.
      intros n a b Ha Hb.
      generalize (length_small Ha); generalize (length_small Hb).
      generalize (small_bound Ha); generalize (small_bound Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc; destruct (zerop n); subst.
      { destruct a, b; cbn; try omega; split; auto with zarith. }
      { pose proof (UniformWeight.uweight_double_le lgr ltac:(omega) n).
        eta_expand; split; [ | lia ].
        rewrite Rows.add_partitions, Rows.add_div by auto.
        rewrite partition_step.
        Z.rewrite_mod_small; reflexivity. }
    Qed.

    Local Lemma drop_high_addT'_correct : forall n a b, small a -> small b -> canon_rep ((eval a + eval b) mod (r^Z.of_nat (S n))) (@drop_high_addT' n a b).
    Proof using lgr_big.
      intros n a b Ha Hb; generalize (length_small Ha); generalize (length_small Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc in *; subst; intros.
      rewrite Rows.add_partitions by auto using Positional.length_extend_to_length.
      autorewrite with push_eval.
      split; try apply partition_eq_mod; auto; rewrite UniformWeight.uweight_eq_alt by omega; subst r; Z.rewrite_mod_small; auto with zarith.
    Qed.

    Local Lemma conditional_sub_correct : forall v, small v -> 0 <= eval v < eval N + R -> canon_rep (eval v + if eval N <=? eval v then -eval N else 0) (conditional_sub v N).
    Proof using small_N lgr_big N_nz N_lt_R.
      pose proof R_plusR_le as R_plusR_le.
      clear - small_N lgr_big N_nz N_lt_R R_plusR_le.
      intros; autounfold with loc; cbv [conditional_sub].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      autorewrite with push_eval.
      assert (weight R_numlimbs < weight (S R_numlimbs)) by (rewrite !UniformWeight.uweight_eq_alt by omega; autorewrite with push_Zof_nat; auto with zarith).
      assert (eval N mod weight R_numlimbs < weight (S R_numlimbs)) by (pose proof (Z.mod_pos_bound (eval N) (weight R_numlimbs) ltac:(auto)); omega).
      rewrite Rows.conditional_sub_partitions by (repeat (autorewrite with distr_length push_eval; auto using partition_eq_mod with zarith)).
      rewrite drop_high_to_length_partition by omega.
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite UniformWeight.uweight_eq_alt by omega; subst R; reflexivity).
      Z.rewrite_mod_small.
      break_match; autorewrite with zsimplify_fast; Z.ltb_to_lt.
      { split; [ reflexivity | ].
        rewrite Z.add_opp_r. fold (eval N).
        auto using Z.mod_small with lia. }
      { split; auto using Z.mod_small with lia. }
    Qed.

    Local Lemma sub_then_maybe_add_correct : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> canon_rep (eval a - eval b + if eval a - eval b <? 0 then eval N else 0) (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
      pose proof mask_r_sub1 as mask_r_sub1.
      clear - small_N lgr_big R_numlimbs_nz N_nz N_lt_R mask_r_sub1.
      intros; autounfold with loc; cbv [sub_then_maybe_add].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      rewrite Rows.sub_then_maybe_add_partitions by (autorewrite with push_eval distr_length; auto with zarith).
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite UniformWeight.uweight_eq_alt by omega; subst r R; reflexivity).
      Z.rewrite_mod_small.
      split; [ reflexivity | ].
      break_match; Z.ltb_to_lt; lia.
    Qed.

    Local Lemma eval_scmul: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> eval (@scmul n a v) = a * eval v.
    Proof using lgr_big. eauto using scmul_correct, eval_canon_rep. Qed.
    Local Lemma small_scmul : forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> small (@scmul n a v).
    Proof using lgr_big. eauto using scmul_correct, small_canon_rep. Qed.
    Local Lemma eval_addT : forall n a b, small a -> small b -> eval (@addT n a b) = eval a + eval b.
    Proof using lgr_big. eauto using addT_correct, eval_canon_rep. Qed.
    Local Lemma small_addT : forall n a b, small a -> small b -> small (@addT n a b).
    Proof using lgr_big. eauto using addT_correct, small_canon_rep. Qed.
    Local Lemma eval_drop_high_addT' : forall n a b, small a -> small b -> eval (@drop_high_addT' n a b) = (eval a + eval b) mod (r^Z.of_nat (S n)).
    Proof using lgr_big. eauto using drop_high_addT'_correct, eval_canon_rep. Qed.
    Local Lemma small_drop_high_addT' : forall n a b, small a -> small b -> small (@drop_high_addT' n a b).
    Proof using lgr_big. eauto using drop_high_addT'_correct, small_canon_rep. Qed.
    Local Lemma eval_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v N) = eval v + if eval N <=? eval v then -eval N else 0.
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, eval_canon_rep. Qed.
    Local Lemma small_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> small (conditional_sub v N).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, small_canon_rep. Qed.
    Local Lemma eval_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> eval (sub_then_maybe_add a b) = eval a - eval b + if eval a - eval b <? 0 then eval N else 0.
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, eval_canon_rep. Qed.
    Local Lemma small_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> small (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, small_canon_rep. Qed.

    Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
    Create HintDb push_mont_eval discriminated.
    Create HintDb word_by_word_montgomery.
    Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.
    Let r_big' := r_big. (* to put it in the context *)
    Local Ltac t_small :=
      repeat first [ assumption
                   | apply small_addT
                   | apply small_drop_high_addT'
                   | apply small_div
                   | apply small_zero
                   | apply small_scmul
                   | apply small_conditional_sub
                   | apply small_sub_then_maybe_add
                   | apply Z_mod_lt
                   | rewrite Z.mul_split_mod
                   | solve [ auto with zarith ]
                   | lia
                   | progress autorewrite with push_mont_eval
                   | progress autounfold with word_by_word_montgomery
                   | match goal with
                     | [ H : and _ _ |- _ ] => destruct H
                     end ].
    Hint Rewrite
         eval_zero
         eval_div
         eval_mod
         eval_addT
         eval_drop_high_addT'
         eval_scmul
         eval_conditional_sub
         eval_sub_then_maybe_add
         using (repeat autounfold with word_by_word_montgomery; t_small)
      : push_mont_eval.

    Local Arguments eval {_} _.
    Local Arguments small {_} _.
    Local Arguments divmod {_} _.

    (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
    Section Iteration_proofs.
      Context (pred_A_numlimbs : nat)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs))
              (small_A : small A)
              (small_S : small S)
              (S_nonneg : 0 <= eval S).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

      Local Coercion eval : T >-> Z.

      Local Notation a := (@a pred_A_numlimbs A).
      Local Notation A' := (@A' pred_A_numlimbs A).
      Local Notation S1 := (@S1 pred_A_numlimbs B A S).
      Local Notation s := (@s pred_A_numlimbs B A S).
      Local Notation q := (@q pred_A_numlimbs B k A S).
      Local Notation S2 := (@S2 pred_A_numlimbs B k A S).
      Local Notation S3 := (@S3' pred_A_numlimbs B k A S).

      Local Notation eval_pre_S3 := ((S + a * B + q * N) / r).

      Lemma eval_S3_eq : eval S3 = eval_pre_S3 mod (r * r ^ Z.of_nat R_numlimbs).
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        unfold S3, S2, S1.
        autorewrite with push_mont_eval push_Zof_nat; [].
        rewrite !Z.pow_succ_r, <- ?Z.mul_assoc by omega.
        rewrite Z.mod_pull_div by Z.zero_bounds.
        do 2 f_equal; nia.
      Qed.

      Lemma pre_S3_bound
        : eval S < eval N + eval B
          -> eval_pre_S3 < eval N + eval B.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
          by (intros x y; pose proof (Z_mod_lt x y); omega).
        intro HS.
        eapply Z.le_lt_trans.
        { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
            [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
          Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
            repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
              autorewrite with push_mont_eval;
              try Z.zero_bounds;
              auto with lia. }
        rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
        autorewrite with zsimplify.
        simpl; omega.
      Qed.

      Lemma pre_S3_nonneg : 0 <= eval_pre_S3.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg lgr_big.
        clear -N_nz B_bounds small_B partition_Proper r_big' small_A small_S S_nonneg.
        repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
          autorewrite with push_mont_eval; [].
        rewrite ?Npos_correct; Z.zero_bounds; lia.
      Qed.

      Lemma small_A'
        : small A'.
      Proof using small_A lgr_big. repeat autounfold with word_by_word_montgomery; t_small. Qed.

      Lemma small_S3
        : small S3.
      Proof using small_A small_S small_N N_lt_R N_nz B_bounds small_B lgr_big.
        clear -small_A small_S small_N N_lt_R N_nz B_bounds small_B partition_Proper r_big'.
        repeat autounfold with word_by_word_montgomery; t_small.
      Qed.

      Lemma S3_nonneg : 0 <= eval S3.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big sub_then_maybe_add.
        rewrite eval_S3_eq; Z.zero_bounds.
      Qed.

      Lemma S3_bound
        : eval S < eval N + eval B
          -> eval S3 < eval N + eval B.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big.
        clear -N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big partition_Proper r_big' sub_then_maybe_add.
        rewrite eval_S3_eq.
        intro H; pose proof (pre_S3_bound H); pose proof pre_S3_nonneg.
        subst R.
        rewrite Z.mod_small by nia.
        assumption.
      Qed.

      Lemma S1_eq : eval S1 = S + a*B.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper.
        cbv [S1 a A'].
        repeat autorewrite with push_mont_eval.
        reflexivity.
      Qed.

      Lemma S2_mod_r_helper : (S + a*B + q * N) mod r = 0.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct.
        cbv [S2 q s]; autorewrite with push_mont_eval; rewrite S1_eq.
        assert (r > 0) by lia.
        assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
        { destruct (Z.eq_dec r 1) as [H'|H'].
          { rewrite H'; split; reflexivity. }
          { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | omega.. ]. } }
        autorewrite with pull_Zmod.
        replace 0 with (0 mod r) by apply Zmod_0_l.
        pose (Z.to_pos r) as r'.
        replace r with (Z.pos r') by (subst r'; rewrite Z2Pos.id; lia).
        eapply F.eq_of_Z_iff.
        rewrite Z.mul_split_mod.
        repeat rewrite ?F.of_Z_add, ?F.of_Z_mul, <-?F.of_Z_mod.
        rewrite <-!Algebra.Hierarchy.associative.
        replace ((F.of_Z r' k * F.of_Z r' (eval N))%F) with (F.opp (m:=r') F.one).
        { cbv [F.of_Z F.add]; simpl.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ].
          simpl.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), Z.mul_sub_distr_l.
          push_Zmod; pull_Zmod.
          apply (f_equal2 Z.modulo); omega. }
        { rewrite <- F.of_Z_mul.
          rewrite F.of_Z_mod.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite k_correct.
          cbv [F.of_Z F.add F.opp F.one]; simpl.
          change (-(1)) with (-1) in *.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ]; simpl.
          rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), (proj2 Hr); Z.rewrite_mod_small; reflexivity. }
      Qed.

      Lemma pre_S3_mod_N
        : eval_pre_S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct sub_then_maybe_add.
        pose proof fun a => Z.div_to_inv_modulo N a r ri ltac:(lia) ri_correct as HH;
                              cbv [Z.equiv_modulo] in HH; rewrite HH; clear HH.
        etransitivity; [rewrite (fun a => Z.mul_mod_l a ri N)|
                        rewrite (fun a => Z.mul_mod_l a ri N); reflexivity].
        rewrite S2_mod_r_helper.
        push_Zmod; pull_Zmod; autorewrite with zsimplify_const.
        reflexivity.
      Qed.

      Lemma S3_mod_N
            (Hbound : eval S < eval N + eval B)
        : S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct small_N N_lt_R N_nz S_nonneg.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct N_nz N_lt_R small_N sub_then_maybe_add Hbound S_nonneg.
        rewrite eval_S3_eq.
        pose proof (pre_S3_bound Hbound); pose proof pre_S3_nonneg.
        rewrite (Z.mod_small _ (r * _)) by (subst R; nia).
        apply pre_S3_mod_N.
      Qed.
    End Iteration_proofs.

    Section redc_proofs.
      Local Notation redc_body := (@redc_body B k).
      Local Notation redc_loop := (@redc_loop B k).
      Local Notation pre_redc A := (@pre_redc _ A B k).
      Local Notation redc A := (@redc _ A B k).

      Section body.
        Context (pred_A_numlimbs : nat)
                (A_S : T (S pred_A_numlimbs) * T (S R_numlimbs)).
        Let A:=fst A_S.
        Let S:=snd A_S.
        Let A_a:=divmod A.
        Let a:=snd A_a.
        Context (small_A : small A)
                (small_S : small S)
                (S_bound : 0 <= eval S < eval N + eval B).

        Lemma small_fst_redc_body : small (fst (redc_body A_S)).
        Proof using S_bound small_A small_S lgr_big. destruct A_S; apply small_A'; assumption. Qed.
        Lemma small_snd_redc_body : small (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound B_bounds N_nz N_lt_R.
          destruct A_S; unfold redc_body; apply small_S3; assumption.
        Qed.
        Lemma snd_redc_body_nonneg : 0 <= eval (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          destruct A_S; apply S3_nonneg; assumption.
        Qed.

        Lemma snd_redc_body_mod_N
          : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
        Proof using small_S small_N small_B small_A ri_correct lgr_big k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A ri_correct k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add r_big' partition_Proper.
          destruct A_S; apply S3_mod_N; auto; omega.
        Qed.

        Lemma fst_redc_body
          : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
        Proof using small_S small_A S_bound lgr_big.
          destruct A_S; simpl; repeat autounfold with word_by_word_montgomery; simpl.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma fst_redc_body_mod_N
          : (eval (fst (redc_body A_S))) mod (eval N) = ((eval (fst A_S) - a)*ri) mod (eval N).
        Proof using small_S small_A ri_correct lgr_big S_bound.
          rewrite fst_redc_body.
          etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption; lia | ].
          unfold a, A_a, A.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma redc_body_bound
          : eval S < eval N + eval B
            -> eval (snd (redc_body A_S)) < eval N + eval B.
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A S_bound N_nz N_lt_R B_bounds r_big' partition_Proper sub_then_maybe_add.
          destruct A_S; apply S3_bound; unfold S in *; cbn [snd] in *; try assumption; try omega.
        Qed.
      End body.

      Local Arguments Z.pow !_ !_.
      Local Arguments Z.of_nat !_.
      Local Ltac induction_loop count IHcount
        := induction count as [|count IHcount]; intros; cbn [redc_loop nat_rect] in *; [ | (*rewrite redc_loop_comm_body in * *) ].
      Lemma redc_loop_good count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : (small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)))
          /\ 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        induction_loop count IHcount; auto; [].
        change (id (0 <= eval B < R)) in B_bounds (* don't let [destruct_head'_and] loop *).
        destruct_head'_and.
        repeat first [ apply conj
                     | apply small_fst_redc_body
                     | apply small_snd_redc_body
                     | apply redc_body_bound
                     | apply snd_redc_body_nonneg
                     | apply IHcount
                     | solve [ auto ] ].
      Qed.

      Lemma small_redc_loop count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

      Lemma redc_loop_bound count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

      Local Ltac handle_IH_small :=
        repeat first [ apply redc_loop_good
                     | apply small_fst_redc_body
                     | apply small_snd_redc_body
                     | apply redc_body_bound
                     | apply snd_redc_body_nonneg
                     | apply conj
                     | progress cbn [fst snd]
                     | progress destruct_head' and
                     | solve [ auto ] ].

      Lemma fst_redc_loop count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : eval (fst (redc_loop count A_S)) = eval (fst A_S) / r^(Z.of_nat count).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound.
        cbv [redc_loop]; induction_loop count IHcount.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { rewrite IHcount, fst_redc_body by handle_IH_small.
          change (1 + R_numlimbs)%nat with (S R_numlimbs) in *.
          rewrite Zdiv_Zdiv by Z.zero_bounds.
          rewrite <- (Z.pow_1_r r) at 1.
          rewrite <- Z.pow_add_r by lia.
          replace (1 + Z.of_nat count) with (Z.of_nat (S count)) by lia.
          reflexivity. }
      Qed.

      Lemma fst_redc_loop_mod_N count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : eval (fst (redc_loop count A_S)) mod (eval N)
          = (eval (fst A_S) - eval (fst A_S) mod r^Z.of_nat count)
            * ri^(Z.of_nat count) mod (eval N).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds ri_correct.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound ri_correct.
        rewrite fst_redc_loop by assumption.
        destruct count.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { etransitivity;
            [ eapply Z.div_to_inv_modulo;
              try solve [ eassumption
                        | apply Z.lt_gt, Z.pow_pos_nonneg; lia ]
            | ].
          { erewrite <- Z.pow_mul_l, <- Z.pow_1_l.
            { apply Z.pow_mod_Proper; [ eassumption | reflexivity ]. }
            { lia. } }
          reflexivity. }
      Qed.

      Local Arguments Z.pow : simpl never.
      Lemma snd_redc_loop_mod_N count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : (eval (snd (redc_loop count A_S))) mod (eval N)
          = ((eval (snd A_S) + (eval (fst A_S) mod r^(Z.of_nat count))*eval B)*ri^(Z.of_nat count)) mod (eval N).
      Proof using small_N small_B ri_correct lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds k_correct.
        clear -small_N small_B ri_correct r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add k_correct Hsmall Hbound.
        cbv [redc_loop].
        induction_loop count IHcount.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { rewrite IHcount by handle_IH_small.
          push_Zmod; rewrite snd_redc_body_mod_N, fst_redc_body by handle_IH_small; pull_Zmod.
          autorewrite with push_mont_eval; [].
          match goal with
          | [ |- ?x mod ?N = ?y mod ?N ]
            => change (Z.equiv_modulo N x y)
          end.
          destruct A_S as [A S].
          cbn [fst snd].
          change (Z.pos (Pos.of_succ_nat ?n)) with (Z.of_nat (Datatypes.S n)).
          rewrite !Z.mul_add_distr_r.
          rewrite <- !Z.mul_assoc.
          replace (ri * ri^(Z.of_nat count)) with (ri^(Z.of_nat (Datatypes.S count)))
            by (change (Datatypes.S count) with (1 + count)%nat;
                autorewrite with push_Zof_nat; rewrite Z.pow_add_r by lia; simpl Z.succ; rewrite Z.pow_1_r; nia).
          rewrite <- !Z.add_assoc.
          apply Z.add_mod_Proper; [ reflexivity | ].
          unfold Z.equiv_modulo; push_Zmod; rewrite (Z.mul_mod_l (_ mod r) _ (eval N)).
          rewrite Z.mod_pull_div by auto with zarith lia.
          push_Zmod.
          erewrite Z.div_to_inv_modulo;
            [
            | apply Z.lt_gt; lia
            | eassumption ].
          pull_Zmod.
          match goal with
          | [ |- ?x mod ?N = ?y mod ?N ]
            => change (Z.equiv_modulo N x y)
          end.
          repeat first [ rewrite <- !Z.pow_succ_r, <- !Nat2Z.inj_succ by lia
                       | rewrite (Z.mul_comm _ ri)
                       | rewrite (Z.mul_assoc _ ri _)
                       | rewrite (Z.mul_comm _ (ri^_))
                       | rewrite (Z.mul_assoc _ (ri^_) _) ].
          repeat first [ rewrite <- Z.mul_assoc
                       | rewrite <- Z.mul_add_distr_l
                       | rewrite (Z.mul_comm _ (eval B))
                       | rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia;
                         rewrite <- Znumtheory.Zmod_div_mod by (apply Z.divide_factor_r || Z.zero_bounds)
                       | rewrite Zplus_minus
                       | rewrite (Z.mul_comm r (r^_))
                       | reflexivity ]. }
      Qed.

      Lemma pre_redc_bound A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : 0 <= eval (pre_redc A) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma small_pre_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : small (pre_redc A).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma pre_redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (pre_redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct sub_then_maybe_add small_A A_bound.
        unfold pre_redc.
        rewrite snd_redc_loop_mod_N; cbn [fst snd];
          autorewrite with push_mont_eval zsimplify;
          [ | rewrite ?Npos_correct; auto; lia.. ].
        Z.rewrite_mod_small.
        reflexivity.
      Qed.

      Lemma redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B ri_correct lgr_big k_correct R_numlimbs_nz N_nz N_lt_R B_bounds.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        autorewrite with push_mont_eval; [].
        break_innermost_match;
          try rewrite Z.add_opp_r, Zminus_mod, Z_mod_same_full;
          autorewrite with zsimplify_fast;
          apply pre_redc_mod_N; auto.
      Qed.

      Lemma redc_bound_tight A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : 0 <= eval (redc A) < eval N + eval B + if eval N <=? eval (pre_redc A) then -eval N else 0.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds r_big' partition_Proper small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; omega.
      Qed.

      Lemma redc_bound_N A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : eval B < eval N -> 0 <= eval (redc A) < eval N.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; omega.
      Qed.

      Lemma redc_bound A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : 0 <= eval (redc A) < R.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; try omega.
      Qed.

      Lemma small_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : small (redc A).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        apply small_conditional_sub; [ apply small_pre_redc | .. ]; auto; omega.
      Qed.
    End redc_proofs.

    Section add_sub.
      Context (Av Bv : T R_numlimbs)
              (small_Av : small Av)
              (small_Bv : small Bv)
              (Av_bound : 0 <= eval Av < eval N)
              (Bv_bound : 0 <= eval Bv < eval N).

      Local Ltac do_clear :=
        clear dependent B; clear dependent k; clear dependent ri.

      Lemma small_add : small (add Av Bv).
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; t_small.
      Qed.
      Lemma small_sub : small (sub Av Bv).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Bv_bound Av_bound. unfold sub; t_small. Qed.
      Lemma small_opp : small (opp Av).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Av_bound. unfold opp, sub; t_small. Qed.

      Lemma eval_add : eval (add Av Bv) = eval Av + eval Bv + if (eval N <=? eval Av + eval Bv) then -eval N else 0.
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; autorewrite with push_mont_eval; reflexivity.
      Qed.
      Lemma eval_sub : eval (sub Av Bv) = eval Av - eval Bv + if (eval Av - eval Bv <? 0) then eval N else 0.
      Proof using small_Bv small_Av Bv_bound Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. unfold sub; autorewrite with push_mont_eval; reflexivity. Qed.
      Lemma eval_opp : eval (opp Av) = (if (eval Av =? 0) then 0 else eval N) - eval Av.
      Proof using small_Av Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R.
        clear -Av_bound N_nz small_Av partition_Proper r_big' small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
        unfold opp, sub; autorewrite with push_mont_eval.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Local Ltac t_mod_N :=
        repeat first [ progress break_innermost_match
                     | reflexivity
                     | let H := fresh in intro H; rewrite H; clear H
                     | progress autorewrite with zsimplify_const
                     | rewrite Z.add_opp_r
                     | progress (push_Zmod; pull_Zmod) ].

      Lemma eval_add_mod_N : eval (add Av Bv) mod eval N = (eval Av + eval Bv) mod eval N.
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        generalize eval_add; clear. t_mod_N.
      Qed.
      Lemma eval_sub_mod_N : eval (sub Av Bv) mod eval N = (eval Av - eval Bv) mod eval N.
      Proof using small_Bv small_Av Bv_bound Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_sub; clear. t_mod_N. Qed.
      Lemma eval_opp_mod_N : eval (opp Av) mod eval N = (-eval Av) mod eval N.
      Proof using small_Av Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_opp; clear. t_mod_N. Qed.

      Lemma add_bound : 0 <= eval (add Av Bv) < eval N.
      Proof using small_Bv small_Av lgr_big R_numlimbs_nz N_lt_R Bv_bound Av_bound small_N ri k N_nz B_bounds B.
        generalize eval_add; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma sub_bound : 0 <= eval (sub Av Bv) < eval N.
      Proof using small_Bv small_Av R_numlimbs_nz Bv_bound Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        generalize eval_sub; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma opp_bound : 0 <= eval (opp Av) < eval N.
      Proof using small_Av R_numlimbs_nz Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        clear Bv small_Bv Bv_bound.
        generalize eval_opp; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
    End add_sub.
  End with_args.

  Section modops.
    Context (bitwidth : Z)
            (n : nat)
            (m : Z).
    Let r := 2^bitwidth.
    Local Notation weight := (UniformWeight.uweight bitwidth).
    Local Notation eval := (@eval bitwidth n).
    Let m_enc := partition weight n m.
    Local Coercion Z.of_nat : nat >-> Z.
    Context (r' : Z)
            (m' : Z)
            (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bitwidth_big : 0 < bitwidth)
            (m_big : 1 < m)
            (n_nz : n <> 0%nat)
            (m_small : m < r^n).

    Local Notation wprops := (@UniformWeight.uwprops bitwidth bitwidth_big).
    Local Notation small := (@small bitwidth n).

    Local Hint Immediate (wprops).
    Local Hint Immediate (weight_0 wprops).
    Local Hint Immediate (weight_positive wprops).
    Local Hint Immediate (weight_multiples wprops).
    Local Hint Immediate (weight_divides wprops).

    Local Lemma m_enc_correct_montgomery : m = eval m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [eval m_enc]; autorewrite with push_eval; auto.
      rewrite UniformWeight.uweight_eq_alt by omega.
      Z.rewrite_mod_small; reflexivity.
    Qed.
    Local Lemma r'_pow_correct : (r'^n * r^n) mod (eval m_enc) = 1.
    Proof using r'_correct m_small m_big bitwidth_big.
      clear -r'_correct m_small m_big bitwidth_big.
      rewrite <- Z.pow_mul_l, Z.mod_pow_full, ?(Z.mul_comm r'), <- m_enc_correct_montgomery, r'_correct.
      autorewrite with zsimplify_const; auto with omega.
      Z.rewrite_mod_small; omega.
    Qed.
    Local Lemma small_m_enc : small m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [m_enc small eval]; autorewrite with push_eval; auto.
      rewrite UniformWeight.uweight_eq_alt by omega.
      Z.rewrite_mod_small; reflexivity.
    Qed.

    Local Ltac t_fin :=
      repeat match goal with
             | _ => assumption
             | [ |- ?x = ?x ] => reflexivity
             | [ |- and _ _ ] => split
             | _ => rewrite <- !m_enc_correct_montgomery
             | _ => rewrite !r'_correct
             | _ => rewrite !Z.mod_1_l by assumption; reflexivity
             | _ => rewrite !(Z.mul_comm m' m)
             | _ => lia
             | _ => exact small_m_enc
             | [ H : small ?x |- context[eval ?x] ]
               => rewrite H; cbv [eval]; rewrite eval_partition by auto
             | [ |- context[weight _] ] => rewrite UniformWeight.uweight_eq_alt by auto with omega
             | _=> progress Z.rewrite_mod_small
             | _ => progress Z.zero_bounds
             | [ |- _ mod ?x < ?x ] => apply Z.mod_pos_bound
             end.

    Definition mulmod (a b : list Z) : list Z := @redc bitwidth n m_enc n a b m'.
    Definition squaremod (a : list Z) : list Z := mulmod a a.
    Definition addmod (a b : list Z) : list Z := @add bitwidth n m_enc a b.
    Definition submod (a b : list Z) : list Z := @sub bitwidth n m_enc a b.
    Definition oppmod (a : list Z) : list Z := @opp bitwidth n m_enc a.
    Definition nonzeromod (a : list Z) : Z := @nonzero a.
    Definition to_bytesmod (a : list Z) : list Z := @to_bytesmod bitwidth 1 n a.

    Definition valid (a : list Z) := small a /\ 0 <= eval a < m.

    Lemma mulmod_correct0
      : forall a b : list Z,
        small a -> small b
        -> small (mulmod a b)
          /\ (eval b < m -> 0 <= eval (mulmod a b) < m)
          /\ (eval (mulmod a b) mod m = (eval a * eval b * r'^n) mod m).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a b Ha Hb; repeat apply conj; cbv [small mulmod eval];
        [ eapply small_redc
        | rewrite m_enc_correct_montgomery; eapply redc_bound_N
        | rewrite !m_enc_correct_montgomery; eapply redc_mod_N ];
        t_fin.
    Qed.

    Definition onemod : list Z := partition weight n 1.

    Definition onemod_correct : eval onemod = 1 /\ valid onemod.
    Proof using n_nz m_big bitwidth_big.
      clear -n_nz m_big bitwidth_big.
      cbv [valid small onemod eval]; autorewrite with push_eval; t_fin.
    Qed.

    Lemma eval_onemod : eval onemod = 1.
    Proof. apply onemod_correct. Qed.

    Definition R2mod : list Z := partition weight n ((r^n * r^n) mod m).

    Definition R2mod_correct : eval R2mod mod m = (r^n*r^n) mod m /\ valid R2mod.
    Proof using n_nz m_small m_big m'_correct bitwidth_big.
      clear -n_nz m_small m_big m'_correct bitwidth_big.
      cbv [valid small R2mod eval]; autorewrite with push_eval; t_fin;
        rewrite !(Z.mod_small (_ mod m)) by (Z.div_mod_to_quot_rem; subst r; lia);
        t_fin.
    Qed.

    Definition from_montgomerymod (v : list Z) : list Z
      := mulmod v onemod.

    Lemma from_montgomerymod_correct (v : list Z)
      : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m
                  /\ valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      clear -r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intro Hv; cbv [from_montgomerymod valid] in *; destruct_head'_and.
      replace (eval v * r'^n) with (eval v * eval onemod * r'^n) by (rewrite (proj1 onemod_correct); lia).
      repeat apply conj; apply mulmod_correct0; auto; try apply onemod_correct; rewrite (proj1 onemod_correct); omega.
    Qed.

    Lemma eval_from_montgomerymod (v : list Z) : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m.
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.
    Lemma valid_from_montgomerymod (v : list Z)
      : valid v -> valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.

    Lemma mulmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (mulmod a b)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (mulmod a b)).
    Proof using r'_correct r' n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          try apply mulmod_correct0; cbv [valid] in *; destruct_head'_and; auto; [].
      rewrite !Z.mul_assoc.
      apply Z.mul_mod_Proper; [ | reflexivity ].
      cbv [Z.equiv_modulo]; etransitivity; [ apply mulmod_correct0 | apply f_equal2; lia ]; auto.
    Qed.

    Lemma eval_mulmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (mulmod a b)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m).
    Proof. apply mulmod_correct. Qed.

    Lemma squaremod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (squaremod a)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (squaremod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros; cbv [squaremod]; apply mulmod_correct; assumption.
    Qed.

    Lemma eval_squaremod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (squaremod a)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m).
    Proof. apply squaremod_correct. Qed.

    Definition encodemod (v : Z) : list Z
      := mulmod (partition weight n v) R2mod.

    Local Ltac t_valid v :=
      cbv [valid]; repeat apply conj;
      auto; cbv [small eval]; autorewrite with push_eval; auto;
      rewrite ?UniformWeight.uweight_eq_alt by omega;
      Z.rewrite_mod_small;
      rewrite ?(Z.mod_small (_ mod m)) by (subst r; Z.div_mod_to_quot_rem; lia);
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia);
      try apply Z.mod_pos_bound; subst r; try lia; try reflexivity.
    Lemma encodemod_correct
      : (forall v, 0 <= v < m -> eval (from_montgomerymod (encodemod v)) mod m = v mod m)
        /\ (forall v, 0 <= v < m -> valid (encodemod v)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros v ?; cbv [encodemod R2mod]; [ rewrite (proj1 mulmod_correct) | apply mulmod_correct ];
        [ | now t_valid v.. ].
      push_Zmod; rewrite !eval_from_montgomerymod; [ | now t_valid v.. ].
      cbv [eval]; autorewrite with push_eval; auto.
      rewrite ?UniformWeight.uweight_eq_alt by omega.
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia).
      rewrite ?(Z.mod_small (_ mod m)) by (subst r; Z.div_mod_to_quot_rem; lia).
      pull_Zmod.
      rewrite <- !Z.mul_assoc; autorewrite with pull_Zpow.
      generalize r'_correct; push_Zmod; intro Heq; rewrite Heq; clear Heq; pull_Zmod; autorewrite with zsimplify_const.
      rewrite (Z.mul_comm r' r); generalize r'_correct; push_Zmod; intro Heq; rewrite Heq; clear Heq; pull_Zmod; autorewrite with zsimplify_const.
      Z.rewrite_mod_small.
      reflexivity.
    Qed.

    Lemma eval_encodemod
      : (forall v, 0 <= v < m
                   -> eval (from_montgomerymod (encodemod v)) mod m = v mod m).
    Proof. apply encodemod_correct. Qed.

    Lemma addmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (addmod a b)) mod m
                                            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (addmod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid addmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_add || eapply add_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with omega; [ ].
      push_Zmod; erewrite eval_add by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with omega); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_addmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (addmod a b)) mod m
            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m).
    Proof. apply addmod_correct. Qed.

    Lemma submod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (submod a b)) mod m
                                            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (submod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid submod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_sub || eapply sub_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with omega; [ ].
      push_Zmod; erewrite eval_sub by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with omega); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_submod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (submod a b)) mod m
            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m).
    Proof. apply submod_correct. Qed.

    Lemma oppmod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (oppmod a)) mod m
                            = (-eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (oppmod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid oppmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_opp || eapply opp_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with omega; [ ].
      push_Zmod; erewrite eval_opp by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with omega); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_oppmod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (oppmod a)) mod m
            = (-eval (from_montgomerymod a)) mod m).
    Proof. apply oppmod_correct. Qed.

    Lemma nonzeromod_correct
      : (forall a (_ : valid a), (nonzeromod a = 0) <-> ((eval (from_montgomerymod a)) mod m = 0)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a Ha; rewrite eval_from_montgomerymod by assumption.
      cbv [nonzeromod valid] in *; destruct_head'_and.
      rewrite eval_nonzero; try eassumption; [ | subst r; apply conj; try eassumption; omega.. ].
      split; intro H'; [ rewrite H'; autorewrite with zsimplify_const; reflexivity | ].
      assert (H'' : ((eval a * r'^n) * r^n) mod m = 0)
        by (revert H'; push_Zmod; intro H'; rewrite H'; autorewrite with zsimplify_const; reflexivity).
      rewrite <- Z.mul_assoc in H''.
      autorewrite with pull_Zpow push_Zmod in H''.
      rewrite (Z.mul_comm r' r), r'_correct in H''.
      autorewrite with zsimplify_const pull_Zmod in H''; [ | lia.. ].
      clear H'.
      generalize dependent (eval a); clear.
      intros z ???.
      assert (z / m = 0) by (Z.div_mod_to_quot_rem; nia).
      Z.div_mod_to_quot_rem; nia.
    Qed.

    Lemma to_bytesmod_correct
      : (forall a (_ : valid a), Positional.eval (UniformWeight.uweight 8) (bytes_n bitwidth 1 n) (to_bytesmod a)
                                 = eval a mod m)
        /\ (forall a (_ : valid a), to_bytesmod a = partition (UniformWeight.uweight 8) (bytes_n bitwidth 1 n) (eval a mod m)).
    Proof using n_nz m_small bitwidth_big.
      clear -n_nz m_small bitwidth_big.
      generalize (@length_small bitwidth n);
        cbv [valid small to_bytesmod eval]; split; intros; (etransitivity; [ apply eval_to_bytesmod | ]);
          fold weight in *; fold (UniformWeight.uweight 8) in *; subst r;
          try solve [ intuition eauto with omega ].
      all: repeat first [ rewrite UniformWeight.uweight_eq_alt by omega
                        | omega
                        | reflexivity
                        | progress Z.rewrite_mod_small ].
    Qed.

    Lemma eval_to_bytesmod
      : (forall a (_ : valid a),
            Positional.eval (UniformWeight.uweight 8) (bytes_n bitwidth 1 n) (to_bytesmod a)
            = eval a mod m).
    Proof. apply to_bytesmod_correct. Qed.
  End modops.
End WordByWordMontgomery.

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
      represents (Partition.partition w 2 x) x.
    Proof.
      intros; cbn. change_weight.
      Z.rewrite_mod_small.
      autorewrite with zsimplify_fast.
      auto using represents_id.
    Qed.

    Lemma eval_represents t x :
      represents t x -> Positional.eval w 2 t = x.
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

    (* TODO: MOVE Equivlalent Keys decl to Arithmetic? *)
    Declare Equivalent Keys BaseConversion.widemul BaseConversion.widemul_inlined.
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
      assert (0 <= x * y / 2^k < 2^k*2^k) by (Z.div_mod_to_quot_rem_in_goal; nia).

      rewrite mul_high_idea with (a:=x) (b:=y) (a0 := low a) (a1 := high a) (b0 := low b) (b1 := high b) in *
        by (push_rep; Z.div_mod_to_quot_rem_in_goal; lia).

      push_rep. subst a0b1.
      assert (y / 2 ^ k < 2) by (apply Z.div_lt_upper_bound; omega).
      replace (x / 2 ^ k) with 1 in * by (rewrite Z.div_between_1; lia).
      autorewrite with zsimplify_fast in *.

      eapply represents_trans.
      { repeat (apply wideadd_represents;
                [ | apply represents_small; Z.div_mod_to_quot_rem_in_goal; nia| ]).
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
        assert (0 <= x / (2 ^ k * (2 ^ k / 2)) < 2) by (Z.div_mod_to_quot_rem_in_goal; auto with nia).
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
End BarrettReduction.

Module MontgomeryReduction.
  Local Coercion Z.of_nat : nat >-> Z.
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

    Definition montred' (lo hi : Z) :=
      dlet_nd y := nth_default 0 (BaseConversion.widemul_inlined Zlog2R n nout lo N') 0  in
      dlet_nd t1_t2 := (BaseConversion.widemul_inlined_reverse Zlog2R n nout N y) in
      dlet_nd sum_carry := Rows.add (weight Zlog2R 1) 2 [lo;hi] t1_t2 in
      dlet_nd y' := Z.zselect (snd sum_carry) 0 N in
      dlet_nd lo''_carry := Z.sub_get_borrow_full R (nth_default 0 (fst sum_carry) 1) y' in
      Z.add_modulo (fst lo''_carry) 0 N.

    Local Lemma Hw : forall i, w i = R ^ Z.of_nat i.
    Proof.
      clear -R_big_enough R_two_pow; cbv [w weight]; intro.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, R_two_pow by omega; reflexivity.
    Qed.

    Declare Equivalent Keys weight w.
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

    Local Lemma eval2 x y : Positional.eval w 2 [x;y] = x + R * y.
    Proof. cbn. change_weight. ring. Qed.

    Hint Rewrite BaseConversion.widemul_inlined_reverse_correct BaseConversion.widemul_inlined_correct
         using (autorewrite with widemul push_nth_default; solve [solve_range]) : widemul.

    Lemma montred'_eq lo hi T (HT_range: 0 <= T < R * N)
          (Hlo: lo = T mod R) (Hhi: hi = T / R):
      montred' lo hi = reduce_via_partial N R N' T.
    Proof.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi.
      assert (0 <= (T mod R) * N' < w 2) by  (solve_range).

      autorewrite with widemul.
      rewrite Rows.add_partitions, Rows.add_div by (distr_length; apply wprops; omega).
      rewrite R_two_pow.
      cbv [Partition.partition seq]. rewrite !eval2.
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

    Lemma montred'_correct lo hi T (HT_range: 0 <= T < R * N)
          (Hlo: lo = T mod R) (Hhi: hi = T / R): montred' lo hi = (T * R') mod N.
    Proof.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; omega).
      apply reduce_via_partial_in_range; omega.
    Qed.
  End MontRed'.
End MontgomeryReduction.
