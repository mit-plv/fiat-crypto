(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
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

#[global]
  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof. induction p; push; nsatz.                            Qed.
#[global]
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; cbv [mul]; push; nsatz.                 Qed.
#[global]
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
#[global]
  Hint Rewrite eval_square : push_eval.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, -snd cx)) p.
  Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
  Proof. induction p; cbv [negate_snd]; push; nsatz.          Qed.
#[global]
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
#[global]
  Hint Rewrite eval_partition : push_eval.

  Lemma eval_partition' f (p:list (Z*Z)) :
    eval (fst (partition f p)) + eval (snd (partition f p)) = eval p.
  Proof. rewrite Z.add_comm, eval_partition; reflexivity. Qed.
#[global]
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
  Proof using Type. rewrite eval_snd_split, eval_fst_partition by assumption; cbv [split Let_In]; cbn [fst snd]; lia. Qed.

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
#[global]
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

  (* reduce at most [n] times, stopping early if the high list is nil at any point *)
  Definition repeat_reduce (n : nat) (s:Z) (c:list _) (p:list _) : list (Z * Z)
    := nat_rect
         _
         (fun p => p)
         (fun n' repeat_reduce_n' p
          => let lo_hi := split s p in
             if (length (snd lo_hi) =? 0)%nat
             then p
             else let p := fst lo_hi ++ mul c (snd lo_hi) in
                  repeat_reduce_n' p)
         n
         p.

  Lemma repeat_reduce_S_step n s c p
    : repeat_reduce (S n) s c p
      = if (length (snd (split s p)) =? 0)%nat
        then p
        else repeat_reduce n s c (reduce s c p).
  Proof using Type. cbv [repeat_reduce]; cbn [nat_rect]; break_innermost_match; auto. Qed.

  Lemma eval_repeat_reduce n s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (repeat_reduce n s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    revert p; induction n as [|n IHn]; intro p; [ reflexivity | ];
      rewrite repeat_reduce_S_step; break_innermost_match;
        [ reflexivity | rewrite IHn ].
    now rewrite eval_reduce.
  Qed.
#[global]
  Hint Rewrite eval_repeat_reduce : push_eval.

  Lemma eval_repeat_reduce_adjusted n s c p w c' (s_nz:s<>0) (modulus_nz:s-eval c<>0)
        (w_mod:w mod s = 0) (w_nz:w <> 0) (Hc' : eval c' = (w / s) * eval c) :
    eval (repeat_reduce n w c' p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    revert p; induction n as [|n IHn]; intro p; [ reflexivity | ];
      rewrite repeat_reduce_S_step; break_innermost_match;
        [ reflexivity | rewrite IHn ].
    now rewrite eval_reduce_adjusted.
  Qed.

  Definition split_one (s:Z) (w fw : Z) (p:list (Z*Z)) :=
    let hi_lo := partition (fun t => (fst t =? w)) p in
      (snd hi_lo, map (fun t => (fst t / fw, snd t)) (fst hi_lo)).

  Lemma eval_split_one s w fw p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0):
    Associational.eval (fst (split_one s w fw p)) + fw * Associational.eval (snd (split_one s w fw p)) = Associational.eval p.
  Proof.
    remember (Z_div_exact_full_2 _ _ fw_nz w_fw) as H2.
    clear HeqH2 fw_nz w_fw.
    induction p as [|t p'].
    - simpl. cbv [Associational.eval]. simpl. lia.
    - cbv [split_one]. simpl. destruct (fst t =? w) eqn:E.
      + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing.
        destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
        ring_simplify. simpl.
        apply Z.eqb_eq in E. rewrite E. rewrite <- H2. rewrite <- IHp'. ring.
      + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing.
        destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
        rewrite <- IHp'. ring.
  Qed.

  Definition reduce_one (s:Z) (w fw : Z) (c: Z) (p:list _) : list (Z*Z) :=
    let lo_hi := split_one s w fw p in
    fst lo_hi ++ map (fun thing => (fst thing, snd thing * (c * (fw / s)))) (snd lo_hi).

  Lemma eval_map_mul_snd (x:Z) (p:list (Z*Z))
    : Associational.eval (List.map (fun t => (fst t, snd t * x)) p) = x * Associational.eval p.
  Proof. induction p; push; nsatz. Qed.

  Lemma eval_reduce_one s w fw c p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0)
                               (modulus_nz: s - c<>0) :
              Associational.eval (reduce_one s w fw c p) mod (s - c) =
              Associational.eval p mod (s - c).
  Proof using Type.
    cbv [reduce_one]; push.
    rewrite eval_map_mul_snd. rewrite <- Z.mul_assoc.
    rewrite <- (reduction_rule _ _ _ _ modulus_nz).
    rewrite Z.mul_assoc. rewrite <- (Z_div_exact_full_2 fw s s_nz fw_s). rewrite eval_split_one; trivial.
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
#[global]
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
      lia.
    Qed.
    Global Instance leb_Transitive : Transitive leb.
    Proof using Type. repeat intro; unfold is_true, leb in *; Z.ltb_to_lt; lia. Qed.
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
#[global]
  Hint Rewrite eval_map_mul_div using solve [ auto ] : push_eval.

  Lemma eval_map_mul_div' s a b c (s_nz:s <> 0) (a_mod : (a*a) mod s = 0)
    : eval (map (fun x => (((a * a) * fst x) / s, (b * b) * snd x)) c) = ((a * a) / s) * (b * b) * eval c.
  Proof using Type. rewrite <- eval_map_mul_div by assumption; f_equal; apply map_ext; intro; Z.div_mod_to_quot_rem_in_goal; f_equal; nia. Qed.
#[global]
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
#[global]
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
#[global]
  Hint Rewrite fst_split_app snd_split_app : push_eval.

  Lemma eval_reduce_list_rect_app A s c N C p :
    eval (reduce s c (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p))
    = eval (@list_rect A _ (reduce s c N) (fun x xs acc => reduce s c (C x xs) ++ acc) p).
  Proof using Type.
    cbv [reduce]; induction p as [|p ps IHps]; cbn [list_rect]; push; [ nsatz | rewrite <- IHps; clear IHps ].
    push; nsatz.
  Qed.
#[global]
  Hint Rewrite eval_reduce_list_rect_app : push_eval.

  Lemma eval_list_rect_app A N C p :
    eval (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p)
    = @list_rect A _ (eval N) (fun x xs acc => eval (C x xs) + acc) p.
  Proof using Type. induction p; cbn [list_rect]; push; nsatz. Qed.
#[global]
  Hint Rewrite eval_list_rect_app : push_eval.

  Local Existing Instances list_rect_Proper pointwise_map flat_map_Proper.
  Local Hint Extern 0 (Proper _ _) => solve_Proper_eq : typeclass_instances.

  Lemma reduce_nil s c : reduce s c nil = nil.
  Proof using Type. cbv [reduce]; induction c; cbn; intuition auto. Qed.
#[global]
  Hint Rewrite reduce_nil : push_eval.

  Lemma eval_reduce_app s c p q : eval (reduce s c (p ++ q)) = eval (reduce s c p) + eval (reduce s c q).
  Proof using Type. cbv [reduce]; push; nsatz. Qed.
#[global]
  Hint Rewrite eval_reduce_app : push_eval.

  Lemma eval_reduce_cons s c p q :
    eval (reduce s c (p :: q))
    = (if fst p mod s =? 0 then eval c * ((fst p / s) * snd p) else fst p * snd p)
      + eval (reduce s c q).
  Proof using Type.
    cbv [reduce split]; cbn [partition fst snd]; eta_expand; push.
    break_innermost_match; cbn [fst snd map]; push; nsatz.
  Qed.
#[global]
  Hint Rewrite eval_reduce_cons : push_eval.

  Lemma mul_cons_l t ts p :
    mul (t::ts) p = map (fun t' => (fst t * fst t', snd t * snd t')) p ++ mul ts p.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_l p : mul nil p = nil.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_r p : mul p nil = nil.
  Proof using Type. cbv [mul]; induction p; cbn; intuition auto. Qed.
#[global]
  Hint Rewrite mul_nil_l mul_nil_r : push_eval.
  Lemma mul_app_l p p' q :
    mul (p ++ p') q = mul p q ++ mul p' q.
  Proof using Type. cbv [mul]; rewrite flat_map_app; reflexivity. Qed.
  Lemma mul_singleton_l_app_r p q q' :
    mul [p] (q ++ q') = mul [p] q ++ mul [p] q'.
  Proof using Type. cbv [mul flat_map]; rewrite !map_app, !app_nil_r; reflexivity. Qed.
#[global]
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
#[global]
  Hint Rewrite eval_reduce_square : push_eval.

  Definition bind_snd (p : list (Z*Z)) :=
    map (fun t => dlet_nd t2 := snd t in (fst t, t2)) p.

  Lemma bind_snd_correct p : bind_snd p = p.
  Proof using Type.
    cbv [bind_snd]; induction p as [| [? ?] ];
      push; [|rewrite IHp]; reflexivity.
  Qed.

  Definition value_at_weight (a : list (Z * Z)) (d : Z) :=
    fold_right (fun p sum => if (d =? fst p) then (sum + snd p) else sum) 0 a.

  Lemma value_at_weight_works a d : d * (value_at_weight a d) = Associational.eval (filter (fun p => d =? fst p) a).
  Proof.
    induction a as [| a0 a' IHa'].
    - cbv [Associational.eval]. simpl. ring.
    - simpl. destruct (d =? fst a0) eqn:E.
      + rewrite Associational.eval_cons. rewrite <- IHa'. apply Z.eqb_eq in E. rewrite E. ring.
      + apply IHa'.
  Qed.

  Definition firsts (a : list (Z*Z)) :=
    map (fun p => fst p) a.

  Lemma not_in_value_0 a d : ~ In d (firsts a) -> value_at_weight a d = 0.
  Proof.
    intros H. induction a as [| x a' IHa'].
    - reflexivity.
    - simpl. destruct (d =? fst x) eqn:E.
      + exfalso. apply H. simpl. left. apply Z.eqb_eq in E. symmetry. apply E.
      + apply IHa'. intros H'. apply H. simpl. right. apply H'.
  Qed.

  Definition dedup_weights a :=
    map (fun d => (d, value_at_weight a d)) (just_once Z.eqb (firsts a)).

  Lemma map_eq (x y : Z) l a : ~ In x l ->
    map (fun d : Z => (d, value_at_weight a d)) l = map (fun d : Z => (d, if d =? x then (value_at_weight a d + y) else value_at_weight a d)) l.
  Proof.
    intros H. induction l as [|x' l' IHl'].
    - reflexivity.
    - simpl. destruct (x' =? x) eqn:E.
      + exfalso. apply H. apply Z.eqb_eq in E. rewrite E. simpl. left. reflexivity.
      + rewrite IHl'.
        -- reflexivity.
        -- intros H'. apply H. simpl. right. apply H'.
  Qed.

  Theorem eval_dedup_weights a : Associational.eval (dedup_weights a) = Associational.eval a.
  Proof.
    induction a as [| a0 a'].
    - reflexivity.
    - cbv [dedup_weights]. simpl. destruct (is_in Z.eqb (fst a0) (just_once Z.eqb (firsts a'))) eqn:E.
      + apply (is_in_true_iff Z.eqb Z.eqb_eq) in E. rewrite <- (just_once_in_iff Z.eqb Z.eqb_eq) in E. apply (just_once_split Z.eqb Z.eqb_eq) in E.
        destruct E as [l1 [l2 [H1 [H2 H3] ] ] ]. rewrite H1. repeat rewrite map_app. rewrite <- (map_eq _ _ _ _ H2).
        rewrite <- (map_eq _ _ _ _ H3). repeat rewrite Associational.eval_app. simpl. rewrite Z.eqb_refl. repeat rewrite Associational.eval_cons.
        rewrite <- IHa'. simpl. rewrite Associational.eval_nil. cbv [dedup_weights]. rewrite H1.
        repeat rewrite map_app. repeat rewrite Associational.eval_app. cbv [Associational.eval]. simpl. ring.
      + simpl. rewrite Z.eqb_refl. apply (is_in_false_iff Z.eqb Z.eqb_eq) in E. rewrite <- (map_eq _ _ _ _ E). repeat rewrite Associational.eval_cons.
        simpl. rewrite <- IHa'. cbv [dedup_weights]. f_equal. f_equal. rewrite <- (just_once_in_iff Z.eqb Z.eqb_eq) in E. rewrite (not_in_value_0 _ _ E). ring.
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

  (* 'carrying down', aka borrowing *)
  Definition carryterm_down (w fw:Z) (t:Z * Z) :=
      let quot := w / fw in
      if (Z.eqb (fst t) w)
        then [(quot, snd t * fw)]
        else [t].

  Lemma eval_carryterm_down w fw (t:Z * Z) (fw_nz:fw<>0) (w_fw:w mod fw = 0) :
        Associational.eval (carryterm_down w fw t) = Associational.eval [t].
  Proof using Type*.
    cbv [carryterm_down Let_In]; break_match; push; [|trivial].
    pose proof (Z.div_mod (snd t) fw fw_nz).
    rewrite Z.eqb_eq in *.
    ring_simplify. rewrite Z.mul_comm. rewrite Z.mul_assoc. rewrite <- Z_div_exact_full_2; lia.
  Qed.

  Definition carry_down (w fw:Z) (p:list (Z*Z)) :=
    flat_map (carryterm_down w fw) p.

  Lemma eval_carry_down w fw p (fw_nz:fw<>0) (w_fw:w mod fw = 0):
        Associational.eval (carry_down w fw p) = Associational.eval p.
  Proof using Type*.
    cbv [carry_down carryterm_down]. induction p.
    - trivial.
    - push. destruct (fst a =? w) eqn:E.
      + rewrite Z.mul_comm. rewrite <- Z.mul_assoc. rewrite <- Z_div_exact_full_2; lia.
      + rewrite IHp. lia.
  Qed.

  End Carries.
End Associational.

Module Weight.
  Section Weight.
    Context weight
            (weight_0 : weight 0%nat = 1)
            (weight_positive : forall i, 0 < weight i)
            (weight_multiples : forall i, weight (S i) mod weight i = 0)
            (weight_divides : forall i : nat, 0 < weight (S i) / weight i).

    Lemma weight_multiples_full' j : forall i, weight (i+j) mod weight i = 0.
    Proof using weight_positive weight_multiples.
      induction j; intros;
        repeat match goal with
               | _ => rewrite Nat.add_succ_r
               | _ => rewrite IHj
               | |- context [weight (S ?x) mod weight _] =>
                 rewrite (Z.div_mod (weight (S x)) (weight x)), weight_multiples by auto with zarith
               | _ => progress autorewrite with push_Zmod natsimplify zsimplify_fast
               | _ => reflexivity
               end.
    Qed.

    Lemma weight_multiples_full j i : (i <= j)%nat -> weight j mod weight i = 0.
    Proof using weight_positive weight_multiples.
      intros; replace j with (i + (j - i))%nat by lia.
      apply weight_multiples_full'.
    Qed.

    Lemma weight_divides_full j i : (i <= j)%nat -> 0 < weight j / weight i.
    Proof using weight_positive weight_multiples. auto using Z.gt_lt, Z.div_positive_gt_0, weight_multiples_full with zarith. Qed.

    Lemma weight_div_mod j i : (i <= j)%nat -> weight j = weight i * (weight j / weight i).
    Proof using weight_positive weight_multiples. intros. apply Z.div_exact; auto using weight_multiples_full with zarith. Qed.

    Lemma weight_mod_pull_div n x :
      x mod weight (S n) / weight n =
      (x / weight n) mod (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto with zarith
             | _ => rewrite Z.mul_div_eq' by auto with zarith
             | _ => rewrite Z.mod_pull_div
             | _ => rewrite weight_multiples by auto with zarith
             | _ => solve [auto with zarith]
             end.
    Qed.

    Lemma weight_div_pull_div n x :
      x / weight (S n) =
      (x / weight n) / (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zdiv_to_mod zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto with zarith
             | _ => rewrite Z.mul_div_eq' by auto with zarith
             | _ => rewrite Z.div_div by auto with zarith
             | _ => rewrite weight_multiples by assumption
             | _ => solve [auto with zarith]
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
  Lemma add_to_nth_zero i l : add_to_nth i 0 l = l.
  Proof. cbv [add_to_nth]. apply update_nth_id_eq. reflexivity. Qed.

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
  Proof using Type. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try lia. Qed.
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
    { destruct (dec (j < i)%nat); [ left; lia | intro H; right; revert H ].
      assert (j = (j - i) + i)%nat by lia.
      generalize dependent (j - i)%nat; intro jmi; intros ? H0.
      subst j.
      destruct jmi as [|j]; [ intros k ?; assert (k = i) by lia; subst; f_equal; lia | ].
      induction j as [|j IH]; cbn [Nat.add] in *.
      { intros k ?; assert (k = i \/ k = S i) by lia; destruct_head'_or; subst;
          eauto using Z.mod_mod_0_0_eq_pos. }
      { specialize_by lia.
        { pose proof (weight_mul (S (j + i))) as H.
          specialize_by eauto using Z.mod_mod_trans with lia.
          intros k H'; destruct (dec (k = S (S (j + i)))); subst;
            try rewrite IH by eauto using Z.mod_mod_trans with lia;
            eauto using Z.mod_mod_trans, Z.mod_mod_0_0_eq_pos with lia.
          rewrite (IH i) in * by lia.
          eauto using Z.mod_mod_trans, Z.mod_mod_0_0_eq_pos with lia. } } }
    { destruct (dec (j < i)%nat) as [H|H]; [ intros _ | intros [H'|H']; try lia ].
      { assert (i = j + (i - j))%nat by lia.
        generalize dependent (i - j)%nat; intro imj; intros.
        subst i.
        apply weight_add_mod; auto. }
      { erewrite H', Z_mod_same_full by lia; lia. } }
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
        rewrite ?Min.min_l in * by lia;
        rewrite ?Min.min_r in * by lia;
        eauto with lia.
    { rewrite weight_mul_iff in * by auto.
      destruct_head'_or; try lia.
      assert (S n = i).
      { apply weight_unique; try lia.
        symmetry; eauto with lia. }
      subst; reflexivity. }
    { rewrite weight_mul_iff in * by auto.
      exfalso; intuition eauto with lia. }
  Qed.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      dlet_nd p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational n p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof using weight_0 weight_nz. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational Let_In] in *; push; try
  pose proof place_in_range a (pred n); try lia; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  destruct n; cbn [pred] in *; try lia.                     Qed.
  Hint Rewrite @eval_from_associational : push_eval.
  Lemma length_from_associational n p : length (from_associational n p) = n.
  Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
  Hint Rewrite length_from_associational : distr_length.

  Definition extend_to_length (n_in n_out : nat) (p:list Z) : list Z :=
    p ++ zeros (n_out - n_in).
  Lemma eval_extend_to_length n_in n_out p :
    length p = n_in -> (n_in <= n_out)%nat ->
    eval n_out (extend_to_length n_in n_out p) = eval n_in p.
  Proof using Type.
    cbv [eval extend_to_length to_associational]; intros.
    replace (seq 0 n_out) with (seq 0 (n_in + (n_out - n_in))) by (f_equal; lia).
    rewrite seq_add, map_app, combine_app_samelength, Associational.eval_app;
      push; lia.
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
         let abm_a := Associational.repeat_reduce n s c ab_a in
         from_associational n abm_a.
    Lemma eval_mulmod n (f g:list Z)
          (Hf : length f = n) (Hg : length g = n) :
      eval n (mulmod n f g) mod (s - Associational.eval c)
      = (eval n f * eval n g) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. cbv [mulmod]; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try lia.. ].
    clear; cbv -[Associational.repeat_reduce].
    induction c as [|?? IHc]; simpl; trivial.                 Qed.

    Definition squaremod (n:nat) (a:list Z) : list Z
      := let a_a := to_associational n a in
         let aa_a := Associational.reduce_square s c a_a in
         let aam_a := Associational.repeat_reduce (pred n) s c aa_a in
         from_associational n aam_a.
    Lemma eval_squaremod n (f:list Z)
          (Hf : length f = n) :
      eval n (squaremod n f) mod (s - Associational.eval c)
      = (eval n f * eval n f) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz. cbv [squaremod]; push; trivial.
    destruct f; simpl in *; [ right; subst n; reflexivity | left; try lia.. ]. Qed.
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

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying. *)
    Definition encode n s c (x : Z) : list Z :=
      chained_carries n s c (from_associational n [(1,x)]) (seq 0 n).
    Lemma eval_encode n s c x :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
      eval n (encode n s c x) mod (s - Associational.eval c)
      = x mod (s - Associational.eval c).
    Proof using Type*. cbv [encode]; intros; push; auto; f_equal; lia. Qed.
    Lemma length_encode n s c x
      : length (encode n s c x) = n.
    Proof using Type. cbv [encode]; repeat distr_length.                 Qed.
  End Carries.
  Hint Rewrite @eval_encode @eval_carry @eval_carry_reduce @eval_chained_carries : push_eval.
  Hint Rewrite @length_encode @length_carry @length_carry_reduce @length_chained_carries : distr_length.

  Section sub.
    Context (n:nat)
            (s:Z) (s_nz:s <> 0)
            (c:list (Z * Z))
            (m_nz:s - Associational.eval c <> 0)
            (balance:list Z)
            (length_balance:length balance = n)
            (eval_balance:eval n balance mod (s - Associational.eval c) = 0).

    Definition negate_snd (a:list Z) : list Z
      := let A := to_associational n a in
         let negA := Associational.negate_snd A in
         from_associational n negA.

    Definition scmul (x:Z) (a:list Z) : list Z
      := let A := to_associational n a in
         let R := Associational.mul A [(1, x)] in
         from_associational n R.

    Definition sub (a b:list Z) : list Z
      := let ca := add n balance a in
         let _b := negate_snd b in
         add n ca _b.

    Lemma length_scmul x a : length (scmul x a) = n.
    Proof using Type. cbv [scmul]; now push. Qed.
    Hint Rewrite length_scmul : distr_length.

    Lemma eval_scmul x a : eval n (scmul x a) = x * eval n a.
    Proof using weight_0 weight_nz.
      clear -weight_0 weight_nz.
      destruct (zerop n) as [->|]; [ cbn; lia | ].
      cbv [scmul]; push; try lia.
    Qed.
    Hint Rewrite eval_scmul : push_eval.

    Hint Rewrite eval_balance : push_eval.
    Lemma eval_sub a b
      : (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        (List.length a = n) -> (List.length b = n) ->
        eval n (sub a b) mod (s - Associational.eval c)
        = (eval n a - eval n b) mod (s - Associational.eval c).
    Proof using s_nz m_nz weight_0 weight_nz eval_balance length_balance.
      destruct (zerop n) as [->|]; try reflexivity.
      intros; cbv [sub negate_snd]; push; repeat distr_length;
        eauto with lia.
      push_Zmod; push; pull_Zmod; push_Zmod; pull_Zmod; distr_length; eauto.
    Qed.
    Hint Rewrite eval_sub : push_eval.
    Lemma length_sub a b
      : length a = n -> length b = n ->
        length (sub a b) = n.
    Proof using length_balance. intros; cbv [sub scmul negate_snd]; repeat distr_length. Qed.
    Hint Rewrite length_sub : distr_length.
    Definition opp (a:list Z) : list Z
      := sub (zeros n) a.
    Lemma eval_opp
          (a:list Z)
      : (length a = n) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval n (opp a) mod (s - Associational.eval c)
        = (- eval n a) mod (s - Associational.eval c).
    Proof using m_nz s_nz weight_0 weight_nz eval_balance length_balance. intros; cbv [opp]; push; distr_length; auto.       Qed.
    Lemma length_opp a
      : length a = n -> length (opp a) = n.
    Proof using length_balance. cbv [opp]; intros; repeat distr_length.            Qed.
  End sub.
  Hint Rewrite @eval_scmul @eval_opp @eval_sub : push_eval.
  Hint Rewrite @length_scmul @length_sub @length_opp : distr_length.

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
    Proof using Type. clear dependent weight. distr_length; lia **. Qed.

    Lemma select_push cond a b f (H : length a = length b) :
      f (select cond a b) = Z.zselect cond (f a) (f b).
    Proof using Type. unfold select, Z.zselect.
                      destruct (Z.eqb_spec cond 0); subst; simpl.
                      - rewrite (map_ext _ fst), ListUtil.map_fst_combine, <- H, firstn_all; reflexivity.
                      - rewrite (map_ext _ snd), ListUtil.map_snd_combine, H, firstn_all; reflexivity. Qed.
  End select.
End Positional.
(* Hint Rewrite disappears after the end of a section *)
#[global]
Hint Rewrite length_zeros length_add_to_nth length_from_associational @length_add @length_carry_reduce @length_carry @length_chained_carries @length_encode @length_scmul @length_sub @length_opp @length_select @length_zselect @length_select_min @length_extend_to_length @length_drop_high_to_length : distr_length.
#[global]
Hint Rewrite @eval_zeros @eval_nil @eval_snoc_S @eval_select @eval_zselect @eval_extend_to_length using solve [auto; distr_length]: push_eval.
Section Positional_nonuniform.
  Context (weight weight' : nat -> Z).

  Lemma eval_hd_tl n (xs:list Z) :
    length xs = n ->
    eval weight n xs = weight 0%nat * hd 0 xs + eval (fun i => weight (S i)) (pred n) (tl xs).
  Proof using Type.
    intro; subst; destruct xs as [|x xs]; [ cbn; lia | ].
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
      cbv [eval to_associational Associational.eval] in *; cbn in *; try lia.
    rewrite Hwt, Z.mul_add_distr_l, Z.mul_assoc by lia.
    erewrite <- !map_S_seq, IHxs; [ reflexivity | ]; cbn; eauto with lia.
  Qed.
End Positional_nonuniform.
#[global]
Hint Rewrite @eval_cons using solve [auto; distr_length]: push_eval.
End Positional.

Record weight_properties {weight : nat -> Z} :=
  {
    weight_0 : weight 0%nat = 1;
    weight_positive : forall i, 0 < weight i;
    weight_multiples : forall i, weight (S i) mod weight i = 0;
    weight_divides : forall i : nat, 0 < weight (S i) / weight i;
  }.
Global Hint Resolve weight_0 weight_positive weight_multiples weight_divides : core.
#[global]
Hint Rewrite @weight_0 @weight_multiples using solve [auto]: push_eval.
Lemma weight_nz {weight : nat -> Z} {wprops : @weight_properties weight}
  : forall i, weight i <> 0.
Proof. intro i; pose proof (@weight_positive _ wprops i); lia. Qed.
Global Hint Resolve weight_nz : core.
