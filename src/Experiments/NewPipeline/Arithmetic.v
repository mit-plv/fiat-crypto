(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div Crypto.Util.ZUtil.Hints.Core.
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
Require Import Crypto.Util.ZUtil.CC Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Zselect Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Equality.
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

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Lemma eval_split s p (s_nz:s<>0) :
    eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
  Proof. cbv [Let_In split]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
  Hint Rewrite eval_reduce : push_eval.

  Definition bind_snd (p : list (Z*Z)) :=
    map (fun t => dlet_nd t2 := snd t in (fst t, t2)) p.

  Lemma bind_snd_correct p : bind_snd p = p.
  Proof.
    cbv [bind_snd]; induction p as [| [? ?] ];
      push; [|rewrite IHp]; reflexivity.
  Qed.

  Lemma eval_rev p : eval (rev p) = eval p.
  Proof. induction p; cbn [rev]; push; lia. Qed.

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

Module Positional. Section Positional.
  Context (weight : nat -> Z)
          (weight_0 : weight 0%nat = 1)
          (weight_nz : forall i, weight i <> 0).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Lemma eval_to_associational n x :
    Associational.eval (@to_associational n x) = eval n x.
  Proof. trivial.                                             Qed.
  Hint Rewrite @eval_to_associational : push_eval.
  Lemma eval_nil n : eval n [] = 0.
  Proof. cbv [eval to_associational]. rewrite combine_nil_r. reflexivity. Qed.
  Hint Rewrite eval_nil : push_eval.
  Lemma eval0 p : eval 0 p = 0.
  Proof. cbv [eval to_associational]. reflexivity. Qed.
  Hint Rewrite eval0 : push_eval.

  Lemma eval_snoc n m x y : n = length x -> m = S n -> eval m (x ++ [y]) = eval n x + weight n * y.
  Proof.
    cbv [eval to_associational]; intros; subst n m.
    rewrite seq_snoc, map_app.
    rewrite combine_app_samelength by distr_length.
    autorewrite with push_eval. simpl.
    autorewrite with push_eval cancel_pair; ring.
  Qed.

  (* SKIP over this: zeros, add_to_nth *)
  Local Ltac push := autorewrite with push_eval push_map distr_length
    push_flat_map push_fold_right push_nth_default cancel_pair natsimplify.
  Definition zeros n : list Z := repeat 0 n.
  Lemma length_zeros n : length (zeros n) = n. Proof. cbv [zeros]; distr_length. Qed.
  Hint Rewrite length_zeros : distr_length.
  Lemma eval_combine_zeros ls n : Associational.eval (List.combine ls (zeros n)) = 0.
  Proof.
    cbv [Associational.eval zeros].
    revert n; induction ls, n; simpl; rewrite ?IHls; nsatz.   Qed.
  Lemma eval_zeros n : eval n (zeros n) = 0.
  Proof. apply eval_combine_zeros.                            Qed.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => x + y) ls.
  Lemma length_add_to_nth i x ls : length (add_to_nth i x ls) = length ls.
  Proof. cbv [add_to_nth]; distr_length. Qed.
  Hint Rewrite length_add_to_nth : distr_length.
  Lemma eval_add_to_nth (n:nat) (i:nat) (x:Z) (xs:list Z) (H:(i<length xs)%nat)
        (Hn : length xs = n) (* N.B. We really only need [i < Nat.min n (length xs)] *) :
    eval n (add_to_nth i x xs) = weight i * x + eval n xs.
  Proof.
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

  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => (nat * Z)%type)
      (O, fst t * snd t)
      (fun i' place_i'
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in c * snd t)
          else place_i')
      i.

  Lemma place_in_range (t:Z*Z) (n:nat) : (fst (place t n) < S n)%nat.
  Proof. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try omega. Qed.
  Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
  Proof. induction i; cbv [place nat_rect] in *; break_match; push;
    repeat match goal with |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(auto) ltac:(auto))
           end; nsatz.                                        Qed.
  Hint Rewrite weight_place : push_eval.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      dlet_nd p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational n p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational Let_In] in *; push; try
  pose proof place_in_range a (pred n); try omega; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  try omega.                                                  Qed.
  Hint Rewrite @eval_from_associational : push_eval.
  Lemma length_from_associational n p : length (from_associational n p) = n.
  Proof. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
  Hint Rewrite length_from_associational : distr_length.

  Definition extend_to_length (n_in n_out : nat) (p:list Z) : list Z :=
    p ++ zeros (n_out - n_in).
  Lemma eval_extend_to_length n_in n_out p :
    length p = n_in -> (n_in <= n_out)%nat ->
    eval n_out (extend_to_length n_in n_out p) = eval n_in p.
  Proof.
    cbv [eval extend_to_length to_associational]; intros.
    replace (seq 0 n_out) with (seq 0 (n_in + (n_out - n_in))) by (f_equal; omega).
    rewrite seq_add, map_app, combine_app_samelength, Associational.eval_app;
      push; omega.
  Qed.
  Hint Rewrite eval_extend_to_length : push_eval.
  Lemma length_eval_extend_to_length n_in n_out p :
    length p = n_in -> (n_in <= n_out)%nat ->
    length (extend_to_length n_in n_out p) = n_out.
  Proof. cbv [extend_to_length]; intros; distr_length.        Qed.
  Hint Rewrite length_eval_extend_to_length : distr_length.

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
    Proof. cbv [mulmod]; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try omega.. ].
    clear; cbv -[Associational.reduce].
    induction c as [|?? IHc]; simpl; trivial.                 Qed.
  End mulmod.
  Hint Rewrite @eval_mulmod : push_eval.

  Definition add (n:nat) (a b:list Z) : list Z
    := let a_a := to_associational n a in
       let b_a := to_associational n b in
       from_associational n (a_a ++ b_a).
  Lemma eval_add n (f g:list Z)
        (Hf : length f = n) (Hg : length g = n) :
    eval n (add n f g) = (eval n f + eval n g).
  Proof. cbv [add]; push; trivial. destruct n; auto.          Qed.
  Hint Rewrite @eval_add : push_eval.
  Lemma length_add n f g
        (Hf : length f = n) (Hg : length g = n) :
    length (add n f g) = n.
  Proof. clear -Hf Hf; cbv [add]; distr_length.               Qed.
  Hint Rewrite @length_add : distr_length.

  Section Carries.
    Definition carry n m (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Lemma length_carry n m index p : length (carry n m index p) = m.
    Proof. cbv [carry]; distr_length. Qed.
    Lemma eval_carry n m i p: (n <> 0%nat) -> (m <> 0%nat) ->
                              weight (S i) / weight i <> 0 ->
      eval m (carry n m i p) = eval n p.
    Proof.
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
    Proof. cbv [carry_reduce]; intros; push; auto.            Qed.
    Hint Rewrite @eval_carry_reduce : push_eval.
    Lemma length_carry_reduce n s c index p
      : length p = n -> length (carry_reduce n s c index p) = n.
    Proof. cbv [carry_reduce]; distr_length.                  Qed.
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
    Proof.
      intros; cbv [chained_carries]; induction (rev idxs) as [|x xs IHxs];
        cbn [fold_right]; distr_length.
    Qed. Hint Rewrite @length_chained_carries : distr_length.

    (* carries without modular reduction; useful for converting between bases *)
    Definition chained_carries_no_reduce n p (idxs : list nat) :=
      fold_right (fun a b => carry n n a b) p (rev idxs).
    Lemma eval_chained_carries_no_reduce n p idxs:
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (chained_carries_no_reduce n p idxs) = eval n p.
    Proof.
      cbv [chained_carries_no_reduce]; intros.
      destruct n; [push;reflexivity|].
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries_no_reduce : push_eval.

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
    Proof. cbv [encode]; repeat distr_length.                 Qed.

  End Carries.
  Hint Rewrite @eval_encode : push_eval.
  Hint Rewrite @length_encode : distr_length.

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
    Proof.
      destruct (zerop n); subst; try reflexivity.
      intros; cbv [sub balance scmul negate_snd]; push; repeat distr_length;
        eauto with omega.
      push_Zmod; push; pull_Zmod; push_Zmod; pull_Zmod; distr_length; eauto.
    Qed.
    Hint Rewrite eval_sub : push_eval.
    Lemma length_sub a b
      : length a = n -> length b = n ->
        length (sub a b) = n.
    Proof. intros; cbv [sub balance scmul negate_snd]; repeat distr_length. Qed.
    Hint Rewrite length_sub : distr_length.
    Definition opp (a:list Z) : list Z
      := sub (zeros n) a.
    Lemma eval_opp
          (a:list Z)
      : (length a = n) ->
        (forall i, In i (seq 0 n) -> weight (S i) / weight i <> 0) ->
        eval n (opp a) mod (s - Associational.eval c)
        = (- eval n a) mod (s - Associational.eval c).
    Proof. intros; cbv [opp]; push; distr_length; auto.       Qed.
    Lemma length_opp a
      : length a = n -> length (opp a) = n.
    Proof. cbv [opp]; intros; repeat distr_length.            Qed.
  End sub.
  Hint Rewrite @eval_opp @eval_sub : push_eval.
  Hint Rewrite @length_sub @length_opp : distr_length.
End Positional.
(* Hint Rewrite disappears after the end of a section *)
Hint Rewrite length_zeros length_add_to_nth length_from_associational @length_add @length_carry_reduce @length_chained_carries @length_encode @length_sub @length_opp : distr_length.
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
  Proof.
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
  Proof.
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
  Proof.
    clear -limbwidth_good.
    cut (1 < weight 1); [ lia | ].
    cbv [weight Z.of_nat]; autorewrite with zsimplify_fast.
    apply Z.pow_gt_1; [ omega | ].
    Z.div_mod_to_quot_rem; nia.
  Qed.

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
  Hint Resolve weight_positive weight_0 weight_multiples weight_divides.
  Hint Resolve Z.positive_is_nonzero Z.lt_gt Nat2Z.is_nonneg.

  Section Weight.
    Context weight {wprops : @weight_properties weight}.

    Lemma weight_multiples_full' j : forall i, weight (i+j) mod weight i = 0.
    Proof.
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
    Proof.
      intros; replace j with (i + (j - i))%nat by omega.
      apply weight_multiples_full'.
    Qed.

    Lemma weight_divides_full j i : (i <= j)%nat -> 0 < weight j / weight i.
    Proof. auto using Z.gt_lt, Z.div_positive_gt_0, weight_multiples_full. Qed.

    Lemma weight_div_mod j i : (i <= j)%nat -> weight j = weight i * (weight j / weight i).
    Proof. intros. apply Z.div_exact; auto using weight_multiples_full. Qed.
  End Weight.

  Module Associational.
    Section Associational.

      Definition sat_multerm s (t t' : (Z * Z)) : list (Z * Z) :=
        dlet_nd xy := Z.mul_split s (snd t) (snd t') in
              [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

      Definition sat_mul s (p q : list (Z * Z)) : list (Z * Z) :=
        flat_map (fun t => flat_map (fun t' => sat_multerm s t t') q) p.

      Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
        Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * Associational.eval q.
      Proof.
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
      Proof.
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
      Proof.
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
      Proof.
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

  Section DivMod.
    Lemma mod_step a b c d: 0 < a -> 0 < b ->
                            c mod a + a * ((c / a + d) mod b) = (a * d + c) mod (a * b).
    Proof.
      intros; rewrite Z.rem_mul_r by omega. push_Zmod.
      autorewrite with zsimplify pull_Zmod. repeat (f_equal; try ring).
    Qed.

    Lemma div_step a b c d : 0 < a -> 0 < b ->
                             (c / a + d) / b = (a * d + c) / (a * b).
    Proof. intros; Z.div_mod_to_quot_rem; nia. Qed.

    Lemma add_mod_div_multiple a b n m:
      n > 0 ->
      0 <= m / n ->
      m mod n = 0 ->
      (a / n + b) mod (m / n) = (a + n * b) mod m / n.
    Proof.
      intros. rewrite <-!Z.div_add' by auto using Z.positive_is_nonzero.
      rewrite Z.mod_pull_div, Z.mul_div_eq' by auto using Z.gt_lt.
      repeat (f_equal; try omega).
    Qed.

    Lemma add_mod_l_multiple a b n m:
      0 < n / m -> m <> 0 -> n mod m = 0 ->
      (a mod n + b) mod m = (a + b) mod m.
    Proof.
      intros.
      rewrite (proj2 (Z.div_exact n m ltac:(auto))) by auto.
      rewrite Z.rem_mul_r by auto.
      push_Zmod. autorewrite with zsimplify.
      pull_Zmod. reflexivity.
    Qed.

    Definition is_div_mod {T} (evalf : T -> Z) dm y n :=
      evalf (fst dm) = y mod n /\ snd dm = y / n.

    Lemma is_div_mod_step {T} evalf1 evalf2 dm1 dm2 y1 y2 n1 n2 x :
      n1 > 0 ->
      0 < n2 / n1 ->
      n2 mod n1 = 0 ->
      evalf2 (fst dm2) = evalf1 (fst dm1) + n1 * ((snd dm1 + x) mod (n2 / n1)) ->
      snd dm2 = (snd dm1 + x) / (n2 / n1) ->
      y2 = y1 + n1 * x ->
      @is_div_mod T evalf1 dm1 y1 n1 ->
      @is_div_mod T evalf2 dm2 y2 n2.
    Proof.
      intros; subst y2; cbv [is_div_mod] in *.
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | H: ?LHS = _ |- _ => match LHS with context [dm2] => rewrite H end
             | H: ?LHS = _ |- _ => match LHS with context [dm1] => rewrite H end
             | _ => rewrite mod_step by omega
             | _ => rewrite div_step by omega
             | _ => rewrite Z.mul_div_eq_full by omega
             end.
      split; f_equal; omega.
    Qed.

    Lemma is_div_mod_result_equal {T} evalf dm y1 y2 n :
      y1 = y2 ->
      @is_div_mod T evalf dm y1 n ->
      @is_div_mod T evalf dm y2 n.
    Proof. congruence. Qed.
  End DivMod.
End Saturated.

Module Columns.
  Import Saturated.
  Section Columns.
    Context weight {wprops : @weight_properties weight}.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof.
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
                       list_rect
                         (fun _ => (Z * Z)%type) (xx mod fw, xx / fw)
                         (fun yy tl' _ =>
                            list_rect
                              (fun _ => (Z * Z)%type) (dlet_nd x := xx in dlet_nd y := yy in Z.add_get_carry_full fw x y)
                              (fun _ _ _ =>
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
               | _ => progress cbv [Let_In]
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
      Proof.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_mod : to_div_mod.

      Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
        snd (flatten_column fw xs)  = sum xs / fw.
      Proof.
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
      Proof. cbv [flatten_step]; push. Qed.
      Hint Rewrite length_flatten_step : distr_length.
      Lemma length_flatten inp : length (fst (flatten inp)) = length inp.
      Proof. cbv [flatten]. induction inp using rev_ind; push. Qed.
      Hint Rewrite length_flatten : distr_length.

      Lemma flatten_div_mod n inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp))
         = (eval n inp) mod (weight n))
        /\ (snd (flatten inp) = eval n inp / weight n).
      Proof.
        (* to make the invariant take the right form, we make everything depend on output length, not input length *)
        intro. subst n. rewrite <-(length_flatten inp). cbv [flatten].
        induction inp using rev_ind; intros; [push|].
        repeat match goal with
               | _ => rewrite Nat.add_1_r
               | _ => progress (fold (flatten inp) in * )
               | _ => erewrite Positional.eval_snoc by (distr_length; reflexivity)
               | H: _ = _ mod (weight _) |- _ => rewrite H
               | H: _ = _ / (weight _) |- _ => rewrite H
               | _ => progress rewrite ?mod_step, ?div_step by auto
               | _ => progress autorewrite with cancel_pair to_div_mod push_sum list push_fold_right push_eval
               | _ => progress (distr_length; push_fast)
               end.
      Qed.

      Lemma flatten_mod {n} inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
      Proof. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_mod : push_eval.

      Lemma flatten_div {n} inp :
        length inp = n -> snd (flatten inp) = eval n inp / weight n.
      Proof. apply flatten_div_mod. Qed.
      Hint Rewrite @flatten_div : push_eval.

      Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
      Proof. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

      Lemma flatten_partitions inp:
        forall n i, length inp = n -> (i < n)%nat ->
                    nth_default 0 (fst (flatten inp)) i = ((eval n inp) mod (weight (S i))) / weight i.
      Proof.
        induction inp using rev_ind; intros; destruct n; distr_length.
        rewrite flatten_snoc.
        push; distr_length;
          [rewrite IHinp with (n:=n) by omega; rewrite weight_div_mod with (j:=n) (i:=S i) by (eauto; omega); push_Zmod; push |].
        repeat match goal with
               | _ => progress replace (length inp) with n by omega
               | _ => progress replace i with n by omega
               | _ => progress push
               | _ => erewrite flatten_div by eauto
               | _ => rewrite <-Z.div_add' by auto
               | _ => rewrite Z.mul_div_eq' by auto
               | _ => rewrite Z.mod_pull_div by auto using Z.lt_le_incl
               | _ => progress autorewrite with push_nth_default natsimplify
               end.
      Qed.
    End Flatten.

    Section FromAssociational.
      (* nils *)
      Definition nils n : list (list Z) := repeat nil n.
      Lemma length_nils n : length (nils n) = n. Proof. cbv [nils]. distr_length. Qed.
      Hint Rewrite length_nils : distr_length.
      Lemma eval_nils n : eval n (nils n) = 0.
      Proof.
        erewrite <-Positional.eval_zeros by eauto.
        cbv [eval nils]; rewrite List.map_repeat; reflexivity.
      Qed. Hint Rewrite eval_nils : push_eval.

      (* cons_to_nth *)
      Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
        ListUtil.update_nth i (fun y => cons x y) xs.
      Lemma length_cons_to_nth i x xs : length (cons_to_nth i x xs) = length xs.
      Proof. cbv [cons_to_nth]. distr_length. Qed.
      Hint Rewrite length_cons_to_nth : distr_length.
      Lemma cons_to_nth_add_to_nth xs : forall i x,
          map sum (cons_to_nth i x xs) = Positional.add_to_nth i x (map sum xs).
      Proof.
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
      Hint Rewrite Positional.length_from_associational : distr_length.
      Hint Rewrite Positional.eval_add_to_nth using (solve [distr_length]): push_eval.

      (* from_associational *)
      Definition from_associational n (p:list (Z*Z)) : list (list Z) :=
        List.fold_right (fun t ls =>
                           dlet_nd p := Positional.place weight t (pred n) in
                           cons_to_nth (fst p) (snd p) ls ) (nils n) p.
      Lemma length_from_associational n p : length (from_associational n p) = n.
      Proof. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
      Hint Rewrite length_from_associational: distr_length.
      Lemma eval_from_associational n p (n_nonzero:n<>0%nat\/p=nil):
        eval n (from_associational n p) = Associational.eval p.
      Proof.
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
      Proof. reflexivity. Qed.
    End FromAssociational.
  End Columns.
End Columns.

Module Rows.
  Import Saturated.
  Section Rows.
    Context weight {wprops : @weight_properties weight}.

    Local Notation rows := (list (list Z)) (only parsing).
    Local Notation cols := (list (list Z)) (only parsing).

    Hint Rewrite Positional.eval_nil Positional.eval0 @Positional.eval_snoc
         Positional.eval_to_associational
         Columns.eval_nil Columns.eval_snoc using (auto; solve [distr_length]) : push_eval.
    Hint Resolve in_eq in_cons.

    Definition eval n (inp : rows) :=
      sum (map (Positional.eval weight n) inp).
    Lemma eval_nil n : eval n nil = 0.
    Proof. cbv [eval]. rewrite map_nil, sum_nil; reflexivity. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval0 x : eval 0 x = 0.
    Proof. cbv [eval]. induction x; autorewrite with push_map push_sum push_eval; omega. Qed.
    Hint Rewrite eval0 : push_eval.
    Lemma eval_cons n r inp : eval n (r :: inp) = Positional.eval weight n r + eval n inp.
    Proof. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
    Hint Rewrite eval_cons : push_eval.
    Lemma eval_app n x y : eval n (x ++ y) = eval n x + eval n y.
    Proof. cbv [eval]; autorewrite with push_map push_sum; reflexivity. Qed.
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
      Proof.
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

      Lemma length_fst_extract_row n (inp : cols) :
        length inp = n -> length (fst (extract_row inp)) = n.
      Proof. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_fst_extract_row : distr_length.

      Lemma length_snd_extract_row n (inp : cols) :
        length inp = n -> length (snd (extract_row inp)) = n.
      Proof. cbv [extract_row]; autorewrite with cancel_pair; distr_length. Qed.
      Hint Rewrite length_snd_extract_row : distr_length.

      (* max column size *)
      Definition max_column_size (x:cols) := fold_right (fun a b => Nat.max a b) 0%nat (map (fun c => length c) x).

      (* TODO: move to where list is defined *)
      Hint Rewrite @app_nil_l : list.
      Hint Rewrite <-@app_comm_cons: list.

      Lemma max_column_size_nil : max_column_size nil = 0%nat.
      Proof. reflexivity. Qed. Hint Rewrite max_column_size_nil : push_max_column_size.
      Lemma max_column_size_cons col (inp : cols) :
        max_column_size (col :: inp) = Nat.max (length col) (max_column_size inp).
      Proof. reflexivity. Qed. Hint Rewrite max_column_size_cons : push_max_column_size.
      Lemma max_column_size_app (x y : cols) :
        max_column_size (x ++ y) = Nat.max (max_column_size x) (max_column_size y).
      Proof. induction x; autorewrite with list push_max_column_size; lia. Qed.
      Hint Rewrite max_column_size_app : push_max_column_size.
      Lemma max_column_size0 (inp : cols) :
        forall n,
          length inp = n -> (* this is not needed to make the lemma true, but prevents reliance on the implementation of Columns.eval*)
          max_column_size inp = 0%nat -> Columns.eval weight n inp = 0.
      Proof.
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

      Lemma eval_from_columns'_with_length m st n:
        (length (fst st) = n) ->
        length (fst (from_columns' m st)) = n /\
        ((forall r, In r (snd st) -> length r = n) ->
         forall r, In r (snd (from_columns' m st)) -> length r = n) /\
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof.
        cbv [from_columns']; intros.
        apply fold_right_invariant; intros;
          repeat match goal with
                 | _ => progress (intros; subst)
                 | _ => progress autorewrite with cancel_pair push_eval
                 | _ => progress In_cases
                 | _ => split; try omega
                 | H: _ /\ _ |- _ => destruct H
                 | _ => solve [auto using length_fst_extract_row, length_snd_extract_row]
                 end.
      Qed.
      Lemma length_fst_from_columns' m st :
        length (fst (from_columns' m st)) = length (fst st).
      Proof. apply eval_from_columns'_with_length; reflexivity. Qed.
      Hint Rewrite length_fst_from_columns' : distr_length.
      Lemma length_snd_from_columns' m st :
        (forall r, In r (snd st) -> length r = length (fst st)) ->
        forall r, In r (snd (from_columns' m st)) -> length r = length (fst st).
      Proof. apply eval_from_columns'_with_length. reflexivity. Qed.
      Hint Rewrite length_snd_from_columns' : distr_length.
      Lemma eval_from_columns' m st n :
        (length (fst st) = n) ->
        eval n (snd (from_columns' m st)) = Columns.eval weight n (fst st) + eval n (snd st)
                                                                             - Columns.eval weight n (fst (from_columns' m st)).
      Proof. apply eval_from_columns'_with_length. Qed.
      Hint Rewrite eval_from_columns' using (auto; solve [distr_length]) : push_eval.

      Lemma max_column_size_extract_row inp :
        max_column_size (fst (extract_row inp)) = (max_column_size inp - 1)%nat.
      Proof.
        cbv [extract_row]. autorewrite with cancel_pair.
        induction inp; [ reflexivity | ].
        autorewrite with push_max_column_size push_map distr_length.
        rewrite IHinp. auto using Nat.sub_max_distr_r.
      Qed.
      Hint Rewrite max_column_size_extract_row : push_max_column_size.

      Lemma max_column_size_from_columns' m st :
        max_column_size (fst (from_columns' m st)) = (max_column_size (fst st) - m)%nat.
      Proof.
        cbv [from_columns']; induction m; intros; cbn - [max_column_size extract_row];
          autorewrite with push_max_column_size; lia.
      Qed.
      Hint Rewrite max_column_size_from_columns' : push_max_column_size.

      Lemma eval_from_columns (inp : cols) :
        forall n, length inp = n -> eval n (from_columns inp) = Columns.eval weight n inp.
      Proof.
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
      Proof.
        cbv [from_columns]; intros.
        change inp with (fst (inp, @nil (list Z))).
        eapply length_snd_from_columns'; eauto.
        autorewrite with cancel_pair; intros; In_cases.
      Qed.
      Hint Rewrite length_from_columns : distr_length.

      (* from associational *)
      Definition from_associational n (p : list (Z * Z)) := from_columns (Columns.from_associational weight n p).

      Lemma eval_from_associational n p: (n <> 0%nat \/ p = nil) ->
                                         eval n (from_associational n p) = Associational.eval p.
      Proof.
        intros. cbv [from_associational].
        rewrite eval_from_columns by auto using Columns.length_from_associational.
        auto using Columns.eval_from_associational.
      Qed.

      Lemma length_from_associational n p :
        forall r, In r (from_associational n p) -> length r = n.
      Proof.
        cbv [from_associational]; intros.
        match goal with H: _ |- _ => apply length_from_columns in H end.
        rewrite Columns.length_from_associational in *; auto.
      Qed.

      (* TODO : move *)
      Lemma max_0_iff a b : Nat.max a b = 0%nat <-> (a = 0%nat /\ b = 0%nat).
      Proof.
        destruct a, b; try tauto.
        rewrite <-Nat.succ_max_distr.
        split; [ | destruct 1]; congruence.
      Qed.
      Lemma max_column_size_zero_iff x :
        max_column_size x = 0%nat <-> (forall c, In c x -> c = nil).
      Proof.
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
      Proof.
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
      Proof.
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
                 | _ => progress autorewrite with cancel_pair natsimplify push_sum_rows list push_nth_default
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
        Proof.
          cbv [sum_rows' Let_In]; autorewrite with push_combine.
          rewrite !fold_left_rev_right. cbn [fold_left].
          autorewrite with cancel_pair to_div_mod. congruence.
        Qed.

        Lemma sum_rows'_nil state :
          sum_rows' state nil nil = state.
        Proof. reflexivity. Qed.

        Hint Rewrite sum_rows'_cons sum_rows'_nil : push_sum_rows.

        Lemma sum_rows'_div_mod_length row1 :
          forall nm start_state row2 row1' row2',
            let m := snd start_state in
            let n := length row1 in
            length row2 = n ->
            length row1' = m ->
            length row2' = m ->
            length (fst (fst start_state)) = m ->
            (nm = n + m)%nat ->
            let eval := Positional.eval weight in
            is_div_mod (eval m) (fst start_state) (eval m row1' + eval m row2') (weight m) ->
            length (fst (fst (sum_rows' start_state row1 row2))) = nm
            /\ is_div_mod (eval nm) (fst (sum_rows' start_state row1 row2))
                          (eval nm (row1' ++ row1) + eval nm (row2' ++ row2))
                          (weight nm).
        Proof.
          induction row1 as [|x1 row1]; destruct row2 as [|x2 row2]; intros; subst nm; push; [ ].
          rewrite (app_cons_app_app _ row1'), (app_cons_app_app _ row2').
          apply IHrow1; clear IHrow1; autorewrite with cancel_pair distr_length in *; try omega.
          eapply is_div_mod_step with (x := x1 + x2); try eassumption; push.
        Qed.

        Lemma sum_rows_div_mod n row1 row2 :
          length row1 = n -> length row2 = n ->
          let eval := Positional.eval weight in
          is_div_mod (eval n) (sum_rows row1 row2) (eval n row1 + eval n row2) (weight n).
        Proof.
          cbv [sum_rows]; intros.
          apply sum_rows'_div_mod_length with (row1':=nil) (row2':=nil);
            cbv [is_div_mod]; autorewrite with cancel_pair push_eval zsimplify; distr_length.
        Qed.

        Lemma sum_rows_mod n row1 row2 :
          length row1 = n -> length row2 = n ->
          Positional.eval weight n (fst (sum_rows row1 row2))
          = (Positional.eval weight n row1 + Positional.eval weight n row2) mod (weight n).
        Proof. apply sum_rows_div_mod. Qed.
        Lemma sum_rows_div row1 row2 n:
          length row1 = n -> length row2 = n ->
          snd (sum_rows row1 row2)
          = (Positional.eval weight n row1 + Positional.eval weight n row2) / (weight n).
        Proof. apply sum_rows_div_mod. Qed.

        Lemma sum_rows'_partitions row1 :
          forall nm start_state row2 row1' row2',
            let m := snd start_state in
            let n := length row1 in
            length row2 = n ->
            length row1' = m ->
            length row2' = m ->
            length (fst (fst start_state)) = m ->
            nm = (n + m)%nat ->
            let eval := Positional.eval weight in
            snd (fst start_state) = (eval m row1' + eval m row2') / weight m ->
            (forall j, (j < m)%nat ->
                       nth_default 0 (fst (fst start_state)) j = ((eval m row1' + eval m row2') mod (weight (S j))) / (weight j)) ->
            forall i, (i < nm)%nat ->
                      nth_default 0 (fst (fst (sum_rows' start_state row1 row2))) i
                      = ((eval nm (row1' ++ row1) + eval nm (row2' ++ row2)) mod (weight (S i))) / (weight i).
        Proof.
          induction row1 as [|x1 row1]; destruct row2 as [|x2 row2]; intros; subst nm; push; [].

          rewrite (app_cons_app_app _ row1'), (app_cons_app_app _ row2').
          apply IHrow1; clear IHrow1; push;
            repeat match goal with
                   | H : ?LHS = _ |- _ =>
                     match LHS with context [start_state] => rewrite H end
                   | H : context [nth_default 0 (fst (fst start_state))] |- _ => rewrite H by omega
                   | _ => rewrite <-(Z.add_assoc _ x1 x2)
                   end.
          { rewrite div_step by auto using Z.gt_lt.
            rewrite Z.mul_div_eq_full by auto; rewrite weight_multiples by auto. push. }
          { rewrite weight_div_mod with (j:=snd start_state) (i:=S j) by (auto; omega).
            push_Zmod. autorewrite with zsimplify_fast. reflexivity. }
          { push. replace (snd start_state) with j in * by omega.
            push. rewrite add_mod_div_multiple by auto using Z.lt_le_incl.
            push. }
        Qed.

        Lemma sum_rows_partitions row1: forall row2 n i,
            length row1 = n -> length row2 = n -> (i < n)%nat ->
            nth_default 0 (fst (sum_rows row1 row2)) i
            = ((Positional.eval weight n row1 + Positional.eval weight n row2) mod weight (S i)) / (weight i).
        Proof.
          cbv [sum_rows]; intros. rewrite <-(Nat.add_0_r n).
          rewrite <-(app_nil_l row1), <-(app_nil_l row2).
          apply sum_rows'_partitions; intros;
            autorewrite with cancel_pair push_eval zsimplify_fast push_nth_default; distr_length.
        Qed.

        Lemma length_sum_rows row1 row2 n:
          length row1 = n -> length row2 = n ->
          length (fst (sum_rows row1 row2)) = n.
        Proof.
          cbv [sum_rows]; intros.
          eapply sum_rows'_div_mod_length; cbv [is_div_mod];
            autorewrite with cancel_pair; distr_length; auto using nil_length0.
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
      Proof. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_snoc state r inp :
        flatten' state (inp ++ r :: nil) = flatten' (fst (sum_rows r (fst state)), snd state + snd (sum_rows r (fst state))) inp.
      Proof. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_nil state : flatten' state [] = state. Proof. reflexivity. Qed.
      Hint Rewrite flatten'_cons flatten'_snoc flatten'_nil : push_flatten.

      Ltac push :=
        repeat match goal with
               | _ => progress intros
               | H: length ?x = ?n |- context [snd (sum_rows ?x _)] => rewrite sum_rows_div with (n:=n) by (distr_length; eauto)
               | H: length ?x = ?n |- context [snd (sum_rows _ ?x)] => rewrite sum_rows_div with (n:=n) by (distr_length; eauto)
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

      Lemma flatten'_div_mod_length n inp : forall start_state,
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten' start_state inp)) = n
        /\ (inp <> nil ->
            is_div_mod (Positional.eval weight n) (flatten' start_state inp)
                       (Positional.eval weight n (fst start_state) + eval n inp + weight n * snd start_state)
                       (weight n)).
      Proof.
        induction inp using rev_ind; push; [apply IHinp; push|].
        destruct (dec (inp = nil)); [subst inp; cbv [is_div_mod]
                                    | eapply is_div_mod_result_equal; try apply IHinp]; push.
        { autorewrite with zsimplify; push. }
        { rewrite Z.div_add' by auto; push. }
      Qed.

      Hint Rewrite (@Positional.length_zeros weight) : distr_length.
      Hint Rewrite (@Positional.eval_zeros weight) using auto : push_eval.

      Lemma flatten_div_mod inp n :
        (forall row, In row inp -> length row = n) ->
        is_div_mod (Positional.eval weight n) (flatten n inp) (eval n inp) (weight n).
      Proof.
        intros; cbv [flatten].
        destruct inp; [|destruct inp]; cbn [hd tl].
        { cbv [is_div_mod]; push.
          erewrite sum_rows_div by (distr_length; reflexivity).
          push. }
        { cbv [is_div_mod]; push. }
        { eapply is_div_mod_result_equal; try apply flatten'_div_mod_length; push. }
      Qed.

      Lemma flatten_mod inp n :
        (forall row, In row inp -> length row = n) ->
        Positional.eval weight n (fst (flatten n inp)) = (eval n inp) mod (weight n).
      Proof. apply flatten_div_mod. Qed.
      Lemma flatten_div inp n :
        (forall row, In row inp -> length row = n) ->
        snd (flatten n inp) = (eval n inp) / (weight n).
      Proof. apply flatten_div_mod. Qed.

      Lemma length_flatten' n start_state inp :
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten' start_state inp)) = n.
      Proof. apply flatten'_div_mod_length. Qed.
      Hint Rewrite length_flatten' : distr_length.

      Lemma length_flatten n inp :
        (forall row, In row inp -> length row = n) ->
        length (fst (flatten n inp)) = n.
      Proof.
        intros.
        apply length_flatten'; push;
          destruct inp as [|? [|? ?] ]; try congruence; cbn [hd tl] in *; push;
            subst row; distr_length.
      Qed. Hint Rewrite length_flatten : distr_length.

      Lemma flatten'_partitions n inp : forall start_state,
        inp <> nil ->
        length (fst start_state) = n ->
        (forall row, In row inp -> length row = n) ->
        forall i, (i < n)%nat ->
                  nth_default 0 (fst (flatten' start_state inp)) i
                  = ((Positional.eval weight n (fst start_state) + eval n inp) mod weight (S i)) / (weight i).
      Proof.
        induction inp using rev_ind; push.
        destruct (dec (inp = nil)).
        { subst inp; push. rewrite sum_rows_partitions with (n:=n) by eauto. push. }
        { erewrite IHinp; push.
          rewrite add_mod_l_multiple by auto using weight_divides_full, weight_multiples_full.
          push. }
      Qed.

      Lemma flatten_partitions inp n :
        (forall row, In row inp -> length row = n) ->
        forall i, (i < n)%nat ->
                  nth_default 0 (fst (flatten n inp)) i = (eval n inp mod weight (S i)) / (weight i).
      Proof.
        intros; cbv [flatten].
        intros; destruct inp as [| ? [| ? ?] ]; try congruence; cbn [hd tl] in *;  try solve [push].
        { cbn. autorewrite with push_nth_default.
          rewrite sum_rows_partitions with (n:=n) by distr_length.
          autorewrite with push_eval zsimplify_fast.
          auto with zarith. }
        { push. rewrite sum_rows_partitions with (n:=n) by distr_length; push. }
        { rewrite flatten'_partitions with (n:=n); push. }
      Qed.

      Definition partition n x :=
        map (fun i => (x mod weight (S i)) / weight i) (seq 0 n).

      Lemma nth_default_partitions x : forall p n,
        (forall i, (i < n)%nat -> nth_default 0 p i = (x mod weight (S i)) / weight i) ->
        length p = n ->
        p = partition n x.
      Proof.
        cbv [partition]; induction p using rev_ind; intros; distr_length; subst n; [reflexivity|].
        rewrite Nat.add_1_r, seq_snoc.
        autorewrite with natsimplify push_map.
        rewrite <-IHp; auto; intros;
          match goal with H : context [nth_default _ (p ++ [ _ ])] |- _ =>
                          rewrite <-H by omega end.
        { autorewrite with push_nth_default natsimplify. reflexivity. }
        { autorewrite with push_nth_default natsimplify.
          break_match; omega. }
      Qed.

      Lemma partition_step n x :
        partition (S n) x = partition n x ++ [(x mod weight (S n)) / weight n].
      Proof.
        cbv [partition]. rewrite seq_snoc.
        autorewrite with natsimplify push_map. reflexivity.
      Qed.

      Lemma length_partition n x : length (partition n x) = n.
      Proof. cbv [partition]; distr_length. Qed.
      Hint Rewrite length_partition : distr_length.

      Lemma eval_partition n x :
        Positional.eval weight n (partition n x) = x mod (weight n).
      Proof.
        induction n; intros.
        { cbn. rewrite (weight_0); auto with zarith. }
        { rewrite (Z.div_mod (x mod weight (S n)) (weight n)) by auto.
          rewrite <-Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto).
          rewrite partition_step, Positional.eval_snoc with (n:=n) by distr_length.
          omega. }
      Qed.

      Lemma flatten_partitions' inp n :
        (forall row, In row inp -> length row = n) ->
        fst (flatten n inp) = partition n (eval n inp).
      Proof. auto using nth_default_partitions, flatten_partitions, length_flatten. Qed.
    End Flatten.

    Section Ops.
      Definition add n p q := flatten n [p; q].

      (* TODO: Although cleaner, using Positional.negate snd inserts
      dlets which prevent add-opp=>sub transformation in partial
      evaluation. Should probably either make partial evaluation
      handle that or remove the dlet in Positional.from_associational.

      NOTE(from jgross): I think partial evaluation now handles that
      fine; we should check this. *)
      Definition sub n p q := flatten n [p; map (fun x => dlet y := x in Z.opp y) q].

      Hint Rewrite eval_cons eval_nil using solve [auto] : push_eval.

      Definition mul base n m (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        flatten m (from_associational m pq_a).

      (* TODO : move sat_reduce and repeat_sat_reduce to Saturated.Associational *)
      Definition sat_reduce base s c (p : list (Z * Z)) :=
        let lo_hi := Associational.split s p in
        fst lo_hi ++ (Associational.sat_mul_const base c (snd lo_hi)).

      Definition repeat_sat_reduce base s c (p : list (Z * Z)) n :=
        fold_right (fun _ q => sat_reduce base s c q) p (seq 0 n).

      Definition mulmod base s c n nreductions (p q : list Z) :=
        let p_a := Positional.to_associational weight n p in
        let q_a := Positional.to_associational weight n q in
        let pq_a := Associational.sat_mul base p_a q_a in
        let r_a := repeat_sat_reduce base s c pq_a nreductions in
        flatten n (from_associational n r_a).

      Hint Rewrite Associational.eval_sat_mul_const Associational.eval_sat_mul Associational.eval_split using solve [auto] : push_eval.
      Hint Rewrite eval_from_associational using solve [auto] : push_eval.
      Hint Rewrite eval_partition using solve [auto] : push_eval.
      Ltac solver :=
        intros; cbv [sub add mul mulmod sat_reduce];
        rewrite ?flatten_partitions' by (intros; In_cases; subst; distr_length; eauto using length_from_associational);
        rewrite ?flatten_div by (intros; In_cases; subst; distr_length; eauto using length_from_associational);
        autorewrite with push_eval; ring_simplify_subterms;
        try reflexivity.

      Lemma add_partitions n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        fst (add n p q) = partition n (Positional.eval weight n p + Positional.eval weight n q).
      Proof. solver. Qed.

      Lemma add_div n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        snd (add n p q) = (Positional.eval weight n p + Positional.eval weight n q) / weight n.
      Proof. solver. Qed.

      Lemma eval_map_opp q :
        forall n, length q = n ->
                  Positional.eval weight n (map Z.opp q) = - Positional.eval weight n q.
      Proof.
        induction q using rev_ind; intros;
          repeat match goal with
                 | _ => progress autorewrite with push_map push_eval
                 | _ => erewrite !Positional.eval_snoc with (n:=length q) by distr_length
                 | _ => rewrite IHq by auto
                 | _ => ring
                 end.
      Qed. Hint Rewrite eval_map_opp using solve [auto]: push_eval.

      Lemma sub_partitions n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        fst (sub n p q) = partition n (Positional.eval weight n p - Positional.eval weight n q).
      Proof. solver. Qed.

      Lemma sub_div n p q :
        n <> 0%nat -> length p = n -> length q = n ->
        snd (sub n p q) = (Positional.eval weight n p - Positional.eval weight n q) / weight n.
      Proof. solver. Qed.

      Lemma mul_partitions base n m p q :
        base <> 0 -> n <> 0%nat -> m <> 0%nat -> length p = n -> length q = n ->
        fst (mul base n m p q) = partition m (Positional.eval weight n p * Positional.eval weight n q).
      Proof. solver. Qed.

      Lemma eval_sat_reduce base s c p :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (sat_reduce base s c p) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof.
        intros; cbv [sat_reduce].
        autorewrite with push_eval.
        rewrite <-Associational.reduction_rule by omega.
        autorewrite with push_eval; reflexivity.
      Qed.
      Hint Rewrite eval_sat_reduce using auto : push_eval.

      Lemma eval_repeat_sat_reduce base s c p n :
        base <> 0 -> s - Associational.eval c <> 0 -> s <> 0 ->
        Associational.eval (repeat_sat_reduce base s c p n) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
      Proof.
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
      Proof.
        solver.
        rewrite <-Z.div_mod'' by auto.
        autorewrite with push_eval; reflexivity.
      Qed.
    End Ops.
  End Rows.
End Rows.

Module BaseConversion.
  Import Positional.
  Section BaseConversion.
    Hint Resolve Z.gt_lt.
    Context (sw dw : nat -> Z) (* source/destination weight functions *)
            {swprops : @weight_properties sw}
            {dwprops : @weight_properties dw}.

    Definition convert_bases (sn dn : nat) (p : list Z) : list Z :=
      let p' := Positional.from_associational dw dn (Positional.to_associational sw sn p) in
      chained_carries_no_reduce dw dn p' (seq 0 (pred dn)).

    Lemma eval_convert_bases sn dn p :
      (dn <> 0%nat) -> length p = sn ->
      eval dw dn (convert_bases sn dn p) = eval sw sn p.
    Proof.
      cbv [convert_bases]; intros.
      rewrite eval_chained_carries_no_reduce; auto using ZUtil.Z.positive_is_nonzero.
      rewrite eval_from_associational; auto.
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
      Proof.
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
    Proof. apply fold_right_invariant; push_eval. Qed.
    Hint Rewrite eval_carries: push_eval.

    Lemma eval_to_associational n m p :
      m <> 0%nat -> length p = n ->
      Associational.eval (to_associational n m p) = Positional.eval sw n p.
    Proof. cbv [to_associational]; push_eval. Qed.
    Hint Rewrite eval_to_associational using solve [push_eval; distr_length] : push_eval.

    Lemma eval_from_associational idxs n p :
      n <> 0%nat -> 0 <= Associational.eval p < sw n ->
      Positional.eval sw n (from_associational idxs n p) = Associational.eval p.
    Proof.
      cbv [from_associational]; intros.
      rewrite Rows.flatten_mod by eauto using Rows.length_from_associational.
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.
    Hint Rewrite eval_from_associational using solve [push_eval; distr_length] : push_eval.

    Lemma from_associational_partitions n idxs p  (_:n<>0%nat):
      forall i, (i < n)%nat ->
                nth_default 0 (from_associational idxs n p) i = (Associational.eval p) mod (sw (S i)) / sw i.
    Proof.
      intros; cbv [from_associational].
      rewrite Rows.flatten_partitions with (n:=n) by (eauto using Rows.length_from_associational; omega).
      rewrite Associational.bind_snd_correct.
      push_eval.
    Qed.

    Lemma from_associational_eq n idxs p  (_:n<>0%nat):
      from_associational idxs n p = Rows.partition sw n (Associational.eval p).
    Proof.
      intros. cbv [from_associational].
      rewrite Rows.flatten_partitions' with (n:=n) by eauto using Rows.length_from_associational.
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
      Proof.  cbv [mul_converted]; push_eval. Qed.
      Hint Rewrite eval_mul_converted : push_eval.

      Lemma mul_converted_partitions n1 n2 m1 m2 n3 idxs p1 p2  (_:n3<>0%nat) (_:m1<>0%nat) (_:m2<>0%nat):
        length p1 = n1 -> length p2 = n2 ->
        mul_converted n1 n2 m1 m2 n3 idxs p1 p2 = Rows.partition sw n3 (Positional.eval sw n1 p1 * Positional.eval sw n2 p2).
      Proof.
        intros; cbv [mul_converted].
        rewrite from_associational_eq by auto. push_eval.
      Qed.
    End mul_converted.
  End BaseConversion.

  (* multiply two (n*k)-bit numbers by converting them to n k-bit limbs each, multiplying, then converting back *)
  Section widemul.
    Context (log2base : Z) (log2base_pos : 0 < log2base).
    Context (n : nat) (n_nz : n <> 0%nat) (n_le_log2base : Z.of_nat n <= log2base)
            (nout : nat) (nout_2 : nout = 2%nat). (* nout is always 2, but partial evaluation is overeager if it's a constant *)
    Let dw : nat -> Z := weight (log2base / Z.of_nat n) 1.
    Let sw : nat -> Z := weight log2base 1.

    Local Lemma base_bounds : 0 < 1 <= log2base. Proof. auto with zarith. Qed.
    Local Lemma dbase_bounds : 0 < 1 <= log2base / Z.of_nat n. Proof. auto with zarith. Qed.
    Let dwprops : @weight_properties dw := wprops (log2base / Z.of_nat n) 1 dbase_bounds.
    Let swprops : @weight_properties sw := wprops log2base 1 base_bounds.

    Hint Resolve Z.gt_lt Z.positive_is_nonzero Nat2Z.is_nonneg.

    Definition widemul a b := mul_converted sw dw 1 1 n n nout (aligned_carries n nout) [a] [b].

    Lemma widemul_correct a b :
      0 <= a * b < 2^log2base * 2^log2base ->
      widemul a b = [(a * b) mod 2^log2base; (a * b) / 2^log2base].
    Proof.
      cbv [widemul]; intros.
      rewrite mul_converted_partitions by auto with zarith.
      subst nout sw; cbv [weight]; cbn.
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
      Focus 2. {
        rewrite from_associational_inlined_correct by (subst nout; auto).
        cbv [from_associational].
        rewrite !Rows.flatten_partitions' by eauto using Rows.length_from_associational.
        rewrite !Rows.eval_from_associational by (subst nout; auto).
        f_equal.
        rewrite !eval_carries, !Associational.bind_snd_correct, !Associational.eval_rev by auto.
        reflexivity. } Unfocus.
      subst widemul_inlined_reverse; reflexivity.
    Qed.
  End widemul.
End BaseConversion.
