From Coq Require Import ZArith Lia.
From Coq Require Import List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

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
               | _ => ring_simplify; lia
               end.
    Qed.
    Hint Rewrite eval_map_sat_multerm using (lia || assumption) : push_eval.

    Lemma eval_sat_mul s p q (s_nonzero:s<>0):
      Associational.eval (sat_mul s p q) = Associational.eval p * Associational.eval q.
    Proof using Type.
      cbv [sat_mul]; induction p; [reflexivity|].
      repeat match goal with
             | _ => progress (autorewrite with push_flat_map push_eval in * )
             | _ => rewrite IHp
             | _ => ring_simplify; lia
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
               | _ => ring_simplify; lia
               end.
    Qed.
    Hint Rewrite eval_map_sat_multerm_const using (lia || assumption) : push_eval.

    Lemma eval_sat_mul_const s p q (s_nonzero:s<>0):
      Associational.eval (sat_mul_const s p q) = Associational.eval p * Associational.eval q.
    Proof using Type.
      cbv [sat_mul_const]; induction p; [reflexivity|].
      repeat match goal with
             | _ => progress (autorewrite with push_flat_map push_eval in * )
             | _ => rewrite IHp
             | _ => ring_simplify; lia
             end.
    Qed.
    Hint Rewrite eval_sat_mul_const : push_eval.
  End Associational.
End Associational.

Module Columns.
  Import Weight.
  Section Columns.
    Context weight {wprops : @weight_properties weight}.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof using Type. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof using Type.
      cbv [eval]; intros; subst. rewrite map_app. simpl map.
      apply Positional.eval_snoc; distr_length.
    Qed. Hint Rewrite eval_snoc using (solve [distr_length]) : push_eval.

    Ltac cases :=
      match goal with
      | |- _ /\ _ => split
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | _ => progress break_match; try discriminate
      end.

    Section Flatten.
      Context (add_split : Z -> Z -> Z -> Z * Z).
      Context (add_split_mod :
                 forall s x y, fst (add_split s x y) = (x + y) mod s)
              (add_split_div :
                 forall s x y, snd (add_split s x y) = (x + y) / s).
      Hint Rewrite add_split_mod add_split_div : to_div_mod.

      Section flatten_column.
        Context (fw : Z). (* maximum size of the result *)

        (* Outputs (sum, carry) *)
        Definition flatten_column (digit: list Z) : (Z * Z) :=
          list_rect (fun _ => (Z * Z)%type) (0,0)
                    (fun x tl flatten_column_tl =>
                       list_case
                         (fun _ => (Z * Z)%type) (x mod fw, x / fw)
                         (fun y tl' =>
                            list_case
                              (fun _ => (Z * Z)%type) (add_split fw x y)
                              (fun _ _ =>
                                 dlet_nd rec := flatten_column_tl in (* recursively get the sum and carry *)
                                   dlet_nd sum_carry := add_split fw x (fst rec) in (* add the new value to the sum *)
                                   dlet_nd carry' := snd sum_carry + snd rec in (* add the two carries together *)
                                   (fst sum_carry, carry'))
                              tl')
                         tl)
                    digit.
      End flatten_column.

      Definition flatten_step (digit:list Z) (acc_carry:list Z * Z) : list Z * Z :=
        let acc := fst acc_carry in
        let carry := snd acc_carry in
        let fw := weight (S (length acc)) / weight (length acc) in
        dlet sum_carry := flatten_column fw (digit ++ [snd acc_carry]) in
              (acc ++ fst sum_carry :: nil, snd sum_carry).

      Definition flatten (xs : list (list Z)) : list Z * Z :=
        fold_right (fun a b => flatten_step a b) (nil,0) (rev xs).

      Ltac push_fast :=
        repeat match goal with
               | _ => progress cbv [Let_In list_case]
               | |- context [list_rect _ _ _ ?ls] => rewrite single_list_rect_to_match; destruct ls
               | _ => progress (unfold flatten_step in *; fold flatten_step in * )
               | _ => rewrite Nat.add_1_r
               | _ => rewrite Z.mul_div_eq_full by (auto with zarith; lia)
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
      Proof using add_split_mod.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_mod : to_div_mod.

      Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
        snd (flatten_column fw xs)  = sum xs / fw.
      Proof using add_split_div add_split_mod.
        (* this hint is already in the database but Z.div_add_l' is triggered first and that screws things up *)
        Hint Rewrite <- Z.div_add' using zutil_arith : pull_Zdiv.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => rewrite <-Z.div_add' by zutil_arith
                 | _ => rewrite Z.mul_div_eq_full by lia
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_div using auto with zarith : to_div_mod.

      Hint Rewrite Positional.eval_nil : push_eval.

      Lemma length_flatten_step digit state :
        length (fst (flatten_step digit state)) = S (length (fst state)).
      Proof using add_split_mod. cbv [flatten_step]; push. Qed.
      Hint Rewrite length_flatten_step : distr_length.
      Lemma length_flatten inp : length (fst (flatten inp)) = length inp.
      Proof using add_split_mod.
        cbv [flatten]. induction inp using rev_ind; push.
      Qed.
      Hint Rewrite length_flatten : distr_length.

      Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
      Proof using Type. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

      Lemma flatten_correct inp:
        forall n,
          length inp = n ->
          flatten inp = (Partition.partition weight n (eval n inp),
                         eval n inp / (weight n)).
      Proof using wprops add_split_mod add_split_div.
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
      Proof using wprops add_split_mod add_split_div.
        intros.
        rewrite flatten_correct with (n:=n) by auto.
        cbn [fst snd].
        rewrite eval_partition; auto.
      Qed.

      Lemma flatten_mod {n} inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
      Proof using wprops add_split_mod add_split_div.
        apply flatten_div_mod.
      Qed.
      Hint Rewrite @flatten_mod : push_eval.

      Lemma flatten_div {n} inp :
        length inp = n -> snd (flatten inp) = eval n inp / weight n.
      Proof using wprops add_split_mod add_split_div.
        apply flatten_div_mod.
      Qed.
      Hint Rewrite @flatten_div : push_eval.

      Lemma flatten_same_sum p q :
        Forall2 (fun x y => sum x = sum y) p q ->
        flatten p = flatten q.
      Proof using wprops add_split_mod add_split_div.
        cbv [flatten].
        let H := fresh in
        intro H; apply Forall2_rev in H;
          induction H; [ reflexivity | ].
        push.
      Qed.
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
        erewrite <-Positional.eval_from_associational by eauto with zarith.
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

    Section Reverse.
      Definition reverse (p : list (list Z)) : list (list Z) :=
        map (@rev Z) p.

      Lemma eval_reverse n p :
        eval n (reverse p) = eval n p.
      Proof.
        cbv [eval reverse]. rewrite map_map.
        f_equal. apply map_ext; intros.
        autorewrite with push_sum. reflexivity.
      Qed. Hint Rewrite @eval_reverse : push_eval.

      Lemma length_reverse p :
        length (reverse p) = length p.
      Proof. cbv [reverse]; distr_length. Qed.
      Hint Rewrite @length_reverse : distr_length.

      Lemma reverse_same_sum p :
        Forall2 (fun x y => sum x = sum y) (reverse p) p.
      Proof.
        cbv [reverse].
        induction p; cbn [rev map]; constructor;
          autorewrite with push_sum; auto.
      Qed.
    End Reverse.
  End Columns.
End Columns.

Module Rows.
  Import Weight.
  Section Rows.
    Context weight {wprops : @weight_properties weight}.
    Local Notation rows := (list (list Z)) (only parsing).
    Local Notation cols := (list (list Z)) (only parsing).

    Hint Rewrite Positional.eval_nil Positional.eval0 @Positional.eval_snoc
         Positional.eval_to_associational
         Columns.eval_nil Columns.eval_snoc using (auto; solve [distr_length]) : push_eval.
    Hint Resolve in_eq in_cons : core.

    Definition eval n (inp : rows) :=
      sum (map (Positional.eval weight n) inp).
    Lemma eval_nil n : eval n nil = 0.
    Proof using Type. cbv [eval]. rewrite map_nil, sum_nil; reflexivity. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval0 x : eval 0 x = 0.
    Proof using Type. cbv [eval]. induction x; autorewrite with push_map push_sum push_eval; lia. Qed.
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
               | _ => split; try lia
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
                 | _ => lia
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
          remember (Nat.pred n) as m. replace n with (S m) by lia.
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
        case_eq (max_column_size (Columns.from_associational weight n p)); [lia|].
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
            (fst (fst start_state) = Partition.partition weight m (eval m row1' + eval m row2')) ->
            let sum := eval nm (row1' ++ row1) + eval nm (row2' ++ row2) in
            sum_rows' start_state row1 row2
            = (Partition.partition weight nm sum, sum / weight nm, nm) .
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
                   | _ => rewrite <-Z.div_add' by auto with zarith
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
            sum_rows row1 row2 = (Partition.partition weight n sum, sum / weight n).
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
      Hint Resolve length_sum_rows : core.
      Hint Rewrite sum_rows_mod using (auto; solve [distr_length; auto]) : push_eval.

      Definition flatten' (start_state : list Z * Z) (inp : rows) : list Z * Z :=
        fold_right (fun next_row (state : list Z * Z)=>
                      let out_carry := sum_rows (fst state) next_row in
                      (fst out_carry, snd state + snd out_carry)) start_state inp.

      (* In order for the output to have the right length and bounds,
         we insert rows of zeroes if there are fewer than two rows. *)
      Definition flatten n (inp : rows) : list Z * Z :=
        let default := Positional.zeros n in
        flatten' (hd default inp, 0) (hd default (tl inp) :: tl (tl inp)).

      Lemma flatten'_cons state r inp :
        flatten' state (r :: inp) = (fst (sum_rows (fst (flatten' state inp)) r), snd (flatten' state inp) + snd (sum_rows (fst (flatten' state inp)) r)).
      Proof using Type. cbv [flatten']; autorewrite with list push_fold_right. reflexivity. Qed.
      Lemma flatten'_snoc state r inp :
        flatten' state (inp ++ r :: nil) = flatten' (fst (sum_rows (fst state) r), snd state + snd (sum_rows (fst state) r)) inp.
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
        flatten' start_state inp = (Partition.partition weight n sum, sum / weight n).
      Proof using wprops.
        induction inp using rev_ind; push. subst sum.
        destruct (dec (inp = nil)); [ subst inp; cbn | ];
          repeat match goal with
                 | _ => rewrite IHinp by push; clear IHinp
                 | |- pair _ _ = pair _ _ => f_equal
                 | _ => apply (@partition_eq_mod _ wprops)
                 | _ => rewrite <-Z.div_add_l' by auto with zarith
                 | _ => rewrite Z.mod_add'_full by lia
                 | _ => rewrite Z.mul_div_eq_full by auto with zarith
                 | _ => progress (push_Zmod; pull_Zmod)
                 | _ => progress push
                 end.
      Qed.

      Hint Rewrite (@Positional.length_zeros) : distr_length.
      Hint Rewrite (@Positional.eval_zeros) using auto : push_eval.

      Lemma flatten_correct inp n :
        (forall row, In row inp -> length row = n) ->
        flatten n inp = (Partition.partition weight n (eval n inp), eval n inp / weight n).
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
        fst (add n p q) = Partition.partition weight n (Positional.eval weight n p + Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma add_div n p q :
        length p = n -> length q = n ->
        snd (add n p q) = (Positional.eval weight n p + Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma conditional_add_partitions n mask cond p q :
        length p = n -> length q = n -> map (Z.land mask) q = q ->
        fst (conditional_add n mask cond p q)
        = Partition.partition weight n (Positional.eval weight n p + (if dec (cond = 0) then 0 else Positional.eval weight n q)).
      Proof using wprops.
        cbv [conditional_add]; intros; rewrite add_partitions by (distr_length; auto).
        autorewrite with push_eval; reflexivity.
      Qed.

      Lemma conditional_add_div n mask cond p q :
        length p = n -> length q = n -> map (Z.land mask) q = q ->
        snd (conditional_add n mask cond p q) = (Positional.eval weight n p + (if dec (cond = 0) then 0 else Positional.eval weight n q)) / weight n.
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
        fst (sub n p q) = Partition.partition weight n (Positional.eval weight n p - Positional.eval weight n q).
      Proof using wprops. solver. Qed.

      Lemma sub_div n p q :
        length p = n -> length q = n ->
        snd (sub n p q) = (Positional.eval weight n p - Positional.eval weight n q) / weight n.
      Proof using wprops. solver. Qed.

      Lemma conditional_sub_partitions n p q
        (Hp : p = Partition.partition weight n (Positional.eval weight n p)) :
        length q = n ->
        0 <= Positional.eval weight n q < weight n ->
        conditional_sub n p q = Partition.partition weight n (if Positional.eval weight n q <=? Positional.eval weight n p then Positional.eval weight n p - Positional.eval weight n q else Positional.eval weight n p).
      Proof using wprops.
        cbv [conditional_sub]; intros.
        rewrite (surjective_pairing (sub _ _ _)).
        assert (length p = n) by (rewrite Hp; distr_length).
        assert (0 <= Positional.eval weight n p < weight n) by
            (rewrite Hp; autorewrite with push_eval; auto using Z.mod_pos_bound).
        rewrite sub_partitions, sub_div; distr_length.
        erewrite Positional.select_eq by (distr_length; eauto).
        rewrite Z.div_sub_small, Z.ltb_antisym by lia.
        destruct (Positional.eval weight n q <=? Positional.eval weight n p);
          cbn [negb]; autorewrite with zsimplify_fast;
            break_match; try lia; congruence.
      Qed.

      Let sub_then_maybe_add_Z a b c :=
        a - b + (if (a - b <? 0) then c else 0).

      Lemma sub_then_maybe_add_partitions n mask p q r :
        length p = n -> length q = n -> length r = n ->
        map (Z.land mask) r = r ->
        0 <= Positional.eval weight n p < weight n ->
        0 <= Positional.eval weight n q < weight n ->
        fst (sub_then_maybe_add n mask p q r) = Partition.partition weight n (sub_then_maybe_add_Z (Positional.eval weight n p) (Positional.eval weight n q) (Positional.eval weight n r)).
      Proof using wprops.
        cbv [sub_then_maybe_add]. subst sub_then_maybe_add_Z.
        intros.
        rewrite (surjective_pairing (sub _ _ _)).
        rewrite (surjective_pairing (add _ _ _)).
        cbn [fst snd].
        rewrite sub_partitions, add_partitions, sub_div by distr_length.
        autorewrite with push_eval.
        Z.rewrite_mod_small.
        rewrite Z.div_sub_small by lia.
        break_innermost_match; Z.ltb_to_lt; try lia;
          auto using partition_eq_mod with zarith.
      Qed.

      Lemma mul_partitions base n m p q :
        base <> 0 -> m <> 0%nat -> length p = n -> length q = n ->
        fst (mul base n m p q) = Partition.partition weight m (Positional.eval weight n p * Positional.eval weight n q).
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
        { break_match; cbn in *; auto with zarith. }
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
        rewrite <-Z.div_mod'' by auto with zarith.
        autorewrite with push_eval; reflexivity.
      Qed.

      (* returns all-but-lowest-limb and lowest limb *)
      Definition divmod (p : list Z) : list Z * Z
        := (tl p, hd 0 p).
    End Ops.
  End Rows.
#[global]
  Hint Rewrite length_from_columns using eassumption : distr_length.
#[global]
  Hint Rewrite length_sum_rows using solve [ reflexivity | eassumption | distr_length; eauto ] : distr_length.
#[global]
  Hint Rewrite length_fst_extract_row length_snd_extract_row length_flatten length_fst_from_columns' length_snd_from_columns' : distr_length.
End Rows.
