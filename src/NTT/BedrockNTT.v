Require Import Spec.ModularArithmetic.
Require Import Crypto.NTT.RupicolaUtils.
Require Import Crypto.NTT.CyclotomicDecomposition.
Require Import Crypto.NTT.RupicolaNTT.
Require Import bedrock2.Array.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.InlineTables.
Require Import Rupicola.Lib.Loops.

Section Utils.
  (* TODO: move somewhere *)
  Lemma set_nth_eq {A: Type} n (l: list A) x:
    ListUtil.set_nth n x l = replace_nth n l x.
  Proof.
    revert n x; induction l; intros.
    - destruct n; reflexivity.
    - destruct n; [reflexivity|].
      simpl. rewrite <- ListUtil.cons_set_nth, IHl. reflexivity.
  Qed.

  Lemma Forall2_replace_nth {A B: Type} (R: A -> B -> Prop) i x y xs ys:
    Forall2 R xs ys ->
    R x y ->
    Forall2 R (replace_nth i xs x) (replace_nth i ys y).
  Proof.
    intros HF HR.
    apply Forall2_nth_error_iff. split.
    - do 2 rewrite replace_nth_length.
      eapply Forall2_length; eauto.
    - do 2 rewrite <- set_nth_eq.
      intros. rewrite ListUtil.nth_set_nth in H, H0.
      rewrite (Forall2_length HF) in H.
      destruct (Nat.eq_dec k i).
      + destruct (lt_dec _ _); [|congruence].
        inversion H; inversion H0; subst; assumption.
      + eapply Forall2_nth_error_iff; eauto.
  Qed.
End Utils.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {ntt ntt_inverse: String.string}.
  Context {q: positive}.
  Local Notation F := (F q).
  Context {n km1: nat}.
  Context (zeta: F) (c:F) (zetas: list F).

  (* Assume we have a partial word evaluation function, returns none if input is invalid *)
  Context {feval: word -> option F}.
  Context {F_to_Z: Convertible F Z}.
  Local Instance F_to_word: Convertible F word := fun x => word.of_Z (cast x).
  (* Converting a field element to a word, and back is correct *)
  Hypothesis feval_ok: forall x, feval (cast x) = Some x.
  (* For montgomery, F_to_Z would be something like fun x => F.to_Z (to_montgomery x), it's not necessarily F.to_Z *)

  (* The field operations we need *)
  Context {add sub mul: String.string}.

  Hypothesis n_ge_km1: (km1 <= n)%nat.
  Hypothesis n_lt_width: (n < Z.to_nat width)%nat.
  Hypothesis zetas_length_ok: length zetas = Nat.pow 2 km1.

  (* This is only needed because we need 2^(width/8) * 2^km1 ≤ 2^width to use InlineTables... Not a problem in practice *)
  Hypothesis km1p3_le_with: (km1 + 3 <= Z.to_nat width)%nat.

  Notation NTT_gallina := (@NTT_gallina q n km1 zetas).
  Notation NTT_inverse_gallina := (@NTT_inverse_gallina q n km1 zetas c).

  Local Instance F_default: HasDefault F := 0%F.

  Definition spec_of_binop {name: String.string} (model: F -> F -> F): spec_of name :=
    fnspec! name (x y: word) / (a b: F) ~> (res: word),
      { requires tr mem :=
          feval x = Some a /\ feval y = Some b;
        ensures tr' mem' :=
          tr'= tr /\ mem' = mem /\ feval res = Some (model a b)
      }.

  (* Assume add sub mul are correct *)
  (* Definition spec_of_binop {name: String.string} (model: F -> F -> F): spec_of name := *)
  (*   fnspec! name (x y: word) / (a b: F) ~> (res: word), *)
  (*     { requires tr mem := *)
  (*         x = cast a /\ y = cast b; *)
  (*       ensures tr' mem' := *)
  (*         tr'= tr /\ mem' = mem /\ res = cast (model a b) *)
  (*     }. *)

  Instance spec_of_add: spec_of add :=
    spec_of_binop F.add.
  Instance spec_of_sub: spec_of sub :=
    spec_of_binop F.sub.
  Instance spec_of_mul: spec_of mul :=
    spec_of_binop F.mul.

  Instance spec_of_ntt: spec_of ntt :=
    fnspec! ntt (p_ptr: word) / (p: ListArray.t F) R,
      { requires tr mem :=
          exists p',
          Forall2 (fun x y => feval y = Some x) p p' /\
          mem =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p') * R;
        ensures tr' mem' :=
          tr' = tr /\
          exists p',
          Forall2 (fun x y => feval y = Some x) (NTT_gallina p) p' /\
          mem' =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p') * R }.

  (* Instance spec_of_ntt: spec_of ntt := *)
  (*   fnspec! ntt (p_ptr: word) / (p: ListArray.t F) R, *)
  (*     { requires tr mem := *)
  (*         mem =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr (List.map cast p)) * R; *)
  (*       ensures tr' mem' := *)
  (*         tr' = tr /\ *)
  (*         mem' =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr (List.map cast (NTT_gallina p))) * R }. *)

  Instance spec_of_ntt_inverse: spec_of ntt_inverse :=
    fnspec! ntt_inverse (p_ptr: word) / (p: ListArray.t F) R,
      { requires tr mem :=
          exists p',
          Forall2 (fun x y => feval y = Some x) p p' /\
          mem =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p') * R;
        ensures tr' mem' :=
          tr' = tr /\
          exists p',
          Forall2 (fun x y => feval y = Some x) (NTT_inverse_gallina p) p' /\
          mem' =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p') * R }.

  (* Instance spec_of_ntt_inverse: spec_of ntt_inverse := *)
  (*   fnspec! ntt_inverse (p_ptr: word) / (p: ListArray.t F) R, *)
  (*     { requires tr mem := *)
  (*         mem =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr (List.map cast p)) * R; *)
  (*       ensures tr' mem' := *)
  (*         tr' = tr /\ *)
  (*         mem' =* (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr (List.map cast (NTT_inverse_gallina p))) * R }. *)

  Definition br2_ntt :=
    func! (p) {
      m = coq:(0);
      len = coq:(Z.pow 2 (Z.of_nat n));
      while (coq:(Z.pow 2 (Z.of_nat (n - km1))) < len) {
        old_len = len;
        len = len >> coq:(1);
        start = coq:(0);
        while (start < coq:(Z.pow 2 (Z.of_nat n))) {
          m = m + coq:(1);
          z = coq:(expr.inlinetable access_size.word (to_byte_table (List.map cast zetas)) (expr.op bopname.mul (expr.literal (width / 8)) (expr.var "m")));
          j = start;
          while (j < (start + len)) {
            x = load(coq:(offset (expr.var "p") bedrock_expr:(j + len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
            unpack! tmp = $mul(z, x);
            y = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
            unpack! x = $sub(y, tmp);
            store(coq:(offset (expr.var "p") bedrock_expr:(j + len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
            unpack! x = $add(y, tmp);
            store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
            j = j + coq:(1)
          };
          start = start + old_len
        }
      }
    }.

  Definition br2_ntt_inverse :=
    func! (p) {
      m = coq:(Z.of_nat (Nat.pow 2 km1));
      len = coq:(Z.of_nat (Nat.pow 2 (n - km1)));
      while (len < coq:(Z.of_nat (Nat.pow 2 n))) {
        start = coq:(0);
        old_len = len;
        len = len << coq:(1);
        while (start < coq:(Z.of_nat (Nat.pow 2 n))) {
          m = m - coq:(1);
          z = coq:(expr.inlinetable access_size.word (to_byte_table (List.map cast zetas)) (expr.op bopname.mul (expr.literal (width / 8)) (expr.var "m")));
          j = start;
          while (j < start + old_len) {
            tmp = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
            x = load(coq:(offset (expr.var "p") bedrock_expr:(j + old_len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
            unpack! y = $add(tmp, x);
            store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), y);
            unpack! x = $sub(x, tmp);
            unpack! y = $mul(z, x);
            store(coq:(offset (expr.var "p") bedrock_expr:(j + old_len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), y);
            j = j + coq:(1)
          };
          start = start + len
        }
      };
      j = coq:(0);
      while (j < coq:(Z.of_nat (Nat.pow 2 n))) {
        x = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
        unpack! x = $mul(coq:(@cast _ Z _ c), x);
        store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
        j = j + coq:(1)
      }
    }.

  Lemma br2_ntt_ok:
    program_logic_goal_for br2_ntt
      (forall functions : map.rep,
          map.get functions ntt = Some br2_ntt ->
          spec_of_mul functions ->
          spec_of_sub functions -> spec_of_add functions -> spec_of_ntt functions).
  Proof.
    Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub cast F.F.
    repeat straightline.
    unfold NTT_gallina. unfold nlet.
    apply wp_while.
    (* First loop invariant *)
    pose (loop_inv1:= fun (fuel: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                        (fuel <= km1)%nat /\
                        let i := (km1 - fuel)%nat in
                        tr' = tr /\
                        exists p' px,
                        layer_decomposition_loop zetas i \< 0, 2 ^ Z.of_nat n, p \> = \< (2 ^ Z.of_nat i) - 1, 2 ^ Z.of_nat (n - i), px \> /\
                        Forall2 (fun x y => feval y = Some x) px p' /\
                        map.get loc "p" = Some p_ptr /\
                        map.get loc "m" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 i) - 1))) /\
                        map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - i)))) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p' * R)%sep mem').
    exists nat, lt, loop_inv1.
    split; [apply lt_wf|].
    split. (* Invariant holds at beginning *)
    { exists km1. repeat split; [Lia.lia|..].
      exists x, p. repeat split.
      - unfold layer_decomposition_loop. rewrite PeanoNat.Nat.sub_diag.
        rewrite <- fold_left_as_nd_ranged_for_all.
        rewrite z_range_nil by Lia.lia. simpl.
        rewrite Z.pow_0_r, Z.sub_diag, PeanoNat.Nat.sub_0_r. reflexivity.
      - assumption.
      (* These map goals could be automated *)
      - unfold l1, l0, l. do 2 (rewrite map.get_put_diff by congruence).
        apply map.get_put_same.
      - unfold l1, l0, l. rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same. unfold m. rewrite PeanoNat.Nat.sub_diag.
        reflexivity.
      - unfold l1. rewrite map.get_put_same. unfold len.
        rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.sub_0_r.
        rewrite Nat2Z.inj_pow. reflexivity.
      - assumption. }
    intros fuel tr' mem' loc' Hinv.
    destruct Hinv as (Hfuel & -> & p' & px' & HF1 & Heq & Hp & Hm & Hlen & Hseps).
    eexists. split.
    { apply expr_compile_word_ltu.
      - apply expr_compile_Z_literal.
      - apply expr_compile_var. eauto. }
    split.
    { (* Invariant preservation *)
      intro Hb. rewrite Nat2Z.inj_pow in Hb.
      rewrite <- word.morph_ltu in Hb.
      2-3: split; try Lia.lia.
      2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
      generalize (Zlt_cases (2 ^ Z.of_nat (n - km1)) (Z.of_nat 2 ^ Z.of_nat (n - (km1 - fuel)))).
      rewrite word.unsigned_b2w in Hb.
      destruct (_ <? _); intros Hlt1; [|cbv in Hb; congruence].
      assert (Hfnz: (fuel <> 0)%nat) by (intro X; subst fuel; rewrite PeanoNat.Nat.sub_0_r in Hlt1; Lia.lia).
      repeat straightline. eexists. split; [apply expr_compile_var; eauto|].
      repeat straightline. eexists. split; [apply expr_compile_word_sru; [apply expr_compile_var; unfold l; rewrite map.get_put_diff by congruence; eauto|apply expr_compile_Z_literal]|].
      repeat straightline.
      assert (Hp1: map.get l1 "p" = Some p_ptr).
      { unfold l1, l0, l; repeat (rewrite map.get_put_diff by congruence). auto. }
      assert (Hm1: map.get l1 "m" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 (km1 - fuel)) - 1)))).
      { unfold l1, l0, l. repeat (rewrite map.get_put_diff by congruence). auto. }
      assert (Hlen1: map.get l1 "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (km1 - (fuel - 1))))))).
      { unfold l1, l0, l; repeat (rewrite map.get_put_diff by congruence).
        rewrite map.get_put_same, <- word.morph_shiftr.
        2: Lia.lia.
        2: split; [|rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone]; Lia.lia.
        rewrite Z.shiftr_div_pow2 by Lia.lia.
        replace (2 ^ 1) with (Z.of_nat (Nat.pow 2 1)) by reflexivity.
        rewrite <- Nat2Z.inj_div, <- PeanoNat.Nat.pow_sub_r by Lia.lia.
        f_equal. f_equal. f_equal. f_equal.
        clear -Hfuel n_ge_km1 Hfnz. Lia.lia. }
      assert (Hold_len1: map.get l1 "old_len" = Some _) by (unfold l1, l0, l; repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same).
      apply wp_while.
      (* second loop *)
      pose (loop_inv2:= fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                        (fuel2 <= Nat.pow 2 (km1 - fuel))%nat /\
                        let i := ((Nat.pow 2 (km1 - fuel) - fuel2))%nat in
                        tr' = tr /\
                        exists p'' px'',
                        polynomial_list_loop zetas (Z.of_nat i) (2 ^ Z.of_nat (n - (km1 - fuel))) (2 ^ Z.of_nat (n - (km1 - (fuel - 1)))) \< (2 ^ Z.of_nat (km1 - fuel) - 1), 0, px' \> = \< (((2 ^ Z.of_nat (km1 - fuel)) - 1) + (Z.of_nat i)), (Z.of_nat i * (2 ^ Z.of_nat (n - (km1 - fuel)))), px'' \> /\
                        Forall2 (fun x y => feval y = Some x) px'' p'' /\
                        map.get loc "p" = Some p_ptr /\
                        map.get loc "m" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 (km1 - fuel)) - 1 + i))) /\
                        map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (km1 - (fuel - 1)))))) /\
                        map.get loc "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (km1 - fuel))))) /\
                        map.get loc "start" = Some (word.of_Z (Z.of_nat (i * (Nat.pow 2 (n - (km1 - fuel)))))) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p'' * R)%sep mem').
      exists nat, lt, loop_inv2. split; [apply lt_wf|]. split.
      { (* invariant holds at beginning *)
        exists (2 ^ (km1 - fuel))%nat. repeat split; [Lia.lia|].
        exists p', px'. repeat split; auto.
        - rewrite PeanoNat.Nat.sub_diag. unfold polynomial_list_loop.
          rewrite <- fold_left_as_nd_ranged_for_all.
          rewrite z_range_nil by Lia.lia. simpl.
          rewrite Z.add_0_r, Z.mul_0_l. reflexivity.
        - rewrite Hm1, PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r. reflexivity.
        - rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_l.
          apply map.get_put_same. }
      intros fuel2 tr2 mem2 l2 Hinv2.
      destruct Hinv2 as (Hfuel2 & -> & p2 & px2 & Heq2 & HF2 & Hp2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & Hseps2).
      eexists; split.
      { apply expr_compile_word_ltu.
        - apply expr_compile_var. eauto.
        - apply expr_compile_Z_literal. }
      rewrite <- word.morph_ltu.
      2-3: split; try Lia.lia.
      4: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
      2: apply Nat2Z.is_nonneg.
      2:{ rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
          assert (km1 - fuel + _ = n)%nat as -> by (clear -Hfnz Hfuel n_ge_km1; Lia.lia).
          assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width; Lia.lia); reflexivity).
          apply Nat2Z.inj_lt.
          eapply Nat.le_lt_trans; [|eapply PeanoNat.Nat.pow_lt_mono_r; try eassumption; Lia.lia].
          clear; Lia.lia. }
      rewrite word.unsigned_b2w. split.
      { (* Invariant preservation *) intro Hcond.
        assert (fuel2 <> 0)%nat as Hfnz2.
        { destruct (Nat.eq_dec fuel2 0%nat) as [->|]; auto.
          elim Hcond. clear Hcond. rewrite PeanoNat.Nat.sub_0_r.
          rewrite <- Nat.pow_add_r.
          assert (_ - _ + _ = n)%nat as -> by (clear -Hfnz Hfuel n_ge_km1; Lia.lia).
          rewrite Nat2Z.inj_pow, Z.ltb_irrefl. reflexivity. }
        repeat straightline.
        eexists. split.
        { apply expr_compile_word_add.
          - apply expr_compile_var. eauto.
          - apply expr_compile_Z_literal. }
        rewrite <- word.ring_morph_add.
        repeat straightline. exists (cast (InlineTable.get zetas ((2 ^ (km1 - fuel) - 1 + 2 ^ (km1 - fuel) - fuel2) + 1)%nat)).
        split.
        { eexists; split.
          - apply map.get_put_same.
          - cbn. rewrite <- word.ring_morph_mul.
            unfold load.
            assert (Z.of_nat _ + 1 = Z.of_nat _ + Z.of_nat 1) as -> by reflexivity.
            rewrite <- Nat2Z.inj_add.
            erewrite load_from_word_table; auto.
            2:{ rewrite length_to_byte_table, map_length.
                rewrite zetas_length_ok. assert (width / 8 = 4 \/ width / 8 = 8) as Hw.
                { clear -BW.
                  destruct width_cases as [-> | ->]; [left|right]; reflexivity. }
                rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -Hw; destruct Hw; Lia.lia).
                rewrite Nat2Z.inj_pow.
                transitivity (2 ^ 3 * 2 ^ Z.of_nat km1).
                - apply Z.mul_le_mono_nonneg_r.
                  + apply Z.lt_le_incl, ZLib.Z.pow2_pos, Nat2Z.is_nonneg.
                  + clear -Hw. destruct Hw as [-> | ->]; Lia.lia.
                - rewrite <- Z.pow_add_r by Lia.lia.
                  apply Z.pow_le_mono_r; Lia.lia. }
            eexists; split; [reflexivity|].
            unfold InlineTable.get. rewrite map_nth.
            repeat f_equal. cbv [cast Convertible_self id].
            clear -n_ge_km1 Hfuel Hfuel2; Lia.lia.
            rewrite map_length, zetas_length_ok.
            eapply (Nat.lt_le_trans _ (2 ^ (km1 - (fuel - 1)))%nat).
            + assert (km1 - (fuel - 1) = S (km1 - fuel))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
              rewrite Nat.pow_succ_r'. clear -Hfuel2 Hfnz2. Lia.lia.
            + apply Nat.pow_le_mono; clear -km1p3_le_with; Lia.lia. }
        repeat straightline. eexists. split.
        { apply expr_compile_var. unfold l4, l3.
          do 2 rewrite map.get_put_diff by congruence.
          apply Hstart2. }
        repeat straightline.
        apply wp_while.
        assert (Hj: map.get l5 "j" = Some _) by (apply map.get_put_same).
        assert (Hz: map.get l5 "z" = Some _) by (unfold l5; rewrite map.get_put_diff by congruence; apply map.get_put_same).
        assert (Hm3: map.get l5 "m" = Some _) by (unfold l5, l4; do 2 (rewrite map.get_put_diff by congruence); apply map.get_put_same).
        assert (Hstart3: map.get l5 "start" = Some _) by (unfold l5, l4, l3; repeat (rewrite map.get_put_diff by congruence); eassumption).
        assert (Hold_len3: map.get l5 "old_len" = Some _) by (unfold l5, l4, l3; repeat (rewrite map.get_put_diff by congruence); eassumption).
        assert (Hlen3: map.get l5 "len" = Some _) by (unfold l5, l4, l3; repeat (rewrite map.get_put_diff by congruence); eassumption).
        assert (Hp3: map.get l5 "p" = Some _) by (unfold l5, l4, l3; repeat (rewrite map.get_put_diff by congruence); eassumption).
        pose (loop_inv3 := fun (fuel3:nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                        (fuel3 <= Nat.pow 2 (n - (km1 - (fuel - 1))))%nat /\
                        let i := (Nat.pow 2 (n - (km1 - (fuel - 1))) - fuel3)%nat in
                        tr' = tr /\
                        let px'' := polynomial_decompose_loop (Z.of_nat i) (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)))) (Z.of_nat (2 ^ (n - (km1 - (fuel - 1))))) (InlineTable.get zetas (2 ^ (km1 - fuel) - 1 + 2 ^ (km1 - fuel) - fuel2 + 1)%nat) px2 in
                        exists p'',
                        Forall2 (fun x y => feval y = Some x) px'' p'' /\
                        map.get loc "p" = Some p_ptr /\
                        map.get loc "m" = Some (word.of_Z (Z.of_nat (2 ^ (km1 - fuel) - 1 + (2 ^ (km1 - fuel) - fuel2)) + 1)) /\
                        map.get loc "len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (km1 - (fuel - 1)))))) /\
                        map.get loc "old_len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (km1 - fuel))))) /\
                        map.get loc "start" = Some (word.of_Z (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel))))) /\
                        map.get loc "j" = Some (word.of_Z (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)) + i))) /\
                        map.get loc "z" = Some (cast (InlineTable.get zetas (2 ^ (km1 - fuel) - 1 + 2 ^ (km1 - fuel) - fuel2 + 1)%nat)) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p'' * R)%sep mem').
        exists nat, lt, loop_inv3. split; [apply lt_wf|].
        split.
        { (* Invariant holds at beginning *)
          exists (2 ^ (n - (km1 - (fuel - 1))))%nat. split; [reflexivity|].
          intros. split; [reflexivity|]. intros.
          assert (i = 0)%nat as -> by (clear; Lia.lia).
          exists p2. repeat split; auto.
          - assert (px'' = px2) as ->; auto.
            unfold px'', polynomial_decompose_loop.
            rewrite Z.add_0_r, <- fold_left_as_nd_ranged_for_all.
            unfold z_range. rewrite z_range'_seq; [|apply Nat2Z.is_nonneg].
            rewrite <- Nat2Z.inj_sub by reflexivity.
            repeat rewrite Nat2Z.id. rewrite Nat.sub_diag, ListUtil.seq_len_0.
            rewrite ListUtil.List.map_nil; reflexivity.
          - rewrite Nat.add_0_r. auto. }
        intros fuel3 tr3 m3 loc3 Hinv3.
        destruct Hinv3 as (Hfuel3 & -> & p3 & HF3 & Hp4 & Hm4 & Hlen4 & Hold_len4 & Hstart4 & Hj4 & Hz4 & Hseps4).
        eexists; split.
        { apply expr_compile_word_ltu.
          - apply expr_compile_var. eauto.
          - apply expr_compile_Z_add; apply expr_compile_var; eauto. }
        rewrite <- word.morph_ltu.
        3: rewrite <- Nat2Z.inj_add.
        2-3: split; try (apply Nat2Z.is_nonneg).
        2-3: assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width; Lia.lia); reflexivity).
        2-3: apply Nat2Z.inj_lt.
        2-3: eapply (Nat.le_lt_trans _ (Nat.pow 2 n)); [|apply Nat.pow_lt_mono_r; auto].
        2-3: rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
        2-3: assert (km1 - fuel + _ = n)%nat as -> by (clear -Hfnz Hfuel n_ge_km1; Lia.lia).
        2: transitivity (2 ^ n - fuel2 * 2 ^ (n - (km1 - fuel)) + (2 ^ (n - (km1 - (fuel - 1)))))%nat; [clear; Lia.lia|].
        2-3: rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - (km1 - (fuel - 1))))).
        2-3: assert (n - (km1 - fuel) = S (n - (km1 - (fuel - 1))))%nat as -> by (clear -n_ge_km1 Hfuel Hfnz; Lia.lia).
        2-3: rewrite Nat.pow_succ_r'.
        2-3: assert (Nat.pow 2 n = (Nat.pow 2 (km1 - (fuel - 1))) * (Nat.pow 2 (n - (km1 - (fuel - 1)))))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; clear -n_ge_km1 Hfuel Hfnz; Lia.lia).
        2-3: rewrite Nat.mul_assoc, <- Nat.mul_sub_distr_r, <- Nat.mul_add_distr_r.
        2-3: apply Nat.mul_le_mono_r; clear -Hfuel Hfuel2 Hfnz Hfnz2 n_ge_km1.
        2-3: generalize (Nat.pow_nonzero 2%nat (km1 - (fuel - 1)) ltac:(Lia.lia)); Lia.lia.
        rewrite word.unsigned_b2w, <- Nat2Z.inj_add. split; intro Hcond2.
        { (* Invariant preservation *)
          clear Hb. match goal with | [H: Z.b2z (?a <? ?b) <> _ |- _] => generalize (Zlt_cases a b); destruct (a <? b); cbv in H; [clear H|congruence]; intro H end.
          apply Nat2Z.inj_lt in Hcond2.
          assert (fuel3 <> 0)%nat as Hfnz3.
          { destruct (Nat.eq_dec fuel3 0%nat) as [->|]; auto.
            clear -Hcond2 Hfuel Hfuel2 Hfuel3 n_ge_km1 Hfnz Hfnz2.
            Lia.lia. }
          generalize (SizedListArray_length (sz:=access_size.word) _ _ _ _ _ Hseps4). intro Xlen.
          assert ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)) + (2 ^ (n - (km1 - (fuel - 1))) - fuel3) + 2 ^ (n - (km1 - (fuel - 1))) < 2 ^ n)%nat as idx_ok.
          { clear -Hfuel Hfuel2 Hfuel3 n_ge_km1 Hfnz Hfnz2 Hfnz3.
            rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
            assert (km1 - fuel + _ = n)%nat as -> by Lia.lia.
            assert (2 ^ n - fuel2 * 2 ^ (n - (km1 - fuel)) + (2 ^ (n - (km1 - (fuel - 1))) - fuel3) + 2 ^ (n - (km1 - (fuel - 1))) = 2 ^ n - fuel2 * 2 ^ (n - (km1 - fuel)) + (2 * 2 ^ (n - (km1 - (fuel - 1))) - fuel3))%nat as -> by Lia.lia.
            rewrite <- Nat.pow_succ_r'.
            assert (S (n - (km1 - (fuel - 1))) = (n - (km1 - fuel)))%nat as -> by Lia.lia.
            generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)).
            generalize (NatUtil.pow_nonzero 2 (km1 - fuel) ltac:(Lia.lia)).
            generalize (NatUtil.pow_nonzero 2 (n - (km1 - fuel)) ltac:(Lia.lia)).
            generalize (NatUtil.pow_nonzero 2 (n - (km1 - (fuel - 1))) ltac:(Lia.lia)).
            generalize (Nat.pow_lt_mono_r 2%nat (n - (km1 - (fuel - 1)))%nat (n - (km1 - fuel))%nat ltac:(Lia.lia) ltac:(Lia.lia)).
            intros. assert (2 ^ n - fuel2 * 2 ^ (n - (km1 - fuel)) + (2 ^ (n - (km1 - fuel)) - fuel3) = 2 ^ n - (fuel2 - 1) * 2 ^ (n - (km1 - fuel)) - fuel3)%nat as ->; [|Lia.lia].
            rewrite Nat.add_sub_assoc; [|Lia.lia]. f_equal.
            assert (Nat.pow 2 n = Nat.pow 2 ((km1 - fuel)+ (n - (km1 - fuel))))%nat as -> by (f_equal; Lia.lia).
            rewrite Nat.pow_add_r. repeat rewrite <- Nat.mul_sub_distr_r.
            rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - (km1 - fuel))))%nat at 2.
            rewrite <- Nat.mul_add_distr_r. f_equal. Lia.lia. }
          set (px3 := (polynomial_decompose_loop (Z.of_nat (2 ^ (n - (km1 - (fuel - 1))) - fuel3))
                      (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel))))
                      (Z.of_nat (2 ^ (n - (km1 - (fuel - 1)))))
                      (InlineTable.get zetas (2 ^ (km1 - fuel) - 1 + 2 ^ (km1 - fuel) - fuel2 + 1)%nat)
                      px2)).
          set (j := ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)) + (2 ^ (n - (km1 - (fuel - 1))) - fuel3))%nat).
          set (len4 := (2 ^ (n - (km1 - (fuel - 1))))%nat).
          eapply weaken_cmd.
          { eapply (@compile_word_sizedlistarray_get _ _ _ _ _ _ _ _ _ nat); eauto.
            - repeat straightline. eexists; split; eauto.
            - instantiate (1 := (j + len4)%nat).
              cbv [cast Convertible_self id].
              repeat straightline. eexists; split; eauto.
              repeat straightline. eexists; split; eauto.
              rewrite Nat2Z.inj_add, word.ring_morph_add. reflexivity.
            - cbv [cast Convertible_self id].
              apply Nat2Z.inj_lt. clear -idx_ok. Lia.lia.
            - repeat straightline. eexists; split; [repeat straightline|straightline_call].
              + eexists; split; [rewrite map.get_put_diff by congruence; eauto|repeat straightline].
                eexists; split; [apply map.get_put_same|repeat straightline].
              + split; [apply feval_ok|].
                instantiate (1 := ListArray.get px3 (j + len4)%nat).
                unfold v, ListArray.get. fold px3 in HF3.
                do 2 rewrite <- nth_default_eq.
                eapply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto.
                * eapply Forall2_length; eauto.
                * cbv [cast Convertible_self id]. cbn in Xlen.
                  rewrite (Forall2_length HF3), Xlen.
                  clear -idx_ok; Lia.lia.
              + destruct H4 as (? & -> & -> & -> & ZZ).
                eexists; split; [reflexivity|].
                eapply weaken_cmd.
                { eapply (@compile_word_sizedlistarray_get _ _ _ _ _ _ _ _ _ nat); eauto.
                  - repeat straightline. eexists; split; [repeat (rewrite map.get_put_diff by congruence)|]; eauto.
                  - eapply expr_compile_var. cbv [cast Convertible_self id].
                    repeat (rewrite map.get_put_diff by congruence). eauto.
                  - cbv [cast Convertible_self id].
                    apply Nat2Z.inj_lt. clear -idx_ok. Lia.lia.
                  - intros. repeat straightline.
                    eexists; split; [repeat straightline|straightline_call].
                    + eexists; split; [apply map.get_put_same|repeat straightline].
                      eexists; split; [rewrite map.get_put_diff by congruence; apply map.get_put_same|].
                      repeat straightline.
                    + split; eauto. unfold v0.
                      instantiate (1 := ListArray.get px3 j).
                      unfold v, ListArray.get. fold px3 in HF3.
                      do 2 rewrite <- nth_default_eq.
                      eapply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto.
                      * eapply Forall2_length; eauto.
                      * cbv [cast Convertible_self id]. cbn in Xlen.
                        rewrite (Forall2_length HF3), Xlen.
                        clear -idx_ok; Lia.lia.
                    + destruct H4 as (? & -> & -> & -> & ZZ2).
                      eexists; split; [reflexivity|].
                      eapply weaken_cmd.
                      { eapply (@compile_word_sizedlistarray_put _ _ _ _ _ _ _ _ _ _ _ nat); eauto.
                        - eapply expr_compile_var.
                          repeat rewrite map.get_put_diff by congruence. auto.
                        - cbv [cast Convertible_self id].
                          eapply expr_compile_nat_add; eapply expr_compile_var; repeat rewrite map.get_put_diff by congruence; eauto.
                        - eapply expr_compile_var; apply map.get_put_same.
                        - cbv [cast Convertible_self id].
                          clear -idx_ok. Lia.lia.
                        - repeat straightline. eexists; split; [repeat straightline|straightline_call].
                          + eexists; split; [repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
                            eexists; split; [repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
                          + split; eauto. unfold v0.
                            instantiate (1 := ListArray.get px3 j).
                            unfold v, ListArray.get. fold px3 in HF3.
                            do 2 rewrite <- nth_default_eq.
                            eapply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto.
                            * eapply Forall2_length; eauto.
                            * cbv [cast Convertible_self id]. cbn in Xlen.
                              rewrite (Forall2_length HF3), Xlen.
                              clear -idx_ok; Lia.lia.
                          + destruct H5 as (? & -> & -> & -> & ZZ3).
                            eexists; split; [reflexivity|].
                            eapply weaken_cmd.
                            { eapply (@compile_word_sizedlistarray_put _ _ _ _ _ _ _ _ _ _ _ nat); eauto.
                              - eapply expr_compile_var.
                                repeat rewrite map.get_put_diff by congruence; eauto.
                              - cbv [cast Convertible_self id].
                                eapply expr_compile_var; repeat rewrite map.get_put_diff by congruence; eauto.
                              - eapply expr_compile_var; apply map.get_put_same.
                              - cbv [cast Convertible_self id].
                                apply Nat2Z.inj_lt. clear -idx_ok. Lia.lia.
                              - repeat straightline.
                                eexists; split; repeat straightline.
                                + eexists; split; repeat straightline.
                                  repeat rewrite map.get_put_diff by congruence; eauto.
                                + instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l).
                                  simpl. repeat split.
                                  * clear -Hfnz3 Hfuel3; Lia.lia.
                                  * eexists; repeat split; eauto.
                                    2-8: unfold l6; repeat rewrite map.get_put_diff by congruence; try apply map.get_put_same; eauto.
                                    2:{ rewrite map.get_put_same, <- word.ring_morph_add. do 2 f_equal.
                                        assert (1%Z = Z.of_nat 1)%nat as -> by reflexivity.
                                        rewrite <- Nat2Z.inj_add. f_equal.
                                        clear -Hfnz Hfnz2 Hfnz3 Hfuel Hfuel2 Hfuel3 n_ge_km1; Lia.lia. }
                                    unfold polynomial_decompose_loop.
                                    match goal with
                                    | |- context [nd_ranged_for_all _ _ ?body _] => assert (nd_ranged_for_all _ _ _ _ = body px3 (Z.of_nat j)) as -> end.
                                    2:{ unfold v2, v1, nlet; simpl.
                                        unfold ListArray.put, ListArray.get.
                                        cbv [cast Convertible_Z_nat Convertible_self id].
                                        repeat rewrite <- Nat2Z.inj_add.
                                        repeat rewrite Nat2Z.id. fold j.
                                        eapply Forall2_replace_nth; eauto.
                                        eapply Forall2_replace_nth; eauto. }
                                    unfold nlet.
                                    rewrite <- fold_left_as_nd_ranged_for_all.
                                    unfold z_range. rewrite z_range'_seq by (apply Nat2Z.is_nonneg).
                                    match goal with
                                    | |- context [seq ?from _] =>
                                        assert (seq from _ = seq from (Z.to_nat (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel))) + Z.of_nat (2 ^ (n - (km1 - (fuel - 1))) - fuel3) - Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel))))) ++ [j]) as ->
                                    end.
                                    { do 2 rewrite Z.add_simpl_l.
                                      repeat rewrite Nat2Z.id.
                                      assert (2 ^ (n - (km1 - (fuel - 1))) - (fuel3 - 1) = S (2 ^ (n - (km1 - (fuel - 1))) - fuel3))%nat as ->; [|rewrite seq_S; reflexivity].
                                      clear -Hfnz Hfnz2 Hfnz3 Hfuel Hfuel2 Hfuel3 n_ge_km1.
                                      Lia.lia. }
                                    rewrite map_app, fold_left_app. cbn [List.map fold_left].
                                    rewrite <- z_range'_seq by (apply Nat2Z.is_nonneg).
                                    assert (z_range' _ _ = z_range (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)))) (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel))) + Z.of_nat (2 ^ (n - (km1 - (fuel - 1))) - fuel3))) as -> by reflexivity.
                                    rewrite fold_left_as_nd_ranged_for_all.
                                    assert (nd_ranged_for_all _ _ _ _ = px3) as -> by reflexivity.
                                    reflexivity. }
                            instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
                      instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
                instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
          simpl. intros. eexists; split; [eauto|clear -Hfnz3; Lia.lia]. }
        { (* Can conclude *)
          clear Hb. match goal with | [H: Z.b2z (?a <? ?b) = 0%Z |- _] => generalize (Zlt_cases a b); destruct (a <? b); cbv in H; [congruence|clear H]; intro H end.
          apply Nat2Z.inj_ge in Hcond2.
          assert (fuel3 = 0)%nat as ->.
          { destruct (Nat.eq_dec fuel3 0%nat); auto.
            clear -Hcond2 n0 Hfuel Hfuel2 Hfuel3 n_ge_km1 Hfnz Hfnz2.
            generalize (NatUtil.pow_nonzero 2 (n - (km1 - fuel)) ltac:(Lia.lia)).
            generalize (NatUtil.pow_nonzero 2 (n - (km1 - (fuel - 1))) ltac:(Lia.lia)).
            Lia.lia. }
          repeat straightline. eexists. split.
          { apply expr_compile_Z_add; apply expr_compile_var; eauto. }
          repeat straightline. exists (fuel2 - 1)%nat. split; [|clear -Hfnz2; Lia.lia].
          split; [clear -Hfnz2 Hfuel2; Lia.lia|].
          split; [reflexivity|].
          unfold l6. repeat rewrite map.get_put_diff by congruence.
          rewrite map.get_put_same. eexists; eexists; repeat split; eauto.
          - unfold polynomial_list_loop.
            rewrite <- fold_left_as_nd_ranged_for_all.
            unfold z_range; rewrite z_range'_seq by reflexivity.
            rewrite Nat.sub_0_r, Z.sub_0_r, Nat2Z.id.
            replace ((2 ^ (km1 - fuel) - (fuel2 - 1)))%nat with (S (2 ^ (km1 - fuel) - fuel2))%nat at 1 by (clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1; Lia.lia).
            rewrite seq_S, List.map_app, fold_left_app.
            rewrite Nat.add_0_l. cbn [List.map fold_left].
            rewrite <- z_range'_seq by reflexivity.
            assert (z_range' 0 _ = z_range 0 (Z.of_nat (2 ^ (km1 - fuel) - fuel2))) as ->.
            { unfold z_range. rewrite Z.sub_0_r, Nat2Z.id. reflexivity. }
            rewrite fold_left_as_nd_ranged_for_all.
            unfold polynomial_list_loop in Heq2; rewrite Heq2.
            unfold nlet; simpl. f_equal.
            { clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1.
              Lia.lia. }
            f_equal.
            { clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1.
              rewrite <- (Z.mul_1_l (2 ^ Z.of_nat (n - (km1 - fuel)))) at 2.
              rewrite <- Z.mul_add_distr_r. f_equal. Lia.lia. }
            f_equal.
            + rewrite Nat2Z.inj_pow; reflexivity.
            + assert (2 ^ Z.of_nat (n - (km1 - fuel)) = Z.of_nat (Nat.pow 2 _)) as -> by (rewrite Nat2Z.inj_pow; reflexivity).
              rewrite <- Nat2Z.inj_mul. reflexivity.
            + rewrite Nat2Z.inj_pow. reflexivity.
            + unfold InlineTable.get. cbv [cast Convertible_Z_nat Convertible_self id].
              f_equal. repeat rewrite Z2Nat.inj_add by (clear; Lia.lia).
              rewrite Z2Nat.inj_sub by (clear; Lia.lia).
              rewrite Z2Nat.inj_pow, Nat2Z.id by (clear; Lia.lia).
              rewrite Nat2Z.inj_sub by assumption.
              rewrite Z2Nat.inj_sub by (clear; Lia.lia).
              repeat rewrite Nat2Z.id. f_equal.
              clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1.
              generalize (NatUtil.pow_nonzero 2 (n - (km1 - fuel)) ltac:(Lia.lia)).
              assert (Z.to_nat 2 = 2)%nat as -> by reflexivity.
              assert (Z.to_nat 1 = 1)%nat as -> by reflexivity.
               Lia.lia.
          - rewrite Hm4. assert (1 = Z.of_nat 1%nat) as -> by reflexivity.
            rewrite <- Nat2Z.inj_add. f_equal. f_equal. f_equal.
            clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1.
            generalize (NatUtil.pow_nonzero 2 (km1 - fuel) ltac:(Lia.lia)). Lia.lia.
          - rewrite <- Nat2Z.inj_add. f_equal. f_equal. f_equal.
            clear -Hfnz2 Hfnz Hfuel Hfuel2 n_ge_km1.
            generalize (NatUtil.pow_nonzero 2 (km1 - fuel) ltac:(Lia.lia)).
            generalize (NatUtil.pow_nonzero 2 (n - (km1 - fuel)) ltac:(Lia.lia)).
            intros. rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - (km1 - fuel)))) at 2.
            rewrite <- Nat.mul_add_distr_r. f_equal. Lia.lia. } }
      { (* Out of loop, conclude *) intro Hcond.
        generalize (Zlt_cases (Z.of_nat ((2 ^ (km1 - fuel) - fuel2) * 2 ^ (n - (km1 - fuel)))) (2 ^ Z.of_nat n)).
        destruct (_ <? _); intros Hcondd; cbv in Hcond; [congruence|clear Hcond].
        assert (fuel2 = 0)%nat as ->.
        { destruct (Nat.eq_dec fuel2 0%nat); auto.
          replace (2 ^ Z.of_nat n) with (Z.of_nat (Nat.pow 2 n)) in Hcondd by (rewrite Nat2Z.inj_pow; reflexivity).
          apply Nat2Z.inj_ge in Hcondd.
          rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r in Hcondd.
          replace (km1 - fuel + _)%nat with n in Hcondd by (clear -Hfnz Hfuel n_ge_km1; Lia.lia).
          clear -Hcondd n0.
          generalize (NatUtil.pow_nonzero 2 (n - (km1 - fuel)) ltac:(Lia.lia)).
          generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)).
          Lia.lia. }
        exists (fuel - 1)%nat. split; [|clear -Hfnz; Lia.lia].
        repeat split; [clear -Hfuel; Lia.lia|].
        exists p2, px2. repeat split; auto.
        - unfold layer_decomposition_loop.
          rewrite <- fold_left_as_nd_ranged_for_all.
          assert (km1 - (fuel - 1) = S (km1 - fuel))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
          unfold z_range. rewrite Z.sub_0_r, Nat2Z.id.
          rewrite z_range'_seq, seq_S, map_app, fold_left_app by reflexivity.
          rewrite PeanoNat.Nat.add_0_l.
          rewrite <- z_range'_seq by reflexivity.
          assert (z_range' 0 _ = z_range 0 (Z.of_nat (km1 - fuel))) as ->.
          { unfold z_range. rewrite Z.sub_0_r, Nat2Z.id. reflexivity. }
          rewrite fold_left_as_nd_ranged_for_all.
          unfold layer_decomposition_loop in HF1. rewrite HF1.
          cbn [List.map fold_left]. unfold nlet.
          rewrite PeanoNat.Nat.sub_0_r in Heq2.
          rewrite Z2Nat.Z.pow_Zpow in Heq2.
          assert ((Z.shiftr (2 ^ Z.of_nat (n - (km1 - fuel))) 1) = (2 ^ Z.of_nat (n - (km1 - (fuel - 1))))) as ->.
          { rewrite Z.shiftr_div_pow2 by Lia.lia.
            rewrite <- Z.pow_sub_r; [|congruence|clear -n_ge_km1 Hfuel Hfnz; Lia.lia].
            f_equal. clear -n_ge_km1 Hfuel Hfnz; Lia.lia. }
          replace (Z.of_nat 2) with 2%Z in Heq2 by reflexivity.
          rewrite Heq2.
          f_equal; [|f_equal].
          + rewrite (Nat2Z.inj_succ (km1 - fuel)), Z.pow_succ_r by (apply Nat2Z.is_nonneg). Lia.lia.
          + f_equal. f_equal. clear -Hfuel Hfnz. Lia.lia.
        - rewrite Hm2. f_equal.
          f_equal. rewrite PeanoNat.Nat.sub_0_r.
          f_equal. assert (km1 - (fuel - 1) = S (km1 - fuel))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
          rewrite Nat.pow_succ_r'. clear. Lia.lia. } }
    (* Out of loop, conclude *)
    intros Hb. rewrite <- word.morph_ltu in Hb.
    2-3: split; try Lia.lia.
    3: rewrite Nat2Z.inj_pow.
    2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
    rewrite word.unsigned_b2w in Hb.
    generalize (Zlt_cases (2 ^ Z.of_nat (n - km1)) (Z.of_nat (2 ^ (n - (km1 - fuel))))).
    destruct (_ <? _); intros; [cbv in Hb; congruence|].
    assert (fuel = 0)%nat as ->.
    { generalize (Zpow_facts.Zpower_le_monotone 2 (Z.of_nat (n - km1)) (Z.of_nat (n - (km1 - fuel))) ltac:(Lia.lia) ltac:(Lia.lia)).
      intro. assert (n - km1 = n - (km1 - fuel))%nat; [|Lia.lia].
      apply Nat2Z.inj_iff. rewrite Nat2Z.inj_pow in H4.
      apply (Z.pow_inj_r 2); Lia.lia. }
    repeat red. split; [reflexivity|].
    split; [reflexivity|].
    rewrite PeanoNat.Nat.sub_0_r in HF1.
    rewrite HF1. eexists; split; eauto.
    Unshelve.
    all: try (apply ""); try (apply (fun _ => unit)); simpl; intros; apply tt.
  Qed.

  Lemma br2_ntt_inverse_ok:
    program_logic_goal_for br2_ntt_inverse
      (forall functions : map.rep,
          map.get functions ntt_inverse = Some br2_ntt_inverse ->
          spec_of_mul functions ->
          spec_of_sub functions -> spec_of_add functions -> spec_of_ntt_inverse functions).
  Proof.
    Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub Nat.pow cast F.F F.to_Z.
    repeat straightline.
    unfold NTT_inverse_gallina. unfold nlet.
    apply wp_while.
    set (loop_inv1 := fun (fuel1: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                        (fuel1 <= km1)%nat /\
                        tr' = tr /\
                        map.get loc' "p" = Some p_ptr /\
                        let i := (km1 - fuel1)%nat in
                        exists p' px',
                        inverse_layer_decomposition_loop (km1:=km1) zetas i \< 2 ^ Z.of_nat km1, 2 ^ Z.of_nat (n - km1), p \> = \< (2 ^ Z.of_nat fuel1), 2 ^ Z.of_nat (n - fuel1), px' \> /\
                        Forall2 (fun x y => feval y = Some x) px' p' /\
                        map.get loc' "m" = Some (word.of_Z (Z.of_nat (Nat.pow 2 fuel1))) /\
                        map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p' * R)%sep mem').
    exists nat, lt, loop_inv1; split; [apply lt_wf|]. split.
    { (* loop_inv1 holds at beginning *)
      exists km1. repeat split; [reflexivity|unfold l1, l0; repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same|].
      rewrite Nat.sub_diag. intros; subst i.
      exists x, p. repeat split; auto.
      - unfold l1, l0; repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same.
      - apply map.get_put_same. }
    intros fuel1 ? mem1 loc1 Hinv1.
    destruct Hinv1 as (Hfuel1 & -> & Hptr1 & p1 & px1 & Heq1 & HF1 & Hm1 & Hlen1 & Hp1).
    eexists; split.
    { apply expr_compile_Z_ltb_u; [apply expr_compile_var; eauto|apply expr_compile_Z_literal|..].
      all: split; [apply Nat2Z.is_nonneg|].
      all: assert (2 ^ width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by Lia.lia; reflexivity).
      all: apply Nat2Z.inj_lt, Nat.pow_lt_mono_r; Lia.lia. }
    rewrite word.unsigned_b2w.
    match goal with | |- context [Z.b2z (Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond1 end.
    split; intros Hb; destruct (_ <? _); cbv in Hb; try congruence; clear Hb; [apply Nat2Z.inj_lt in Hcond1|apply Nat2Z.inj_ge in Hcond1].
    { (* loop_inv1 preserved *)
      assert (fuel1 <> 0)%nat as Hfnz1 by (intro; subst fuel1; rewrite Nat.sub_0_r in Hcond1; clear -Hcond1; Lia.lia).
      repeat straightline. eexists; split; [eapply expr_compile_var; unfold l; rewrite map.get_put_diff by congruence; eauto|].
      repeat straightline.
      eexists; split; [eapply expr_compile_word_slu; [eapply expr_compile_var; unfold l0, l; repeat (rewrite map.get_put_diff by congruence); eauto|apply expr_compile_Z_literal]|].
      repeat straightline.
      apply wp_while.
      set (loop_inv2 := fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                        (fuel2 <= Nat.pow 2 (fuel1 - 1))%nat /\
                        tr' = tr /\
                        map.get loc' "p" = Some p_ptr /\
                        let i := ((Nat.pow 2 (fuel1 - 1)) - fuel2)%nat in
                        exists p' px',
                        inverse_polynomial_list_loop zetas (Z.of_nat i) (Z.of_nat (2 ^ (n - fuel1))) (Z.of_nat (2 ^ (n - (fuel1 - 1)))) \< Z.of_nat (2 ^ fuel1) , 0%Z, px1 \> = \< Z.of_nat ((2 ^ fuel1) - i) , Z.of_nat (i * (2 ^ (n - (fuel1 - 1)))), px' \> /\
                        Forall2 (fun x y => feval y = Some x) px' p' /\
                        map.get loc' "m" = Some (word.of_Z (Z.of_nat ((2 ^ fuel1) - i))) /\
                        map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\
                        map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                        map.get loc' "start" = Some (word.of_Z (Z.of_nat (i * (2 ^ (n - (fuel1 - 1)))))) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p' * R)%sep mem').
      exists nat, lt, loop_inv2. split; [apply lt_wf|].
      split.
      { (* loop_inv2 holds at start *)
        exists (Nat.pow 2 (fuel1 - 1)). repeat split; [reflexivity|..].
        - unfold l1, l0, l. repeat (rewrite map.get_put_diff by congruence). auto.
        - rewrite Nat.sub_diag. intro; subst i.
          rewrite Nat.sub_0_r, Nat.mul_0_l.
          unfold l1, l0, l. repeat (rewrite map.get_put_diff by congruence).
          exists p1, px1; repeat split; auto.
          + rewrite map.get_put_same.
            rewrite <- word.morph_shiftl by Lia.lia.
            f_equal. f_equal. rewrite Z.shiftl_mul_pow2 by Lia.lia.
            assert (2 ^ 1 = Z.of_nat (2 ^ 1)) as -> by reflexivity.
            rewrite <- Nat2Z.inj_mul, <- Nat.pow_add_r. f_equal.
            f_equal. clear -Hfuel1 Hfnz1 n_ge_km1. Lia.lia.
          + repeat (rewrite map.get_put_diff by congruence).
            apply map.get_put_same.
          + repeat (rewrite map.get_put_diff by congruence).
            apply map.get_put_same. }
      intros fuel2 ? mem2 loc2 Hinv2.
      destruct Hinv2 as (Hfuel2 & -> & Hptr2 & p2 & px2 & Heq2 & HF2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & Hp2).
      eexists; split.
      { apply expr_compile_Z_ltb_u; [apply expr_compile_var; eauto|apply expr_compile_Z_literal|..].
        all: split; [apply Nat2Z.is_nonneg|].
        all: assert (Z.pow 2 width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by Lia.lia; reflexivity).
        all: apply Nat2Z.inj_lt.
        rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
        assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfuel1 Hfnz1 n_ge_km1; Lia.lia).
        apply (Nat.le_lt_trans _ (Nat.pow 2 n)); [Lia.lia|].
        all: apply Nat.pow_lt_mono_r; Lia.lia. }
      rewrite word.unsigned_b2w.
      match goal with | |- context [Z.b2z (Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond2 end.
      split; intros Hb; destruct (_ <? _); cbv in Hb; try congruence; clear Hb; [apply Nat2Z.inj_lt in Hcond2|apply Nat2Z.inj_ge in Hcond2].
      { (* loop_inv2 is preserved *)
        assert (fuel2 <> 0)%nat as Hfnz2.
        { intro; subst fuel2. rewrite Nat.sub_0_r in Hcond2.
          rewrite <- Nat.pow_add_r in Hcond2.
          replace (fuel1 - 1 + _)%nat with n in Hcond2 by Lia.lia. Lia.lia. }
        repeat straightline. eexists; split.
        { eapply expr_compile_nat_sub.
          - eapply expr_compile_var; eauto.
          - instantiate (1:=1%nat). apply expr_compile_Z_literal.
          - assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as ->.
            rewrite <- Nat.pow_succ_r'. f_equal. Lia.lia.
            generalize (NatUtil.pow_nonzero 2 (fuel1 - 1)%nat ltac:(Lia.lia)). Lia.lia. }
        straightline.
        eapply weaken_cmd.
        { eapply (compile_inlinetable_get_any_as_word (K:=nat)).
          1,3: cbv [cast Convertible_self id].
          2: eapply expr_compile_var; apply map.get_put_same.
          - rewrite zetas_length_ok. apply (Nat.lt_le_trans _ (Nat.pow 2 fuel1)); [|apply Nat.pow_le_mono_r; try Lia.lia].
            generalize (NatUtil.pow_nonzero 2 fuel1 ltac:(Lia.lia)); Lia.lia.
          - rewrite length_to_byte_table, map_length, zetas_length_ok.
            rewrite Nat2Z.inj_mul, Z2Nat.id by Lia.lia.
            assert (width / 8 = 4 \/ width / 8 = 8) as Hw.
            { clear -BW. destruct width_cases as [-> | ->]; [left|right]; reflexivity. }
            rewrite Nat2Z.inj_pow.
            transitivity (2 ^ 3 * 2 ^ Z.of_nat km1).
            + apply Z.mul_le_mono_nonneg_r.
              * apply Z.lt_le_incl, ZLib.Z.pow2_pos, Nat2Z.is_nonneg.
              * clear -Hw. destruct Hw as [-> | ->]; Lia.lia.
            + rewrite <- Z.pow_add_r by Lia.lia.
              apply Z.pow_le_mono_r; Lia.lia.
          - repeat straightline. unfold l.
            eexists; split; [apply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); eauto|].
            repeat straightline.
            apply wp_while.
            set (loop_inv3 := fun (fuel3: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                        (fuel3 <= Nat.pow 2 (n - fuel1))%nat /\
                        tr' = tr /\
                        map.get loc' "p" = Some p_ptr /\
                        let i := ((Nat.pow 2 (n - fuel1)) - fuel3)%nat in
                        let px3 := inverse_polynomial_decompose_loop (Z.of_nat i) (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) (Z.of_nat (2 ^ (n - fuel1))) v px2 in
                        exists p',
                        Forall2 (fun x y => feval y = Some x) px3 p' /\
                        map.get loc' "m" = Some (word.of_Z (Z.of_nat (2 ^ fuel1 - (2 ^ (fuel1 - 1) - fuel2) - 1))) /\
                        map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\
                        map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                        map.get loc' "start" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))))) /\
                        map.get loc' "j" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + i))) /\
                        map.get loc' "z" = Some (cast v) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p' * R)%sep mem').
            exists nat, lt, loop_inv3. split; [apply lt_wf|].
            split.
            { (* loop_inv3 holds at beginning *)
              exists (Nat.pow 2 (n - fuel1)). repeat split; [reflexivity|..].
              - unfold l. repeat (rewrite map.get_put_diff by congruence); auto.
              - exists p2. repeat split; auto.
                + rewrite Nat.sub_diag. assert (inverse_polynomial_decompose_loop _ _ _ _ _ = px2) as ->; [|assumption].
                  unfold inverse_polynomial_decompose_loop.
                  rewrite Z.add_0_r, <- fold_left_as_nd_ranged_for_all.
                  unfold z_range; rewrite z_range'_seq by (apply Nat2Z.is_nonneg).
                  rewrite Z.sub_diag. simpl. cbn [List.map].
                  rewrite ListUtil.List.fold_left_nil. reflexivity.
                + unfold l. repeat (rewrite map.get_put_diff by congruence).
                  apply map.get_put_same.
                + unfold l. repeat (rewrite map.get_put_diff by congruence); auto.
                + unfold l. repeat (rewrite map.get_put_diff by congruence); auto.
                + unfold l. repeat (rewrite map.get_put_diff by congruence); auto.
                + rewrite Nat.sub_diag, Nat.add_0_r. apply map.get_put_same.
                + unfold l. repeat (rewrite map.get_put_diff by congruence).
                  apply map.get_put_same. }
            intros fuel3 ? mem3 loc3 Hinv3.
            destruct Hinv3 as (Hfuel3 & -> & Hptr3 & p3 & HF3 & Hm3 & Hlen3 & Hold_len3 & Hstart3 & Hj3 & Hz3 & Hp3).
            eexists; split.
            { apply expr_compile_Z_ltb_u; [eapply expr_compile_var|eapply expr_compile_nat_add; eapply expr_compile_var|..]; eauto.
              all: split; [apply Nat2Z.is_nonneg|].
              all: assert (Z.pow 2 width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id; Lia.lia).
              all: apply Nat2Z.inj_lt.
              all: eapply (Nat.le_lt_trans _ (Nat.pow 2 n)); [|apply Nat.pow_lt_mono_r; auto].
              all: rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
              all: assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfnz1 Hfuel1 n_ge_km1; Lia.lia).
              1: transitivity (2 ^ n - fuel2 * 2 ^ (n - (fuel1 - 1)) + 2 ^ (n - fuel1))%nat; [clear; Lia.lia|].
              all: rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - fuel1))).
              all: assert (n - (fuel1 - 1) = S (n - fuel1))%nat as -> by (clear -Hfnz1 Hfuel1 n_ge_km1; Lia.lia).
              all: rewrite Nat.pow_succ_r'.
              all: assert (Nat.pow 2 n = (Nat.pow 2 fuel1) * (Nat.pow 2 (n - fuel1)))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia).
              all: rewrite Nat.mul_assoc, <- Nat.mul_sub_distr_r, <- Nat.mul_add_distr_r.
              all: apply Nat.mul_le_mono_r.
              all: generalize (Nat.pow_nonzero 2 fuel1 ltac:(Lia.lia)).
              all: clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 n_ge_km1; Lia.lia. }
            rewrite word.unsigned_b2w.
            match goal with | |- context [Z.b2z (Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond3 end.
            split; intros Hb; destruct (_ <? _); cbv in Hb; try congruence; clear Hb; [apply Nat2Z.inj_lt in Hcond3|apply Nat2Z.inj_ge in Hcond3].
            { (* loop_inv3 preservation *)
              assert (fuel3 <> 0)%nat as Hfnz3.
              { intro; subst fuel3. rewrite Nat.sub_0_r in Hcond3.
                clear -Hcond3. Lia.lia. }
              (* Memory accesses are in bounds *)
              assert ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + (2 ^ (n - fuel1) - fuel3) + 2 ^ (n - fuel1) < 2 ^ n)%nat as idx_ok.
              { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
                assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 n_ge_km1; Lia.lia).
                apply (Nat.lt_le_trans _ (2 ^ n - fuel2 * 2 ^ (n - (fuel1 - 1)) + (2 * 2 ^ (n - fuel1)))); [clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3 n_ge_km1; Lia.lia|].
                rewrite <- Nat.pow_succ_r'.
                assert (n - (fuel1 - 1) = S (n - fuel1))%nat as <- by (clear -Hfnz1 Hfuel1 n_ge_km1; Lia.lia).
                clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3 n_ge_km1.
                assert (Nat.pow 2 n = (Nat.pow 2 (fuel1 - 1)) * (Nat.pow 2 (n - (fuel1 - 1))))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia).
                rewrite <- Nat.mul_sub_distr_r.
                rewrite <- (Nat.mul_1_l (2 ^ (n - (fuel1 - 1)))) at 2.
                rewrite <- Nat.mul_add_distr_r.
                apply Nat.mul_le_mono_r. Lia.lia. }
              generalize (length_of_sizedlistarray_value_R Hp3). intro Xlen.
              cbn in Xlen. eapply weaken_cmd.
              { eapply (compile_word_sizedlistarray_get _ nat); eauto.
                - eapply expr_compile_var. auto.
                - eapply expr_compile_var.
                  cbv [cast Convertible_self id]. eauto.
                - cbv [cast Convertible_self id]. apply Nat2Z.inj_lt.
                  clear -idx_ok. Lia.lia.
                - intros. eapply weaken_cmd.
                  { eapply (compile_word_sizedlistarray_get _ nat); eauto.
                    - eapply expr_compile_var.
                      rewrite map.get_put_diff by congruence; auto.
                    - cbv [cast Convertible_self id].
                      eapply expr_compile_nat_add; eapply expr_compile_var; rewrite map.get_put_diff by congruence; eauto.
                    - cbv [cast Convertible_self id].
                      apply Nat2Z.inj_lt. exact idx_ok.
                    - intros. repeat straightline.
                      eexists; split; [repeat straightline|].
                      + eexists; split; [repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|].
                        repeat straightline. eexists; split; [apply map.get_put_same|].
                        repeat straightline.
                      + straightline_call.
                        { unfold v0, v1, ListArray.get.
                          do 2 rewrite <- nth_default_eq.
                          split; eapply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto; try (apply (Forall2_length HF3)).
                          all: cbv [cast Convertible_self id]; rewrite (Forall2_length HF3), Xlen.
                          all: clear -idx_ok; Lia.lia. }
                        destruct H4 as (? & -> & -> & -> & ZZ).
                        eexists; split; [reflexivity|].
                        eapply weaken_cmd.
                        { eapply (compile_word_sizedlistarray_put _ nat); eauto.
                          - eapply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); auto.
                          - cbv [cast Convertible_self id].
                            eapply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); eauto.
                          - cbv [cast].
                            eapply expr_compile_var. apply map.get_put_same.
                          - cbv [cast Convertible_self id].
                            apply Nat2Z.inj_lt. clear -idx_ok. Lia.lia.
                          - repeat straightline.
                            eexists; split; [repeat straightline|].
                            + eexists; split; [repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
                              eexists; split; [repeat rewrite map.get_put_diff by congruence; apply map.get_put_same|repeat straightline].
                            + straightline_call.
                              { unfold v0, v1, ListArray.get.
                                do 2 rewrite <- nth_default_eq.
                                split; eapply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto; try (apply (Forall2_length HF3)).
                                all: cbv [cast Convertible_self id]; rewrite (Forall2_length HF3), Xlen.
                                all: clear -idx_ok; Lia.lia. }
                              repeat straightline.
                              unfold l'. eexists; split; [repeat straightline|].
                              * eexists; split; [repeat rewrite map.get_put_diff by congruence; eauto|repeat straightline].
                                eexists; split; [apply map.get_put_same|repeat straightline].
                              * straightline_call; [split; eauto; eapply feval_ok|].
                                destruct H5 as (? & -> & -> & -> & ZZ2).
                                eexists; split; [repeat straightline; reflexivity|].
                                eapply weaken_cmd.
                                { eapply (compile_word_sizedlistarray_put _ nat); eauto.
                                  - eapply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); auto.
                                  - cbv [cast Convertible_self id].
                                    eapply expr_compile_nat_add; eapply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); eauto.
                                  - cbv [cast]. eapply expr_compile_var.
                                    apply map.get_put_same.
                                  - cbv [cast Convertible_self id].
                                    apply Nat2Z.inj_lt.
                                    clear -idx_ok; Lia.lia.
                                  - intros. repeat straightline.
                                    eexists; split.
                                    + eapply expr_compile_nat_add.
                                      * eapply expr_compile_var.
                                        repeat (rewrite map.get_put_diff by congruence).
                                        eauto.
                                      * instantiate (1:=1%nat).
                                        apply expr_compile_Z_literal.
                                    + repeat straightline.
                                      instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l).
                                      simpl. unfold l. repeat split.
                                      * clear -Hfuel3; Lia.lia.
                                      * repeat (rewrite map.get_put_diff by congruence); auto.
                                      * repeat (rewrite map.get_put_diff by congruence); auto.
                                        eexists; repeat split; eauto.
                                        2:{ rewrite map.get_put_same. f_equal. f_equal. f_equal.
                                            Lia.lia. }
                                        2:{ repeat rewrite map.get_put_diff by congruence. eauto. }
                                        unfold v3, v2, inverse_polynomial_decompose_loop.
                                        rewrite <- fold_left_as_nd_ranged_for_all.
                                        assert (z_range _ _ = z_range (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))) + Z.of_nat (2 ^ (n - fuel1) - fuel3)) ++ [(Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))) + Z.of_nat (2 ^ (n - fuel1) - fuel3))]) as ->.
                                        { unfold z_range. do 2 (rewrite z_range'_seq; [|apply Nat2Z.is_nonneg]).
                                          rewrite Nat2Z.id.
                                          repeat rewrite <- Nat2Z.inj_add, <- Nat2Z.inj_sub by Lia.lia.
                                          repeat rewrite Nat2Z.id.
                                          assert ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + (2 ^ (n - fuel1) - (fuel3 - 1)) - (2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) = S ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + (2 ^ (n - fuel1) - fuel3) - (2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))))%nat as -> by Lia.lia.
                                          rewrite seq_S, map_app.
                                          f_equal. cbn [List.map]. f_equal.
                                          Lia.lia. }
                                        rewrite fold_left_app, fold_left_as_nd_ranged_for_all.
                                        assert (nd_ranged_for_all _ _ _ _ = inverse_polynomial_decompose_loop (Z.of_nat (2 ^ (n - fuel1) - fuel3)) (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) (Z.of_nat (2 ^ (n - fuel1))) v px2) as -> by reflexivity.
                                        rewrite <- Nat2Z.inj_add.
                                        cbn [fold_left]. unfold nlet, v3, v2, v1, v0, ListArray.put, ListArray.get.
                                        cbv [cast Convertible_Z_nat Convertible_self id].
                                        repeat rewrite <- Nat2Z.inj_add.
                                        repeat rewrite Nat2Z.id. repeat rewrite <- nth_default_eq.
                                        apply Forall2_replace_nth; [|rewrite ZZ2; reflexivity].
                                        apply Forall2_replace_nth; [|rewrite ZZ; reflexivity]. auto. }
                                simpl. instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
                        simpl. instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
                  simpl. instantiate (2 := fun _ t m l => loop_inv3 (fuel3 - 1)%nat t m l). auto. }
              simpl. intros. exists (fuel3 - 1)%nat; split; [assumption|Lia.lia]. }
            { assert (fuel3 = 0)%nat as ->.
              { clear -Hcond3. destruct (Nat.eq_dec fuel3 0); auto.
                generalize (NatUtil.pow_nonzero 2 (n - fuel1) ltac:(Lia.lia)); Lia.lia. }
              repeat straightline.
              eexists; split.
              - eapply expr_compile_nat_add; apply expr_compile_var; eauto.
              - repeat straightline.
                instantiate (2 := fun _ t m l => loop_inv2 (fuel2 - 1)%nat t m l).
                simpl. repeat split.
                + clear -Hfuel2. Lia.lia.
                + unfold l. rewrite map.get_put_diff by congruence. auto.
                + rewrite Nat.sub_0_r in *.
                  set (px3 := (inverse_polynomial_decompose_loop (Z.of_nat (2 ^ (n - fuel1))) (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) (Z.of_nat (2 ^ (n - fuel1))) v px2)).
                  eexists; exists px3; repeat split; eauto.
                  2-5: unfold l; repeat (rewrite map.get_put_diff by congruence); auto.
                  * unfold inverse_polynomial_list_loop.
                    rewrite <- fold_left_as_nd_ranged_for_all.
                    unfold z_range. rewrite z_range'_seq by reflexivity.
                    assert (seq _ _ = (seq (Z.to_nat 0) (Z.to_nat (Z.of_nat (2 ^ (fuel1 - 1) - fuel2) - 0))) ++ [(2 ^ (fuel1 - 1) - fuel2)%nat]) as ->.
                    { repeat rewrite Z.sub_0_r, Nat2Z.id.
                      assert (Nat.pow 2 (fuel1 - 1) - (fuel2 - 1) = S (Nat.pow 2 (fuel1 - 1) - fuel2))%nat as ->; [|rewrite seq_S; reflexivity].
                      clear -Hfuel1 Hfuel2 Hfnz1 Hfnz2 n_ge_km1; Lia.lia. }
                    rewrite map_app, fold_left_app.
                    rewrite <- z_range'_seq by reflexivity. fold z_range.
                    assert (z_range' _ _ = z_range 0 (Z.of_nat (2 ^ (fuel1 - 1) - fuel2))) as -> by reflexivity.
                    rewrite fold_left_as_nd_ranged_for_all.
                    unfold inverse_polynomial_list_loop in Heq2. rewrite Heq2.
                    cbn [List.map fold_left].
                    unfold nlet. f_equal; [|f_equal].
                    { assert (1 = Z.of_nat 1) as -> by reflexivity.
                      assert (Nat.pow 2 fuel1 = 2 * (Nat.pow 2 (fuel1 - 1)))%nat as ->.
                      { rewrite <- Nat.pow_succ_r'; f_equal. clear -Hfnz1; Lia.lia. }
                      rewrite <- Nat2Z.inj_sub by Lia.lia. f_equal.
                      clear -Hfuel1 Hfuel2 Hfnz1 Hfnz2 n_ge_km1.
                      Lia.lia. }
                    { rewrite <- Nat2Z.inj_add. f_equal.
                      clear -Hfuel1 Hfuel2 Hfnz1 Hfnz2 n_ge_km1.
                      generalize (NatUtil.pow_nonzero 2 (fuel1 - 1) ltac:(Lia.lia)).
                      generalize (NatUtil.pow_nonzero 2 (n - (fuel1 - 1)) ltac:(Lia.lia)).
                      intros. assert (_ - (fuel2 - 1) = Nat.pow 2 (fuel1 - 1) - fuel2 + 1)%nat as ->; Lia.lia. }
                    { unfold px3. f_equal. unfold v.
                      unfold InlineTable.get. f_equal.
                      cbv [cast Convertible_self id Convertible_Z_nat].
                      assert (1 = Z.of_nat 1) as -> by reflexivity.
                      assert (Nat.pow 2 fuel1 = 2 * (Nat.pow 2 (fuel1 - 1)))%nat as ->.
                      { rewrite <- Nat.pow_succ_r'; f_equal. clear -Hfnz1; Lia.lia. }
                      rewrite <- Nat2Z.inj_sub by Lia.lia. rewrite Nat2Z.id. reflexivity. }
                  * rewrite Hm3. f_equal. f_equal. f_equal.
                    clear -Hfuel1 Hfuel2 Hfnz1 Hfnz2 n_ge_km1.
                    Lia.lia.
                  * rewrite map.get_put_same. f_equal. f_equal. f_equal.
                    clear -Hfuel1 Hfuel2 Hfnz1 Hfnz2 n_ge_km1.
                    generalize (NatUtil.pow_nonzero 2 (fuel1 - 1) ltac:(Lia.lia)).
                    generalize (NatUtil.pow_nonzero 2 (n - (fuel1 - 1)) ltac:(Lia.lia)).
                    intros. assert (_ - (fuel2 - 1) = Nat.pow 2 (fuel1 - 1) - fuel2 + 1)%nat as ->; Lia.lia. } }
        simpl. intros. exists (fuel2 - 1)%nat; split; [assumption|Lia.lia]. }
      { assert (fuel2 = 0)%nat as ->.
        { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r in Hcond2.
          clear -Hfuel1 Hfnz1 n_ge_km1 Hcond2.
          replace (fuel1 - 1 + _)%nat with n in Hcond2 by Lia.lia.
          generalize (NatUtil.pow_nonzero 2 (n - (fuel1 - 1)) ltac:(Lia.lia)).
          generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)). Lia.lia. }
        rewrite Nat.sub_0_r in *.
        exists (fuel1 - 1)%nat. split; [|Lia.lia].
        repeat split; [Lia.lia|auto|].
        exists p2, px2; repeat split; auto.
        - assert (km1 - (fuel1 - 1) = S (km1 - fuel1))%nat as -> by Lia.lia.
          unfold inverse_layer_decomposition_loop.
          rewrite <- fold_left_as_nd_ranged_for_all.
          unfold z_range; rewrite z_range'_seq by reflexivity.
          rewrite Z.sub_0_r, Nat2Z.id, seq_S, map_app, fold_left_app, Nat.add_0_l.
          cbn [List.map fold_left].
          assert (fold_left _ _ _ = inverse_layer_decomposition_loop (km1:=km1) zetas (km1 - fuel1) \< 2 ^ Z.of_nat km1, 2 ^ Z.of_nat (n - km1), p \>) as ->.
          { unfold inverse_layer_decomposition_loop.
            rewrite <- fold_left_as_nd_ranged_for_all.
            unfold z_range. rewrite z_range'_seq by reflexivity.
            rewrite Z.sub_0_r, Nat2Z.id. reflexivity. }
          rewrite Heq1. unfold nlet.
          assert (inverse_polynomial_list_loop zetas _ _ _ _ = inverse_polynomial_list_loop zetas (Z.of_nat (2 ^ (fuel1 - 1))) (Z.of_nat (2 ^ (n - fuel1))) (Z.of_nat (2 ^ (n - (fuel1 - 1)))) \< Z.of_nat (2 ^ fuel1), 0, px1 \>) as ->.
          2:{ rewrite Heq2. f_equal; [|f_equal].
              - assert ((Nat.pow 2 fuel1) - (Nat.pow 2 (fuel1 - 1)) = Nat.pow 2 (fuel1 - 1))%nat as ->; [|rewrite Nat2Z.inj_pow; reflexivity].
                assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as ->; [|Lia.lia].
                rewrite <- Nat.pow_succ_r'. f_equal; Lia.lia.
              - rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by Lia.lia.
                f_equal. Lia.lia. }
          f_equal.
          + rewrite Nat2Z.inj_pow. f_equal.
            Lia.lia.
          + rewrite Nat2Z.inj_pow. reflexivity.
          + rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by Lia.lia.
            rewrite Nat2Z.inj_pow. f_equal. Lia.lia.
          + rewrite Nat2Z.inj_pow. reflexivity.
        - rewrite Hm2. do 3 f_equal.
          generalize (Nat.pow_nonzero 2 (fuel1 - 1) ltac:(Lia.lia)); intros.
          assert (Nat.pow 2 fuel1 = 2 * (Nat.pow 2 (fuel1 - 1)))%nat as ->; [|Lia.lia].
          assert (Nat.pow 2 fuel1 = Nat.pow 2 (S (fuel1 - 1)))%nat as -> by (f_equal; Lia.lia).
          apply Nat.pow_succ_r'. } }
    { assert (fuel1 = 0)%nat as ->.
      { assert (n - fuel1 = n)%nat; [|Lia.lia].
        apply (Nat.pow_inj_r 2); [Lia.lia|].
        generalize (Nat.pow_le_mono_r 2 (n - fuel1) n ltac:(congruence) ltac:(clear; Lia.lia)).
        clear -Hcond1; Lia.lia. }
      repeat rewrite Nat.sub_0_r in *.
      rewrite Heq1. repeat straightline.
      apply wp_while.
      set (loop_inv4 := fun (fuel4: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                        (fuel4 <= Nat.pow 2 n)%nat /\
                        tr' = tr /\
                        map.get loc' "p" = Some p_ptr /\
                        let i := ((Nat.pow 2 n) - fuel4)%nat in
                        exists p4,
                        Forall2 (fun x y => feval y = Some x) (div_loop c (Z.of_nat i) px1) p4 /\
                        map.get loc' "j" = Some (word.of_Z (Z.of_nat i)) /\
                        (sizedlistarray_value access_size.word (Nat.pow 2 n) p_ptr p4 * R)%sep mem').
      exists nat, lt, loop_inv4; split; [apply lt_wf|].
      split.
      { exists (Nat.pow 2 n). unfold loop_inv4. rewrite Nat.sub_diag.
        repeat split; [Lia.lia|..].
        - unfold l; rewrite map.get_put_diff by congruence; auto.
        - exists p1; repeat split; auto.
          apply map.get_put_same. }
      intros fuel4 ? mem4 loc4 Hinv4.
      destruct Hinv4 as (Hfuel4 & -> & Hptr4 & p4 & HF4 & Hj & Hp4).
      eexists; split.
      { apply expr_compile_Z_ltb_u; [apply expr_compile_var; eauto|apply expr_compile_Z_literal|..].
        all: split; [apply Nat2Z.is_nonneg|].
        all: assert (2 ^ width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by Lia.lia; reflexivity).
        all: apply Nat2Z.inj_lt.
        1: apply (Nat.le_lt_trans _ (Nat.pow 2 n)); [clear; Lia.lia|].
        all: apply Nat.pow_lt_mono_r; Lia.lia. }
      rewrite word.unsigned_b2w.
      match goal with | |- context [Z.b2z (Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond4 end.
      split; intros Hb; destruct (_ <? _); cbv in Hb; try congruence; clear Hb; [apply Nat2Z.inj_lt in Hcond4|apply Nat2Z.inj_ge in Hcond4].
      { assert (fuel4 <> 0)%nat as Hfnz4 by (intro; subst fuel4; clear -Hcond4; Lia.lia).
        eapply weaken_cmd.
        { eapply (compile_word_sizedlistarray_get _ nat); eauto.
          - eapply expr_compile_var; auto.
          - cbv [cast Convertible_self id].
            eapply expr_compile_var; eauto.
          - cbv [cast Convertible_self id].
            apply Nat2Z.inj_lt. clear -Hfuel4 Hfnz4. Lia.lia.
          - repeat straightline. eexists; split.
            + repeat straightline. eexists; split; [apply map.get_put_same|].
              repeat straightline.
            + straightline_call.
              { split; [generalize (feval_ok c); cbv [cast F_to_word]; eauto|].
                unfold v, ListArray.get. rewrite <- nth_default_eq.
                apply (ListUtil.Forall2_forall_iff (fun x y => feval y = Some x)); eauto.
                - apply (Forall2_length HF4).
                - cbv [cast Convertible_self id].
                  rewrite (Forall2_length HF4).
                  generalize (length_of_sizedlistarray_value_R Hp4). intro Xlen.
                  cbn in Xlen. rewrite Xlen. Lia.lia. }
              destruct H4 as (? & -> & -> & -> & ZZ3).
              eexists; split; [repeat straightline; reflexivity|].
              eapply weaken_cmd.
              * eapply (compile_word_sizedlistarray_put _ nat); eauto.
                1-3: repeat straightline; repeat (rewrite map.get_put_diff by congruence).
                2: cbv [cast Convertible_self id].
                1-3: eexists; split; eauto.
                apply map.get_put_same.
                cbv [cast Convertible_self id]. apply Nat2Z.inj_lt; auto.
                intros. repeat straightline.
                eexists; split; [eapply expr_compile_nat_add; [eapply expr_compile_var; repeat (rewrite map.get_put_diff by congruence); eauto|instantiate(1:=1%nat); eapply expr_compile_Z_literal]|].
                repeat straightline.
                instantiate (2 := fun _ t m l => loop_inv4 (fuel4 - 1)%nat t m l).
                repeat split.
                { clear -Hfuel4 Hfnz4; Lia.lia. }
                { unfold l. repeat (rewrite map.get_put_diff by congruence); auto. }
                { eexists; repeat split; eauto.
                  - unfold div_loop. rewrite <- fold_left_as_nd_ranged_for_all.
                    unfold z_range. rewrite z_range'_seq by reflexivity.
                    rewrite Z2Nat.inj_sub, Nat2Z.id by reflexivity.
                    rewrite Nat.sub_0_r.
                    assert ((Nat.pow 2 n) - _ = S (Nat.pow 2 n - fuel4))%nat as -> by (clear -Hfnz4 Hfuel4; Lia.lia).
                    rewrite seq_S, map_app, fold_left_app, Nat.add_0_l.
                    cbn [List.map fold_left].
                    assert (List.map _ _ = z_range 0 (Z.of_nat (2 ^ n - fuel4))) as ->; [|rewrite fold_left_as_nd_ranged_for_all; unfold nlet].
                    { unfold z_range. rewrite z_range'_seq, Z.sub_0_r, Nat2Z.id by reflexivity; reflexivity. }
                    unfold v0, v. unfold ListArray.put, ListArray.get.
                    cbv [cast Convertible_Z_nat Convertible_self id].
                    assert (nd_ranged_for_all _ _ _ _ = div_loop c (Z.of_nat (2 ^ n - fuel4)) px1) as -> by reflexivity.
                    rewrite Nat2Z.id. apply Forall2_replace_nth; eauto.
                    rewrite ZZ3. rewrite <- nth_default_eq. reflexivity.
                  - unfold l. rewrite map.get_put_same. f_equal. f_equal.
                    f_equal. clear -Hfuel4 Hfnz4; Lia.lia. }
              * instantiate (2 := fun _ t m l => loop_inv4 (fuel4 - 1)%nat t m l).
                simpl. auto. }
        { simpl; intros. eexists; split; eauto.
          clear -Hfnz4; Lia.lia. } }
      { assert (fuel4 = 0)%nat as -> by (generalize (NatUtil.pow_nonzero 2 n ltac:(congruence)); clear -Hcond4; Lia.lia).
        rewrite Nat.sub_0_r in *.
        repeat straightline. eexists; split; eauto.
        assert (2 ^ Z.of_nat n = Z.of_nat (Nat.pow 2 n)) as ->; [|assumption].
        rewrite Nat2Z.inj_pow; reflexivity. } }
      Unshelve.
      all: try (apply (fun _ => unit)).
      all: try (apply "").
      all: simpl; intros; apply tt.
  Qed.
End __.

Section Zetas.
  Context {q: positive} {zeta: F q}.

  (* Computes the list of ζ^0 to ζ^n, hence the length is (n + 1) *)
  Fixpoint make_zetas (n: nat): list (F q) :=
    match n with
    | O => [1%F]
    | S n => 1%F::(List.map (F.mul zeta) (make_zetas n))
    end.

  Lemma make_zetas_spec n:
    forall k, (k <= n)%nat ->
         nth_error (make_zetas n) k = Some (F.pow zeta (N.of_nat k)).
  Proof.
    induction n; intros.
    - assert (k = 0)%nat as -> by Lia.lia. simpl.
      rewrite ModularArithmeticTheorems.F.pow_0_r. reflexivity.
    - simpl. destruct k.
      + simpl. rewrite ModularArithmeticTheorems.F.pow_0_r. reflexivity.
      + simpl. rewrite nth_error_map.
        rewrite IHn by Lia.lia. simpl.
        rewrite <- ModularArithmeticTheorems.F.pow_succ_r.
        assert (N.succ (N.of_nat k) = N.pos (Pos.of_succ_nat k)) as -> by Lia.lia.
        reflexivity.
  Qed.

  Lemma make_zetas_length n:
    length (make_zetas n) = S n.
  Proof.
    induction n; [reflexivity|].
    simpl. rewrite map_length, IHn. reflexivity.
  Qed.
End Zetas.

