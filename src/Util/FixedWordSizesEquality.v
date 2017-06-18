Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Arith.
Require Import Bedrock.Word.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.

Definition wordT_beq_hetero {logsz1 logsz2} : wordT logsz1 -> wordT logsz2 -> bool
  := match logsz1 return wordT logsz1 -> wordT logsz2 -> bool with
     | 5 as logsz1' | 6 as logsz1' | 7 as logsz1'
     | _ as logsz1'
       => match logsz2 return wordT logsz1' -> wordT logsz2 -> bool with
          | 5 as logsz2' | 6 as logsz2' | 7 as logsz2'
          | _ as logsz2'
            => @Word.weqb_hetero (2^logsz1') (2^logsz2')
          end
     end.

(* transparent so the equality proof can compute away *)
Lemma pow2_inj_helper x y : 2^x = 2^y -> x = y.
Proof.
  destruct (NatUtil.nat_eq_dec x y) as [pf|pf]; [ intros; assumption | ].
  intro H; exfalso.
  let pf := pf in
  abstract (apply pf; eapply NPeano.Nat.pow_inj_r; [ | eassumption ]; omega).
Defined.
Lemma pow2_inj_helper_refl x p : pow2_inj_helper x x p = eq_refl.
Proof.
  induction x; simpl; [ reflexivity | ].
  etransitivity; [ | exact (f_equal (fun p => f_equal S p) (IHx eq_refl)) ]; clear IHx.
  unfold pow2_inj_helper in *; simpl.
  pose proof (NatUtil.nat_eq_dec_S x x).
  do 2 edestruct NatUtil.nat_eq_dec; try assumption; try (exfalso; assumption).
  match goal with
  | [ H : ?x <> ?x |- _ ] => exfalso; clear -H; exact (H eq_refl)
  end.
Defined.
Lemma pow2_inj_helper_eq_rect x y P v v'
  : (exists pf : 2^x = 2^y, eq_rect _ P v _ pf = v')
    -> (exists pf : x = y, eq_rect _ (fun e => P (2^e)) v _ pf = v').
Proof.
  intros [pf H]; exists (pow2_inj_helper x y pf); subst v'.
  destruct (NatUtil.nat_eq_dec x y) as [H|H];
    [ | exfalso; clear -pf H;
        let pf := pf in
        abstract (apply pow2_inj_helper in pf; omega) ].
  subst; rewrite pow2_inj_helper_refl; simpl.
  pose proof (NatUtil.UIP_nat_transparent _ _ pf eq_refl); subst pf.
  reflexivity.
Defined.

Definition wordT_beq_lb logsz1
  : forall x y : wordT logsz1, x = y -> wordT_beq_hetero x y = true
  := match logsz1 return forall x y : wordT logsz1, x = y -> wordT_beq_hetero x y = true with
     | 5 as logsz1' | 6 as logsz1' | 7 as logsz1'
     | _ as logsz1'
       => fun x y pf => proj2 (@Word.weqb_hetero_true_iff (2^logsz1') x (2^logsz1') y) (ex_intro _ eq_refl pf)
     end.
Definition wordT_beq_hetero_lb {logsz1 logsz2}
  : forall x y, (exists pf : logsz1 = logsz2, eq_rect _ wordT x _ pf = y) -> wordT_beq_hetero x y = true.
Proof.
  intros x y [pf H]; subst logsz2; revert x y H; simpl.
  apply wordT_beq_lb.
Defined.

Definition wordT_beq_bl logsz
  : forall x y : wordT logsz, wordT_beq_hetero x y = true -> x = y
  := match logsz return forall x y : wordT logsz, wordT_beq_hetero x y = true -> x = y with
     | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
     | _
       => fun x y pf => proj1 (Word.weqb_hetero_homo_true_iff _ x y) pf
     end.

Lemma wordT_beq_hetero_type_lb_false logsz1 logsz2 x y : logsz1 <> logsz2 -> @wordT_beq_hetero logsz1 logsz2 x y = false.
Proof.
  destruct (wordT_beq_hetero x y) eqn:H; [ | reflexivity ].
  revert H.
  repeat (try destruct logsz1 as [|logsz1];
          try destruct logsz2 as [|logsz2];
          try (intros; omega);
          try (intro H'; apply Word.weqb_hetero_true_iff in H'; destruct H' as [pf H']; pose proof (pow2_inj_helper _ _ pf); try omega)).
Qed.

Definition wordT_beq_hetero_bl {logsz1 logsz2}
  : forall x y, wordT_beq_hetero x y = true -> (exists pf : logsz1 = logsz2, eq_rect _ wordT x _ pf = y).
Proof.
  refine match logsz1, logsz2 return forall x y, wordT_beq_hetero x y = true -> (exists pf : logsz1 = logsz2, eq_rect _ wordT x _ pf = y) with
         | 0, 0 | 1, 1 | 2, 2 | 3, 3 | 4, 4 | 5, 5 | 6, 6
         | 7, 7
           => fun x y pf => ex_intro _ eq_refl (@wordT_beq_bl _ x y pf)
         | S (S (S (S (S (S (S (S a))))))), S (S (S (S (S (S (S (S b)))))))
           => match NatUtil.nat_eq_dec a b with
              | left pf
                => match pf with
                   | eq_refl => fun x y pf => ex_intro _ eq_refl (@wordT_beq_bl _ x y pf)
                   end
              | right n => fun x y pf => match _ : False with end
              end
         | _, _
           => fun x y pf => match _ : False with end
         end;
    match goal with
    | [ pf : _ = _ |- _ ]
      => abstract (rewrite wordT_beq_hetero_type_lb_false in pf by omega; clear -pf; congruence)
    end.
Defined.

Lemma ZToWord_gen_wordToZ_gen : forall {sz} v, ZToWord_gen (@wordToZ_gen sz v) = v.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros.
  rewrite N2Z.id, NToWord_wordToN; reflexivity.
Qed.

Lemma wordToZ_gen_ZToWord_gen : forall {sz} v, (0 <= v < 2^(Z.of_nat sz))%Z -> @wordToZ_gen sz (ZToWord_gen v) = v.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros ?? [H0 H1].
  rewrite wordToN_NToWord_idempotent, Z2N.id; try omega.
  rewrite Npow2_N.
  apply Z2N.inj_lt in H1; [ | omega.. ].
  rewrite Z2N.inj_pow, <- nat_N_Z, N2Z.id in H1 by omega.
  assumption.
Qed.

Lemma wordToZ_gen_ZToWord_gen_mod : forall {sz} w, (0 <= w)%Z -> wordToZ_gen (@ZToWord_gen sz w) = (w mod (2^Z.of_nat sz))%Z.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros sz w H.
  rewrite wordToN_NToWord_mod.
  rewrite N2Z.inj_mod by (destruct sz; simpl; congruence).
  rewrite Z2N.id, N2Z.inj_pow, nat_N_Z by assumption.
  reflexivity.
Qed.

Lemma wordToZ_gen_ZToWord_gen_0 : forall {sz}, wordToZ_gen (@ZToWord_gen sz 0) = 0%Z.
Proof.
  intros; rewrite wordToZ_gen_ZToWord_gen_mod by reflexivity.
  rewrite Z.mod_0_l by auto with zarith.
  reflexivity.
Qed.

Lemma wordToZ_gen_ZToWord_gen_neg : forall {sz} w, (w <= 0)%Z -> wordToZ_gen (@ZToWord_gen sz w) = 0%Z.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros sz w H.
  destruct w.
  { apply wordToZ_gen_ZToWord_gen_0. }
  { compute in H; congruence. }
  { apply wordToZ_gen_ZToWord_gen_0. }
Qed.

Lemma wordToZ_gen_ZToWord_gen_mod_full : forall {sz} w, wordToZ_gen (@ZToWord_gen sz w) = (Z.max 0 w mod (2^Z.of_nat sz))%Z.
Proof.
  intros; apply Z.max_case_strong; intro.
  { apply wordToZ_gen_ZToWord_gen_neg; omega. }
  { apply wordToZ_gen_ZToWord_gen_mod; assumption. }
Qed.

Lemma ZToWord_gen_wordToZ_gen_ZToWord_gen : forall {sz1 sz2} v,
    (sz2 <= sz1)%nat -> @ZToWord_gen sz2 (wordToZ_gen (@ZToWord_gen sz1 v)) = ZToWord_gen v.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros sz1 sz2 v H.
  rewrite N2Z.id, NToWord_wordToN_NToWord by omega.
  reflexivity.
Qed.

Lemma ZToWord_gen_wordToZ_gen_ZToWord_gen_small : forall {sz1 sz2} v,
    (wordToZ_gen (@ZToWord_gen sz2 v) < 2^(Z.of_nat sz1))%Z
    -> @ZToWord_gen sz2 (wordToZ_gen (@ZToWord_gen sz1 v)) = ZToWord_gen v.
Proof.
  unfold ZToWord_gen, wordToZ_gen.
  intros sz1 sz2 v H.
  change 2%Z with (Z.of_nat 2) in H.
  rewrite <- !nat_N_Z, <- N2Z.inj_pow, <- N2Z.inj_lt in H.
  rewrite N2Z.id, NToWord_wordToN_NToWord_small by assumption.
  reflexivity.
Qed.

Lemma wordToZ_gen_ZToWord_gen_wordToZ_gen sz1 sz2 w
  : (sz1 <= sz2)%nat -> wordToZ_gen (@ZToWord_gen sz2 (@wordToZ_gen sz1 w)) = wordToZ_gen w.
Proof.
  unfold ZToWord_gen, wordToZ_gen; intro H.
  rewrite N2Z.id, wordToN_NToWord_wordToN by omega.
  reflexivity.
Qed.

Lemma eq_ZToWord_gen : forall {sz} v1 v2, (Z.max 0 v1 mod 2^Z.of_nat sz = Z.max 0 v2 mod 2^Z.of_nat sz)%Z
                                          <-> @ZToWord_gen sz v1 = @ZToWord_gen sz v2.
Proof.
  intros; split; intro H.
  { rewrite <- (ZToWord_gen_wordToZ_gen (ZToWord_gen v1)), <- (ZToWord_gen_wordToZ_gen (ZToWord_gen v2)).
    rewrite !wordToZ_gen_ZToWord_gen_mod_full.
    congruence. }
  { apply (f_equal wordToZ_gen) in H; revert H.
    rewrite !wordToZ_gen_ZToWord_gen_mod_full.
    trivial. }
Qed.

Lemma ZToWord_wordToZ : forall {sz} v, ZToWord (@wordToZ sz v) = v.
Proof.
  unfold wordT, word_case in *.
  intro sz; break_match; simpl; apply ZToWord_gen_wordToZ_gen.
Qed.

Lemma wordToZ_ZToWord : forall {sz} v, (0 <= v < 2^(Z.of_nat (2^sz)))%Z -> @wordToZ sz (ZToWord v) = v.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros; break_match; apply wordToZ_gen_ZToWord_gen;
    assumption.
Qed.

Lemma wordToZ_ZToWord_mod : forall {sz} v, (0 <= v)%Z -> wordToZ (@ZToWord sz v) = (v mod (2^Z.of_nat (2^sz)))%Z.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros; break_match; apply wordToZ_gen_ZToWord_gen_mod;
    assumption.
Qed.

Local Ltac handle_le :=
  repeat match goal with
         | [ |- (S ?a <= 2^?b)%nat ]
           => change (2^(Nat.log2 (S a)) <= 2^b)%nat
         | [ |- (2^_ <= 2^_)%nat ]
           => apply Nat.pow_le_mono_r
         | [ |- _ <> _ ] => intro; omega
         | _ => assumption
         | [ |- (_ <= S _)%nat ]
           => apply Nat.leb_le; vm_compute; reflexivity
         | _ => exfalso; omega
         end.

Lemma ZToWord_wordToZ_ZToWord : forall {sz1 sz2} v,
    (sz2 <= sz1)%nat -> @ZToWord sz2 (wordToZ (@ZToWord sz1 v)) = ZToWord v.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz1 sz2; break_match; intros; apply ZToWord_gen_wordToZ_gen_ZToWord_gen;
    handle_le.
Qed.

Lemma ZToWord_wordToZ_ZToWord_small : forall {sz1 sz2} v,
    (wordToZ (@ZToWord sz2 v) < 2^Z.of_nat (2^sz1))%Z -> @ZToWord sz2 (wordToZ (@ZToWord sz1 v)) = ZToWord v.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz1 sz2; break_match; intros; apply ZToWord_gen_wordToZ_gen_ZToWord_gen_small;
    handle_le; try omega.
Qed.

Lemma wordToZ_ZToWord_wordToZ : forall sz1 sz2 w, (sz1 <= sz2)%nat -> wordToZ (@ZToWord sz2 (@wordToZ sz1 w)) = wordToZ w.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz1 sz2; break_match; intros; apply wordToZ_gen_ZToWord_gen_wordToZ_gen;
    handle_le.
Qed.

Lemma wordToZ_ZToWord_0 : forall {sz}, wordToZ (@ZToWord sz 0) = 0%Z.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz; break_match; intros; apply wordToZ_gen_ZToWord_gen_0.
Qed.

Lemma wordToZ_ZToWord_neg : forall {sz} w, (w <= 0)%Z -> wordToZ (@ZToWord sz w) = 0%Z.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz w; break_match; apply wordToZ_gen_ZToWord_gen_neg.
Qed.

Lemma wordToZ_ZToWord_mod_full : forall {sz} w, wordToZ (@ZToWord sz w) = ((Z.max 0 w) mod (2^Z.of_nat (2^sz)))%Z.
Proof.
  unfold wordToZ, ZToWord, word_case_dep.
  intros sz w; break_match; apply wordToZ_gen_ZToWord_gen_mod_full.
Qed.

Lemma eq_ZToWord : forall {sz} v1 v2, (Z.max 0 v1 mod 2^Z.of_nat (2^sz) = Z.max 0 v2 mod 2^Z.of_nat (2^sz))%Z
                                      <-> @ZToWord sz v1 = @ZToWord sz v2.
Proof.
  unfold ZToWord, word_case_dep.
  intros sz v1 v2; break_innermost_match; apply eq_ZToWord_gen.
Qed.

Local Ltac wordToZ_word_case_dep_t :=
  let H := fresh in
  intro H;
  intros; unfold wordToZ, word_case_dep, wordT, word_case, word32, word64, word128, word32ToZ, word64ToZ, word128ToZ in *;
  break_innermost_match;
  change 128%nat with (2^7)%nat in *;
  change 64%nat with (2^6)%nat in *;
  change 32%nat with (2^5)%nat in *;
  apply H.

Lemma wordToZ_word_case_dep_unop (wop : forall sz, word sz -> word sz)
      (P : nat -> Z -> Z -> Type)
  : (forall logsz (x : word (2^logsz)), P logsz (wordToZ_gen x) (wordToZ_gen (wop (2^logsz) x)))
    -> forall logsz (x : wordT logsz), P logsz (wordToZ x) (wordToZ (word_case_dep (T:=fun _ W => W -> W) logsz (wop 32) (wop 64) (wop 128) (fun _ => wop _) x)).
Proof. wordToZ_word_case_dep_t. Qed.

Lemma wordToZ_word_case_dep_11op {T} (wop : forall sz, T -> word sz -> word sz)
      (P : nat -> Z -> Z -> Type)
      {v}
  : (forall logsz (x : word (2^logsz)), P logsz (wordToZ_gen x) (wordToZ_gen (wop (2^logsz) v x)))
    -> forall logsz (x : wordT logsz), P logsz (wordToZ x) (wordToZ (word_case_dep (T:=fun _ W => T -> W -> W) logsz (wop 32) (wop 64) (wop 128) (fun _ => wop _) v x)).
Proof. wordToZ_word_case_dep_t. Qed.

Lemma wordToZ_word_case_dep_binop (wop : forall sz, word sz -> word sz -> word sz)
      (P : nat -> Z -> Z -> Z -> Type)
  : (forall logsz (x y : word (2^logsz)), P logsz (wordToZ_gen x) (wordToZ_gen y) (wordToZ_gen (wop (2^logsz) x y)))
    -> forall logsz (x y : wordT logsz), P logsz (wordToZ x) (wordToZ y) (wordToZ (word_case_dep (T:=fun _ W => W -> W -> W) logsz (wop 32) (wop 64) (wop 128) (fun _ => wop _) x y)).
Proof. wordToZ_word_case_dep_t. Qed.

Lemma wordToZ_word_case_dep_quadop (wop : forall sz, word sz -> word sz -> word sz -> word sz -> word sz)
      (P : nat -> Z -> Z -> Z -> Z -> Z -> Type)
  : (forall logsz (x y z w : word (2^logsz)), P logsz (wordToZ_gen x) (wordToZ_gen y) (wordToZ_gen z) (wordToZ_gen w) (wordToZ_gen (wop (2^logsz) x y z w)))
    -> forall logsz (x y z w : wordT logsz), P logsz (wordToZ x) (wordToZ y) (wordToZ z) (wordToZ w) (wordToZ (word_case_dep (T:=fun _ W => W -> W -> W -> W -> W) logsz (wop 32) (wop 64) (wop 128) (fun _ => wop _) x y z w)).
Proof. wordToZ_word_case_dep_t. Qed.

(** This converts goals involving (currently only binary) [wordT]
    operations to the corresponding goals involving [word]
    operations. *)
Ltac syntactic_fixed_size_op_to_word :=
  lazymatch goal with
  | [ |- context[wordToZ (word_case_dep (T:=?T) ?logsz (?wop 32) (?wop 64) (?wop 128) ?f ?x)] ]
    => move x at top;
       revert dependent logsz; intros logsz x;
       pattern (wordToZ x), (wordToZ (word_case_dep (T:=T) logsz (wop 32) (wop 64) (wop 128) f x));
       let P := lazymatch goal with |- ?P _ _ => P end in
       let P := lazymatch (eval pattern logsz in P) with ?P _ => P end in
       revert logsz x;
       refine (@wordToZ_word_case_dep_unop wop P _);
       intros logsz x; intros
  | [ |- context[wordToZ (word_case_dep (T:=?T) ?logsz (?wop 32) (?wop 64) (?wop 128) ?f ?x ?y)] ]
    => lazymatch type of x with
       | context[logsz]
         => move y at top; move x at top;
            revert dependent logsz; intros logsz x y;
            pattern (wordToZ x), (wordToZ y), (wordToZ (word_case_dep (T:=T) logsz (wop 32) (wop 64) (wop 128) f x y));
            let P := lazymatch goal with |- ?P _ _ _ => P end in
            let P := lazymatch (eval pattern logsz in P) with ?P _ => P end in
            revert logsz x y;
            refine (@wordToZ_word_case_dep_binop wop P _);
            intros logsz x y; intros
       | _
         => move y at top;
            revert dependent logsz; intros logsz y;
            pattern (wordToZ y), (wordToZ (word_case_dep (T:=T) logsz (wop 32) (wop 64) (wop 128) f x y));
            let P := lazymatch goal with |- ?P _ _ => P end in
            let P := lazymatch (eval pattern logsz in P) with ?P _ => P end in
            revert logsz y;
            refine (@wordToZ_word_case_dep_11op _ wop P x _);
            intros logsz y; intros
       end
  | [ |- context[wordToZ (word_case_dep (T:=?T) ?logsz (?wop 32) (?wop 64) (?wop 128) ?f ?x ?y ?z ?w)] ]
    => move w at top; move z at top; move y at top; move x at top;
       revert dependent logsz; intros logsz x y z w;
       pattern (wordToZ x), (wordToZ y), (wordToZ z), (wordToZ w), (wordToZ (word_case_dep (T:=T) logsz (wop 32) (wop 64) (wop 128) f x y z w));
       let P := lazymatch goal with |- ?P _ _ _ _ _ => P end in
       let P := lazymatch (eval pattern logsz in P) with ?P _ => P end in
       revert logsz x y z w;
       refine (@wordToZ_word_case_dep_quadop wop P _);
       intros logsz x y z w; intros
  end.
Ltac fixed_size_op_to_word :=
  repeat autounfold with fixed_size_constants in *;
  syntactic_fixed_size_op_to_word.

Lemma wordToZ_gen_range {sz} w : (0 <= @wordToZ_gen sz w < 2^Z.of_nat sz)%Z.
Proof. apply WordNZ_range; reflexivity. Qed.

Lemma wordToZ_range {logsz} w : (0 <= @wordToZ logsz w < 2^Z.of_nat (2^logsz))%Z.
Proof.
  generalize (@wordToZ_gen_range (2^logsz)); wordToZ_word_case_dep_t.
Qed.

Section log_Updates.
  Local Notation bound n lower value upper := (
       (0 <= lower)%Z
    /\ (lower <= @wordToZ n value)%Z
    /\ (@wordToZ n value <= upper)%Z
    /\ (Z.log2 upper < Z.of_nat (2^n))%Z).

  Definition valid_log_update n lowerF valueF upperF : Prop :=
    forall lower0 value0 upper0
          lower1 value1 upper1,

       bound n lower0 value0 upper0
    -> bound n lower1 value1 upper1
    -> (0 <= lowerF lower0 upper0 lower1 upper1)%Z
    -> (Z.log2 (upperF lower0 upper0 lower1 upper1) < Z.of_nat (2^n))%Z
    -> bound n (lowerF lower0 upper0 lower1 upper1)
                (valueF value0 value1)
                (upperF lower0 upper0 lower1 upper1).

  Lemma word_case_dep_valid_log_update f g wop
    : (forall n,
          WordUtil.valid_update
            n
            f
            (wop n)
            g)
      -> forall n,
          valid_log_update
            n
            f
            (word_case_dep
               (T:=fun _ W => W -> W -> W)
               n (wop 32) (wop 64) (wop 128)
               (fun k : nat => wop (2 ^ k)))
            g.
  Proof.
    intros H n; specialize (H (2^n)%nat).
    unfold valid_log_update; intros; fixed_size_op_to_word; unfold wordToZ_gen; auto.
  Qed.

  Lemma wadd_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => l0 + l1)%Z
        (@wadd n)
        (fun l0 u0 l1 u1 => u0 + u1)%Z.
  Proof. apply word_case_dep_valid_log_update, add_valid_update. Qed.

  Lemma wsub_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => l0 - u1)%Z
        (@wsub n)
        (fun l0 u0 l1 u1 => u0 - l1)%Z.
  Proof. apply word_case_dep_valid_log_update, sub_valid_update. Qed.

  Lemma wmul_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => l0 * l1)%Z
        (@wmul n)
        (fun l0 u0 l1 u1 => u0 * u1)%Z.
  Proof. apply word_case_dep_valid_log_update, mul_valid_update. Qed.

  Lemma wland_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => 0)%Z
        (@wland n)
        (fun l0 u0 l1 u1 => Z.min u0 u1)%Z.
  Proof. apply word_case_dep_valid_log_update, land_valid_update. Qed.

  Lemma wlor_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => Z.max l0 l1)%Z
        (@wlor n)
        (fun l0 u0 l1 u1 => 2^(Z.max (Z.log2_up (u0+1)) (Z.log2_up (u1+1))) - 1)%Z.
  Proof. apply word_case_dep_valid_log_update, lor_valid_update. Qed.

  Lemma wshr_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => Z.shiftr l0 u1)%Z
        (@wshr n)
        (fun l0 u0 l1 u1 => Z.shiftr u0 l1)%Z.
  Proof. apply word_case_dep_valid_log_update, shr_valid_update. Qed.

  Lemma wshl_valid_log_update: forall n,
    valid_log_update n
        (fun l0 u0 l1 u1 => Z.shiftl l0 l1)%Z
        (@wshl n)
        (fun l0 u0 l1 u1 => Z.shiftl u0 u1)%Z.
  Proof. apply word_case_dep_valid_log_update, shl_valid_update. Qed.
End log_Updates.

Lemma lt_log_helper (v : Z) (n : nat)
  : (v < 2^2^Z.of_nat n)%Z <-> (Z.log2 v < Z.of_nat (2^n))%Z.
Proof.
  rewrite Z.log2_lt_pow2_alt, Z.pow_Zpow by auto with zarith.
  reflexivity.
Qed.

Section Updates.
  Local Notation bound n lower value upper := (
       (0 <= lower)%Z
    /\ (lower <= @wordToZ n value)%Z
    /\ (@wordToZ n value <= upper)%Z
    /\ (upper < 2^2^Z.of_nat n)%Z).

  Definition valid_update n lowerF valueF upperF : Prop :=
    forall lower0 value0 upper0
           lower1 value1 upper1,
      bound n lower0 value0 upper0
      -> bound n lower1 value1 upper1
      -> (0 <= lowerF lower0 upper0 lower1 upper1)%Z
      -> (upperF lower0 upper0 lower1 upper1 < 2^2^Z.of_nat n)%Z
      -> bound n (lowerF lower0 upper0 lower1 upper1)
               (valueF value0 value1)
               (upperF lower0 upper0 lower1 upper1).

  Local Ltac t lem :=
    let H := fresh in
    pose proof lem as H;
    repeat (let x := fresh in intro x; specialize (H x));
    rewrite !lt_log_helper; assumption.

  Lemma word_case_dep_valid_update f g wop
    : (forall n,
          WordUtil.valid_update
            n
            f
            (wop n)
            g)
      -> forall n,
          valid_update
            n
            f
            (word_case_dep
               (T:=fun _ W => W -> W -> W)
               n (wop 32) (wop 64) (wop 128)
               (fun k : nat => wop (2 ^ k)))
            g.
  Proof. t (@word_case_dep_valid_log_update f g wop). Qed.

  Lemma wadd_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => l0 + l1)%Z
        (@wadd n)
        (fun l0 u0 l1 u1 => u0 + u1)%Z.
  Proof. t (@wadd_valid_log_update). Qed.

  Lemma wsub_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => l0 - u1)%Z
        (@wsub n)
        (fun l0 u0 l1 u1 => u0 - l1)%Z.
  Proof. t (@wsub_valid_log_update). Qed.

  Lemma wmul_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => l0 * l1)%Z
        (@wmul n)
        (fun l0 u0 l1 u1 => u0 * u1)%Z.
  Proof. t (@wmul_valid_log_update). Qed.

  Lemma wland_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => 0)%Z
        (@wland n)
        (fun l0 u0 l1 u1 => Z.min u0 u1)%Z.
  Proof. t (@wland_valid_log_update). Qed.

  Lemma wlor_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.max l0 l1)%Z
        (@wlor n)
        (fun l0 u0 l1 u1 => 2^(Z.max (Z.log2_up (u0+1)) (Z.log2_up (u1+1))) - 1)%Z.
  Proof. t (@wlor_valid_log_update). Qed.

  Lemma wshr_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.shiftr l0 u1)%Z
        (@wshr n)
        (fun l0 u0 l1 u1 => Z.shiftr u0 l1)%Z.
  Proof. t (@wshr_valid_log_update). Qed.

  Lemma wshl_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.shiftl l0 l1)%Z
        (@wshl n)
        (fun l0 u0 l1 u1 => Z.shiftl u0 u1)%Z.
  Proof. t (@wshl_valid_log_update). Qed.
End Updates.

Section pull_ZToWord.
  Local Ltac t0 :=
    intros;
    etransitivity; [ symmetry; apply ZToWord_wordToZ | ]; fixed_size_op_to_word; unfold wordToZ_gen, wordBin;
    apply f_equal.
  Local Ltac t1 lem :=
    let solver := solve [ apply Npow2_Zlog2; autorewrite with push_Zof_N; assumption
                        | apply N2Z.inj_ge; unfold wordToZ_gen in *; omega
                        | apply N2Z.inj_lt; rewrite Npow2_N; autorewrite with push_Zof_N push_Zof_nat; assumption ] in
    first [ rewrite <- lem by solver | rewrite -> lem by solver ].
  Local Ltac t2 :=
    autorewrite with push_Zof_N; unfold wordToZ_gen in *;
    try first [ reflexivity
              | apply Z.max_case_strong; omega ].

  Local Ltac t lem :=
    t0; t1 lem; solve [ t2 ].

  Local Notation pull_ZToWordT_2op wop zop
    := (forall {logsz} (x y : wordT logsz),
           (zop (wordToZ x) (wordToZ y) < 2^2^Z.of_nat logsz)%Z
           -> wop logsz x y = ZToWord (zop (wordToZ x) (wordToZ y)))
         (only parsing).
  Local Notation pull_ZToWordT_2op' wop zop
    := (forall {logsz} (x y : wordT logsz),
           (0 <= zop (wordToZ x) (wordToZ y))%Z
           -> wop logsz x y = ZToWord (zop (wordToZ x) (wordToZ y)))
         (only parsing).

  Lemma wadd_def_ZToWord : pull_ZToWordT_2op (@wadd) (@Z.add).
  Proof. t (@wordize_plus). Qed.
  Lemma wsub_def_ZToWord : pull_ZToWordT_2op' (@wsub) (@Z.sub).
  Proof. t (@wordize_minus). Qed.
  Lemma wmul_def_ZToWord : pull_ZToWordT_2op (@wmul) (@Z.mul).
  Proof. t (@wordize_mult). Qed.
  Lemma wland_def_ZToWord : pull_ZToWordT_2op (@wland) (@Z.land).
  Proof. t (@wordize_and). Qed.
  Lemma wlor_def_ZToWord : pull_ZToWordT_2op (@wlor) (@Z.lor).
  Proof. t (@wordize_or). Qed.
  Lemma wshl_def_ZToWord : pull_ZToWordT_2op (@wshl) (@Z.shiftl).
  Proof. t (@wordToN_NToWord_idempotent). Qed.
  Lemma wshr_def_ZToWord : pull_ZToWordT_2op (@wshr) (@Z.shiftr).
  Proof. t (@wordToN_NToWord_idempotent). Qed.
End pull_ZToWord.
Section pull_ZToWord_log.
  Local Ltac t lem :=
    let H := fresh in
    pose proof lem as H;
    repeat (let x := fresh in intro x; specialize (H x));
    rewrite <- !lt_log_helper; assumption.

  Local Notation pull_ZToWordT_log_2op wop zop
    := (forall {logsz} (x y : wordT logsz),
           (Z.log2 (zop (wordToZ x) (wordToZ y)) < Z.of_nat (2^logsz))%Z
           -> wop logsz x y = ZToWord (zop (wordToZ x) (wordToZ y)))
         (only parsing).
  Lemma wadd_def_ZToWord_log : pull_ZToWordT_log_2op (@wadd) (@Z.add).
  Proof. t (@wadd_def_ZToWord). Qed.
  Lemma wmul_def_ZToWord_log : pull_ZToWordT_log_2op (@wmul) (@Z.mul).
  Proof. t (@wmul_def_ZToWord). Qed.
  Lemma wland_def_ZToWord_log : pull_ZToWordT_log_2op (@wland) (@Z.land).
  Proof. t (@wland_def_ZToWord). Qed.
  Lemma wlor_def_ZToWord_log : pull_ZToWordT_log_2op (@wlor) (@Z.lor).
  Proof. t (@wlor_def_ZToWord). Qed.
  Lemma wshl_def_ZToWord_log : pull_ZToWordT_log_2op (@wshl) (@Z.shiftl).
  Proof. t (@wshl_def_ZToWord). Qed.
  Lemma wshr_def_ZToWord_log : pull_ZToWordT_log_2op (@wshr) (@Z.shiftr).
  Proof. t (@wshr_def_ZToWord). Qed.
End pull_ZToWord_log.
Hint Rewrite wadd_def_ZToWord wsub_def_ZToWord wmul_def_ZToWord wland_def_ZToWord wlor_def_ZToWord wshl_def_ZToWord wshr_def_ZToWord : pull_ZToWord.
Hint Rewrite <- wadd_def_ZToWord wsub_def_ZToWord wmul_def_ZToWord wland_def_ZToWord wlor_def_ZToWord wshl_def_ZToWord wshr_def_ZToWord : push_ZToWord.
Hint Rewrite wadd_def_ZToWord_log wsub_def_ZToWord wmul_def_ZToWord_log wland_def_ZToWord_log wlor_def_ZToWord_log wshl_def_ZToWord_log wshr_def_ZToWord_log : pull_ZToWord_log.
Hint Rewrite <- wadd_def_ZToWord_log wsub_def_ZToWord wmul_def_ZToWord_log wland_def_ZToWord_log wlor_def_ZToWord_log wshl_def_ZToWord_log wshr_def_ZToWord_log : push_ZToWord_log.
