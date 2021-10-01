Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.COperationSpecifications. (* for list_Z_bounded_by *)
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Translation.Proofs.LoadStoreList.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Local Open Scope Z_scope.

Import ListNotations.
Import AbstractInterpretation.Compilers.
Import Types.Notations.

Section __.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Existing Instances rep.Z rep.listZ_mem.

  Let all_access_sizes :=
    [access_size.one; access_size.two; access_size.four; access_size.word].

  Fixpoint loosest_range (ranges : list (option zrange)) : option zrange :=
    match ranges with
    | [] => None
    | x :: ranges' =>
      let y := loosest_range ranges' in
      match x, y with
      | Some rx, Some ry =>
        if is_tighter_than_bool rx ry
        then Some ry else Some rx
      | Some rx, None => Some rx
      | _, _ => None
      end
    end.

  Definition access_size_to_zrange (size : access_size) : zrange :=
    let bytes := Z.of_nat (Memory.bytes_per
                             (width:=width) size) in
    {| lower:=0; upper:= (2^(bytes*8) - 1) |}.

  Definition zrange_to_access_size'
             (r : zrange)
             (access_sizes : list access_size) : option access_size :=
    fold_right
      (fun nsize current =>
         match current with
         | Some csize =>
           let nr := access_size_to_zrange nsize in
           let cr := access_size_to_zrange csize in
           if ((is_tighter_than_bool nr cr)
                 && (is_tighter_than_bool r nr))%bool
           then Some nsize
           else Some csize
         | None =>
           let nr := access_size_to_zrange nsize in
           if is_tighter_than_bool r nr
           then Some nsize else None
         end
      ) None access_sizes.
  Definition zrange_to_access_size r :=
    zrange_to_access_size' r all_access_sizes.

  Definition make_access_size (ranges : list (option zrange))
    : option access_size :=
    match loosest_range ranges with
    | Some r =>
      let wordr := access_size_to_zrange access_size.word in
      if is_tighter_than_bool r wordr
      then
        match zrange_to_access_size r with
        | Some s =>
          let sr := access_size_to_zrange s in
          if zrange_beq sr wordr
          then Some access_size.word (* prioritize word over equivalent sizes (e.g. over access_size.four on 32-bit) *)
          else Some s
        | None => None
        end
      else None
    | None => None
    end.

  Fixpoint make_base_access_sizes {t} :
    ZRange.type.base.option.interp t ->
    option (base_access_sizes t) :=
    match t as t0 return
          ZRange.type.base.option.interp t0 ->
          option (base_access_sizes t0) with
    | base.type.prod a b =>
      fun r =>
        match make_base_access_sizes (fst r),
              make_base_access_sizes (snd r) with
        | Some s1, Some s2 => Some (s1, s2)
        | _, _ => None
        end
    | base_listZ =>
      fun r =>
        match r with
        | Some ranges => make_access_size ranges
        | None => None
        end
    | _ => fun _ => Some tt
    end.

  Fixpoint make_access_sizes_args {t} :
    type.for_each_lhs_of_arrow
      ZRange.type.option.interp t ->
    option (type.for_each_lhs_of_arrow
              access_sizes t) :=
    match t with
    | type.base _ => fun _ => Some tt
    | type.arrow (type.base s) d =>
      fun r =>
        match make_base_access_sizes (fst r),
              make_access_sizes_args (snd r) with
        | Some ssizes, Some dsizes => Some (ssizes, dsizes)
        | _, _ => None
        end
    | _ => fun _ => None
    end.

  Fixpoint access_sizes_repeat_base (s : access_size) t
    : base_access_sizes t :=
    match t as t0 return base_access_sizes t0 with
    | base.type.prod a b =>
      (access_sizes_repeat_base s a, access_sizes_repeat_base s b)
    | base_listZ => s
    | _ => tt
    end.
  Fixpoint access_sizes_repeat_args (sz : access_size) t
    : type.for_each_lhs_of_arrow access_sizes t :=
    match t as t0 return type.for_each_lhs_of_arrow access_sizes t0 with
    | type.base b => tt
    | type.arrow (type.base s) d =>
      (access_sizes_repeat_base sz s, access_sizes_repeat_args sz d)
    | type.arrow s d => (tt, access_sizes_repeat_args sz d)
    end.

  Section proofs.
    Context {ok : Types.ok}.

    Lemma access_size_to_zrange_lower s :
      lower (access_size_to_zrange s) = 0.
    Proof. reflexivity. Qed.

    Lemma is_tighter_than_bool_reverse_same_lower r1 r2 :
      lower r1 = lower r2 ->
      (r1 <=? r2)%zrange = false ->
      (r2 <=? r1)%zrange = true.
    Proof.
      cbv [is_tighter_than_bool].
      rewrite Bool.andb_false_iff, Bool.andb_true_iff.
      intros; DestructHead.destruct_head'_or; split;
        Z.ltb_to_lt; try lia.
    Qed.

    Lemma is_tighter_than_bool_reverse_access_size s1 s2 :
      (access_size_to_zrange s1
       <=? access_size_to_zrange s2)%zrange = false ->
      (access_size_to_zrange s2
       <=? access_size_to_zrange s1)%zrange = true.
    Proof.
      apply is_tighter_than_bool_reverse_same_lower.
      rewrite !access_size_to_zrange_lower; auto.
    Qed.

    Lemma zrange_to_access_size'_correct r :
      forall sizes,
        (zrange_to_access_size' r sizes = None
         /\ (forall sz',
                In sz' sizes ->
                ~ is_true (r <=? access_size_to_zrange sz')%zrange))
        \/ (exists sz,
               zrange_to_access_size' r sizes = Some sz
               /\ In sz sizes
               /\ (forall sz',
                      In sz' sizes ->
                      is_true (r <=? access_size_to_zrange sz')%zrange ->
                      is_true (access_size_to_zrange sz <=? access_size_to_zrange sz')%zrange)).
    Proof.
      cbv [zrange_to_access_size'].
      induction sizes;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fold_right] in *
               | H : _ /\ _ |- _ => destruct H
               | H : In _ [] |- _ => solve [inversion H]
               | H : In _ (_ :: _) |- _ =>
                 inversion H; clear H; subst
               | H : Forall _ (_ :: _) |- _ =>
                 inversion H; clear H; subst
               | H : Some _ = Some _ |- _ =>
                 inversion H; clear H; subst
               | H : (_ && _)%bool = true |- _ =>
                 apply Bool.andb_true_iff in H; destruct H
               | H : (_ && _)%bool = false |- _ =>
                 apply Bool.andb_false_iff in H; destruct H
               | _ => progress break_match
               | |- (Some _ = None /\ _) \/ _ => right
               | |- (None = None /\ _) \/ _ => left
               | |- exists x, Some ?y = Some x /\ _ =>
                 exists y; split; [ reflexivity | ]
               | |- _ /\ _ => split
               | H : (Some _ = None /\ _) \/ exists _, _ |- _ =>
                   destruct H as [ [? ?] |H]; [ congruence | destruct H ]
               | H : _ \/ exists _, None = Some _ /\ _ |- _ =>
                   destruct H as [H|H];
                   [ | destruct H as [? [? ?] ]; congruence ]
               | H : forall _, In _ _ -> ~ _ |- _ =>
                 specialize (H _ ltac:(eassumption)); contradiction
               | _ => reflexivity
               | _ => congruence
               | _ => solve [auto using
                                  in_eq, in_cons,
                                  is_tighter_than_bool_reverse_access_size]
               | _ => etransitivity; [ eassumption | ]; solve [auto]
               end.
    Qed.

    Lemma zrange_to_access_size_tighter_than_word r :
      is_true (r <=? access_size_to_zrange access_size.word)%zrange ->
      forall sz,
        zrange_to_access_size r = Some sz ->
        is_true (access_size_to_zrange sz
                 <=? access_size_to_zrange access_size.word)%zrange.
    Proof.
      cbv [zrange_to_access_size]. intros.
      pose proof (zrange_to_access_size'_correct r all_access_sizes).
      assert (In access_size.word all_access_sizes) by (cbn; tauto).
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | H: exists _, _ |- _ => destruct H
             | H1: ?x = Some ?y1, H2 : ?x = Some ?y2 |- _ =>
               assert (y1 = y2) by congruence; subst; clear H1 H2
             | _ => congruence
             | _ => solve [auto]
             end.
    Qed.

    Lemma make_access_size_tighter_than_word ranges size :
      make_access_size ranges = Some size ->
      is_true (access_size_to_zrange size
               <=? access_size_to_zrange access_size.word)%zrange.
    Proof.
      cbv [make_access_size].
      break_match; try congruence; [ | ]; intros;
        match goal with
        | H : Some _ = Some _ |- _ =>
          inversion H; clear H; subst
        end;
        try reflexivity;
        eauto using zrange_to_access_size_tighter_than_word.
    Qed.

    Lemma bits_per_word_eq_width :
      (Z.of_nat (Memory.bytes_per
                   (width:=width) access_size.word) * 8
       = width).
    Proof.
      destruct Bitwidth.width_cases; subst; cbv; trivial.
    Qed.

    Lemma bits_per_word_le_width :
      (Z.of_nat (Memory.bytes_per
                   (width:=width) access_size.word) * 8
       <= width).
    Proof.
      rewrite bits_per_word_eq_width; reflexivity.
    Qed.

    Lemma bytes_per_word_eq :
      Z.to_nat (Memory.bytes_per_word width)
      = Memory.bytes_per (width:=width) access_size.word.
    Proof. reflexivity. Qed.

    Lemma make_access_size_good ranges size :
      make_access_size ranges = Some size ->
      (Z.of_nat (Memory.bytes_per
                   (width:=width) size) * 8
       <= width).
    Proof.
      intros.
      pose proof word.width_pos.
      pose proof make_access_size_tighter_than_word ranges size
           ltac:(assumption).
      eapply Z.le_trans; [ | apply bits_per_word_le_width ].
      cbv [is_true is_tighter_than_bool] in *.
      cbn [lower upper access_size_to_zrange] in *.
      match goal with
      | H : (_ && _)%bool = true |- _ =>
        apply Bool.andb_true_iff in H; destruct H
      end; Z.ltb_to_lt.
      apply (Z.pow_le_mono_r_iff 2); lia.
    Qed.

    Lemma make_base_access_sizes_good t bounds sizes :
      make_base_access_sizes bounds = Some sizes ->
      base_access_sizes_good (t:=t) sizes.
    Proof.
      induction t;
        repeat match goal with
               | _ => progress intros
               | _ => progress
                        cbn [fst snd make_base_access_sizes
                                 base_access_sizes_good] in *
               | _ => progress break_match_hyps
               | H : Some _ = Some _ |- _ =>
                 inversion H; clear H; subst
               | H : None = Some _ |- _ =>
                 solve [inversion H]
               | _ => progress ssplit
               | H : _ |- _ => eapply H; solve [eauto]
               | |- True => tauto
               | _ => solve [eauto using make_access_size_good]
               end.
    Qed.

    Lemma make_access_sizes_args_good t bounds sizes :
      make_access_sizes_args bounds = Some sizes ->
      access_sizes_good_args (t:=t) sizes.
    Proof.
      induction t;
        repeat match goal with
               | _ => progress intros
               | _ => progress
                        cbn [fst snd make_access_sizes_args
                                 access_sizes_good_args] in *
               | H : Some _ = Some _ |- _ =>
                 inversion H; clear H; subst
               | H : None = Some _ |- _ => congruence
               | _ => progress break_match_hyps
               | |- _ /\ _ => split
               | |- True => tauto
               | _ => eapply make_base_access_sizes_good;
                        eassumption
               | H : _ |- _ => eapply H; solve [eauto]
               end.
    Qed.

    (* useful for proving byte access sizes are legal *)
    Lemma width_ge_8 : 8 <= width.
    Proof.
      pose proof word.width_pos.
      pose proof width_0mod_8.
      let H := fresh in
      let x := fresh in
      pose proof width_0mod_8 as H; apply Z.mod_divide in H;
        [ | lia ]; destruct H as [x ?];
          destruct (Z.eq_dec x 0); subst; lia.
    Qed.
  End proofs.
End __.
