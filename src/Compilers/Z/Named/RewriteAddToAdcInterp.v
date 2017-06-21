Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.Proper.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdc.
Require Import Crypto.Compilers.Named.GetNames.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Decidable.

Local Open Scope Z_scope.

Section named.
  Context {Name : Type}
          {InterpContext : Context Name interp_base_type}
          {InterpContextOk : ContextOk InterpContext}
          (Name_beq : Name -> Name -> bool)
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation name_list_has_duplicate := (@name_list_has_duplicate Name Name_beq).
  Local Notation exprf := (@exprf base_type op Name).
  Local Notation expr := (@expr base_type op Name).
  Local Notation do_rewrite := (@do_rewrite Name Name_beq).
  Local Notation invert_for_do_rewrite := (@invert_for_do_rewrite Name Name_beq).
  Local Notation rewrite_exprf := (@rewrite_exprf Name Name_beq).
  Local Notation rewrite_exprf_prestep := (@rewrite_exprf_prestep Name).
  Local Notation rewrite_expr := (@rewrite_expr Name Name_beq).

  Local Instance Name_dec : DecidableRel (@eq Name)
    := dec_rel_of_bool_dec_rel Name_beq Name_bl Name_lb.

  Local Notation retT e re :=
    (forall (ctx : InterpContext)
            v,
        Named.interpf (interp_op:=interp_op) (ctx:=ctx) re = Some v
        -> Named.interpf (interp_op:=interp_op) (ctx:=ctx) e = Some v)
      (only parsing).
  Local Notation tZ := (Tbase TZ).
  Local Notation ADC bw c x y := (Op (@AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                     (Pair (Pair (t1:=tZ) c (t2:=tZ) x) (t2:=tZ) y)).
  Local Notation ADD bw x y := (ADC bw (Op (OpConst 0) TT) x y).
  Local Notation ADX x y := (Op (@Add TZ TZ TZ) (Pair (t1:=tZ) x (t2:=tZ) y)).
  Local Infix "=Z?" := Z.eqb.
  Local Infix "=n?" := Name_beq.

  Local Ltac simple_t_step :=
    first [ exact I
          | progress intros
          | progress subst
          | progress inversion_option
          | progress inversion_sum
          | progress inversion_prod ].
  Local Ltac destruct_t_step :=
    first [ break_innermost_match_hyps_step
          | break_innermost_match_step ].
  Local Ltac do_small_inversion e :=
    is_var e;
    lazymatch type of e with
    | exprf ?T
      => revert dependent e;
         let P := match goal with |- forall e, @?P e => P end in
         intro e;
         lazymatch T with
         | Unit
           => refine match e in Named.exprf _ _ _ t return match t return Named.exprf _ _ _ t -> _ with Unit => P | _ => fun _ => True end e with TT => _ | _ => _ end
         | tZ
           => refine match e in Named.exprf _ _ _ t return match t return Named.exprf _ _ _ t -> _ with tZ => P | _ => fun _ => True end e with TT => _ | _ => _ end
         | (tZ * tZ)%ctype
           => refine match e in Named.exprf _ _ _ t return match t return Named.exprf _ _ _ t -> _ with (tZ * tZ)%ctype => P | _ => fun _ => True end e with TT => _ | _ => _ end
         | (tZ * tZ * tZ)%ctype
           => refine match e in Named.exprf _ _ _ t return match t return Named.exprf _ _ _ t -> _ with (tZ * tZ * tZ)%ctype => P | _ => fun _ => True end e with TT => _ | _ => _ end
         end;
         try exact I
    | op ?a ?T
      => first [ is_var a;
                 move e at top;
                 revert dependent a;
                 let P := match goal with |- forall a e, @?P a e => P end in
                 intros a e;
                 lazymatch T with
                 | tZ
                   => refine match e in op a t return match t return op a t -> _ with tZ => P a | _ => fun _ => True end e with OpConst _ _ => _ | _ => _ end
                 | (tZ * tZ)%ctype
                   => refine match e in op a t return match t return op a t -> _ with (tZ * tZ)%ctype => P a | _ => fun _ => True end e with OpConst _ _ => _ | _ => _ end
                 end ];
         try exact I
    end.
  Local Ltac small_inversion_prestep _ :=
    match goal with
    | [ H : match ?e with _ => _ end = Some _ |- _ ] => do_small_inversion e
    | [ H : match ?e with _ => _ end = true |- _ ] => do_small_inversion e
    | [ H : match ?e with _ => _ end _ = Some _ |- _ ] => do_small_inversion e
    end.
  Local Ltac small_inversion_step :=
    small_inversion_prestep (); break_innermost_match; intros; try exact I.

  Local Ltac t_rewrite_step_correct_step :=
    first [ reflexivity
          | progress inversion_option
          | simple_t_step
          | break_innermost_match_hyps_step
          | small_inversion_step
          | progress unfold invert_for_do_rewrite_step1, invert_for_do_rewrite_step2, invert_for_do_rewrite_step3 in * ].
  Local Ltac t_rewrite_step_correct := repeat t_rewrite_step_correct_step.

  Local Ltac mk_lookupb_extendb_lemma_debug := constr:(false).
  Local Ltac debug_print_fail tac :=
    let lvl := mk_lookupb_extendb_lemma_debug in
    lazymatch lvl with
    | true => let dummy := match goal with
                           | _ => tac ()
                           end in
              constr:(I : I)
    | false => constr:(I : I)
    | _ => let TRUE := uconstr:(true) in
           let FALSE := uconstr:(false) in
           let dummy := match goal with
                        | _ => idtac "Error: Invalid mk_lookupb_extendb_lemma_debug level" lvl "which is neither" TRUE "nor" FALSE
                        end in
           constr:(I : I)
    end.

  (** We build the lemma explicitly, because letting [rewrite] and
     [assumption || congruence] pick out the hypotheses and build the
     lemmas is actually a bottleneck (timesavings: about 25s) *)
  Local Ltac mk_lookupb_extendb_lemma base_type_code Name var Context t t' ctx n n' v :=
    lazymatch n with
    | n' => lazymatch t with
            | t' => constr:(@lookupb_extendb_same base_type_code Name var Context _ ctx n t v)
            | _ => let lem := constr:(@lookupb_extendb_wrong_type base_type_code Name var Context _ ctx n t t' v) in
                   lazymatch goal with
                   | [ H : t <> t' |- _ ]
                     => constr:(lem H)
                   | [ H : t' <> t |- _ ]
                     => constr:(lem (@not_eq_sym _ _ _ H))
                   | _ => let HT := uconstr:(t <> t') in
                          debug_print_fail ltac:(fun _ => idtac "Error in mk_lookupb_exntedb_lemma: could not find hypothesis of type" HT)
                   end
            end
    | _ => let lem := constr:(@lookupb_extendb_different base_type_code Name var Context _ ctx n n' t t' v) in
           lazymatch goal with
           | [ H : n <> n' |- _ ]
             => constr:(lem H)
           | [ H : n' <> n |- _ ]
             => constr:(lem (@not_eq_sym _ _ _ H))
           | _ => let HT := uconstr:(n <> n') in
                  debug_print_fail ltac:(fun _ => idtac "Error in mk_lookupb_exntedb_lemma: could not find hypothesis of type" HT)
           end
    end.
  Local Ltac rewrite_lookupb_step :=
    first [ match goal with
            | [ H : context[@lookupb ?base_type_code ?Name ?var ?Context ?t' (extendb (t:=?t) ?ctx ?n ?v) ?n'] |- _ ]
              => let lem := mk_lookupb_extendb_lemma base_type_code Name var Context t t' ctx n n' v in
                 rewrite lem in H
            | [ |- context[@lookupb ?base_type_code ?Name ?var ?Context ?t' (extendb (t:=?t) ?ctx ?n ?v) ?n'] ]
              => let lem := mk_lookupb_extendb_lemma base_type_code Name var Context t t' ctx n n' v in
                 rewrite lem
            end
          | match goal with
            | [ H : context[lookupb (extendb _ _ _) _] |- _ ] => revert H
            | [ |- context[lookupb (extendb _ ?n _) ?n'] ]
              => (tryif constr_eq n n' then fail else idtac);
                 lazymatch goal with
                 | [ H : n = n' |- _ ] => fail
                 | [ H : n' = n |- _ ] => fail
                 | [ H : n <> n' |- _ ] => fail
                 | [ H : n' <> n |- _ ] => fail
                 | _ => destruct (dec (n = n')); subst
                 end
            | [ |- context[lookupb (t:=?t0) (extendb (t:=?t1) _ _ _) _] ]
              => (tryif constr_eq t0 t1 then fail else idtac);
                 lazymatch goal with
                 | [ H : t0 = t1 |- _ ] => fail
                 | [ H : t1 = t0 |- _ ] => fail
                 | [ H : t0 <> t1 |- _ ] => fail
                 | [ H : t1 <> t0 |- _ ] => fail
                 | _ => destruct (dec (t0 = t1)); subst
                 end
            end ].
  Local Ltac rewrite_lookupb := repeat rewrite_lookupb_step.

  Local Ltac do_rewrite_adc' P :=
    let lem := open_constr:(Z.add_get_carry_to_add_with_get_carry_cps _ _ _ _ P) in
    let T := type of lem in
    let T := (eval cbv [Let_In Definitions.Z.add_with_get_carry Definitions.Z.add_with_get_carry Definitions.Z.get_carry Definitions.Z.add_get_carry] in T) in
    etransitivity; [ | eapply (lem : T) ];
    try reflexivity.
  Local Ltac do_rewrite_adc :=
    first [ do_rewrite_adc' uconstr:(fun a b => Some b)
          | do_rewrite_adc' uconstr:(fun a b => Some a) ].
  Local Ltac do_small_inversion_ctx :=
    repeat match goal with
           | [ H : is_const_or_var ?e = true |- _ ]
             => do_small_inversion e; break_innermost_match; intros; try exact I;
                simpl in H; try solve [ clear -H; discriminate ]
           | [ H : match ?e with _ => _ end = true |- _ ]
             => do_small_inversion e; break_innermost_match; intros; try exact I;
                simpl in H; try solve [ clear -H; discriminate ]
           | [ H : match ?e with _ => _ end _ = true |- _ ]
             => do_small_inversion e; break_innermost_match; intros; try exact I;
                simpl in H; try solve [ clear -H; discriminate ]
           end.
  Local Ltac t_fin_step :=
    match goal with
    | [ |- ?x = ?x ] => reflexivity
    | [ H : ?x = Some _ |- context[?x] ] => rewrite H
    | [ H : ?x = None |- context[?x] ] => rewrite H
    | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
      => assert (a = b) by congruence; (subst a || subst b)
    | [ H : interpf ?x = Some ?v, H' : interpf ?x = None |- interpf _ = None ]
      => cut (Some v = None);
         [ congruence | rewrite <- H, <- H'; clear H H' ]
    | _ => progress rewrite_lookupb
    | _ => progress simpl in *
    | _ => progress intros
    | _ => progress subst
    | _ => progress inversion_option
    | [ |- (dlet x := _ in _) = (dlet y := _ in _) ]
      => apply Proper_Let_In_nd_changebody_eq; intros ??
    | _ => progress unfold Let_In
    | [ |- interpf ?x = interpf ?x ]
      => eapply @interpf_Proper; [ eauto with typeclass_instances.. | intros ?? | reflexivity ]
    | _ => progress break_innermost_match; try reflexivity
    | _ => progress break_innermost_match_hyps; try reflexivity
    | _ => progress break_match; try reflexivity
    end.
  Local Ltac t_fin :=
    repeat t_fin_step;
    try do_rewrite_adc.


  Lemma invert_for_do_rewrite_step1_correct {t} {e : exprf t} {v}
        (H : invert_for_do_rewrite_step1 e = Some v)
    : e = let '((a2, c1, bw1, a, b), P) := v in
          (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in P)%nexpr.
  Proof. t_rewrite_step_correct. Qed.
  Lemma invert_for_do_rewrite_step2_correct {t} {e : exprf t} {v}
        (H : invert_for_do_rewrite_step2 e = Some v)
    : e = let '((s, c2, bw2, c0, a2'), P) := v in
          (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var a2')) in P)%nexpr.
  Proof. t_rewrite_step_correct. Qed.
  Lemma invert_for_do_rewrite_step3_correct {t} {e : exprf t} {v}
        (H : invert_for_do_rewrite_step3 e = Some v)
    : e = let '((c, c1', c2'), P) := v in
          (nlet c        : tZ      := (ADX (Var c1') (Var c2')) in P)%nexpr.
  Proof. t_rewrite_step_correct. Qed.

  Lemma invert_for_do_rewrite_correct {t} {e : exprf t} {v}
        (H : invert_for_do_rewrite e = Some v)
    : match v with
      | ((a2, c1, bw1, a, b),
         (s, c2, bw2, c0, a2'),
         inl ((c, c1', c2'), P))
        => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
            nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
            nlet c        : tZ      := ADX (Var c1') (Var c2') in
            P) = e
           /\ ((((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                  && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                  && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
               = true)
      | ((a2, c1, bw1, a, b),
         (s, c2, bw2, c0, a2'),
         inr P)
        => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
            nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
            P) = e
           /\ ((((bw1 =Z? bw2) && (a2 =n? a2'))
                  && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                  && negb (name_list_has_duplicate (a2::c1::s::c2::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
               = true)
      end%core%nexpr%bool.
  Proof.
    unfold invert_for_do_rewrite in H; break_innermost_match_hyps;
      repeat first [ progress subst
                   | progress inversion_option
                   | progress inversion_sum
                   | progress inversion_prod
                   | match goal with
                     | [ H : _ = Some _ |- _ ]
                       => first [ rewrite (invert_for_do_rewrite_step1_correct H)
                                | rewrite (invert_for_do_rewrite_step2_correct H)
                                | rewrite (invert_for_do_rewrite_step3_correct H) ]
                     | [ H : ?x = true |- _ ] => rewrite H; clear H
                     | [ |- _ /\ _ ] => split
                     | [ |- ?x = ?x ] => reflexivity
                     | [ H : Name_beq _ _ = true |- _ ] => apply Name_bl in H
                     | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
                     | [ H : Name_beq ?x ?y = false |- _ ]
                       => assert (x <> y) by (clear -H Name_lb; intro; rewrite Name_lb in H by assumption; congruence);
                          clear H
                     end
                   | progress rewrite !Bool.negb_orb in *
                   | progress rewrite !Bool.negb_true_iff in *
                   | progress split_andb
                   | progress simpl @negb in *
                   | progress do_small_inversion_ctx ].
  Qed.

  Lemma interpf_do_rewrite
        {t} {e : exprf t}
    : retT e (do_rewrite e).
  Proof.
    unfold do_rewrite.
    pose proof (@invert_for_do_rewrite_correct t e) as H'.
    break_innermost_match; inversion_option;
      [ specialize (H' _ eq_refl)
      | specialize (H' _ eq_refl)
      | intros; subst; assumption ].
    all: intros *; let H := fresh in intro H; rewrite <- H; clear H.
    Time all:repeat first [ progress cbv beta iota in *
                          | progress destruct_head'_and
                          | progress subst
                          | progress rewrite !Bool.negb_orb in *
                          | progress split_andb
                          | progress simpl @name_list_has_duplicate in *
                          | match goal with
                            | [ H : Name_beq _ _ = true |- _ ] => apply Name_bl in H
                            | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
                            | [ H : Name_beq ?x ?y = false |- _ ]
                              => assert (x <> y) by (clear -H Name_lb; intro; rewrite Name_lb in H by assumption; congruence);
                                   clear H
                            | [ H : context[List.fold_left orb ?ls ?v] |- _ ]
                              => lazymatch v with
                                 | false => fail
                                 | _ => rewrite (fold_left_orb_pull ls v) in H
                                 end
                            end
                          | progress simpl @List.fold_left in *
                          | progress do_small_inversion_ctx
                          | progress rewrite !Bool.negb_true_iff in *
                          | progress intros *
                          | match goal with
                            | [ H : invert_for_do_rewrite _ = Some _ |- _ ] => clear H
                            end ].
    Time all: repeat first [ progress simpl
                           | progress cbv [interp_op option_map lift_op Zinterp_op] in * ].
    Time all: repeat first [ progress subst
                           | progress inversion_option
                           | progress rewrite_lookupb
                           | progress intros
                           | match goal with
                             | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                               => assert (a = b) by congruence; (subst a || subst b)
                             | [ H : ?T, H' : ?T |- _ ] => clear H'
                             end ].
    Set Ltac Profiling.
    Time all: repeat first [ reflexivity
                           | progress subst
                           | progress inversion_option
                           | progress rewrite_lookupb
                           | progress intros
                           | progress cbn [fst snd]
                           | match goal with
                             | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                               => assert (a = b) by congruence; (subst a || subst b)
                             | [ H : ?T, H' : ?T |- _ ] => clear H'
                             | [ |- context[match lookupb ?ctx ?n with _ => _ end] ]
                               => is_var ctx; destruct (lookupb ctx n) eqn:?
                             | [ |- (dlet x := ?e in _) = (dlet y := ?e in _) ]
                               => apply Proper_Let_In_nd_changebody_eq; intros ??
                             end
                           | progress unfold Let_In at 1 ].
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
  Time Qed.

  Local Opaque RewriteAddToAdc.do_rewrite.
  Lemma interpf_rewrite_exprf
        {t} (e : exprf t)
    : retT e (rewrite_exprf e).
  Proof.
    pose t as T.
    pose (rewrite_exprf_prestep (@rewrite_exprf) e) as E.
    induction e; simpl in *;
      intros ctx v H;
      pose proof (interpf_do_rewrite (t:=T) (e:=E) ctx v H); clear H;
      subst T E;
      repeat first [ assumption
                   | progress unfold option_map, Let_In in *
                   | progress simpl in *
                   | progress subst
                   | progress inversion_option
                   | apply (f_equal (@Some _))
                   | break_innermost_match_step
                   | break_innermost_match_hyps_step
                   | congruence
                   | solve [ eauto ]
                   | match goal with
                     | [ IH : forall ctx v, interpf ?e = Some v -> _ = Some _, H' : interpf ?e = Some _ |- _ ]
                       => specialize (IH _ _ H')
                     | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                       => assert (a = b) by congruence; (subst a || subst b)
                     | [ |- ?rhs = Some _ ]
                       => lazymatch rhs with
                          | Some _ => fail
                          | None => fail
                          | _ => destruct rhs eqn:?
                          end
                     end ].
  Qed.

  Lemma interp_rewrite_expr
        {t} (e : expr t)
    : forall (ctx : InterpContext)
             v x,
      Named.interp (interp_op:=interp_op) (ctx:=ctx) (rewrite_expr e) x = Some v
      -> Named.interp (interp_op:=interp_op) (ctx:=ctx) e x = Some v.
  Proof.
    unfold Named.interp, rewrite_expr; destruct e; simpl.
    intros *; apply interpf_rewrite_exprf.
  Qed.

  Lemma Interp_rewrite_expr
        {t} (e : expr t)
    : forall v x,
      Named.Interp (Context:=InterpContext) (interp_op:=interp_op) (rewrite_expr e) x = Some v
      -> Named.Interp (Context:=InterpContext) (interp_op:=interp_op) e x = Some v.
  Proof.
    intros *; apply interp_rewrite_expr.
  Qed.
End named.
