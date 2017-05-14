Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.Proper.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdc.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.Decidable.

Local Open Scope Z_scope.

Section named.
  Context {Name : Type}
          {InterpContext : Context Name interp_base_type}
          {InterpContextOk : ContextOk InterpContext}
          (Name_beq : Name -> Name -> bool)
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation exprf := (@exprf base_type op Name).
  Local Notation expr := (@expr base_type op Name).
  Local Notation do_rewrite := (@do_rewrite Name Name_beq).
  Local Notation do_rewriteo := (@do_rewriteo Name Name_beq).
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

  Local Ltac simple_t_step :=
    first [ discriminate
          | exact I
          | progress intros
          | progress subst
          | progress inversion_option ].
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
  Local Ltac small_inversion_step _ :=
    match goal with
    | [ H : match ?e with _ => _ end = Some _ |- _ ] => do_small_inversion e
    | [ H : match ?e with _ => _ end = true |- _ ] => do_small_inversion e
    | [ H : match ?e with _ => _ end _ = Some _ |- _ ] => do_small_inversion e
    end.

  Local Ltac rewrite_lookupb_step :=
    first [ rewrite !lookupb_extendb_different in * by (assumption || congruence)
          | rewrite !lookupb_extendb_same in * by assumption
          | rewrite !lookupb_extendb_wrong_type in * by (assumption || congruence)
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

  Lemma interpf_do_rewrite
        {t} {e e' : exprf t}
        (H : do_rewrite e = Some e')
    : retT e e'.
  Proof.
    unfold do_rewrite in H;
      repeat first [ simple_t_step
                   | small_inversion_step ()
                   | destruct_t_step ].
    Time all:match goal with
             | [ H : _ = ?x |- _ = ?x ] => rewrite <- H; clear H
             end.
    Time all:split_andb.
    Time all:progress simpl @negb in *.
    Time all:repeat match goal with
                    | [ H : Name_beq _ _ = true |- _ ] => apply Name_bl in H
                    | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
                    end.
    Time all:subst.
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
    Time all:do_small_inversion_ctx.
    Time all:simpl @negb in *.
    Time all:rewrite !Bool.negb_orb in *.
    Time all:split_andb.
    Time all:rewrite !Bool.negb_true_iff in *.
    Time all:repeat
               match goal with
               | [ H : Name_beq ?x ?y = false |- _ ]
                 => assert (x <> y) by (clear -H Name_lb; intro; rewrite Name_lb in H by assumption; congruence);
                      clear H
               end.
    Time all:subst.
    Time all:simpl @interpf in *.
    Time all:cbv [interp_op option_map lift_op Zinterp_op] in *; simpl in *.
    Time all:unfold Let_In in * |- .
    Time all:break_innermost_match; try reflexivity.
    Local Ltac t_fin_step :=
      match goal with
      | [ |- ?x = ?x ] => reflexivity
      | [ H : ?x = Some _ |- context[?x] ] => rewrite H
      | [ H : ?x = None |- context[?x] ] => rewrite H
      | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
        => assert (a = b) by congruence; (subst a || subst b)
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
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
    { Time t_fin. }
  Time Qed.

  Lemma interpf_do_rewriteo
        {t} {e : exprf t}
    : retT e (do_rewriteo e).
  Proof.
    unfold do_rewriteo; intros *; break_innermost_match; try congruence.
    apply interpf_do_rewrite; assumption.
  Qed.

  Local Opaque RewriteAddToAdc.do_rewriteo.
  Lemma interpf_rewrite_exprf
        {t} (e : exprf t)
    : retT e (rewrite_exprf e).
  Proof.
    pose t as T.
    pose (rewrite_exprf_prestep (@rewrite_exprf) e) as E.
    induction e; simpl in *;
      intros ctx v H;
      pose proof (interpf_do_rewriteo (t:=T) (e:=E) ctx v H); clear H;
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
