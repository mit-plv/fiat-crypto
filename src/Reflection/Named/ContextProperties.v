Require Import Coq.omega.Omega.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Named.NameUtilProperties.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Logic.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var)
          (base_type_code_dec : DecidableRel (@eq base_type_code))
          (Name_dec : DecidableRel (@eq Name))
          (ContextOk : ContextOk Context).

  Local Notation find_Name := (@find_Name base_type_code Name Name_dec).
  Local Notation find_Name_and_val := (@find_Name_and_val base_type_code Name base_type_code_dec Name_dec).

  Let base_type_UIP_refl : forall t (p : t = t :> base_type_code), p = eq_refl.
  Proof.
    intro; apply K_dec; intros; [ | reflexivity ].
    edestruct base_type_code_dec; eauto.
  Defined.

  Lemma lookupb_eq_cast
    : forall (ctx : Context) n t t' (pf : t = t'),
      lookupb ctx n t' = option_map (fun v => eq_rect _ var v _ pf) (lookupb ctx n t).
  Proof.
    intros; subst; edestruct lookupb; reflexivity.
  Defined.
  Lemma lookupb_extendb_eq
    : forall (ctx : Context) n t t' (pf : t = t') v,
      lookupb (extendb ctx n (t:=t) v) n t' = Some (eq_rect _ var v _ pf).
  Proof.
    intros; subst; apply lookupb_extendb_same; assumption.
  Defined.

  Local Ltac fin_t_step :=
    solve [ reflexivity ].
  Local Ltac fin_t_late_step :=
    solve [ tauto
          | congruence
          | eauto
          | exfalso; unfold not in *; eauto ].
  Local Ltac inversion_step :=
    first [ progress subst
          | progress inversion_option
          | progress inversion_sigma
          | progress inversion_prod
          | progress destruct_head' and
          | match goal with
            | [ H : ?t = ?t :> base_type_code |- _ ]
              => pose proof (base_type_UIP_refl t H); subst H
            end
          | progress split_and ].
  Local Ltac rewrite_lookupb_extendb_step :=
    first [ rewrite lookupb_extendb_different by congruence
          | rewrite lookupb_extendb_same
          | rewrite lookupb_extendb_wrong_type by assumption ].
  Local Ltac specializer_t_step :=
    match goal with
    | _ => progress specialize_by_assumption
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : ?T, H' : ?T |- _ ] => clear H'
    | [ H : forall v, Some _ = Some v -> _ |- _ ]
      => specialize (H _ eq_refl)
    | [ H : forall v, Some v = Some _ -> _ |- _ ]
      => specialize (H _ eq_refl)
    end.
  Local Ltac misc_t_step :=
    first [ progress intros
          | progress simpl in * ].
  Local Ltac misc_oname_t_step :=
    match goal with
    | [ H : oname_list_unique (List.skipn _ _) -> _ |- _ ]
      => specialize (fun pf => H (@oname_list_unique_skipn _ _ _ pf))
    | [ H : ((_, _) = (_, _))%core -> _ |- _ ]
      => specialize (fun a b => H (f_equal2 (@pair _ _) a b))
    | [ H : ?x = (_,_)%core -> _ |- _ ]
      => rewrite (surjective_pairing x) in H;
         specialize (fun a b => H (f_equal2 (@pair _ _) a b))
    end.
  Local Ltac break_t_step :=
    first [ progress break_innermost_match_step
          | progress unfold cast_if_eq in *
          | match goal with
            | [ H : context[match _ with _ => _ end] |- _ ]
              => revert H; progress break_innermost_match_step
            | [ |- _ /\ _ ] => split
            | [ |- _ <-> _ ] => split
            | [ |- ~ _ ] => intro
            end
          | progress destruct_head' ex
          | progress destruct_head' or ].
  Local Ltac myfold_in_star c :=
    let c' := (eval cbv [interp_flat_type] in c) in
    change c' with c in *.
  Local Ltac refolder_t_step :=
    first [ progress myfold_in_star (@interp_flat_type base_type_code var)
          | progress myfold_in_star (@interp_flat_type base_type_code (fun _ => Name))
          | match goal with
            | [ var : base_type_code -> Type |- _ ]
              => progress myfold_in_star (@interp_flat_type base_type_code var)

            end ].
  Local Ltac rewriter_t_step :=
    first [ match goal with
            | [ H : _ |- _ ] => rewrite H by (assumption || congruence)
            | [ H : _ |- _ ] => etransitivity; [ | rewrite H by (assumption || congruence); reflexivity ]
            | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
            | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
            | [ H : ?x = ?a :> option _, H' : ?x = ?b :> option _ |- _ ]
              => assert (a = b)
                by (transitivity x; [ symmetry | ]; assumption);
                 clear H'
            | _ => progress autorewrite with ctx_db in *
            | [ H : context[snd (split_onames _ _)] |- _ ]
              => rewrite snd_split_onames_skipn in H
            | [ |- context[snd (split_onames _ _)] ]
              => rewrite snd_split_onames_skipn
            end ].
  Local Ltac t_step :=
    first [ fin_t_step
          | inversion_step
          | rewrite_lookupb_extendb_step
          | specializer_t_step
          | misc_oname_t_step
          | misc_t_step
          | break_t_step
          | refolder_t_step
          | rewriter_t_step
          | fin_t_late_step ].
  Local Ltac t := repeat t_step.

  Lemma lookupb_extend (ctx : Context)
        T N t n v
    : lookupb (extend ctx N (t:=T) v) n t
      = find_Name_and_val t n N v (lookupb ctx n t).
  Proof. revert ctx; induction T; t. Qed.

  Lemma find_Name_and_val_Some_None
        {var' var''}
        {t n T N}
        {x : interp_flat_type var' T}
        {y : interp_flat_type var'' T}
        {default default' v}
        (H0 : @find_Name_and_val var' t n T N x default = Some v)
        (H1 : @find_Name_and_val var'' t n T N y default' = None)
    : default = Some v /\ default' = None.
  Proof.
    revert dependent default; revert dependent default'; induction T; t.
  Qed.

  Lemma find_Name_and_val_default_to_None
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N <> None)
    : @find_Name_and_val var' t n T N x default
      = @find_Name_and_val var' t n T N x None.
  Proof. revert default; induction T; t. Qed.
  Hint Rewrite @find_Name_and_val_default_to_None using congruence : ctx_db.

  Lemma find_Name_and_val_different
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = None)
    : @find_Name_and_val var' t n T N x default = default.
  Proof. revert default; induction T; t. Qed.
  Hint Rewrite @find_Name_and_val_different using assumption : ctx_db.

  Lemma find_Name_and_val_wrong_type_iff
        {var'}
        {t t' n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = Some t')
    : t <> t'
      <-> @find_Name_and_val var' t n T N x default = None.
  Proof. split; revert default; induction T; t. Qed.
  Lemma find_Name_and_val_wrong_type
        {var'}
        {t t' n T N}
        {x : interp_flat_type var' T}
        {default}
        (H : @find_Name n T N = Some t')
        (Ht : t <> t')
    : @find_Name_and_val var' t n T N x default = None.
  Proof. eapply find_Name_and_val_wrong_type_iff; eassumption. Qed.
  Hint Rewrite @find_Name_and_val_wrong_type using congruence : ctx_db.

  Lemma find_Name_find_Name_and_val_wrong {var' n t' T V N}
    : find_Name n N = Some t'
      -> @find_Name_and_val var' t' n T N V None = None
      -> False.
  Proof. induction T; t. Qed.

  Lemma find_Name_and_val_None_iff
        {var'}
        {t n T N}
        {x : interp_flat_type var' T}
        {default}
    : (@find_Name n T N <> Some t
       /\ (@find_Name n T N <> None \/ default = None))
      <-> @find_Name_and_val var' t n T N x default = None.
  Proof.
    destruct (@find_Name n T N) eqn:?; unfold not; t;
      try solve [ eapply find_Name_and_val_wrong_type; [ eassumption | congruence ]
                | eapply find_Name_find_Name_and_val_wrong; eassumption
                | left; congruence ].
  Qed.

  Lemma find_Name_and_val_split
        {var' t n T N V default}
    : @find_Name_and_val var' t n T N V default
      = match @find_Name n T N with
        | Some t' => if dec (t = t')
                     then @find_Name_and_val var' t n T N V None
                     else None
        | None => default
        end.
  Proof.
    t; erewrite find_Name_and_val_wrong_type by solve [ eassumption | congruence ]; reflexivity.
  Qed.
  Lemma find_Name_and_val_find_Name_Some
        {var' t n T N V v}
        (H : @find_Name_and_val var' t n T N V None = Some v)
    : @find_Name n T N = Some t.
  Proof.
    rewrite find_Name_and_val_split in H; break_match_hyps; subst; congruence.
  Qed.
  Local Ltac find_Name_and_val_default_to_None_step :=
    match goal with
    | [ H : context[find_Name_and_val _ _ _ _ ?default] |- _ ]
      => lazymatch default with None => fail | _ => idtac end;
         rewrite (find_Name_and_val_split (default:=default)) in H
    | [ |- context[find_Name_and_val _ _ _ _ ?default] ]
      => lazymatch default with None => fail | _ => idtac end;
         rewrite (find_Name_and_val_split (default:=default))
    end.
  Local Ltac find_Name_and_val_default_to_None := repeat find_Name_and_val_default_to_None_step.

  Lemma find_Name_and_val_flatten_binding_list
        {var' var'' t n T N V1 V2 v1 v2}
        (H1 : @find_Name_and_val var' t n T N V1 None = Some v1)
        (H2 : @find_Name_and_val var'' t n T N V2 None = Some v2)
    : List.In (existT (fun t => (var' t * var'' t)%type) t (v1, v2)) (Wf.flatten_binding_list V1 V2).
  Proof.
    induction T;
      [ | | specialize (IHT1 (fst N) (fst V1) (fst V2));
            specialize (IHT2 (snd N) (snd V1) (snd V2)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | rewrite List.in_app_iff
                   | t_step ].
  Qed.

  Lemma split_onames_find_Name
        {n T N ls ls'}
        (H : split_onames _ ls = (Some N, ls')%core)
    : (exists t, @find_Name n T N = Some t)
      <-> List.In (Some n) (List.firstn (CountLets.count_pairs T) ls).
  Proof.
    revert dependent ls; intro ls; revert ls ls'; induction T; intros;
      [ | | specialize (IHT1 (fst N) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ progress t
                   | progress split_iff
                   | progress specialize_by (eexists; eauto)
                   | solve [ eauto using In_skipn, In_firstn ]
                   | match goal with
                     | [ H : List.In ?x (List.firstn ?n ?ls) |- List.In ?x (List.firstn (?n + ?m) ?ls) ]
                       => apply (In_firstn n); rewrite firstn_firstn by omega
                     | [ H : _ |- _ ] => first [ rewrite firstn_skipn_add in H
                                               | rewrite firstn_firstn in H by omega ]
                     | [ H : List.In ?x' (List.firstn (?n + ?m) ?ls) |- List.In ?x' (List.firstn ?m (List.skipn ?n ?ls)) ]
                       => apply (In_firstn_skipn_split n) in H
                     end ].
  Qed.

  Lemma split_onames_find_Name_Some_unique_iff
        {n T N ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : (exists t, @find_Name n T N = Some t)
      <-> List.In (Some n) ls /\ ~List.In (Some n) ls'.
  Proof.
    rewrite (split_onames_find_Name (ls':=ls') (ls:=ls)) by assumption.
    rewrite (surjective_pairing (split_onames _ _)) in H.
    rewrite fst_split_onames_firstn, snd_split_onames_skipn in H.
    inversion_prod; subst.
    split; [ split | intros [? ?] ]; eauto using In_firstn, oname_list_unique_specialize.
    eapply In_firstn_skipn_split in H; destruct_head' or; eauto; exfalso; eauto.
  Qed.

  Lemma split_onames_find_Name_Some_unique
        {t n T N ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
        (Hfind : @find_Name n T N = Some t)
    : List.In (Some n) ls /\ ~List.In (Some n) ls'.
  Proof.
    eapply split_onames_find_Name_Some_unique_iff; eauto.
  Qed.

  (*Lemma flatten_binding_list_find_Name_unique_None
        {var' n T N V ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : @find_Name n T N = None
      <-> (forall t v, ~List.In (existT (fun t => (Name * var' t)%type) t (n, v)) (Wf.flatten_binding_list N V)).
  Proof.
    revert dependent ls; intro ls; revert ls ls'; induction T; intros;
      [ | | specialize (IHT1 (fst N) (fst V) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd V) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | progress simpl in *
                   | setoid_rewrite List.in_app_iff
                   | t_step
                   | progress split_iff ].
    Grab Existential Variables.
    eassumption.
  Qed.*)

  (*Lemma flatten_binding_list_find_Name_unique
        {var' t n T N V ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : @find_Name n T N = Some t
      <-> (exists v, List.In (existT (fun t => (Name * var' t)%type) t (n, v)) (Wf.flatten_binding_list N V)).
  Proof.
    revert t; revert dependent ls; intro ls; revert ls ls'; induction T; intros;
      [ | | specialize (IHT1 (fst N) (fst V) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd V) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | progress simpl in *
                   | setoid_rewrite List.in_app_iff
                   | t_step
                   | progress split_iff
                   | progress destruct_head' ex
                   | progress destruct_head' or
                   | progress specialize_by (eexists; eassumption)
                   | lazymatch goal with
                     | [ H : forall t : base_type_code, _ |- _ ]
                       => progress repeat match goal with
                                          | [ t' : base_type_code |- _ ]
                                            => unique pose proof (H t')
                                          end;
                          clear H
                     end
                   | lazymatch goal with
                     | [ H : find_Name ?n ?x = Some ?t, H' : find_Name ?n ?x' = Some ?t' |- _ ]
                       => let apply_in_tac H :=
                              (eapply split_onames_find_Name_Some_unique in H;
                               [ | | apply path_prod_uncurried; split; [ eassumption | reflexivity ] ];
                               [ | solve [ eauto using oname_list_unique_firstn, oname_list_unique_skipn ] ]) in
                          first [ constr_eq x x'; fail 1
                                | constr_eq t t'; fail 1
                                | apply_in_tac H; apply_in_tac H' ]
                     end ].
  Qed.*)

  Lemma flatten_binding_list_find_Name_and_val_unique
        {var' t n T N V v ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : @find_Name_and_val var' t n T N V None = Some v
      <-> List.In (existT (fun t => (Name * var' t)%type) t (n, v)) (Wf.flatten_binding_list N V).
  Proof.
    revert dependent ls; intro ls; revert ls ls'; induction T; intros;
      [ | | specialize (IHT1 (fst N) (fst V) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd V) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | progress simpl in *
                   | rewrite List.in_app_iff
                   | t_step
                   | progress split_iff
                   | lazymatch goal with
                     | [ H : find_Name ?n ?x = Some ?t, H' : find_Name_and_val ?t' ?n ?X ?V None = Some ?v |- _ ]
                       => apply find_Name_and_val_find_Name_Some in H'
                     | [ H : find_Name ?n ?x = Some ?t, H' : find_Name ?n ?x' = Some ?t' |- _ ]
                       => let apply_in_tac H :=
                              (eapply split_onames_find_Name_Some_unique in H;
                               [ | | apply path_prod_uncurried; split; [ eassumption | simpl; reflexivity ] ];
                               [ | solve [ eauto using oname_list_unique_firstn, oname_list_unique_skipn ] ]) in
                          first [ constr_eq x x'; fail 1
                                | apply_in_tac H; apply_in_tac H' ]
                     end ].
  Qed.

  Lemma fst_split_mnames__flatten_binding_list__find_Name
        (MName : Type) (force : MName -> option Name)
        {var' t n T N V v} {ls : list MName}
        (Hs : fst (split_mnames force T ls) = Some N)
        (HN : List.In (existT _ t (n, v)%core) (Wf.flatten_binding_list (var2:=var') N V))
    : find_Name n N = Some t.
  Proof.
    revert dependent ls; induction T;
      [ | | specialize (IHT1 (fst N) (fst V));
            specialize (IHT2 (snd N) (snd V)) ];
      repeat first [ t_step
                   | match goal with
                     | [ H : _ |- _ ] => first [ rewrite snd_split_mnames_skipn in H
                                               | rewrite List.in_app_iff in H ]
                     | [ H : context[fst (split_mnames _ _ ?ls)] |- _ ]
                       => is_var ls; rewrite (@fst_split_mnames_firstn _ _ _ _ _ ls) in H
                     end ].
  Abort.

  Lemma fst_split_mnames__find_Name__flatten_binding_list
        (MName : Type) (force : MName -> option Name)
        {var' t n T N V v default} {ls : list MName}
        (Hs : fst (split_mnames force T ls) = Some N)
        (Hfind : find_Name n N = Some t)
        (HN : List.In (existT _ t (n, v)%core) (Wf.flatten_binding_list N V))
    : @find_Name_and_val var' t n T N V default = Some v.
  Proof.
    revert default; revert dependent ls; induction T;
      [ | | specialize (IHT1 (fst N) (fst V));
            specialize (IHT2 (snd N) (snd V)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | rewrite List.in_app_iff in *
                   | t_step ].
  Abort.

  Lemma find_Name_SmartFlatTypeMapInterp2_None_iff {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      <-> find_Name n N = None.
  Proof.
    split;
      (induction T;
       [ | | specialize (IHT1 (fst V) (fst N));
             specialize (IHT2 (snd V) (snd N)) ]);
      t.
  Qed.
  Hint Rewrite @find_Name_SmartFlatTypeMapInterp2_None_iff : ctx_db.
  Lemma find_Name_SmartFlatTypeMapInterp2_None {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      -> find_Name n N = None.
  Proof. apply find_Name_SmartFlatTypeMapInterp2_None_iff. Qed.
  Hint Rewrite @find_Name_SmartFlatTypeMapInterp2_None using eassumption : ctx_db.
  Lemma find_Name_SmartFlatTypeMapInterp2_None' {var' n f T V N}
    : find_Name n N = None
      -> @find_Name n (SmartFlatTypeMap f (t:=T) V)
                    (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None.
  Proof. apply find_Name_SmartFlatTypeMapInterp2_None_iff. Qed.
  Lemma find_Name_SmartFlatTypeMapInterp2_None_Some_wrong {var' n f T V N v}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) = None
      -> find_Name n N = Some v
      -> False.
  Proof.
    intro; erewrite find_Name_SmartFlatTypeMapInterp2_None by eassumption; congruence.
  Qed.
  Local Hint Resolve @find_Name_SmartFlatTypeMapInterp2_None_Some_wrong.

  Lemma find_Name_SmartFlatTypeMapInterp2 {var' n f T V N}
    : @find_Name n (SmartFlatTypeMap f (t:=T) V)
                 (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N)
      = match find_Name n N with
        | Some t' => match find_Name_and_val t' n N V None with
                     | Some v => Some (f t' v)
                     | None => None
                     end
        | None => None
        end.
  Proof.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N));
            specialize (IHT2 (snd V) (snd N)) ].
    { t. }
    { t. }
    { repeat first [ fin_t_step
                   | inversion_step
                   | rewrite_lookupb_extendb_step
                   | misc_t_step
                   | refolder_t_step ].
      repeat match goal with
             | [ |- context[match @find_Name ?n ?T ?N with _ => _ end] ]
               => destruct (@find_Name n T N) eqn:?
             | [ H : context[match @find_Name ?n ?T ?N with _ => _ end] |- _ ]
               => destruct (@find_Name n T N) eqn:?
             end;
        repeat first [ fin_t_step
                     | rewriter_t_step
                     | fin_t_late_step ]. }
  Qed.

  Lemma find_Name_and_val__SmartFlatTypeMapInterp2__SmartFlatTypeMapUnInterp__Some_Some_alt
        {var' var'' var''' t b n f g T V N X v v'}
        (Hfg
         : forall (V : var' t) (X : var'' (f t V)) (H : f t V = f t b),
            g t b (eq_rect (f t V) var'' X (f t b) H) = g t V X)
    : @find_Name_and_val
           var'' (f t b) n (SmartFlatTypeMap f (t:=T) V)
           (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) X None = Some v
      -> @find_Name_and_val
           var''' t n T N (SmartFlatTypeMapUnInterp (f:=f) g X) None = Some v'
      -> g t b v = v'.
  Proof.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N) (fst X));
            specialize (IHT2 (snd V) (snd N) (snd X)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step
                   | match goal with
                     | [ H : _ |- _ ]
                       => progress rewrite find_Name_and_val_different in H
                         by solve [ congruence
                                  | apply find_Name_SmartFlatTypeMapInterp2_None'; assumption ]
                     end ].
  Qed.

  Lemma find_Name_and_val__SmartFlatTypeMapInterp2__SmartFlatTypeMapUnInterp__Some_Some
        {var' var'' var''' t b n f g T V N X v v'}
    : @find_Name_and_val
           var'' (f t b) n (SmartFlatTypeMap f (t:=T) V)
           (SmartFlatTypeMapInterp2 (var':=var') (fun _ _ (n' : Name) => n') V N) X None = Some v
      -> @find_Name_and_val
           _ t n T N V None = Some b
      -> @find_Name_and_val
           var''' t n T N (SmartFlatTypeMapUnInterp (f:=f) g X) None = Some v'
      -> g t b v = v'.
  Proof.
    induction T;
      [ | | specialize (IHT1 (fst V) (fst N) (fst X));
            specialize (IHT2 (snd V) (snd N) (snd X)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step
                   | match goal with
                     | [ H : _ |- _ ]
                       => progress rewrite find_Name_and_val_different in H
                         by solve [ congruence
                                  | apply find_Name_SmartFlatTypeMapInterp2_None'; assumption ]
                     end ].
  Qed.

  Lemma interp_flat_type_rel_pointwise__find_Name_and_val
        {var' var'' t n T N x y R v0 v1}
        (H0 : @find_Name_and_val var' t n T N x None = Some v0)
        (H1 : @find_Name_and_val var'' t n T N y None = Some v1)
        (HR : interp_flat_type_rel_pointwise R x y)
    : R _ v0 v1.
  Proof.
    induction T;
      [ | | specialize (IHT1 (fst N) (fst x) (fst y));
            specialize (IHT2 (snd N) (snd x) (snd y)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | t_step ].
  Qed.
End with_context.
