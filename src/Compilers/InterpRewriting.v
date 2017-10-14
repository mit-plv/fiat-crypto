Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.Not.
Require Import Crypto.Util.Tactics.BreakMatch.

Section lang.
  Context {base_type}
          {op : flat_type base_type -> flat_type base_type -> Type}
          {interp_base_type : base_type -> Type}
          {interp_op : forall s d, op s d
                                   -> interp_flat_type interp_base_type s
                                   -> interp_flat_type interp_base_type d}.
  Local Notation Expr := (@Expr base_type op).
  Local Notation Interp := (@Interp base_type interp_base_type op interp_op).

  Definition packaged_expr_functionP A :=
    (fun F : Expr A -> Expr A
     => forall e',
         Wf e'
         -> Wf (F e')
            /\ forall v, Interp (F e') v = Interp e' v).
  Local Notation packaged_expr_function A :=
    (sig (packaged_expr_functionP A)).

  Definition compose {A} (f g : packaged_expr_function A)
    : packaged_expr_function A.
  Proof.
    exists (fun x => proj1_sig f (proj1_sig g x)).
    clear.
    abstract (
        destruct f as [f Hf], g as [g Hg]; cbn [proj1_sig];
        intros e' Wfe; split; [ apply Hf, Hg, Wfe | ];
        intro x; etransitivity; [ apply Hf, Hg, Wfe | apply Hg, Wfe ]
      ).
  Defined.

  Definition id_package {A} : packaged_expr_function A
    := exist (packaged_expr_functionP A)
             id
             (fun e' Wfe' => conj Wfe' (fun v => eq_refl)).

  Inductive reified_transformation :=
  | base (idx : nat)
  | transform (idx : nat) (rest : reified_transformation)
  | cond (test : bool) (iftrue iffalse : reified_transformation).
  Fixpoint denote {A}
           (ls : list (packaged_expr_function A))
           (ls' : list { x : Expr A | Wf x })
           default
           (f : reified_transformation)
    := match f with
       | base idx => proj1_sig (List.nth_default default ls' idx)
       | transform idx rest
         => proj1_sig (List.nth_default id_package ls idx)
                      (denote ls ls' default rest)
       | cond test iftrue iffalse
         => if test
            then denote ls ls' default iftrue
            else denote ls ls' default iffalse
       end.
  Fixpoint reduce (f : reified_transformation) : reified_transformation
    := match f with
       | base idx => base idx
       | transform idx rest => reduce rest
       | cond test iftrue iffalse
         => match reduce iftrue, reduce iffalse with
            | base idx0 as t, base idx1 as f
              => if nat_beq idx0 idx1
                 then base idx0
                 else cond test t f
            | t, f => cond test t f
            end
       end.
  Lemma Wf_denote A ctx es d f : Wf (@denote A ctx es d f).
  Proof.
    induction f; simpl; unfold proj1_sig; break_innermost_match; split_and; auto.
    match goal with H : _ |- _ => apply H; assumption end.
  Qed.
  Lemma Wf_denote_iff_True A ctx es d f : Wf (@denote A ctx es d f) <-> True.
  Proof. split; auto using Wf_denote. Qed.
  Lemma Interp_denote_reduce A ctx es d f
    : forall v, Interp (@denote A ctx es d f) v = Interp (@denote A nil es d (reduce f)) v.
  Proof.
    induction f; simpl; unfold proj1_sig; break_innermost_match;
      nat_beq_to_eq; subst;
        try reflexivity; auto.
    intro; rewrite <- IHf.
    match goal with H : _ |- _ => apply H, Wf_denote end.
  Qed.
End lang.

Local Ltac find ctx f :=
  lazymatch ctx with
  | (exist _ f _ :: _)%list => constr:(0)
  | (_ :: ?ctx)%list
    => let v := find ctx f in
       constr:(S v)
  end.

Local Ltac reify_transformation interp_base_type interp_op ctx es T cont :=
  let reify_transformation := reify_transformation interp_base_type interp_op in
  let ExprA := type of T in
  let packageP := lazymatch type of T with
                 | @Expr ?base_type_code ?op ?A
                   => constr:(@packaged_expr_functionP base_type_code op interp_base_type interp_op A)
                 end in
  let es := lazymatch es with
            | tt => constr:(@nil { x : ExprA | Wf x })
            | _ => es
            end in
  let ctx := lazymatch ctx with
             | tt => constr:(@nil (sig packageP))
             | _ => ctx
             end in
  lazymatch T with
  | ?f ?e
    => let ctx := lazymatch ctx with
                  | context[exist _ f _] => ctx
                  | _ => let hf := head f in
                         let fId := fresh hf in
                         let rfPf :=
                             cache_proof_with_type_by
                               (packageP f)
                               ltac:(refine (fun e Hwf
                                             => (fun Hwf'
                                                 => conj Hwf' (fun v => _)) _);
                                     [ autorewrite with reflective_interp; reflexivity
                                     | auto with wf ])
                                      fId in
                         constr:(cons (exist packageP f rfPf)
                                      ctx)
                  end in
       reify_transformation
         ctx es e
         ltac:(fun ctx es re
               => let idx := find ctx f in
                  cont ctx es (transform idx re))
  | match ?b with true => ?t | false => ?f end
    => reify_transformation
         ctx es t
         ltac:(fun ctx es rt
               => reify_transformation
                    ctx es f
                    ltac:(fun ctx es rf
                          => reify_transformation
                               ctx es t
                               ltac:(fun ctx es rt
                                     => cont ctx es (cond b rt rf))))
  | _ => let es := lazymatch es with
                   | context[exist _ T _] => es
                   | _
                     => let Hwf := lazymatch goal with
                                   | [ Hwf : Wf T |- _ ] => Hwf

                                   | _
                                     => let Hwf := fresh "Hwf" in
                                        cache_proof_with_type_by
                                          (Wf T)
                                          ltac:(idtac; solve_wf_side_condition)
                                                 Hwf
                                   end in
                        constr:(cons (exist Wf T Hwf) es)
                   end in
         let idx := find es T in
         cont ctx es (base idx)
  end.
Ltac finish_rewrite_reflective_interp_cached :=
  rewrite ?Wf_denote_iff_True;
  cbv [reduce nat_beq];
  try (rewrite Interp_denote_reduce;
       cbv [reduce nat_beq];
       cbv [denote List.nth_default List.nth_error];
       cbn [proj1_sig]).
Ltac rewrite_reflective_interp_cached_then ctx es cont :=
  let e := match goal with
           | [ |- context[@Interp _ _ _ _ _ ?e] ]
             => let test := match goal with _ => not is_var e end in
                e
           end in
  lazymatch goal with
  | [ |- context[@Interp ?base_type ?interp_base_type ?op ?interp_op _ e] ]
    => reify_transformation
         interp_base_type interp_op ctx es e
         ltac:(fun ctx es r
               => lazymatch es with
                  | cons ?default _
                    => change e with (denote ctx es default r)
                  end;
                  finish_rewrite_reflective_interp_cached;
                  cont ctx es)
  end.
Ltac rewrite_reflective_interp_cached :=
  rewrite_reflective_interp_cached_then tt tt ltac:(fun _ _ => idtac).
