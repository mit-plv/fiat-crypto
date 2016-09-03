Require Import Coq.Arith.Arith Coq.Logic.Eqdep_dec.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Notations Crypto.Util.Tactics Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod.

Inductive pointed_Prop := trivial | inject (_ : Prop).
Definition and_pointed_Prop (x y : pointed_Prop) : pointed_Prop
  := match x, y with
     | trivial, trivial => trivial
     | trivial, inject p => inject p
     | inject p, trivial => inject p
     | inject p, inject q => inject (p /\ q)
     end.
Definition to_prop (x : pointed_Prop) : Prop
  := match x with
     | trivial => True
     | inject p => p
     end.

Local Infix "/\" := and_pointed_Prop : type_scope.

Definition f_equal2 {A1 A2 B} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2} (H : x1 = y1)
  := match H in (_ = y) return (x2 = y2 -> f x1 x2 = f y y2) with
     | eq_refl =>
       fun H0 : x2 = y2 =>
         match H0 in (_ = y) return (f x1 x2 = f x1 y) with
         | eq_refl => eq_refl
         end
     end.

Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (base_type_eq_semidec_transparent : forall t1 t2 : base_type_code, option (t1 = t2)).
  Context (base_type_eq_semidec_is_dec : forall t1 t2, base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (op_beq : forall t1 tR, op t1 tR -> op t1 tR -> option pointed_Prop).
  Context (op_beq_bl : forall t1 tR x y, match op_beq t1 tR x y with
                                    | Some p => to_prop p
                                    | _ => False
                                    end -> x = y).
  Context {var1 var2 : base_type_code -> Type}.

  Local Notation eP := (fun t => var1 (fst t) * var2 (snd t))%type (only parsing).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op).

  (*Fixpoint eq_interp_flat_type (t1 t2 : flat_type)
    : interp_flat_type t1 -> interp_flat_type t2 -> option pointed_Prop
    := match t1, t2 return interp_flat_type t1 -> interp_flat_type t2 -> option _ with
       | Prod A B, Prod A' B'
         => fun x y => match @eq_interp_flat_type A A' (fst x) (fst y),
                         @eq_interp_flat_type B B' (snd x) (snd y) with
                   | Some p, Some q => Some (p /\ q)
                   | _, _ => None
                   end
       | Prod _ _, _ => fun _ _ => None
       | Syntax.Tbase t1, Syntax.Tbase t2
         => fun x y => base_type_eq_and_cast t1 t2 x y (*Some (exists pf : t1 = t2, eq_rect _ interp_base_type x _ pf = y)*)
       | Syntax.Tbase _, _ => fun _ _ => None
       end.*)
  Fixpoint flat_type_eq_semidec_transparent (t1 t2 : flat_type) : option (t1 = t2)
    := match t1, t2 return option (t1 = t2) with
       | Syntax.Tbase t1, Syntax.Tbase t2
         => option_map (@f_equal _ _ Tbase _ _)
                      (base_type_eq_semidec_transparent t1 t2)
       | Syntax.Tbase _, _ => None
       | Prod A B, Prod A' B'
         => match flat_type_eq_semidec_transparent A A', flat_type_eq_semidec_transparent B B' with
           | Some p, Some q => Some (f_equal2 Prod p q)
           | _, _ => None
           end
       | Prod _ _, _ => None
       end.
  Definition op_beq' t1 tR t1' tR' (x : op t1 tR) (y : op t1' tR') : option pointed_Prop
    := match flat_type_eq_semidec_transparent t1 t1', flat_type_eq_semidec_transparent tR tR' with
       | Some p, Some q
         => match p in (_ = t1'), q in (_ = tR') return op t1' tR' -> _ with
           | eq_refl, eq_refl => fun y => op_beq _ _ x y
           end y
       | _, _ => None
       end.

  Definition eq_type_and_var : sigT eP -> sigT eP -> option pointed_Prop
    := fun x y =>
         let 'existT (t1, t2) (a, b) := x in
         let 'existT (t1', t2') (a', b') := y in
         match base_type_eq_semidec_transparent t1 t1', base_type_eq_semidec_transparent t2 t2' with
         | Some p, Some q
           => Some (inject (and (eq_rect _ var1 a _ p = a') (eq_rect _ var2 b _ q = b')))
         | _, _ => None
         end.


  Definition duplicate_type (ls : list (sigT (fun t => var1 t * var2 t)%type)) : list (sigT eP)
    := List.map (fun v => existT eP (projT1 v, projT1 v) (projT2 v)) ls.

  Lemma duplicate_type_app ls ls'
    : (duplicate_type (ls ++ ls') = duplicate_type ls ++ duplicate_type ls')%list.
  Proof. apply List.map_app. Qed.
  Lemma duplicate_type_length ls
    : List.length (duplicate_type ls) = List.length ls.
  Proof. apply List.map_length. Qed.
  (** TODO: Clean up this proof *)
  Lemma base_type_eq_dec : forall t1 t2 : base_type_code, {t1 = t2} + {t1 <> t2}.
  Proof.
    intros t1 t2; destruct (base_type_eq_semidec_transparent t1 t2) eqn:H;
      [ left; assumption | right; auto using base_type_eq_semidec_is_dec ].
  Qed.
  Lemma duplicae_type_in t v ls
    : List.In (existT _ (t, t) v) (duplicate_type ls) -> List.In (existT _ t v) ls.
  Proof.
    unfold duplicate_type; intro H.
    apply List.in_map_iff in H.
    destruct H as [ [t' ?] [? ?] ].
    simpl in *.
    inversion_sigma; subst.
    match goal with H : _ |- _ => generalize (path_prod_eta H) end.
    let x := match goal with |- ?x = _ -> _ => x end in
    generalize (fst_path x); generalize (snd_path x); simpl.
    intro; subst; intro H'; intros; subst.
    assert (H' = eq_refl) by apply UIP_dec, base_type_eq_dec.
    subst; simpl; assumption.
  Qed.
  Lemma duplicate_type_not_in G t t0 v (H : base_type_eq_semidec_transparent t t0 = None)
    : ~List.In (existT _ (t, t0) v) (duplicate_type G).
  Proof.
    apply base_type_eq_semidec_is_dec in H.
    clear -H.
    intro H'.
    induction G as [|? ? IHG]; simpl in *; try tauto.
    destruct H'; intuition eauto; congruence.
  Qed.

  Definition preflatten_binding_list2 t1 t2 : option (forall (x : interp_flat_type_gen var1 t1) (y : interp_flat_type_gen var2 t2), list (sigT (fun t => var1 t * var2 t)%type))
    := match flat_type_eq_semidec_transparent t1 t2 with
       | Some p
         => Some (fun x y
                 => let x := eq_rect _ (interp_flat_type_gen var1) x _ p in
                   flatten_binding_list base_type_code x y)
       | None => None
       end.
  Definition flatten_binding_list2 t1 t2 : option (forall (x : interp_flat_type_gen var1 t1) (y : interp_flat_type_gen var2 t2), list (sigT eP))
    := option_map (fun f x y => duplicate_type (f x y)) (preflatten_binding_list2 t1 t2).
  Fixpoint natize_interp_flat_type_gen {var t} (base : nat) (v : interp_flat_type_gen var t) {struct t}
    : nat * interp_flat_type_gen (fun t : base_type_code => nat * var t)%type t
    := match t return interp_flat_type_gen var t -> nat * interp_flat_type_gen _ t with
       | Prod A B => fun v => let ret := @natize_interp_flat_type_gen _ B base (snd v) in
                          let base := fst ret in
                          let b := snd ret in
                          let ret := @natize_interp_flat_type_gen _ A base (fst v) in
                          let base := fst ret in
                          let a := snd ret in
                          (base, (a, b))
       | Syntax.Tbase t => fun v => (S base, (base, v))
       end v.
  Lemma length_natize_interp_flat_type_gen1 {t} (base : nat) (v1 : interp_flat_type_gen var1 t) (v2 : interp_flat_type_gen var2 t)
    : fst (natize_interp_flat_type_gen base v1) = length (flatten_binding_list base_type_code v1 v2) + base.
  Proof.
    revert base; induction t; simpl; [ reflexivity | ].
    intros; rewrite List.app_length, <- plus_assoc.
    rewrite_hyp <- ?*; reflexivity.
  Qed.
  Lemma length_natize_interp_flat_type_gen2 {t} (base : nat) (v1 : interp_flat_type_gen var1 t) (v2 : interp_flat_type_gen var2 t)
    : fst (natize_interp_flat_type_gen base v2) = length (flatten_binding_list base_type_code v1 v2) + base.
  Proof.
    revert base; induction t; simpl; [ reflexivity | ].
    intros; rewrite List.app_length, <- plus_assoc.
    rewrite_hyp <- ?*; reflexivity.
  Qed.

  Fixpoint unnatize_exprf {var t} (base : nat) (e : @exprf (fun t => nat * var t)%type t) : @exprf var t
    := match e in @Syntax.exprf _ _ _ _ t return exprf t with
       | Const _ x => Const x
       | Var _ x => Var (snd x)
       | Op _ _ op args => Op op (@unnatize_exprf _ _ base args)
       | Let _ ex _ eC => Let (@unnatize_exprf _ _ base ex) (fun x => let v := natize_interp_flat_type_gen base x in
                                                                  @unnatize_exprf _ _ (fst v) (eC (snd v)))
       | Pair _ x _ y => Pair (@unnatize_exprf _ _ base x) (@unnatize_exprf _ _ base y)
       end.

  Fixpoint reflect_wffT (G : list (sigT (fun t => var1 (fst t) * var2 (snd t))%type))
           {t1 t2 : flat_type}
           (e1 : @exprf (fun t => nat * var1 t)%type t1) (e2 : @exprf (fun t => nat * var2 t)%type t2)
           {struct e1}
    : option pointed_Prop
    := match e1, e2 return option _ with
       | Const t0 x, Const t1 y
         => match flat_type_eq_semidec_transparent t0 t1 with
           | Some p => Some (inject (eq_rect _ interp_flat_type x _ p = y))
           | None => None
           end
       | Const _ _, _ => None
       | Var t0 x, Var t1 y
         => match Nat.eqb (fst x) (fst y), List.nth_error G (List.length G - S (fst x)) with
           | true, Some v => eq_type_and_var v (existT _ (t0, t1) (snd x, snd y))
           | _, _ => None
           end
       | Var _ _, _ => None
       | Op t1 tR op args, Op t1' tR' op' args'
         => match @reflect_wffT G t1 t1' args args', op_beq' t1 tR t1' tR' op op' with
           | Some p, Some q => Some (p /\ q)
           | _, _ => None
           end
       | Op _ _ _ _, _ => None
       | Let tx ex tC eC, Let tx' ex' tC' eC'
         => match @reflect_wffT G tx tx' ex ex', @flatten_binding_list2 tx tx', flat_type_eq_semidec_transparent tC tC' with
           | Some p, Some G0, Some _
             => Some (p /\ inject (forall (x : interp_flat_type_gen var1 tx) (x' : interp_flat_type_gen var2 tx'),
                                    match @reflect_wffT (G0 x x' ++ G)%list _ _
                                                       (eC (snd (natize_interp_flat_type_gen (List.length G) x)))
                                                       (eC' (snd (natize_interp_flat_type_gen (List.length G) x'))) with
                                    | Some p => to_prop p
                                    | None => False
                                    end))
           | _, _, _ => None
           end
       | Let _ _ _ _, _ => None
       | Pair tx ex ty ey, Pair tx' ex' ty' ey'
         => match @reflect_wffT G tx tx' ex ex', @reflect_wffT G ty ty' ey ey' with
           | Some p, Some q => Some (p /\ q)
           | _, _ => None
           end
       | Pair _ _ _ _, _ => None
       end.

  Local Ltac handle_op_beq_correct :=
    repeat match goal with
           | [ H : op_beq ?t1 ?tR ?x ?y = _ |- _ ]
             => let H' := fresh in
               pose proof (op_beq_bl t1 tR x y) as H'; rewrite H in H'; clear H
           end.
  Local Ltac t_step :=
    match goal with
    | _ => progress unfold eq_type_and_var, op_beq', flatten_binding_list2, preflatten_binding_list2, option_map in *
    | _ => progress simpl in *
    | _ => progress break_match
    | _ => progress subst
    | _ => progress inversion_option
    | _ => congruence
    | _ => tauto
    | _ => progress intros
    | _ => progress handle_op_beq_correct
    | _ => progress specialize_by tauto
    | [ H : forall x x', _ |- wff _ _ _ (flatten_binding_list _ ?x1 ?x2 ++ _)%list _ _ ]
      => specialize (H x1 x2)
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : context[duplicate_type (_ ++ _)%list] |- _ ]
      => rewrite duplicate_type_app in H
    | [ H : context[List.length (duplicate_type _)] |- _ ]
      => rewrite duplicate_type_length in H
    | [ H : context[List.length (_ ++ _)%list] |- _ ]
      => rewrite List.app_length in H
    | [ |- wff _ _ _ _ (unnatize_exprf (fst _) _) (unnatize_exprf (fst _) _) ]
      => erewrite length_natize_interp_flat_type_gen1, length_natize_interp_flat_type_gen2; eassumption
    | [ H : base_type_eq_semidec_transparent _ _ = None |- False ] => eapply duplicate_type_not_in; eassumption
    | [ H : List.nth_error _ _ = Some _ |- _ ] => apply List.nth_error_In in H
    | [ H : List.In _ (duplicate_type _) |- _ ] => apply duplicae_type_in in H
    | [ H : context[match _ with _ => _ end] |- _ ] => revert H; progress break_match
    | [ H : inject _ = inject _ |- _ ] => inversion H; clear H
    | [ |- wff _ _ _ _ _ _ ] => constructor
    | _ => progress unfold and_pointed_Prop in *
    end.
  Local Ltac t := repeat t_step.
  Fixpoint reflect_wff (G : list (sigT (fun t => var1 t * var2 t)%type))
           {t1 t2 : flat_type}
           (e1 : @exprf (fun t => nat * var1 t)%type t1) (e2 : @exprf (fun t => nat * var2 t)%type t2)
           {struct e1}
    : match reflect_wffT (duplicate_type G) e1 e2 with
      | Some p => to_prop p
      | None => False
      end
      -> match flat_type_eq_semidec_transparent t1 t2 with
        | Some p => @wff base_type_code interp_base_type op var1 var2 G t2 (eq_rect _ exprf (unnatize_exprf (List.length G) e1) _ p) (unnatize_exprf (List.length G) e2)
        | None => False
        end.
  Proof.
    destruct e1 as [ | | ? ? ? args | tx ex tC eC | ? ex ? ey ],
                   e2 as [ | | ? ? ? args' | tx' ex' tC' eC' | ? ex' ? ey' ]; simpl; try solve [ intros [] ];
      [ clear reflect_wff
      | clear reflect_wff
      | specialize (reflect_wff G _ _ args args')
      | pose proof (reflect_wff G _ _ ex ex');
        pose proof (fun x x'
                    => match preflatten_binding_list2 tx tx' as v return match v with Some _ => _ | None => True end with
                      | Some G0
                        => reflect_wff
                            (G0 x x' ++ G)%list _ _
                            (eC (snd (natize_interp_flat_type_gen (length (duplicate_type G)) x)))
                            (eC' (snd (natize_interp_flat_type_gen (length (duplicate_type G)) x')))
                      | None => I
                      end);
        clear reflect_wff
      | pose proof (reflect_wff G _ _ ex ex'); pose proof (reflect_wff G _ _ ey ey'); clear reflect_wff ].
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
  Qed.
End language.
