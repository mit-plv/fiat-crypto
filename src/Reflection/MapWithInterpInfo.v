Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (new_type : forall t, interp_base_type t -> base_type_code)
          (transfer_constant : forall t v, interp_base_type (new_type t v))
          (transfer_op
           : forall src dst (opc : op src dst)
                    (src' : interp_flat_type interp_base_type src),
              op (SmartFlatTypeMap new_type src')
                 (SmartFlatTypeMap new_type (interp_op src dst opc src'))).
  Axiom admit : forall {T}, T.
  Section with_var.
    Context {ovar : base_type_code -> Type}.
    Local Notation ivar t := { v : interp_base_type t & ovar (new_type t v) } (only parsing).
    Local Notation ivarf := (fun t => ivar t).

    Fixpoint mapf_interp
             {t} (e : @exprf base_type_code interp_base_type op ivarf t)
      : { val : interp_flat_type interp_base_type t & @exprf base_type_code interp_base_type op ovar (SmartFlatTypeMap new_type val) }.
    Proof.
      refine (match e in exprf _ _ _ t
                    return { val : interp_flat_type _ t & _ } with
              | Const tx x
                => existT _ x (Const (SmartFlatTypeMapInterp transfer_constant x))
              | Var _ x
                => existT _ (projT1 x) (Var admit (* need ≈ CSE / lookup here *))
              | Op _ _ op args
                => let mapf_interp_args := @mapf_interp _ args in
                   existT
                     _
                     (interp_op _ _ op (projT1 mapf_interp_args))
                     (Op (transfer_op _ _ op _) (projT2 mapf_interp_args))
              | LetIn _ ex _ eC
                => let mapf_interp_ex := @mapf_interp _ ex in
                   let mapf_interp_eC := fun v => @mapf_interp _ (eC v) in
                   let impossible1 := admit in
                   existT
                     _
                     impossible1 (* This is impossible; we need a second expression which lines up nicely here *)
                     (LetIn
                        (projT2 mapf_interp_ex)
                        (fun v => let v' : interp_flat_type ivarf _ := admit in
                                  let impossible : projT1 (mapf_interp_eC v') = impossible1 := admit in
                                  match impossible in _ = y
                                        return exprf _ _ _ (SmartFlatTypeMap new_type y)
                                  with
                                  | eq_refl => projT2 (mapf_interp_eC v')
                                  end))
              | Pair _ ex _ ey
                => let mapf_interp_ex := @mapf_interp _ ex in
                   let mapf_interp_ey := @mapf_interp _ ey in
                   existT
                     _
                     (projT1 mapf_interp_ex, projT1 mapf_interp_ey)%core
                     (Pair (projT2 mapf_interp_ex) (projT2 mapf_interp_ey))
              end).
    Defined.

    Fixpoint mapf_interp'
             {t1} (e1 : @exprf base_type_code interp_base_type op ivarf t1)
             {t2} (e2 : @exprf base_type_code interp_base_type op interp_base_type t2)
             G
             (wf : { pf : t2 = t1 | wff G e1 (eq_rect _ (exprf _ _ _) e2 _ pf) })
             {struct e1}
      : @exprf base_type_code interp_base_type op ovar (SmartFlatTypeMap new_type (interpf interp_op e2)).
    Proof.
      Local Ltac t wf mapf_interp' invert_wff_ex :=
        let mytac := fun _
                     => (try clear mapf_interp';
                         try clear invert_wff_ex;
                         repeat match goal with
                                | [ H : ex _ |- _ ] => destruct H
                                | [ H : sig _ |- _ ] => destruct H
                                | [ H : and _ _ |- _ ] => destruct H
                                | [ |- ?x = ?x ] => reflexivity
                                | _ => progress subst
                                | _ => progress simpl in *
                                | _ => progress inversion_prod
                                | _ => progress inversion_option
                                | _ => progress inversion_wff
                                | [ H : Pair _ _ = _ |- _ ]
                                  => apply (f_equal invert_Pair) in H
                                | [ H : LetIn _ _ = _ |- _ ]
                                  => apply (f_equal invert_LetIn) in H
                                | [ |- exists pf : ?x = ?x, _ ] => exists eq_refl
                                | [ |- { pf : ?x = ?x | _ } ] => exists eq_refl
                                | _ => assumption
                                | [ H : Prod ?A ?B = Prod ?A' ?B' |- _ ]
                                  => let A'' := fresh A' in (* TODO: Find a better way to do this *)
                                     let B'' := fresh B' in
                                     revert dependent H; intro H; move H at top;
                                     revert dependent B'; intros B'' H; move H at top;
                                     revert dependent A'; intros A'' H; move H at top;
                                     refine (match H with eq_refl => _ end); clear A'' B'' H;
                                     intros
                                | [ H : Tbase ?A = Tbase ?A' |- _ ]
                                  => let A'' := fresh A' in (* TODO: Find a better way to do this *)
                                     revert dependent H; intro H; move H at top;
                                     revert dependent A'; intros A'' H; move H at top;
                                     refine (match H with eq_refl => _ end); clear A'' H;
                                     intros
                                | _ => solve [ auto with nocore ]
                                end) in
        lazymatch goal with
        | [ |- False ]
          => clear -wf;
             abstract (
                 destruct wf as [pf H]; (subst || inversion pf); simpl @eq_rect in *;
                 clear -H; inversion H
               )
        | [ |- sig _ ] => mytac ()
        | [ |- ex _ ] => mytac ()
        | [ |- _ = _ ] => mytac ()
        | _ => idtac
        end.
      refine (match e1 in exprf _ _ _ t1, e2 in exprf _ _ _ t2
                    return { pf : t2 = t1 | wff _ e1 (eq_rect _ _ e2 _ pf) } -> exprf _ _ _ (SmartFlatTypeMap _ (interpf _ e2)) with
              | Const tx1 x1, Const tx2 x2
                => fun wf => Const (SmartFlatTypeMapInterp transfer_constant _)
              | Var _ x1, Var _ x2
                => fun wf => Var admit (* need something ≈ CSE here? *)
              | Op _ _ op1 args1, Op _ _ op2 args2
                => fun wf
                   => let invert_wff := _ in
                      let mapf_interp'_args := @mapf_interp' _ args1 _ args2 G invert_wff in
                      Op
                        (transfer_op _ _ op2 _)
                        mapf_interp'_args
              | LetIn _ ex1 _ eC1, LetIn _ ex2 _ eC2
                => fun wf
                   => let invert_wff_ex := _ in
                      let invert_wff_eC := _ in
                      let mapf_interp'_ex := @mapf_interp' _ ex1 _ ex2 G invert_wff_ex in
                      let mapf_interp'_eC := fun v1 v2 (pf : _ = _) => @mapf_interp' _ (eC1 v1) _ (eC2 v2) (flatten_binding_list base_type_code v1 (eq_rect _ _ v2 _ pf) ++ G)%list (invert_wff_eC v1 v2 pf) in
                      LetIn
                        mapf_interp'_ex
                        (fun v => let v1 := _ in
                                  let v2 := _ in
                                  let pf := _ in
                                  mapf_interp'_eC v1 v2 pf)
              | Pair _ ex1 _ ey1, Pair _ ex2 _ ey2
                => fun wf
                   => let invert_wff_ex := _ in
                      let invert_wff_ey := _ in
                      let mapf_interp'_ex := @mapf_interp' _ ex1 _ ex2 G invert_wff_ex in
                      let mapf_interp'_ey := @mapf_interp' _ ey1 _ ey2 G invert_wff_ey in
                      Pair mapf_interp'_ex mapf_interp'_ey
              | Const _ _, _
              | Var _ _, _
              | Op _ _ _ _, _
              | LetIn _ _ _ _, _
              | Pair _ _ _ _, _
                => fun wf => match _ : False with end
              end wf);
        t wf mapf_interp' invert_wff_ex.
      Grab Existential Variables.
      { t wf mapf_interp' invert_wff_ex. }
      { repeat match goal with
               | [ H := _ |- _ ] => clearbody H
               | [ H : ex _ |- _ ] => destruct H
               | [ H : sig _ |- _ ] => destruct H
               | _ => progress subst
               | _ => progress simpl in *
               end.
        clear -v.
        refine (SmartFlatTypeMapUnInterp
                  (fun t x (p : ovar (new_type t x)) => existT _ x p)
                  v). }
      { intros; t wf (@mapf_interp') invert_wff_ex.
        match goal with
        | [ H : ?x = ?x |- _ ] => assert (eq_refl = H) by exact admit; subst (* XXX TODO: FIXME *)
        end.
        simpl in *; auto. }
      { t wf mapf_interp' invert_wff_ex. }
    Defined.

    (*
    Fixpoint mapf_interp {t} (e : @exprf base_type_code interp_base_type1 op var t)
      : @exprf base_type_code interp_base_type2 op var t
      := match e in exprf _ _ _ t return exprf _ _ _ t with
         | Const tx x => Const (mapf_interp_flat_type f x)
         | Var _ x => Var x
         | Op _ _ op args => Op op (@mapf_interp _ args)
         | LetIn _ ex _ eC => LetIn (@mapf_interp _ ex) (fun x => @mapf_interp _ (eC x))
         | Pair _ ex _ ey => Pair (@mapf_interp _ ex) (@mapf_interp _ ey)
         end.

    Fixpoint map_interp {t} (e : @expr base_type_code interp_base_type1 op var t)
      : @expr base_type_code interp_base_type2 op var t
      := match e in expr _ _ _ t return expr _ _ _ t with
         | Return _ x => Return (mapf_interp x)
         | Abs _ _ f => Abs (fun x => @map_interp _ (f x))
         end.*)
  End with_var.

  (*Definition MapInterp {t} (e : @Expr base_type_code interp_base_type1 op t)
    : @Expr base_type_code interp_base_type2 op t
    := fun var => map_interp (e _).*)
End language.
(*Global Arguments mapf_interp {_ _ _ _} f {_ t} e.
Global Arguments map_interp {_ _ _ _} f {_ t} e.
Global Arguments MapInterp {_ _ _ _} f {t} e _.*)
