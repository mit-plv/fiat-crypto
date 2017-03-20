Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics Crypto.Util.Option Crypto.Util.Sigma.
Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.NamedBase.Syntax.
Require Import Crypto.Util.Bool.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {op : forall t1 t2 tR : base_type_code, Type}
          {Name : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src1 src2 dst, op src1 src2 dst -> interp_base_type_bounds src1 -> interp_base_type_bounds src2 -> interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code)
          (cast_op : forall t1 t2 tR (opc : op t1 t2 tR), forall arg1_bs arg2_bs, op (pick_typeb _ arg1_bs) (pick_typeb _ arg2_bs) (pick_typeb _ (interp_op_bounds t1 t2 tR opc arg1_bs arg2_bs)))
          {BoundsContext : Context Name interp_base_type_bounds}
          (BoundsContextOk : ContextOk BoundsContext).

  Fixpoint mapf_cast
           (ctx : BoundsContext)
           {t} (e : exprf base_type_code op Name t)
           {struct e}
    : option { bounds : interp_base_type_bounds t
                        & exprf base_type_code op Name (pick_typeb _ bounds) }
    := match e in exprf _ _ _ t return option { bounds : interp_base_type_bounds t
                                                       & exprf base_type_code op Name (pick_typeb _ bounds) } with
       | Var t x
         => option_map
              (fun bounds => existT _ bounds (Var x))
              (lookupb (t:=t) ctx x)
       | LetIn tx n ex tC eC
         => match @mapf_cast ctx _ ex with
            | Some (existT x_bounds ex')
              => option_map
                   (fun eC' => let 'existT Cx_bounds C_expr := eC' in
                               existT _ Cx_bounds (LetIn n ex' C_expr))
                   (@mapf_cast (extendb (t:=tx) ctx n x_bounds) _ eC)
            | None => None
            end
       | BinOp t1 t2 tR o arg1 arg2
         => match @mapf_cast ctx _ arg1, @mapf_cast ctx _ arg2 with
            | Some (existT arg1_bounds arg1'),
              Some (existT arg2_bounds arg2')
              => Some (existT _
                              (interp_op_bounds _ _ _ o arg1_bounds arg2_bounds)
                              (BinOp (cast_op t1 t2 tR o arg1_bounds arg2_bounds) arg1' arg2'))
            | None, _ | _, None => None
            end
       end.

  Local Ltac handle_lookupb_step Name_dec base_type_dec :=
    let check_neq t t' :=
        first [ constr_eq t t'; fail 1
              | lazymatch goal with
                | [ H : t = t' |- _ ] => fail 1
                | [ H : t <> t' |- _ ] => fail 1
                | [ H : t = t' -> False |- _ ] => fail 1
                | _ => idtac
                end ] in
    match goal with
    | _ => progress subst
    | [ |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n ?t] ]
      => setoid_rewrite lookupb_extendb_same; [ | assumption.. ]
    | [ H : ?t = ?t' |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n ?t'] ]
      => setoid_rewrite (fun H' => lookupb_extendb_eq H' ctx n t t' H); [ | assumption.. ]
    | [ H' : ?n <> ?n' |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n' ?t'] ]
      => setoid_rewrite lookupb_extendb_different; [ | assumption.. ]
    | [ H' : ?t <> ?t' |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n ?t'] ]
      => setoid_rewrite lookupb_extendb_wrong_type; [ | assumption.. ]
    | [ |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n ?t'] ]
      => check_neq t t'; destruct (base_type_dec t t')
    | [ |- context[lookupb (extendb ?ctx ?n (t:=?t) _) ?n' ?t'] ]
      => check_neq n n'; destruct (Name_dec n n')
    | [ H : lookupb ?ctx ?n ?t = _, H' : ?t = ?t' |- context[lookupb ?ctx ?n ?t'] ]
      => rewrite (fun H'' => lookupb_eq_cast H'' ctx n _ _ H')
    | [ H : lookupb ?ctx ?n ?t = _ |- context[lookupb ?ctx ?n ?t'] ]
      => check_neq t t'; destruct (base_type_dec t t')
    | _ => progress inversion_option
    | [ H : ?x = Some _ |- context[?x] ] => rewrite H
    | [ H : ?x = None |- context[?x] ] => rewrite H
    | _ => progress simpl @option_map
    end.

  Local Arguments interpf {_} {_} {_} {_} {_} {_} _ {_} _.
  Lemma mapf_cast_correct
        {interp_base_type : base_type_code -> Type}
        (interp_op:forall src1 src2 dst : base_type_code,
            op src1 src2 dst -> interp_base_type src1 -> interp_base_type src2 -> interp_base_type dst)
        (cast_back: forall t b, interp_base_type (pick_typeb t b) -> interp_base_type t)
        {Context : Context Name interp_base_type}
        (ContextOk : ContextOk Context)
        (inbounds : forall t, interp_base_type_bounds t -> interp_base_type t -> Prop)
        (interp_op_bounds_correct:
           forall t1 t2 tR o b1 b2
             (v1 : interp_base_type t1) (v2 : interp_base_type t2)
             (H1 : inbounds t1 b1 v1) (H2 : inbounds t2 b2 v2),
             inbounds tR (interp_op_bounds t1 t2 tR o b1 b2) (interp_op t1 t2 tR o v1 v2))
        (pull_cast_back:
           forall t1 t2 tR o b1 b2
             (v1 : interp_base_type (pick_typeb t1 b1)) (v2 : interp_base_type (pick_typeb t2 b2))
             (H1 : inbounds t1 b1 (cast_back t1 b1 v1)) (H2 : inbounds t2 b2 (cast_back t2 b2 v2)),
             interp_op t1 t2 tR o (cast_back t1 b1 v1) (cast_back t2 b2 v2)
             =
             cast_back _ _ (interp_op _ _ _  (cast_op _ _ _ o b1 b2) v1 v2))
        (base_type_dec : forall t1 t2 : base_type_code, t1 = t2 \/ t1 <> t2)
        (Name_dec : forall t1 t2 : Name, t1 = t2 \/ t1 <> t2)
        {t} (e:exprf base_type_code op Name t)
    : forall
        (oldValues:Context)
        (newValues:Context)
        (varBounds:BoundsContext)
        {b} e' (He':mapf_cast varBounds e = Some (existT _ b e'))
        (Hctx:forall {t} n v,
            lookupb (t:=t) oldValues n = Some v
            -> exists b, lookupb (t:=t) varBounds n = Some b
                         /\ @inbounds _ b v
                         /\ exists v', lookupb (t:=pick_typeb t b) newValues n = Some v'
                                       /\ cast_back t b v' = v)
        r (Hr:interpf (interp_op:=interp_op) oldValues e = Some r)
        r' (Hr':interpf (interp_op:=interp_op) newValues e' = Some r')
        , @inbounds _ b r /\ cast_back _ _ r' = r.
  Proof.
    induction e; simpl interpf; simpl mapf_cast; unfold option_map; intros;
      repeat (break_match_hyps; inversion_option; inversion_sigma; simpl in *; subst).
    { destruct (Hctx _ _ _ Hr) as [b' [Hb'[Hb'v[v'[Hv' Hv'v]]]]]; clear Hctx Hr; subst.
      repeat match goal with
               [H: ?e = Some ?x, G:?e = Some ?x' |- _] =>
               pose proof (eq_trans (eq_sym G) H); clear G; inversion_option; subst
             end.
      auto. }
    { specialize (IHe1 oldValues newValues varBounds _ _ Heqo2 Hctx _ Heqo0 _ Heqo4); clear Heqo2 Heqo0 Heqo4.
      specialize (IHe2 oldValues newValues varBounds _ _ Heqo3 Hctx _ Heqo1 _ Heqo5); clear Heqo3 Heqo1 Heqo5.
      destruct_head and; subst; intuition eauto; symmetry; auto. }
    { repeat match goal with
             | [ IH : context[interpf _ ?e], H' : interpf ?ctx ?e = _ |- _ ]
               => let check_tac _ := (rewrite H' in IH) in
                  first [ specialize (IH ctx); check_tac ()
                        | specialize (fun a => IH a ctx); check_tac ()
                        | specialize (fun a b => IH a b ctx); check_tac () ]
             | [ IH : context[mapf_cast _ ?e], H' : mapf_cast ?ctx ?e = _ |- _ ]
               => let check_tac _ := (rewrite H' in IH) in
                  first [ specialize (IH ctx); check_tac ()
                        | specialize (fun a => IH a ctx); check_tac ()
                        | specialize (fun a b => IH a b ctx); check_tac () ]
             | [ H : forall x y z, Some _ = Some _ -> _ |- _ ]
               => first [ specialize (H _ _ _ eq_refl)
                        | specialize (fun x => H x _ _ eq_refl) ]
             end.
      { assert (base_type_UIP_refl : forall t (p : t = t :> base_type_code), p = eq_refl)
          by (intro; apply K_dec; auto).
        apply IHe2; clear IHe2; try reflexivity.
        intros ??? H.
        let b := fresh "b" in
        let H' := fresh "H'" in
        match goal with |- exists b0, ?v = Some b0 /\ _ => destruct v as [b|] eqn:H' end;
          [ exists b; split; [ reflexivity | ] | exfalso ];
          revert H H';
          repeat match goal with
                 | _ => handle_lookupb_step Name_dec base_type_dec
                 | _ => progress intros
                 | _ => progress destruct_head' ex
                 | _ => progress destruct_head' and
                 | _ => congruence
                 | [ H : ?x = Some ?y, H' : ?x = Some ?y' |- _ ]
                   => assert (y = y') by congruence; (subst y' || subst y)
                 | [ |- ?A /\ (exists v, Some ?k = Some v /\ @?B v) ]
                   => cut (A /\ B k); [ clear; solve [ intuition eauto ] | cbv beta ]
                 | [ |- ?A /\ (exists v, None = Some v /\ @?B v) ]
                   => exfalso
                 | [ H : ?x = ?x :> base_type_code |- _ ]
                   => pose proof (base_type_UIP_refl x H); subst H; simpl
                 | _ => solve [ auto ]
                 | _ => progress specialize_by auto
                 | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                 | [ H : forall t n v, lookupb ?ctx n = _ -> _, H' : lookupb ?ctx ?n' = _ |- _ ]
                   => specialize (H _ _ _ H')
                 end. } }
  Qed.
End language.

Require Import ZArith Lia.
Local Set Decidable Equality Schemes.
Section example.
  Inductive base_type_code :=
  | TZ
  | TW32
  | TW64.
  Lemma base_type_code_dec_or : forall t t' : base_type_code, t = t' \/ t <> t'.
  Proof. decide equality. Defined.
  Inductive op : base_type_code -> base_type_code -> base_type_code -> Type :=
  | OpMul : forall t1 t2 tR, op t1 t2 tR
  | OpSub : forall t1 t2 tR, op t1 t2 tR.
  Definition bounds (t:base_type_code) := (Z * Z)%type. (* upper bound only for now *)
  Definition interp_op_bounds (src1 src2 dst : base_type_code) (opc : op src1 src2 dst) : bounds src1 -> bounds src2 -> bounds dst
    := fun x y
       => let '(lx, ux) := x in
          let '(ly, uy) := y in
          match opc with
          | OpMul _ _ _ => let '(l, u) := (Z.min (lx * ly) (Z.min (lx * uy) (Z.min (ux * ly) (ux * uy))),
                                           Z.max (lx * ly) (Z.max (lx * uy) (Z.max (ux * ly) (ux * uy)))) in
                           if ((lx <=? 0) && (0 <=? ux)) || ((ly <=? 0) && (0 <=? uy))
                           then (Z.min 0 l, Z.max 0 u)
                           else (l, u)
          | OpSub _ _ _ => (lx - uy, ux - ly)
          end%Z%bool.
  Definition pick_typeb (t : base_type_code) (b:bounds t) : base_type_code :=
      match t with
        | TW32 => TW32
        | TW64 => let '(l, u) := b in
                  if Z.ltb u (2^32) then TW32 else TW64
        | TZ =>
          let '(l, u) := b in
          if Z.leb 0 l
          then if Z.ltb u (2^32) then TW32
               else if Z.ltb u (2^64) then TW64
                    else TZ
          else TZ
      end.

  Definition cast_op (t1 t2 tR : base_type_code) (o:op t1 t2 tR) (arg1_bs : bounds t1) (arg2_bs : bounds t2)
    : op (pick_typeb t1 arg1_bs) (pick_typeb t2 arg2_bs)
         (pick_typeb tR (interp_op_bounds t1 t2 tR o arg1_bs arg2_bs))
    := match o with
       | OpMul _ _ _ => OpMul _ _ _
       | OpSub _ _ _ => OpSub _ _ _
       end.

  Definition interp_base_type t :=
    match t with
    | TZ => Z
    | TW32 => { z | (Z.leb 0 z && Z.ltb z (2^32)%Z = true)%bool }
    | TW64 => { z | (Z.leb 0 z && Z.ltb z (2^64)%Z = true)%bool }
    end.
  Check @mapf_cast_correct base_type_code op positive bounds interp_op_bounds pick_typeb cast_op
        _ (* ctx *) _ (* ctx_ok *)
        interp_base_type.

  Definition to_Z {t:base_type_code} : interp_base_type t -> Z :=
    match t with
    | TZ => fun v => v
    | _ => fun v => proj1_sig v
    end.

  Definition of_Z (t:base_type_code) (v:Z) : interp_base_type t. refine
    match t as t return interp_base_type t with
    | TZ => v
    | TW32 => exist _ (v mod 2^32)%Z _
    | TW64 => exist _ (v mod 2^64)%Z _
    end; abstract(rewrite !Bool.andb_true_iff, !Z.leb_le, Z.ltb_lt; apply Z_mod_lt; reflexivity). Defined.

  Definition cast_back (t : base_type_code) (b : bounds t) (v:interp_base_type (pick_typeb t b))
    : interp_base_type t := of_Z _ (to_Z v).

  Definition interp_op (src1 src2 dst : base_type_code) (o:op src1 src2 dst)
             (x:interp_base_type src1) (y:interp_base_type src2) : interp_base_type dst :=
    of_Z _ (match o with
            | OpMul _ _ _ => Z.mul
            | OpSub _ _ _ => Z.sub
            end (to_Z x) (to_Z y)).

  Definition inbounds t (b:bounds t) (v:interp_base_type t)
    := let '(l, u) := b in (l <= to_Z v < u)%Z.

  Lemma interp_op_bounds_correct t1 t2 tR o b1 b2
        (v1 : interp_base_type t1) (v2 : interp_base_type t2)
        (H1 : @inbounds t1 b1 v1) (H2 : @inbounds t2 b2 v2)
    : inbounds tR (interp_op_bounds t1 t2 tR o b1 b2) (interp_op t1 t2 tR o v1 v2).
  Proof.
    destruct o; cbv [inbounds interp_op_bounds interp_op] in *;
      generalize dependent (to_Z v1); generalize dependent (to_Z v2);
        clear dependent v1; clear dependent v2;
          intros z1 H1 z2 H2; cbv [of_Z to_Z id proj1_sig] in *;
            cbv [of_Z to_Z id] in *;
            repeat match goal with
                   | _ => nia
                   | [ H : and _ _ |- _ ] => destruct H
                   | _ => progress split_andb
                   | [ H : orb _ _ = true |- _ ] => rewrite Bool.orb_true_iff in H
                   | _ => progress Z.ltb_to_lt
                   | [ H : (?a <= ?x)%Z, H' : (?x <= ?y)%Z |- _ ]
                     => lazymatch goal with
                        | [ H'' : (a <= y)%Z |- _ ] => fail
                        | _ => assert ((a <= y)%Z) by omega
                        end
                   | _ => break_innermost_match_step
                   | [ H : or _ _ |- _ ] => destruct H
                   | [ |- _ /\ _ ] => split
                   | [ |- (0 <= _ mod _)%Z ] => apply Z.mod_pos_bound; vm_compute; reflexivity
                   | [ |- (_ mod _ < _)%Z ] => eapply Z.le_lt_trans; [ apply Z.mod_le | ]
                   | _ => apply Z.min_case_strong; intros
                   end.
  Admitted.

  Local Arguments Z.pow : simpl never.
  Lemma to_Z_cast_back t (b:bounds t) (v:interp_base_type (pick_typeb t b))
    : to_Z (cast_back t b v) = to_Z v.
  Proof.
    destruct t;
      repeat (trivial;
              rewrite ?Bool.andb_true_iff, ?Z.leb_le, ?Z.ltb_lt in *;
              cbv [cast_back]; break_match; simpl in *;
              destruct_head' sig;
              rewrite ?Zmod_small by nia).
  Qed.

  Require Import Decidable.
  Lemma pull_cast_back t1 t2 tR o b1 b2
        (v1 : interp_base_type (pick_typeb t1 b1)) (v2 : interp_base_type (pick_typeb t2 b2))
        (H1 : inbounds t1 b1 (cast_back t1 b1 v1)) (H2 : inbounds t2 b2 (cast_back t2 b2 v2))
  : interp_op t1 t2 tR o (cast_back t1 b1 v1) (cast_back t2 b2 v2)
  = cast_back _ _ (interp_op _ _ _  (cast_op _ _ _ o b1 b2) v1 v2).
  Proof.
    cbv [inbounds interp_op_bounds interp_op] in *.
    cbv [cast_back pick_typeb]; rewrite !to_Z_cast_back in *.
    break_match; (* does this succeed in finite time? *)
      repeat first [ reflexivity
                   | rewrite !to_Z_cast_back in * by fail
                   | progress simpl in *
                   | progress destruct_head sig
                   | progress split_andb
                   | progress Z.ltb_to_lt
                   | rewrite !Decidable.eqsig_eq by fail
                   | progress rewrite ?Zmod_mod by fail
                   | progress Z.rewrite_mod_small
                   | rewrite !Zmod_small by solve [ nia | rewrite !Zmod_small; nia ]
                   | progress rewrite ?Bool.andb_true_iff, ?Z.leb_le, ?Z.ltb_lt in * by fail
                   | nia
                   | push_Zmod; reflexivity
                   | progress break_match_hyps ].
  Admitted.

  Lemma eq_dec_positive_or : forall p q : positive, p = q \/ p <> q.
  Proof. decide equality. Defined.

  Check @mapf_cast_correct base_type_code op positive bounds interp_op_bounds pick_typeb cast_op
        _ (* ctx *) _ (* ctx_ok *)
        interp_base_type interp_op cast_back
        _ (* ctx *) _ (* ctx_ok *)
        inbounds
        interp_op_bounds_correct
        pull_cast_back
        base_type_code_dec_or
        eq_dec_positive_or
  .
End example.
