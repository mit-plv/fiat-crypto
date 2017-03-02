Require Import Coq.Classes.Morphisms.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Section homogenous_type.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {var : base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_flat_type := (@interp_flat_type base_type_code).
  Local Notation exprf := (@exprf base_type_code op var).
  Local Notation expr := (@expr base_type_code op var).

  (** Sometimes, we want to deal with partially-interpreted
      expressions, things like [prod (exprf A) (exprf B)] rather than
      [exprf (Prod A B)], or like [prod (var A) (var B)] when we start
      with the type [Prod A B].  These convenience functions let us
      recurse on the type in only one place, and replace one kind of
      pairing operator (be it [pair] or [Pair] or anything else) with
      another kind, and simultaneously mapping a function over the
      base values (e.g., [Var] (for turning [var] into [exprf]) or
      [Const] (for turning [interp_base_type] into [exprf])). *)
  Fixpoint smart_interp_flat_map {f g}
           (h : forall x, f x -> g (Tbase x))
           (tt : g Unit)
           (pair : forall A B, g A -> g B -> g (Prod A B))
           {t}
    : interp_flat_type f t -> g t
    := match t return interp_flat_type f t -> g t with
       | Syntax.Tbase _ => h _
       | Unit => fun _ => tt
       | Prod A B => fun v => pair _ _
                                   (@smart_interp_flat_map f g h tt pair A (fst v))
                                   (@smart_interp_flat_map f g h tt pair B (snd v))
       end.
  Fixpoint smart_interp_flat_map2 {f1 f2 g}
           (h : forall x, f1 x -> f2 x -> g (Tbase x))
           (tt : g Unit)
           (pair : forall A B, g A -> g B -> g (Prod A B))
           {t}
    : interp_flat_type f1 t -> interp_flat_type f2 t -> g t
    := match t return interp_flat_type f1 t -> interp_flat_type f2 t -> g t with
       | Syntax.Tbase _ => h _
       | Unit => fun _ _ => tt
       | Prod A B => fun v1 v2 => pair _ _
                                       (@smart_interp_flat_map2 f1 f2 g h tt pair A (fst v1) (fst v2))
                                       (@smart_interp_flat_map2 f1 f2 g h tt pair B (snd v1) (snd v2))
       end.
  Definition smart_interp_map_hetero {f g g'}
             (h : forall x, f x -> g (Tbase x))
             (tt : g Unit)
             (pair : forall A B, g A -> g B -> g (Prod A B))
             (abs : forall A B, (g A -> g B) -> g' (Arrow A B))
             {t}
    : interp_type_gen_hetero g (interp_flat_type f) t -> g' t
    := match t return interp_type_gen_hetero g (interp_flat_type f) t -> g' t with
       | Arrow A B => fun v => abs _ _
                                   (fun x => @smart_interp_flat_map f g h tt pair _ (v x))
       end.
  Fixpoint SmartValf {T} (val : forall t : base_type_code, T t) t : interp_flat_type T t
    := match t return interp_flat_type T t with
       | Syntax.Tbase _ => val _
       | Unit => tt
       | Prod A B => (@SmartValf T val A, @SmartValf T val B)
       end.

  (** [SmartVar] is like [Var], except that it inserts
      pair-projections and [Pair] as necessary to handle [flat_type],
      and not just [base_type_code] *)
  Local Notation exprfb := (fun t => exprf (Tbase t)).
  Definition SmartPairf {t} : interp_flat_type exprfb t -> exprf t
    := @smart_interp_flat_map exprfb exprf (fun t x => x) TT (fun A B x y => Pair x y) t.
  Lemma SmartPairf_Pair {A B} (e1 : interp_flat_type _ A) (e2 : interp_flat_type _ B)
    : SmartPairf (t:=Prod A B) (e1, e2)%core = Pair (SmartPairf e1) (SmartPairf e2).
  Proof. reflexivity. Qed.
  Definition SmartVarf {t} : interp_flat_type var t -> exprf t
    := @smart_interp_flat_map var exprf (fun t => Var) TT (fun A B x y => Pair x y) t.
  Definition SmartVarf_Pair {A B v}
    : @SmartVarf (Prod A B) v = Pair (SmartVarf (fst v)) (SmartVarf (snd v))
    := eq_refl.
  Definition SmartVarfMap {var var'} (f : forall t, var t -> var' t) {t}
    : interp_flat_type var t -> interp_flat_type var' t
    := @smart_interp_flat_map var (interp_flat_type var') f tt (fun A B x y => pair x y) t.
  Lemma SmartVarfMap_compose {var' var'' var''' t} f g x
    : @SmartVarfMap var'' var''' g t (@SmartVarfMap var' var'' f t x)
      = @SmartVarfMap _ _ (fun t v => g t (f t v)) t x.
  Proof.
    unfold SmartVarfMap; clear; induction t; simpl; destruct_head_hnf unit; destruct_head_hnf prod;
      rewrite_hyp ?*; congruence.
  Qed.
  Lemma SmartVarfMap_id {var' t} x : @SmartVarfMap var' var' (fun _ x => x) t x = x.
  Proof.
    unfold SmartVarfMap; clear; induction t; simpl; destruct_head_hnf unit; destruct_head_hnf prod;
      rewrite_hyp ?*; congruence.
  Qed.
  Global Instance smart_interp_flat_map_Proper {f g}
    : Proper ((forall_relation (fun t => pointwise_relation _ eq))
                ==> eq
                ==> (forall_relation (fun A => forall_relation (fun B => pointwise_relation _ (pointwise_relation _ eq))))
                ==> forall_relation (fun t => eq ==> eq))
             (@smart_interp_flat_map f g).
  Proof.
    unfold forall_relation, pointwise_relation, respectful.
    intros F G HFG x y ? Q R HQR t a b ?; subst y b.
    induction t; simpl in *; auto.
    rewrite_hyp !*; reflexivity.
  Qed.
  Global Instance SmartVarfMap_Proper {var' var''}
    : Proper (forall_relation (fun t => pointwise_relation _ eq) ==> forall_relation (fun t => eq ==> eq))
             (@SmartVarfMap var' var'').
  Proof.
    repeat intro; eapply smart_interp_flat_map_Proper; trivial; repeat intro; reflexivity.
  Qed.
  Definition SmartVarfMap2 {var var' var''} (f : forall t, var t -> var' t -> var'' t) {t}
    : interp_flat_type var t -> interp_flat_type var' t -> interp_flat_type var'' t
    := @smart_interp_flat_map2 var var' (interp_flat_type var'') f tt (fun A B x y => pair x y) t.
  Lemma SmartVarfMap2_fst_arg {var' var''} {t}
        (x : interp_flat_type var' t)
        (y : interp_flat_type var'' t)
    : SmartVarfMap2 (fun _ a b => a) x y = x.
  Proof.
    unfold SmartVarfMap2; clear; induction t; simpl; destruct_head_hnf unit; destruct_head_hnf prod;
      rewrite_hyp ?*; congruence.
  Qed.
  Lemma SmartVarfMap2_snd_arg {var' var''} {t}
        (x : interp_flat_type var' t)
        (y : interp_flat_type var'' t)
    : SmartVarfMap2 (fun _ a b => b) x y = y.
  Proof.
    unfold SmartVarfMap2; clear; induction t; simpl; destruct_head_hnf unit; destruct_head_hnf prod;
      rewrite_hyp ?*; congruence.
  Qed.
  Definition SmartVarfTypeMap {var} (f : forall t, var t -> Type) {t}
    : interp_flat_type var t -> Type
    := @smart_interp_flat_map var (fun _ => Type) f unit (fun _ _ P Q => P * Q)%type t.
  Definition SmartVarfPropMap {var} (f : forall t, var t -> Prop) {t}
    : interp_flat_type var t -> Prop
    := @smart_interp_flat_map var (fun _ => Prop) f True (fun _ _ P Q => P /\ Q)%type t.
  Definition SmartVarfTypeMap2 {var var'} (f : forall t, var t -> var' t -> Type) {t}
    : interp_flat_type var t -> interp_flat_type var' t -> Type
    := @smart_interp_flat_map2 var var' (fun _ => Type) f unit (fun _ _ P Q => P * Q)%type t.
  Definition SmartVarfPropMap2 {var var'} (f : forall t, var t -> var' t -> Prop) {t}
    : interp_flat_type var t -> interp_flat_type var' t -> Prop
    := @smart_interp_flat_map2 var var' (fun _ => Prop) f True (fun _ _ P Q => P /\ Q)%type t.
  Definition SmartFlatTypeMap {var'} (f : forall t, var' t -> base_type_code) {t}
    : interp_flat_type var' t -> flat_type
    := @smart_interp_flat_map var' (fun _ => flat_type) (fun t v => Tbase (f t v)) Unit (fun _ _ => Prod) t.
  Definition SmartFlatTypeUnMap (t : flat_type)
    : interp_flat_type (fun _ => base_type_code) t
    := SmartValf (fun t => t) t.
  Fixpoint SmartFlatTypeMapInterp {var' var''} (f : forall t, var' t -> base_type_code)
           (fv : forall t v, var'' (f t v)) t {struct t}
    : forall v, interp_flat_type var'' (SmartFlatTypeMap f (t:=t) v)
    := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap f (t:=t) v) with
       | Syntax.Tbase x => fv _
       | Unit => fun v => v
       | Prod A B => fun xy => (@SmartFlatTypeMapInterp _ _ f fv A (fst xy),
                                @SmartFlatTypeMapInterp _ _ f fv B (snd xy))
       end.
  Fixpoint SmartFlatTypeMapUnInterp var' var'' var''' (f : forall t, var' t -> base_type_code)
           (fv : forall t (v : var' t), var'' (f t v) -> var''' t)
           {t} {struct t}
    : forall v, interp_flat_type var'' (SmartFlatTypeMap f (t:=t) v)
                -> interp_flat_type var''' t
    := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap f (t:=t) v)
                                -> interp_flat_type var''' t with
       | Syntax.Tbase x => fv _
       | Unit => fun _ v => v
       | Prod A B => fun v xy => (@SmartFlatTypeMapUnInterp _ _ _ f fv A _ (fst xy),
                                  @SmartFlatTypeMapUnInterp _ _ _ f fv B _ (snd xy))
       end.
  Definition SmartVarMap {var' var''} (f : forall t, var' t -> var'' t) (f' : forall t, var'' t -> var' t) {t}
    : interp_type_gen (interp_flat_type var') t -> interp_type_gen (interp_flat_type var'') t
    := match t return interp_type_gen (interp_flat_type var') t -> interp_type_gen (interp_flat_type var'') t with
       | Arrow src dst => fun F x => SmartVarfMap f (F (SmartVarfMap f' x))
       end.
  Lemma SmartVarMap_id {var' t} x v : @SmartVarMap var' var' (fun _ x => x) (fun _ x => x) t x v = x v.
  Proof. destruct t; simpl; rewrite !SmartVarfMap_id; reflexivity. Qed.
  Definition SmartVarVarf {t} : interp_flat_type var t -> interp_flat_type exprfb t
    := SmartVarfMap (fun t => Var).
End homogenous_type.

Global Arguments SmartVarf {_ _ _ _} _.
Global Arguments SmartPairf {_ _ _ t} _.
Global Arguments SmartValf {_} T _ t.
Global Arguments SmartVarVarf {_ _ _ _} _.
Global Arguments SmartVarfMap {_ _ _} _ {!_} _ / .
Global Arguments SmartVarfMap2 {_ _ _ _} _ {!t} _ _ / .
Global Arguments SmartVarfTypeMap {_ _} _ {_} _.
Global Arguments SmartVarfPropMap {_ _} _ {_} _.
Global Arguments SmartVarfTypeMap2 {_ _ _} _ {t} _ _.
Global Arguments SmartVarfPropMap2 {_ _ _} _ {t} _ _.
Global Arguments SmartFlatTypeMap {_ _} _ {_} _.
Global Arguments SmartFlatTypeUnMap {_} _.
Global Arguments SmartFlatTypeMapInterp {_ _ _ _} _ {_} _.
Global Arguments SmartFlatTypeMapUnInterp {_ _ _ _ _} fv {_ _} _.
Global Arguments SmartVarMap {_ _ _} _ _ {!_} _ / _.

Section hetero_type.
  Fixpoint flatten_flat_type {base_type_code} (t : flat_type (flat_type base_type_code)) : flat_type base_type_code
    := match t with
       | Tbase T => T
       | Unit => Unit
       | Prod A B => Prod (@flatten_flat_type _ A) (@flatten_flat_type _ B)
       end.

  Section smart_flat_type_map2.
    Context {base_type_code1 base_type_code2 : Type}.

    Definition SmartFlatTypeMap2 {var' : base_type_code1 -> Type} (f : forall t, var' t -> flat_type base_type_code2) {t}
      : interp_flat_type var' t -> flat_type base_type_code2
      := @smart_interp_flat_map base_type_code1 var' (fun _ => flat_type base_type_code2) f Unit (fun _ _ => Prod) t.
    Fixpoint SmartFlatTypeMapInterp2 {var' var''} (f : forall t, var' t -> flat_type base_type_code2)
             (fv : forall t v, interp_flat_type var'' (f t v)) t {struct t}
      : forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
      := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v) with
         | Tbase x => fv _
         | Unit => fun v => v
         | Prod A B => fun xy => (@SmartFlatTypeMapInterp2 _ _ f fv A (fst xy),
                                  @SmartFlatTypeMapInterp2 _ _ f fv B (snd xy))
         end.
    Fixpoint SmartFlatTypeMapUnInterp2 var' var'' var''' (f : forall t, var' t -> flat_type base_type_code2)
             (fv : forall t (v : var' t), interp_flat_type var'' (f t v) -> var''' t)
             {t} {struct t}
      : forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
                  -> interp_flat_type var''' t
      := match t return forall v, interp_flat_type var'' (SmartFlatTypeMap2 f (t:=t) v)
                                  -> interp_flat_type var''' t with
         | Tbase x => fv _
         | Unit => fun _ v => v
         | Prod A B => fun v xy => (@SmartFlatTypeMapUnInterp2 _ _ _ f fv A _ (fst xy),
                                    @SmartFlatTypeMapUnInterp2 _ _ _ f fv B _ (snd xy))
         end.
    Fixpoint SmartFlatTypeMap2Interp2 {var' var'' var'''} (f : forall t, var' t -> flat_type base_type_code2)
             (fv : forall t v, var'' t -> interp_flat_type var''' (f t v)) t {struct t}
      : forall v, interp_flat_type var'' t -> interp_flat_type var''' (SmartFlatTypeMap2 f (t:=t) v)
      := match t return forall v, interp_flat_type var'' t -> interp_flat_type var''' (SmartFlatTypeMap2 f (t:=t) v) with
         | Tbase x => fv _
         | Unit => fun v _ => v
         | Prod A B => fun xy x'y' => (@SmartFlatTypeMap2Interp2 _ _ _ f fv A (fst xy) (fst x'y'),
                                       @SmartFlatTypeMap2Interp2 _ _ _ f fv B (snd xy) (snd x'y'))
         end.

    Lemma SmartFlatTypeMapUnInterp2_SmartFlatTypeMap2Interp2
          var' var'' var'''
          (f : forall t, var' t -> flat_type base_type_code2)
          (fv : forall t (v : var' t), interp_flat_type var'' (f t v) -> var''' t)
          (gv : forall t v, var''' t -> interp_flat_type var'' (f t v))
          {t} v
          (e : interp_flat_type var''' t)
      : @SmartFlatTypeMapUnInterp2
          _ _ _ f fv t v
          (@SmartFlatTypeMap2Interp2
             _ _ _ f gv t v e)
        = SmartVarfMap2 (fun t v e => fv t v (gv t v e)) v e.
    Proof.
      induction t; simpl in *; destruct_head' unit;
        rewrite_hyp ?*; reflexivity.
    Qed.
  End smart_flat_type_map2.
End hetero_type.

Global Arguments SmartFlatTypeMap2 {_ _ _} _ {!_} _ / .
Global Arguments SmartFlatTypeMapInterp2 {_ _ _ _ _} fv {_} _.
Global Arguments SmartFlatTypeMap2Interp2 {_ _ _ _ _ _} fv {t} v _.
Global Arguments SmartFlatTypeMapUnInterp2 {_ _ _ _ _ _} fv {_ _} _.
