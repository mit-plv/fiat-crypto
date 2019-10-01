Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Language.Pre.
Require Import Crypto.Language.Language.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.DebugPrint.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.HProp.
Import Coq.Lists.List ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.
Export Language.Pre.
Export Language.

Import EqNotations.
Module Compilers.
  Export Language.Pre.
  Export Language.Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.

  Inductive base := Z | bool | nat | zrange. (* Not Variant because COQBUG(https://github.com/coq/coq/issues/7738) *)
  Notation base_type := (@base.type base).

  Global Instance baseHasNat : base.type.BaseTypeHasNatT base := nat.
  Definition eta_base_cps_gen
             (P : base -> Type)
             (f : forall t, P t)
    : { f' : forall t, P t | forall t, f' t = f t }.
  Proof. (unshelve eexists; let t := fresh in intro t; destruct t); shelve_unifiable; reflexivity. Defined.

  Definition eta_base_cps {P : base -> Type} (f : forall t, P t) : forall t, P t
    := proj1_sig (eta_base_cps_gen _ f).

  Global Instance reflect_base_beq : reflect_rel (@eq base) base_beq | 10
    := reflect_of_beq internal_base_dec_bl internal_base_dec_lb.

  Definition base_interp (ty : base)
    := match ty with
       | Z => BinInt.Z
       | bool => Datatypes.bool
       | nat => Datatypes.nat
       | zrange => ZRange.zrange
       end.

  Global Instance baseHasNatCorrect : base.BaseHasNatCorrectT base_interp
    := {
        to_nat := fun x => x;
        of_nat := fun x => x;
        to_of_nat := fun P x v => v;
        of_to_nat := fun P x v => v;
      }.

  Ltac build_base_interp_beq base_interp :=
    (eval cbv beta in
        (ltac:(let t := fresh "t" in
               intro t; destruct t;
               let h := head base_interp in
               cbv [h];
               refine ((fun T (beq : T -> T -> Datatypes.bool) (_ : reflect_rel (@eq T) beq) => beq) _ _ _))
         : forall t, base_interp t -> base_interp t -> Datatypes.bool)).
  Ltac make_base_interp_beq base_interp := let v := build_base_interp_beq base_interp in refine v.

  Definition base_interp_beq : forall {t}, base_interp t -> base_interp t -> Datatypes.bool
    := ltac:(make_base_interp_beq base_interp).

  Notation base_type_interp := (base.interp base_interp).

  Global Instance reflect_base_interp_eq {t} : reflect_rel (@eq (base_interp t)) (@base_interp_beq t) | 10.
  Proof. destruct t; cbn [base_interp base_interp_beq]; eauto with typeclass_instances. Qed.

  Definition try_make_base_transport_cps : @type.try_make_transport_cpsT base
    := Eval cbv [eta_base_cps base_beq internal_base_dec_bl eq_rect proj1_sig eta_base_cps_gen base_ind base_rect base_rec] in
        (fun (P : base -> Type) (t1 t2 : base)
         => eta_base_cps
              (fun t1
               => @eta_base_cps
                    (fun t2 => ~> option (P t1 -> P t2))
                    (fun t2
                     => (if base_beq t1 t2 as b return base_beq t1 t2 = b -> _
                         then fun pf => (return (Some (rew [fun t2 => P t1 -> P t2] (internal_base_dec_bl _ _ pf) in id)))
                         else fun _ => (return None)) eq_refl)
                    t2)
              t1)%cps.
  Global Existing Instance try_make_base_transport_cps | 5.

  Global Instance try_make_base_transport_cps_correct
    : type.try_make_transport_cps_correctT base.
  Proof.
    intros P t1 t2; revert P t2; induction t1, t2; cbn;
      Reflect.reflect_beq_to_eq base_beq; reflexivity.
  Qed.

  Ltac reify_base ty :=
    let __ := Reify.debug_enter_reify_base_type ty in
    lazymatch eval cbv beta in ty with
    | Datatypes.nat => nat
    | Datatypes.bool => bool
    | BinInt.Z => Z
    | ZRange.zrange => zrange
    | base_interp ?T => T
    | @base.interp base base_interp (@base.type.type_base base ?T) => T
    | @type.interp base_type (@base.interp base base_interp) (@Compilers.type.base base_type (@base.type.type_base base ?T)) => T
    | _ => constr_fail_with ltac:(fun _ => fail 1 "Unrecognized type:" ty)
    end.
  Ltac reify_base_type ty := Language.Compilers.base.reify base reify_base ty.
  Ltac reify_type ty := Language.Compilers.type.reify reify_base_type constr:(base_type) ty.

  Global Hint Extern 1 (@type.reified_of base_type _ ?T ?e)
  => (solve [ let rT := reify_type T in unify e rT; reflexivity | idtac "ERROR: Failed to reify" T ])
     : typeclass_instances.
  Bind Scope etype_scope with base.

  Section ident.
    Import Language.Compilers.ident.
    Local Notation type := (type base_type).
    Local Notation ttype := type.

    Section with_base.
      Let type_base (x : Compilers.base) : base_type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : Compilers.base >-> base.type.
      Section with_scope.
        Import base.type.
        Local Notation nat := Compilers.nat.
        Notation type := ttype.
        (* N.B. [ident] must have essentially flat structure for the
           python script constructing [pattern.ident] to work *)
        Inductive ident : type -> Type :=
        | ident_Literal {t:Compilers.base} (v : base_interp t) : ident t
        | ident_Nat_succ : ident (nat -> nat)
        | ident_Nat_pred : ident (nat -> nat)
        | ident_Nat_max : ident (nat -> nat -> nat)
        | ident_Nat_mul : ident (nat -> nat -> nat)
        | ident_Nat_add : ident (nat -> nat -> nat)
        | ident_Nat_sub : ident (nat -> nat -> nat)
        | ident_Nat_eqb : ident (nat -> nat -> bool)
        | ident_nil {t} : ident (list t)
        | ident_cons {t:base_type} : ident (t -> list t -> list t)
        | ident_tt : ident unit
        | ident_pair {A B:base_type} : ident (A -> B -> A * B)
        | ident_fst {A B} : ident (A * B -> A)
        | ident_snd {A B} : ident (A * B -> B)
        | ident_prod_rect {A B T:base_type} : ident ((A -> B -> T) -> A * B -> T)
        | ident_bool_rect {T:base_type} : ident ((unit -> T) -> (unit -> T) -> bool -> T)
        | ident_nat_rect {P:base_type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | ident_nat_rect_arrow {P Q:base_type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | ident_eager_nat_rect {P:base_type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | ident_eager_nat_rect_arrow {P Q:base_type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | ident_list_rect {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | ident_list_rect_arrow {A P Q:base_type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | ident_eager_list_rect {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | ident_eager_list_rect_arrow {A P Q:base_type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | ident_list_case {A P:base_type} : ident ((unit -> P) -> (A -> list A -> P) -> list A -> P)
        | ident_List_length {T} : ident (list T -> nat)
        | ident_List_seq : ident (nat -> nat -> list nat)
        | ident_List_firstn {A:base_type} : ident (nat -> list A -> list A)
        | ident_List_skipn {A:base_type} : ident (nat -> list A -> list A)
        | ident_List_repeat {A:base_type} : ident (A -> nat -> list A)
        | ident_List_combine {A B} : ident (list A -> list B -> list (A * B))
        | ident_List_map {A B:base_type} : ident ((A -> B) -> list A -> list B)
        | ident_List_app {A} : ident (list A -> list A -> list A)
        | ident_List_rev {A} : ident (list A -> list A)
        | ident_List_flat_map {A B:base_type} : ident ((A -> (list B)) -> list A -> (list B))
        | ident_List_partition {A:base_type} : ident ((A -> bool) -> list A -> (list A * list A))
        | ident_List_fold_right {A B:base_type} : ident ((B -> A -> A) -> A -> list B -> A)
        | ident_List_update_nth {T:base_type} : ident (nat -> (T -> T) -> list T -> list T)
        | ident_List_nth_default {T:base_type} : ident (T -> list T -> nat -> T)
        | ident_eager_List_nth_default {T:base_type} : ident (T -> list T -> nat -> T)
        | ident_Z_add : ident (Z -> Z -> Z)
        | ident_Z_mul : ident (Z -> Z -> Z)
        | ident_Z_pow : ident (Z -> Z -> Z)
        | ident_Z_sub : ident (Z -> Z -> Z)
        | ident_Z_opp : ident (Z -> Z)
        | ident_Z_div : ident (Z -> Z -> Z)
        | ident_Z_modulo : ident (Z -> Z -> Z)
        | ident_Z_log2 : ident (Z -> Z)
        | ident_Z_log2_up : ident (Z -> Z)
        | ident_Z_eqb : ident (Z -> Z -> bool)
        | ident_Z_leb : ident (Z -> Z -> bool)
        | ident_Z_ltb : ident (Z -> Z -> bool)
        | ident_Z_geb : ident (Z -> Z -> bool)
        | ident_Z_gtb : ident (Z -> Z -> bool)
        | ident_Z_of_nat : ident (nat -> Z)
        | ident_Z_to_nat : ident (Z -> nat)
        | ident_Z_shiftr : ident (Z -> Z -> Z)
        | ident_Z_shiftl : ident (Z -> Z -> Z)
        | ident_Z_land : ident (Z -> Z -> Z)
        | ident_Z_lor : ident (Z -> Z -> Z)
        | ident_Z_min : ident (Z -> Z -> Z)
        | ident_Z_max : ident (Z -> Z -> Z)
        | ident_Z_bneg : ident (Z -> Z)
        | ident_Z_lnot_modulo : ident (Z -> Z -> Z)
        | ident_Z_truncating_shiftl : ident (Z -> Z -> Z -> Z)
        | ident_Z_mul_split : ident (Z -> Z -> Z -> Z * Z)
        | ident_Z_add_get_carry : ident (Z -> Z -> Z -> (Z * Z))
        | ident_Z_add_with_carry : ident (Z -> Z -> Z -> Z)
        | ident_Z_add_with_get_carry : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | ident_Z_sub_get_borrow : ident (Z -> Z -> Z -> (Z * Z))
        | ident_Z_sub_with_get_borrow : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | ident_Z_zselect : ident (Z -> Z -> Z -> Z)
        | ident_Z_add_modulo : ident (Z -> Z -> Z -> Z)
        | ident_Z_rshi : ident (Z -> Z -> Z -> Z -> Z)
        | ident_Z_cc_m : ident (Z -> Z -> Z)
        | ident_Z_combine_at_bitwidth : ident (Z -> Z -> Z -> Z)
        | ident_Z_cast (range : ZRange.zrange) : ident (Z -> Z)
        | ident_Z_cast2 (range : ZRange.zrange * ZRange.zrange) : ident ((Z * Z) -> (Z * Z))
        | ident_Some {A:base_type} : ident (A -> option A)
        | ident_None {A:base_type} : ident (option A)
        | ident_option_rect {A P : base_type} : ident ((A -> P) -> (unit -> P) -> option A -> P)
        | ident_Build_zrange : ident (Z -> Z -> zrange)
        | ident_zrange_rect {P:base_type} : ident ((Z -> Z -> P) -> zrange -> P)
        | ident_fancy_add : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | ident_fancy_addc : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | ident_fancy_sub : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | ident_fancy_subb : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | ident_fancy_mulll : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mullh : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mulhl : ident (Z * (Z * Z) -> Z)
        | ident_fancy_mulhh : ident (Z * (Z * Z) -> Z)
        | ident_fancy_rshi : ident ((Z * Z) * (Z * Z) -> Z)
        | ident_fancy_selc : ident (Z * Z * Z -> Z)
        | ident_fancy_selm : ident (Z * (Z * Z * Z) -> Z)
        | ident_fancy_sell : ident (Z * Z * Z -> Z)
        | ident_fancy_addm : ident (Z * Z * Z -> Z)
        .
      End with_scope.

      Section gen.
        Context (cast_outside_of_range : ZRange.zrange -> BinInt.Z -> BinInt.Z).

        Local Notation is_more_pos_than_neg := ident.is_more_pos_than_neg.
        Local Notation cast := (ident.cast cast_outside_of_range).
        Local Notation cast2 := (ident.cast2 cast_outside_of_range).

        (** Interpret identifiers where the behavior of [Z_cast] on a
            value that does not fit in the range is given by a context
            variable.  (This allows us to treat [Z_cast] as "undefined
            behavior" when the value doesn't fit in the range by
            quantifying over all possible interpretations. *)
        Definition ident_gen_interp {t} (idc : ident t) : type.interp base_type_interp t
          := match idc in ident t return type.interp base_type_interp t with
             | ident_Literal _ v => v
             | ident_Nat_succ => Nat.succ
             | ident_Nat_pred => Nat.pred
             | ident_Nat_max => Nat.max
             | ident_Nat_mul => Nat.mul
             | ident_Nat_add => Nat.add
             | ident_Nat_sub => Nat.sub
             | ident_Nat_eqb => Nat.eqb
             | ident_nil t => Datatypes.nil
             | ident_cons t => Datatypes.cons
             | ident_tt => Datatypes.tt
             | ident_pair A B => Datatypes.pair
             | ident_fst A B => Datatypes.fst
             | ident_snd A B => Datatypes.snd
             | ident_prod_rect A B T => fun f '((a, b) : base_type_interp A * base_type_interp B) => f a b
             | ident_bool_rect T
               => fun t f => Datatypes.bool_rect _ (t Datatypes.tt) (f Datatypes.tt)
             | ident_nat_rect P
             | ident_eager_nat_rect P
               => fun O_case S_case => Datatypes.nat_rect _ (O_case Datatypes.tt) S_case
             | ident_nat_rect_arrow P Q
             | ident_eager_nat_rect_arrow P Q
               => fun O_case S_case => Datatypes.nat_rect _ O_case S_case
             | ident_list_rect A P
             | ident_eager_list_rect A P
               => fun N_case C_case => Datatypes.list_rect _ (N_case Datatypes.tt) C_case
             | ident_list_rect_arrow A P Q
             | ident_eager_list_rect_arrow A P Q
               => fun N_case C_case => Datatypes.list_rect _ N_case C_case
             | ident_list_case A P
               => fun N_case C_case => ListUtil.list_case _ (N_case Datatypes.tt) C_case
             | ident_List_length T => @List.length _
             | ident_List_seq => List.seq
             | ident_List_firstn A => @List.firstn _
             | ident_List_skipn A => @List.skipn _
             | ident_List_repeat A => @repeat _
             | ident_List_combine A B => @List.combine _ _
             | ident_List_map A B => @List.map _ _
             | ident_List_app A => @List.app _
             | ident_List_rev A => @List.rev _
             | ident_List_flat_map A B => @List.flat_map _ _
             | ident_List_partition A => @List.partition _
             | ident_List_fold_right A B => @List.fold_right _ _
             | ident_List_update_nth T => update_nth
             | ident_List_nth_default T => @nth_default _
             | ident_eager_List_nth_default T => @nth_default _
             | ident_Z_add => Z.add
             | ident_Z_mul => Z.mul
             | ident_Z_pow => Z.pow
             | ident_Z_sub => Z.sub
             | ident_Z_opp => Z.opp
             | ident_Z_div => Z.div
             | ident_Z_modulo => Z.modulo
             | ident_Z_eqb => Z.eqb
             | ident_Z_leb => Z.leb
             | ident_Z_ltb => Z.ltb
             | ident_Z_geb => Z.geb
             | ident_Z_gtb => Z.gtb
             | ident_Z_log2 => Z.log2
             | ident_Z_log2_up => Z.log2_up
             | ident_Z_of_nat => Z.of_nat
             | ident_Z_to_nat => Z.to_nat
             | ident_Z_shiftr => Z.shiftr
             | ident_Z_shiftl => Z.shiftl
             | ident_Z_land => Z.land
             | ident_Z_lor => Z.lor
             | ident_Z_min => Z.min
             | ident_Z_max => Z.max
             | ident_Z_mul_split => Z.mul_split
             | ident_Z_add_get_carry => Z.add_get_carry_full
             | ident_Z_add_with_carry => Z.add_with_carry
             | ident_Z_add_with_get_carry => Z.add_with_get_carry_full
             | ident_Z_sub_get_borrow => Z.sub_get_borrow_full
             | ident_Z_sub_with_get_borrow => Z.sub_with_get_borrow_full
             | ident_Z_zselect => Z.zselect
             | ident_Z_add_modulo => Z.add_modulo
             | ident_Z_truncating_shiftl => Z.truncating_shiftl
             | ident_Z_bneg => Z.bneg
             | ident_Z_lnot_modulo => Z.lnot_modulo
             | ident_Z_rshi => Z.rshi
             | ident_Z_cc_m => Z.cc_m
             | ident_Z_combine_at_bitwidth => Z.combine_at_bitwidth
             | ident_Z_cast r => cast r
             | ident_Z_cast2 (r1, r2) => fun '(x1, x2) => (cast r1 x1, cast r2 x2)
             | ident_Some A => @Datatypes.Some _
             | ident_None A => @Datatypes.None _
             | ident_option_rect A P
               => fun S_case N_case o => @Datatypes.option_rect _ _ S_case (N_case Datatypes.tt) o
             | ident_Build_zrange => ZRange.Build_zrange
             | ident_zrange_rect A => @ZRange.zrange_rect _
             | ident_fancy_add => ident.fancy.add
             | ident_fancy_addc => ident.fancy.addc
             | ident_fancy_sub => ident.fancy.sub
             | ident_fancy_subb => ident.fancy.subb
             | ident_fancy_mulll => ident.fancy.mulll
             | ident_fancy_mullh => ident.fancy.mullh
             | ident_fancy_mulhl => ident.fancy.mulhl
             | ident_fancy_mulhh => ident.fancy.mulhh
             | ident_fancy_rshi => ident.fancy.rshi
             | ident_fancy_selc => ident.fancy.selc
             | ident_fancy_selm => ident.fancy.selm
             | ident_fancy_sell => ident.fancy.sell
             | ident_fancy_addm => ident.fancy.addm
             end.
      End gen.
    End with_base.
  End ident.

  Global Instance buildEagerIdent : ident.BuildEagerIdentT ident
    := {
        ident_nat_rect := @ident_nat_rect
        ; ident_nat_rect_arrow := @ident_nat_rect_arrow
        ; ident_list_rect := @ident_list_rect
        ; ident_list_rect_arrow := @ident_list_rect_arrow
        ; ident_List_nth_default := @ident_List_nth_default
        ; ident_eager_nat_rect := @ident_eager_nat_rect
        ; ident_eager_nat_rect_arrow := @ident_eager_nat_rect_arrow
        ; ident_eager_list_rect := @ident_eager_list_rect
        ; ident_eager_list_rect_arrow := @ident_eager_list_rect_arrow
        ; ident_eager_List_nth_default := @ident_eager_List_nth_default
      }.

  Global Instance buildInterpEagerIdentCorrect
         {cast_outside_of_range}
    : ident.BuildInterpEagerIdentCorrectT (@ident_gen_interp cast_outside_of_range).
  Proof. split; cbn; reflexivity. Defined.

  Definition toRestrictedIdentAndCorrect
    : { toRestrictedIdent : ident.ToRestrictedIdentT ident
                            & ident.ToFromRestrictedIdentT ident }.
  Proof.
    unshelve eexists; hnf; [ | split ]; cbv;
      let idc := fresh "idc" in
      intros ? idc; destruct idc;
        try (((instantiate (1 := Datatypes.None) + idtac); reflexivity)).
  Defined.

  Definition fromRestrictedIdent : ident.ToRestrictedIdentT ident
    := Eval hnf in projT1 toRestrictedIdentAndCorrect.
  Global Existing Instance fromRestrictedIdent.

  Definition toFromRestrictedIdent : ident.ToFromRestrictedIdentT ident
    := Eval hnf in projT2 toRestrictedIdentAndCorrect.
  Global Existing Instance toFromRestrictedIdent.

  (** Interpret identifiers where [Z_cast] is an opaque identity
        function when the value is not inside the range *)
  Notation ident_interp := (@ident_gen_interp ident.cast_outside_of_range).

  (** TODO: MOVE ME? *)
  Ltac require_primitive_const_extra term := fail 0 "Not a known const:" term.
  Ltac require_primitive_const term :=
    lazymatch term with
    | Datatypes.S ?n => require_primitive_const n
    | Datatypes.O => idtac
    | Datatypes.true => idtac
    | Datatypes.false => idtac
    (*| Datatypes.tt => idtac*)
    | Z0 => idtac
    | Zpos ?p => require_primitive_const p
    | Zneg ?p => require_primitive_const p
    | xI ?p => require_primitive_const p
    | xO ?p => require_primitive_const p
    | xH => idtac
    | Datatypes.Some ?x => require_primitive_const x
    | Datatypes.None => idtac
    | ZRange.Build_zrange ?x ?y
      => require_primitive_const x; require_primitive_const y
    | ident.literal ?x => idtac
    | ?term => require_primitive_const_extra term
    end.
  Ltac is_primitive_const term :=
    match constr:(Set) with
    | _ => let check := match goal with
                        | _ => require_primitive_const term
                        end in
           true
    | _ => false
    end.

  Ltac reify_ident
       term
       then_tac
       reify_rec
       else_tac :=
    (*let __ := match goal with _ => idtac "attempting to reify_op" term end in*)
    let term_is_primitive_const := is_primitive_const term in
    lazymatch term_is_primitive_const with
    | true
      =>
      let T := type of term in
      let rT := reify_base T in
      then_tac (@ident_Literal rT term)
    | false
      =>
      lazymatch term with
      | Nat.succ => then_tac ident_Nat_succ
      | Nat.add => then_tac ident_Nat_add
      | Nat.sub => then_tac ident_Nat_sub
      | Nat.eqb => then_tac ident_Nat_eqb
      | Nat.mul => then_tac ident_Nat_mul
      | Nat.max => then_tac ident_Nat_max
      | Nat.pred => then_tac ident_Nat_pred
      | Datatypes.S => then_tac ident_Nat_succ
      | Datatypes.tt => then_tac ident_tt
      | @Datatypes.nil ?T
        => let rT := reify_base_type T in
           then_tac (@ident_nil rT)
      | @Datatypes.cons ?T
        => let rT := reify_base_type T in
           then_tac (@ident_cons rT)
      | @Datatypes.fst ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_fst rA rB)
      | @Datatypes.snd ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_snd rA rB)
      | @Datatypes.pair ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_pair rA rB)
      | @Datatypes.bool_rect ?T0 ?Ptrue ?Pfalse
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@ident.Thunked.bool_rect T (fun _ : Datatypes.unit => Ptrue) (fun _ : Datatypes.unit => Pfalse))
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.bool_rect T' Ptrue Pfalse)
           end
      | @ident.Thunked.bool_rect ?T
        => let rT := reify_base_type T in
           then_tac (@ident_bool_rect rT)
      | @Datatypes.option_rect ?A ?T0 ?PSome ?PNone
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@ident.Thunked.option_rect A T PSome (fun _ : Datatypes.unit => PNone))
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.option_rect A T' PSome PNone)
           end
      | @ident.Thunked.option_rect ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_option_rect rA rT)
      | @Datatypes.prod_rect ?A ?B ?T0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T
             => let rA := reify_base_type A in
                let rB := reify_base_type B in
                let rT := reify_base_type T in
                then_tac (@ident_prod_rect rA rB rT)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.prod_rect A B T')
           end
      | @ZRange.zrange_rect ?T0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T
             => let rT := reify_base_type T in
                then_tac (@ident_zrange_rect rT)
           | T0 => else_tac ()
           | ?T' => reify_rec (@ZRange.zrange_rect T')
           end
      | @Datatypes.nat_rect ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => _ -> _ => else_tac ()
           | fun _ => ?T => reify_rec (@ident.Thunked.nat_rect T (fun _ : Datatypes.unit => P0))
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.nat_rect T' P0)
           end
      | @Datatypes.nat_rect ?T0
        => lazymatch (eval cbv beta in T0) with
           | (fun _ => ?P -> ?Q)
             => let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_nat_rect_arrow rP rQ)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.nat_rect T')
           end
      | @ident.Thunked.nat_rect ?T
        => let rT := reify_base_type T in
           then_tac (@ident_nat_rect rT)
      | ident.eagerly (@Datatypes.nat_rect) ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => _ -> _ => else_tac ()
           | fun _ => ?T => reify_rec (ident.eagerly (@ident.Thunked.nat_rect) T (fun _ : Datatypes.unit => P0))
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.nat_rect) T' P0)
           end
      | ident.eagerly (@Datatypes.nat_rect) ?T0
        => lazymatch (eval cbv beta in T0) with
           | (fun _ => ?P -> ?Q)
             => let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_eager_nat_rect_arrow rP rQ)
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.nat_rect) T')
           end
      | ident.eagerly (@ident.Thunked.nat_rect) ?T
        => let rT := reify_base_type T in
           then_tac (@ident_eager_nat_rect rT)
      | @Datatypes.list_rect ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => _ -> _ => else_tac ()
           | fun _ => ?T => reify_rec (@ident.Thunked.list_rect A T (fun _ : Datatypes.unit => Pnil))
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.list_rect A T' Pnil)
           end
      | @Datatypes.list_rect ?A ?T0
        => lazymatch (eval cbv beta in T0) with
           | (fun _ => ?P -> ?Q)
             => let rA := reify_base_type A in
                let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_list_rect_arrow rA rP rQ)
           | T0 => else_tac ()
           | ?T' => reify_rec (@Datatypes.list_rect A T')
           end
      | @ident.Thunked.list_rect ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_list_rect rA rT)
      | ident.eagerly (@Datatypes.list_rect) ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => _ -> _ => else_tac ()
           | fun _ => ?T => reify_rec (ident.eagerly (@ident.Thunked.list_rect) A T (fun _ : Datatypes.unit => Pnil))
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.list_rect) A T' Pnil)
           end
      | ident.eagerly (@Datatypes.list_rect) ?A ?T0
        => lazymatch (eval cbv beta in T0) with
           | (fun _ => ?P -> ?Q)
             => let rA := reify_base_type A in
                let rP := reify_base_type P in
                let rQ := reify_base_type Q in
                then_tac (@ident_eager_list_rect_arrow rA rP rQ)
           | T0 => else_tac ()
           | ?T' => reify_rec (ident.eagerly (@Datatypes.list_rect) A T')
           end
      | ident.eagerly (@ident.Thunked.list_rect) ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_eager_list_rect rA rT)
      | @ListUtil.list_case ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_rec (@ident.Thunked.list_case A T (fun _ : Datatypes.unit => Pnil))
           | T0 => else_tac ()
           | ?T' => reify_rec (@ListUtil.list_case A T' Pnil)
           end
      | @ident.Thunked.list_case ?A ?T
        => let rA := reify_base_type A in
           let rT := reify_base_type T in
           then_tac (@ident_list_case rA rT)
      | @List.length ?A =>
        let rA := reify_base_type A in
        then_tac (@ident_List_length rA)
      | List.seq => then_tac ident_List_seq
      | @List.firstn ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_firstn rA)
      | @List.skipn ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_skipn rA)
      | @repeat ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_repeat rA)
      | @List.combine ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_combine rA rB)
      | @List.map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_map rA rB)
      | @List.flat_map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_flat_map rA rB)
      | @List.partition ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_partition rA)
      | @List.app ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_app rA)
      | @List.map ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_map rA rB)
      | @List.rev ?A
        => let rA := reify_base_type A in
           then_tac (@ident_List_rev rA)
      | @List.fold_right ?A ?B
        => let rA := reify_base_type A in
           let rB := reify_base_type B in
           then_tac (@ident_List_fold_right rA rB)
      | @update_nth ?T
        => let rT := reify_base_type T in
           then_tac (@ident_List_update_nth rT)
      | @List.nth_default ?T
        => let rT := reify_base_type T in
           then_tac (@ident_List_nth_default rT)
      | ident.eagerly (@List.nth_default) ?T
        => let rT := reify_base_type T in
           then_tac (@ident_eager_List_nth_default rT)
      | Z.add => then_tac ident_Z_add
      | Z.mul => then_tac ident_Z_mul
      | Z.pow => then_tac ident_Z_pow
      | Z.sub => then_tac ident_Z_sub
      | Z.opp => then_tac ident_Z_opp
      | Z.div => then_tac ident_Z_div
      | Z.modulo => then_tac ident_Z_modulo
      | Z.eqb => then_tac ident_Z_eqb
      | Z.leb => then_tac ident_Z_leb
      | Z.ltb => then_tac ident_Z_ltb
      | Z.geb => then_tac ident_Z_geb
      | Z.gtb => then_tac ident_Z_gtb
      | Z.log2 => then_tac ident_Z_log2
      | Z.log2_up => then_tac ident_Z_log2_up
      | Z.shiftl => then_tac ident_Z_shiftl
      | Z.shiftr => then_tac ident_Z_shiftr
      | Z.land => then_tac ident_Z_land
      | Z.lor => then_tac ident_Z_lor
      | Z.min => then_tac ident_Z_min
      | Z.max => then_tac ident_Z_max
      | Z.bneg => then_tac ident_Z_bneg
      | Z.lnot_modulo => then_tac ident_Z_lnot_modulo
      | Z.truncating_shiftl => then_tac ident_Z_truncating_shiftl
      | Z.of_nat => then_tac ident_Z_of_nat
      | Z.to_nat => then_tac ident_Z_to_nat
      | Z.mul_split => then_tac ident_Z_mul_split
      | Z.add_get_carry_full => then_tac ident_Z_add_get_carry
      | Z.add_with_carry => then_tac ident_Z_add_with_carry
      | Z.add_with_get_carry_full => then_tac ident_Z_add_with_get_carry
      | Z.sub_get_borrow_full => then_tac ident_Z_sub_get_borrow
      | Z.sub_with_get_borrow_full => then_tac ident_Z_sub_with_get_borrow
      | Z.zselect => then_tac ident_Z_zselect
      | Z.add_modulo => then_tac ident_Z_add_modulo
      | Z.rshi => then_tac ident_Z_rshi
      | Z.cc_m => then_tac ident_Z_cc_m
      | Z.combine_at_bitwidth => then_tac ident_Z_combine_at_bitwidth
      | ident.cast _ ?r => then_tac (ident_Z_cast r)
      | ident.cast2 _ ?r => then_tac (ident_Z_cast2 r)
      | @Some ?A
        => let rA := reify_base_type A in
           then_tac (@ident_Some rA)
      | @None ?A
        => let rA := reify_base_type A in
           then_tac (@ident_None rA)
      | ZRange.Build_zrange => then_tac ident_Build_zrange
      | ident.fancy.add => then_tac ident_fancy_add
      | ident.fancy.addc => then_tac ident_fancy_addc
      | ident.fancy.sub => then_tac ident_fancy_sub
      | ident.fancy.subb => then_tac ident_fancy_subb
      | ident.fancy.mulll => then_tac ident_fancy_mulll
      | ident.fancy.mullh => then_tac ident_fancy_mullh
      | ident.fancy.mulhl => then_tac ident_fancy_mulhl
      | ident.fancy.mulhh => then_tac ident_fancy_mulhh
      | ident.fancy.rshi => then_tac ident_fancy_rshi
      | ident.fancy.selc => then_tac ident_fancy_selc
      | ident.fancy.selm => then_tac ident_fancy_selm
      | ident.fancy.sell => then_tac ident_fancy_sell
      | ident.fancy.addm => then_tac ident_fancy_addm
      | ident.eagerly (?f ?x) => reify_rec (ident.eagerly f x)
      | @ident_gen_interp _ _ ?idc => then_tac idc
      | _ => else_tac ()
      end
    end.

  Global Instance buildIdent : @ident.BuildIdentT base base_interp ident | 5
    := { ident_Literal := @ident_Literal
         ; ident_nil := @ident_nil
         ; ident_cons := @ident_cons
         ; ident_Some := @ident_Some
         ; ident_None := @ident_None
         ; ident_pair := @ident_pair
         ; ident_tt := @ident_tt
       }.

  Definition ident_is_var_like {t} (idc : ident t) : Datatypes.bool
    := match idc with
       | ident_Literal _ _
       | ident_nil _
       | ident_cons _
       | ident_pair _ _
       | ident_fst _ _
       | ident_snd _ _
       | ident_Z_opp
       | ident_Z_cast _
       | ident_Z_cast2 _
       | ident_Z_combine_at_bitwidth
         => Datatypes.true
       | _ => Datatypes.false
       end.

  Global Instance buildInterpIdentCorrect {cast_outside_of_range}
    : @ident.BuildInterpIdentCorrectT base base_interp ident _ (@ident_gen_interp cast_outside_of_range).
  Proof. constructor; cbn; reflexivity. Qed.


  Global Instance gen_eqv_Reflexive_Proper cast_outside_of_range {t} (idc : ident t) : Proper type.eqv (ident_gen_interp cast_outside_of_range idc) | 1.
  Proof.
    destruct idc; cbn [type.eqv ident_gen_interp type.interp base.interp base_interp];
      try solve [ typeclasses eauto
                | cbv [respectful]; repeat intro; subst; destruct_head_hnf Datatypes.bool; destruct_head_hnf Datatypes.prod; destruct_head_hnf Datatypes.option; destruct_head_hnf ZRange.zrange; eauto
                | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper || apply list_rect_arrow_Proper); repeat intro; eauto ].
  Qed.

  Global Instance eqv_Reflexive_Proper {t} (idc : ident t) : Proper type.eqv (ident_interp idc) | 1.
  Proof. exact _. Qed.

  Global Instance ident_gen_interp_Proper {cast_outside_of_range} {t} : Proper (@eq (ident t) ==> type.eqv) (ident_gen_interp cast_outside_of_range) | 1.
  Proof. intros idc idc' ?; subst idc'; apply gen_eqv_Reflexive_Proper. Qed.

  Global Instance ident_interp_Proper {t} : Proper (@eq (ident t) ==> type.eqv) ident_interp | 1.
  Proof. exact _. Qed.

  Global Strategy -1000 [base_interp ident_gen_interp].

  Definition invert_ident_Literal {t} (idc : ident t) : option (type.interp base_type_interp t)
    := match idc with
       | ident_Literal _ n => Datatypes.Some n
       | _ => Datatypes.None
       end.

  Global Instance invertIdent : @invert_expr.InvertIdentT base base_interp ident
    := {
        invert_ident_Literal := @invert_ident_Literal
        ; is_nil t idc := match idc with ident_nil _ => Datatypes.true | _ => Datatypes.false end
        ; is_cons t idc := match idc with ident_cons _ => Datatypes.true | _ => Datatypes.false end
        ; is_Some t idc := match idc with ident_Some _ => Datatypes.true | _ => Datatypes.false end
        ; is_None t idc := match idc with ident_None _ => Datatypes.true | _ => Datatypes.false end
        ; is_pair t idc := match idc with ident_pair _ _ => Datatypes.true | _ => Datatypes.false end
        ; is_tt t idc := match idc with ident_tt => Datatypes.true | _ => Datatypes.false end
      }.

  Global Instance buildInvertIdentCorrect : @invert_expr.BuildInvertIdentCorrectT base base_interp ident _ _.
  Proof.
    constructor; intros t idc; destruct idc;
      repeat first [ progress intros
                   | progress cbn in *
                   | apply conj
                   | progress destruct_head'_False
                   | progress inversion_option
                   | discriminate
                   | progress subst
                   | reflexivity
                   | break_innermost_match_hyps_step
                   | match goal with
                     | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                     end ].
  Qed.

  Local Ltac inhabit := (constructor; fail) + (constructor; inhabit).
  Local Ltac build_base_default base base_interp :=
    constr:(ltac:(let t := fresh "t" in
                  intro t; destruct t; hnf; inhabit)
            : @DefaultValue.type.base.DefaultT base base_interp).
  Local Ltac make_base_default base base_interp := let res := build_base_default base base_interp in refine res.
  Global Instance base_default : @DefaultValue.type.base.DefaultT base base_interp
    := ltac:(make_base_default base base_interp).

  Module expr.
    Global Hint Extern 1 (@expr.Reified_of _ ident _ _ ?t ?v ?e)
    => solve [ let rv := expr.Reify constr:(base_type) ident ltac:(reify_base_type) ltac:(reify_ident) v in unify e rv; reflexivity | idtac "ERROR: Failed to reify" v "(of type" t "); try setting Reify.debug_level to see output" ]
       : typeclass_instances.
  End expr.

  Import Language.Compilers.Classes.
  Global Instance exprInfo : ExprInfoT :=
    {
      base := Compilers.base;
      ident := Compilers.ident;
      base_interp := Compilers.base_interp;
      ident_gen_interp := Compilers.ident_gen_interp
    }.

  Definition exprExtraInfo : ExprExtraInfoT.
  Proof.
    econstructor; typeclasses eauto.
  Defined.
End Compilers.
