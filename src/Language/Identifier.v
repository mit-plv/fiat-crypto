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

  Module base.
    Export Language.Compilers.base.
    Module type.
      Export Language.Compilers.base.type.
      Inductive base := Z | bool | nat | zrange. (* Not Variant because COQBUG(https://github.com/coq/coq/issues/7738) *)
      Notation type := (@type base).

      Global Instance baseHasNat : BaseTypeHasNatT base := nat.
      Definition eta_base_cps_gen
                 (P : base -> Type)
                 (f : forall t, P t)
        : { f' : forall t, P t | forall t, f' t = f t }.
      Proof. (unshelve eexists; let t := fresh in intro t; destruct t); shelve_unifiable; reflexivity. Defined.

      Definition eta_base_cps {P : base -> Type} (f : forall t, P t) : forall t, P t
        := proj1_sig (eta_base_cps_gen _ f).
    End type.
    Notation type := type.type.

    Global Instance reflect_base_beq : reflect_rel (@eq type.base) type.base_beq | 10
      := reflect_of_beq type.internal_base_dec_bl type.internal_base_dec_lb.

    Definition base_interp (ty : type.base)
      := match ty with
         | type.Z => BinInt.Z
         | type.bool => Datatypes.bool
         | type.nat => Datatypes.nat
         | type.zrange => zrange
         end.

    Global Instance baseHasNatCorrect : BaseHasNatCorrectT base_interp
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
                 refine ((fun T (beq : T -> T -> bool) (_ : reflect_rel (@eq T) beq) => beq) _ _ _))
           : forall t, base_interp t -> base_interp t -> bool)).
    Ltac make_base_interp_beq base_interp := let v := build_base_interp_beq base_interp in refine v.

    Definition base_interp_beq : forall {t}, base_interp t -> base_interp t -> bool
      := ltac:(make_base_interp_beq base_interp).

    Notation interp := (base.interp base_interp).

    Global Instance reflect_base_interp_eq {t} : reflect_rel (@eq (base_interp t)) (@base_interp_beq t) | 10.
    Proof. destruct t; cbn [base_interp base_interp_beq]; eauto with typeclass_instances. Qed.

    Definition try_make_base_transport_cps : @type.try_make_transport_cpsT type.base
      := Eval cbv [type.eta_base_cps type.base_beq type.internal_base_dec_bl eq_rect proj1_sig type.eta_base_cps_gen type.base_ind type.base_rect type.base_rec] in
          (fun (P : type.base -> Type) (t1 t2 : type.base)
           => type.eta_base_cps
                (fun t1
                 => @type.eta_base_cps
                      (fun t2 => ~> option (P t1 -> P t2))
                      (fun t2
                       => (if type.base_beq t1 t2 as b return type.base_beq t1 t2 = b -> _
                           then fun pf => (return (Some (rew [fun t2 => P t1 -> P t2] (type.internal_base_dec_bl _ _ pf) in id)))
                           else fun _ => (return None)) eq_refl)
                      t2)
                t1)%cps.
    Global Existing Instance try_make_base_transport_cps | 5.

    Global Instance try_make_base_transport_cps_correct
      : type.try_make_transport_cps_correctT base.type.base.
    Proof.
      intros P t1 t2; revert P t2; induction t1, t2; cbn;
        Reflect.reflect_beq_to_eq base.type.base_beq; reflexivity.
    Qed.

    Ltac reify_base ty :=
      let __ := Reify.debug_enter_reify_base_type ty in
      lazymatch eval cbv beta in ty with
      | Datatypes.nat => type.nat
      | Datatypes.bool => type.bool
      | BinInt.Z => type.Z
      | zrange => type.zrange
      | base_interp ?T => T
      | @base.interp type.base base_interp (@type.type_base type.base ?T) => T
      | @type.interp (base.type type.base) (@base.interp type.base base_interp) (@Compilers.type.base (@base.type type.base) (@type.type_base type.base ?T)) => T
      | _ => constr_fail_with ltac:(fun _ => fail 1 "Unrecognized type:" ty)
      end.
    Ltac reify ty := Language.Compilers.base.reify type.base reify_base ty.
    Ltac reify_type ty := Language.Compilers.type.reify reify (Language.Compilers.base.type type.base) ty.

    Global Hint Extern 1 (@type.reified_of (Language.Compilers.base.type base.type.base) _ ?T ?e)
    => (solve [ let rT := reify_type T in unify e rT; reflexivity | idtac "ERROR: Failed to reify" T ])
       : typeclass_instances.
  End base.
  Bind Scope etype_scope with base.type.base.

  Module ident.
    Export Language.Compilers.ident.
    Local Notation type := (type base.type).
    Local Notation ttype := type.

    Section with_base.
      Let type_base (x : base.type.base) : base.type := base.type.type_base x.
      Let base {bt} (x : Language.Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base : base.type >-> type.type.
      Local Coercion type_base : base.type.base >-> base.type.
      Section with_scope.
        Import base.type.
        Notation type := ttype.
        (* N.B. [ident] must have essentially flat structure for the
           python script constructing [pattern.ident] to work *)
        Inductive ident : type -> Type :=
        | Literal {t:base.type.base} (v : base.base_interp t) : ident t
        | Nat_succ : ident (nat -> nat)
        | Nat_pred : ident (nat -> nat)
        | Nat_max : ident (nat -> nat -> nat)
        | Nat_mul : ident (nat -> nat -> nat)
        | Nat_add : ident (nat -> nat -> nat)
        | Nat_sub : ident (nat -> nat -> nat)
        | Nat_eqb : ident (nat -> nat -> bool)
        | nil {t} : ident (list t)
        | cons {t:base.type} : ident (t -> list t -> list t)
        | tt : ident unit
        | pair {A B:base.type} : ident (A -> B -> A * B)
        | fst {A B} : ident (A * B -> A)
        | snd {A B} : ident (A * B -> B)
        | prod_rect {A B T:base.type} : ident ((A -> B -> T) -> A * B -> T)
        | bool_rect {T:base.type} : ident ((unit -> T) -> (unit -> T) -> bool -> T)
        | nat_rect {P:base.type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | nat_rect_arrow {P Q:base.type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | eager_nat_rect {P:base.type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | eager_nat_rect_arrow {P Q:base.type} : ident ((P -> Q) -> (nat -> (P -> Q) -> (P -> Q)) -> nat -> P -> Q)
        | list_rect {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | list_rect_arrow {A P Q:base.type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | eager_list_rect {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | eager_list_rect_arrow {A P Q:base.type} : ident ((P -> Q) -> (A -> list A -> (P -> Q) -> (P -> Q)) -> list A -> P -> Q)
        | list_case {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P) -> list A -> P)
        | List_length {T} : ident (list T -> nat)
        | List_seq : ident (nat -> nat -> list nat)
        | List_firstn {A:base.type} : ident (nat -> list A -> list A)
        | List_skipn {A:base.type} : ident (nat -> list A -> list A)
        | List_repeat {A:base.type} : ident (A -> nat -> list A)
        | List_combine {A B} : ident (list A -> list B -> list (A * B))
        | List_map {A B:base.type} : ident ((A -> B) -> list A -> list B)
        | List_app {A} : ident (list A -> list A -> list A)
        | List_rev {A} : ident (list A -> list A)
        | List_flat_map {A B:base.type} : ident ((A -> (list B)) -> list A -> (list B))
        | List_partition {A:base.type} : ident ((A -> bool) -> list A -> (list A * list A))
        | List_fold_right {A B:base.type} : ident ((B -> A -> A) -> A -> list B -> A)
        | List_update_nth {T:base.type} : ident (nat -> (T -> T) -> list T -> list T)
        | List_nth_default {T:base.type} : ident (T -> list T -> nat -> T)
        | eager_List_nth_default {T:base.type} : ident (T -> list T -> nat -> T)
        | Z_add : ident (Z -> Z -> Z)
        | Z_mul : ident (Z -> Z -> Z)
        | Z_pow : ident (Z -> Z -> Z)
        | Z_sub : ident (Z -> Z -> Z)
        | Z_opp : ident (Z -> Z)
        | Z_div : ident (Z -> Z -> Z)
        | Z_modulo : ident (Z -> Z -> Z)
        | Z_log2 : ident (Z -> Z)
        | Z_log2_up : ident (Z -> Z)
        | Z_eqb : ident (Z -> Z -> bool)
        | Z_leb : ident (Z -> Z -> bool)
        | Z_ltb : ident (Z -> Z -> bool)
        | Z_geb : ident (Z -> Z -> bool)
        | Z_gtb : ident (Z -> Z -> bool)
        | Z_of_nat : ident (nat -> Z)
        | Z_to_nat : ident (Z -> nat)
        | Z_shiftr : ident (Z -> Z -> Z)
        | Z_shiftl : ident (Z -> Z -> Z)
        | Z_land : ident (Z -> Z -> Z)
        | Z_lor : ident (Z -> Z -> Z)
        | Z_min : ident (Z -> Z -> Z)
        | Z_max : ident (Z -> Z -> Z)
        | Z_bneg : ident (Z -> Z)
        | Z_lnot_modulo : ident (Z -> Z -> Z)
        | Z_truncating_shiftl : ident (Z -> Z -> Z -> Z)
        | Z_mul_split : ident (Z -> Z -> Z -> Z * Z)
        | Z_add_get_carry : ident (Z -> Z -> Z -> (Z * Z))
        | Z_add_with_carry : ident (Z -> Z -> Z -> Z)
        | Z_add_with_get_carry : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_sub_get_borrow : ident (Z -> Z -> Z -> (Z * Z))
        | Z_sub_with_get_borrow : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_zselect : ident (Z -> Z -> Z -> Z)
        | Z_add_modulo : ident (Z -> Z -> Z -> Z)
        | Z_rshi : ident (Z -> Z -> Z -> Z -> Z)
        | Z_cc_m : ident (Z -> Z -> Z)
        | Z_combine_at_bitwidth : ident (Z -> Z -> Z -> Z)
        | Z_cast (range : ZRange.zrange) : ident (Z -> Z)
        | Z_cast2 (range : ZRange.zrange * ZRange.zrange) : ident ((Z * Z) -> (Z * Z))
        | option_Some {A:base.type} : ident (A -> option A)
        | option_None {A:base.type} : ident (option A)
        | option_rect {A P : base.type} : ident ((A -> P) -> (unit -> P) -> option A -> P)
        | Build_zrange : ident (Z -> Z -> zrange)
        | zrange_rect {P:base.type} : ident ((Z -> Z -> P) -> zrange -> P)
        | fancy_add : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | fancy_addc : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | fancy_sub : ident ((Z * Z) * (Z * Z) -> Z * Z)
        | fancy_subb : ident ((Z * Z) * (Z * Z * Z) -> Z * Z)
        | fancy_mulll : ident (Z * (Z * Z) -> Z)
        | fancy_mullh : ident (Z * (Z * Z) -> Z)
        | fancy_mulhl : ident (Z * (Z * Z) -> Z)
        | fancy_mulhh : ident (Z * (Z * Z) -> Z)
        | fancy_rshi : ident ((Z * Z) * (Z * Z) -> Z)
        | fancy_selc : ident (Z * Z * Z -> Z)
        | fancy_selm : ident (Z * (Z * Z * Z) -> Z)
        | fancy_sell : ident (Z * Z * Z -> Z)
        | fancy_addm : ident (Z * Z * Z -> Z)
        .
        Notation Some := option_Some.
        Notation None := option_None.

        Global Arguments Z_cast2 _%zrange_scope.
      End with_scope.
      Notation Some := option_Some.
      Notation None := option_None.

      Section gen.
        Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

        Local Notation is_more_pos_than_neg := ident.is_more_pos_than_neg.
        Local Notation cast := (ident.cast cast_outside_of_range).
        Local Notation cast2 := (ident.cast2 cast_outside_of_range).

        (** Interpret identifiers where the behavior of [Z_cast] on a
            value that does not fit in the range is given by a context
            variable.  (This allows us to treat [Z_cast] as "undefined
            behavior" when the value doesn't fit in the range by
            quantifying over all possible interpretations. *)
        Definition gen_interp {t} (idc : ident t) : type.interp base.interp t
          := match idc in ident t return type.interp base.interp t with
             | Literal _ v => v
             | Nat_succ => Nat.succ
             | Nat_pred => Nat.pred
             | Nat_max => Nat.max
             | Nat_mul => Nat.mul
             | Nat_add => Nat.add
             | Nat_sub => Nat.sub
             | Nat_eqb => Nat.eqb
             | nil t => Datatypes.nil
             | cons t => Datatypes.cons
             | tt => Datatypes.tt
             | pair A B => Datatypes.pair
             | fst A B => Datatypes.fst
             | snd A B => Datatypes.snd
             | prod_rect A B T => fun f '((a, b) : base.interp A * base.interp B) => f a b
             | bool_rect T
               => fun t f => Datatypes.bool_rect _ (t Datatypes.tt) (f Datatypes.tt)
             | nat_rect P
             | eager_nat_rect P
               => fun O_case S_case => Datatypes.nat_rect _ (O_case Datatypes.tt) S_case
             | nat_rect_arrow P Q
             | eager_nat_rect_arrow P Q
               => fun O_case S_case => Datatypes.nat_rect _ O_case S_case
             | list_rect A P
             | eager_list_rect A P
               => fun N_case C_case => Datatypes.list_rect _ (N_case Datatypes.tt) C_case
             | list_rect_arrow A P Q
             | eager_list_rect_arrow A P Q
               => fun N_case C_case => Datatypes.list_rect _ N_case C_case
             | list_case A P
               => fun N_case C_case => ListUtil.list_case _ (N_case Datatypes.tt) C_case
             | List_length T => @List.length _
             | List_seq => List.seq
             | List_firstn A => @List.firstn _
             | List_skipn A => @List.skipn _
             | List_repeat A => @repeat _
             | List_combine A B => @List.combine _ _
             | List_map A B => @List.map _ _
             | List_app A => @List.app _
             | List_rev A => @List.rev _
             | List_flat_map A B => @List.flat_map _ _
             | List_partition A => @List.partition _
             | List_fold_right A B => @List.fold_right _ _
             | List_update_nth T => update_nth
             | List_nth_default T => @nth_default _
             | eager_List_nth_default T => @nth_default _
             | Z_add => Z.add
             | Z_mul => Z.mul
             | Z_pow => Z.pow
             | Z_sub => Z.sub
             | Z_opp => Z.opp
             | Z_div => Z.div
             | Z_modulo => Z.modulo
             | Z_eqb => Z.eqb
             | Z_leb => Z.leb
             | Z_ltb => Z.ltb
             | Z_geb => Z.geb
             | Z_gtb => Z.gtb
             | Z_log2 => Z.log2
             | Z_log2_up => Z.log2_up
             | Z_of_nat => Z.of_nat
             | Z_to_nat => Z.to_nat
             | Z_shiftr => Z.shiftr
             | Z_shiftl => Z.shiftl
             | Z_land => Z.land
             | Z_lor => Z.lor
             | Z_min => Z.min
             | Z_max => Z.max
             | Z_mul_split => Z.mul_split
             | Z_add_get_carry => Z.add_get_carry_full
             | Z_add_with_carry => Z.add_with_carry
             | Z_add_with_get_carry => Z.add_with_get_carry_full
             | Z_sub_get_borrow => Z.sub_get_borrow_full
             | Z_sub_with_get_borrow => Z.sub_with_get_borrow_full
             | Z_zselect => Z.zselect
             | Z_add_modulo => Z.add_modulo
             | Z_truncating_shiftl => Z.truncating_shiftl
             | Z_bneg => Z.bneg
             | Z_lnot_modulo => Z.lnot_modulo
             | Z_rshi => Z.rshi
             | Z_cc_m => Z.cc_m
             | Z_combine_at_bitwidth => Z.combine_at_bitwidth
             | Z_cast r => cast r
             | Z_cast2 (r1, r2) => fun '(x1, x2) => (cast r1 x1, cast r2 x2)
             | Some A => @Datatypes.Some _
             | None A => @Datatypes.None _
             | option_rect A P
               => fun S_case N_case o => @Datatypes.option_rect _ _ S_case (N_case Datatypes.tt) o
             | Build_zrange => ZRange.Build_zrange
             | zrange_rect A => @ZRange.zrange_rect _
             | fancy_add => ident.fancy.add
             | fancy_addc => ident.fancy.addc
             | fancy_sub => ident.fancy.sub
             | fancy_subb => ident.fancy.subb
             | fancy_mulll => ident.fancy.mulll
             | fancy_mullh => ident.fancy.mullh
             | fancy_mulhl => ident.fancy.mulhl
             | fancy_mulhh => ident.fancy.mulhh
             | fancy_rshi => ident.fancy.rshi
             | fancy_selc => ident.fancy.selc
             | fancy_selm => ident.fancy.selm
             | fancy_sell => ident.fancy.sell
             | fancy_addm => ident.fancy.addm
             end.
      End gen.
    End with_base.
    Notation Some := option_Some.
    Notation None := option_None.

    Global Instance buildEagerIdent : BuildEagerIdentT ident
      := {
          ident_nat_rect := @nat_rect
          ; ident_nat_rect_arrow := @nat_rect_arrow
          ; ident_list_rect := @list_rect
          ; ident_list_rect_arrow := @list_rect_arrow
          ; ident_List_nth_default := @List_nth_default
          ; ident_eager_nat_rect := @eager_nat_rect
          ; ident_eager_nat_rect_arrow := @eager_nat_rect_arrow
          ; ident_eager_list_rect := @eager_list_rect
          ; ident_eager_list_rect_arrow := @eager_list_rect_arrow
          ; ident_eager_List_nth_default := @eager_List_nth_default
        }.

    Global Instance buildInterpEagerIdentCorrect
           {cast_outside_of_range}
      : BuildInterpEagerIdentCorrectT (@ident.gen_interp cast_outside_of_range).
    Proof. split; cbn; reflexivity. Defined.

    Definition toRestrictedIdentAndCorrect
      : { toRestrictedIdent : ToRestrictedIdentT ident
                              & ToFromRestrictedIdentT ident }.
    Proof.
      unshelve eexists; hnf; [ | split ]; cbv;
        let idc := fresh "idc" in
        intros ? idc; destruct idc;
          try (((instantiate (1 := Datatypes.None) + idtac); reflexivity)).
    Defined.

    Definition fromRestrictedIdent : ToRestrictedIdentT ident
      := Eval hnf in projT1 toRestrictedIdentAndCorrect.
    Global Existing Instance fromRestrictedIdent.

    Definition toFromRestrictedIdent : ToFromRestrictedIdentT ident
      := Eval hnf in projT2 toRestrictedIdentAndCorrect.
    Global Existing Instance toFromRestrictedIdent.

    (** Interpret identifiers where [Z_cast] is an opaque identity
        function when the value is not inside the range *)
    Notation interp := (@gen_interp ident.cast_outside_of_range).
    Notation LiteralUnit := (@Literal base.type.unit).
    Notation LiteralZ := (@Literal base.type.Z).
    Notation LiteralBool := (@Literal base.type.bool).
    Notation LiteralNat := (@Literal base.type.nat).
    Notation LiteralZRange := (@Literal base.type.zrange).

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

    Ltac reify
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
        let rT := base.reify_base T in
        then_tac (@ident.Literal rT term)
      | false
        =>
        lazymatch term with
        | Nat.succ => then_tac Nat_succ
        | Nat.add => then_tac Nat_add
        | Nat.sub => then_tac Nat_sub
        | Nat.eqb => then_tac Nat_eqb
        | Nat.mul => then_tac Nat_mul
        | Nat.max => then_tac Nat_max
        | Nat.pred => then_tac Nat_pred
        | Datatypes.S => then_tac Nat_succ
        | Datatypes.tt => then_tac tt
        | @Datatypes.nil ?T
          => let rT := base.reify T in
             then_tac (@ident.nil rT)
        | @Datatypes.cons ?T
          => let rT := base.reify T in
             then_tac (@ident.cons rT)
        | @Datatypes.fst ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.fst rA rB)
        | @Datatypes.snd ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.snd rA rB)
        | @Datatypes.pair ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.pair rA rB)
        | @Datatypes.bool_rect ?T0 ?Ptrue ?Pfalse
          => lazymatch (eval cbv beta in T0) with
            | fun _ => ?T => reify_rec (@ident.Thunked.bool_rect T (fun _ : Datatypes.unit => Ptrue) (fun _ : Datatypes.unit => Pfalse))
            | T0 => else_tac ()
            | ?T' => reify_rec (@Datatypes.bool_rect T' Ptrue Pfalse)
            end
        | @ident.Thunked.bool_rect ?T
          => let rT := base.reify T in
             then_tac (@ident.bool_rect rT)
        | @Datatypes.option_rect ?A ?T0 ?PSome ?PNone
          => lazymatch (eval cbv beta in T0) with
             | fun _ => ?T => reify_rec (@ident.Thunked.option_rect A T PSome (fun _ : Datatypes.unit => PNone))
             | T0 => else_tac ()
             | ?T' => reify_rec (@Datatypes.option_rect A T' PSome PNone)
             end
        | @ident.Thunked.option_rect ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.option_rect rA rT)
        | @Datatypes.prod_rect ?A ?B ?T0
          => lazymatch (eval cbv beta in T0) with
            | fun _ => ?T
              => let rA := base.reify A in
                let rB := base.reify B in
                let rT := base.reify T in
                then_tac (@ident.prod_rect rA rB rT)
            | T0 => else_tac ()
            | ?T' => reify_rec (@Datatypes.prod_rect A B T')
            end
        | @ZRange.zrange_rect ?T0
          => lazymatch (eval cbv beta in T0) with
             | fun _ => ?T
               => let rT := base.reify T in
                  then_tac (@ident.zrange_rect rT)
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
               => let rP := base.reify P in
                  let rQ := base.reify Q in
                  then_tac (@ident.nat_rect_arrow rP rQ)
             | T0 => else_tac ()
             | ?T' => reify_rec (@Datatypes.nat_rect T')
             end
        | @ident.Thunked.nat_rect ?T
          => let rT := base.reify T in
             then_tac (@ident.nat_rect rT)
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
               => let rP := base.reify P in
                  let rQ := base.reify Q in
                  then_tac (@ident.eager_nat_rect_arrow rP rQ)
             | T0 => else_tac ()
             | ?T' => reify_rec (ident.eagerly (@Datatypes.nat_rect) T')
            end
        | ident.eagerly (@ident.Thunked.nat_rect) ?T
          => let rT := base.reify T in
             then_tac (@ident.eager_nat_rect rT)
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
               => let rA := base.reify A in
                  let rP := base.reify P in
                  let rQ := base.reify Q in
                  then_tac (@ident.list_rect_arrow rA rP rQ)
             | T0 => else_tac ()
             | ?T' => reify_rec (@Datatypes.list_rect A T')
             end
        | @ident.Thunked.list_rect ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.list_rect rA rT)
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
               => let rA := base.reify A in
                  let rP := base.reify P in
                  let rQ := base.reify Q in
                  then_tac (@ident.eager_list_rect_arrow rA rP rQ)
             | T0 => else_tac ()
             | ?T' => reify_rec (ident.eagerly (@Datatypes.list_rect) A T')
             end
        | ident.eagerly (@ident.Thunked.list_rect) ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.eager_list_rect rA rT)
        | @ListUtil.list_case ?A ?T0 ?Pnil
          => lazymatch (eval cbv beta in T0) with
            | fun _ => ?T => reify_rec (@ident.Thunked.list_case A T (fun _ : Datatypes.unit => Pnil))
            | T0 => else_tac ()
            | ?T' => reify_rec (@ListUtil.list_case A T' Pnil)
            end
        | @ident.Thunked.list_case ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.list_case rA rT)
        | @List.length ?A =>
          let rA := base.reify A in
          then_tac (@ident.List_length rA)
        | List.seq => then_tac ident.List_seq
        | @List.firstn ?A
          => let rA := base.reify A in
             then_tac (@ident.List_firstn rA)
        | @List.skipn ?A
          => let rA := base.reify A in
             then_tac (@ident.List_skipn rA)
        | @repeat ?A
          => let rA := base.reify A in
             then_tac (@ident.List_repeat rA)
        | @List.combine ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.List_combine rA rB)
        | @List.map ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.List_map rA rB)
        | @List.flat_map ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.List_flat_map rA rB)
        | @List.partition ?A
          => let rA := base.reify A in
             then_tac (@ident.List_partition rA)
        | @List.app ?A
          => let rA := base.reify A in
             then_tac (@ident.List_app rA)
        | @List.map ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.List_map rA rB)
        | @List.rev ?A
          => let rA := base.reify A in
             then_tac (@ident.List_rev rA)
        | @List.fold_right ?A ?B
          => let rA := base.reify A in
             let rB := base.reify B in
             then_tac (@ident.List_fold_right rA rB)
        | @update_nth ?T
          => let rT := base.reify T in
             then_tac (@ident.List_update_nth rT)
        | @List.nth_default ?T
          => let rT := base.reify T in
             then_tac (@ident.List_nth_default rT)
        | ident.eagerly (@List.nth_default) ?T
          => let rT := base.reify T in
             then_tac (@ident.eager_List_nth_default rT)
        | Z.add => then_tac ident.Z_add
        | Z.mul => then_tac ident.Z_mul
        | Z.pow => then_tac ident.Z_pow
        | Z.sub => then_tac ident.Z_sub
        | Z.opp => then_tac ident.Z_opp
        | Z.div => then_tac ident.Z_div
        | Z.modulo => then_tac ident.Z_modulo
        | Z.eqb => then_tac ident.Z_eqb
        | Z.leb => then_tac ident.Z_leb
        | Z.ltb => then_tac ident.Z_ltb
        | Z.geb => then_tac ident.Z_geb
        | Z.gtb => then_tac ident.Z_gtb
        | Z.log2 => then_tac ident.Z_log2
        | Z.log2_up => then_tac ident.Z_log2_up
        | Z.shiftl => then_tac ident.Z_shiftl
        | Z.shiftr => then_tac ident.Z_shiftr
        | Z.land => then_tac ident.Z_land
        | Z.lor => then_tac ident.Z_lor
        | Z.min => then_tac ident.Z_min
        | Z.max => then_tac ident.Z_max
        | Z.bneg => then_tac ident.Z_bneg
        | Z.lnot_modulo => then_tac ident.Z_lnot_modulo
        | Z.truncating_shiftl => then_tac ident.Z_truncating_shiftl
        | Z.of_nat => then_tac ident.Z_of_nat
        | Z.to_nat => then_tac ident.Z_to_nat
        | Z.mul_split => then_tac ident.Z_mul_split
        | Z.add_get_carry_full => then_tac ident.Z_add_get_carry
        | Z.add_with_carry => then_tac ident.Z_add_with_carry
        | Z.add_with_get_carry_full => then_tac ident.Z_add_with_get_carry
        | Z.sub_get_borrow_full => then_tac ident.Z_sub_get_borrow
        | Z.sub_with_get_borrow_full => then_tac ident.Z_sub_with_get_borrow
        | Z.zselect => then_tac ident.Z_zselect
        | Z.add_modulo => then_tac ident.Z_add_modulo
        | Z.rshi => then_tac ident.Z_rshi
        | Z.cc_m => then_tac ident.Z_cc_m
        | Z.combine_at_bitwidth => then_tac ident.Z_combine_at_bitwidth
        | ident.cast _ ?r => then_tac (ident.Z_cast r)
        | ident.cast2 _ ?r => then_tac (ident.Z_cast2 r)
        | @Some ?A
          => let rA := base.reify A in
             then_tac (@ident.Some rA)
        | @None ?A
          => let rA := base.reify A in
             then_tac (@ident.None rA)
        | ZRange.Build_zrange => then_tac ident.Build_zrange
        | ident.fancy.add => then_tac ident.fancy_add
        | ident.fancy.addc => then_tac ident.fancy_addc
        | ident.fancy.sub => then_tac ident.fancy_sub
        | ident.fancy.subb => then_tac ident.fancy_subb
        | ident.fancy.mulll => then_tac ident.fancy_mulll
        | ident.fancy.mullh => then_tac ident.fancy_mullh
        | ident.fancy.mulhl => then_tac ident.fancy_mulhl
        | ident.fancy.mulhh => then_tac ident.fancy_mulhh
        | ident.fancy.rshi => then_tac ident.fancy_rshi
        | ident.fancy.selc => then_tac ident.fancy_selc
        | ident.fancy.selm => then_tac ident.fancy_selm
        | ident.fancy.sell => then_tac ident.fancy_sell
        | ident.fancy.addm => then_tac ident.fancy_addm
        | ident.eagerly (?f ?x) => reify_rec (ident.eagerly f x)
        | @gen_interp _ _ ?idc => then_tac idc
        | _ => else_tac ()
        end
      end.

    Global Instance buildIdent : @BuildIdentT base.type.base base.base_interp ident | 5
      := { ident_Literal := @Literal
           ; ident_nil := @nil
           ; ident_cons := @cons
           ; ident_Some := @Some
           ; ident_None := @None
           ; ident_pair := @pair
           ; ident_tt := @tt
         }.

    Definition is_var_like {t} (idc : ident t) : bool
      := match idc with
         | Literal _ _
         | nil _
         | cons _
         | pair _ _
         | fst _ _
         | snd _ _
         | Z_opp
         | Z_cast _
         | Z_cast2 _
         | Z_combine_at_bitwidth
           => Datatypes.true
         | _ => Datatypes.false
         end.

    Global Instance buildInterpIdentCorrect {cast_outside_of_range}
      : @BuildInterpIdentCorrectT base.type.base base.base_interp ident _ (@ident.gen_interp cast_outside_of_range).
    Proof. constructor; cbn; reflexivity. Qed.


    Global Instance gen_eqv_Reflexive_Proper cast_outside_of_range {t} (idc : ident t) : Proper type.eqv (ident.gen_interp cast_outside_of_range idc) | 1.
    Proof.
      destruct idc; cbn [type.eqv ident.gen_interp type.interp base.interp base.base_interp];
        try solve [ typeclasses eauto
                  | cbv [respectful]; repeat intro; subst; destruct_head_hnf bool; destruct_head_hnf prod; destruct_head_hnf option; destruct_head_hnf zrange; eauto
                  | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper || apply list_rect_arrow_Proper); repeat intro; eauto ].
    Qed.

    Global Instance eqv_Reflexive_Proper {t} (idc : ident t) : Proper type.eqv (ident.interp idc) | 1.
    Proof. exact _. Qed.

    Global Instance gen_interp_Proper {cast_outside_of_range} {t} : Proper (@eq (ident t) ==> type.eqv) (ident.gen_interp cast_outside_of_range) | 1.
    Proof. intros idc idc' ?; subst idc'; apply gen_eqv_Reflexive_Proper. Qed.

    Global Instance interp_Proper {t} : Proper (@eq (ident t) ==> type.eqv) ident.interp | 1.
    Proof. exact _. Qed.
  End ident.
  Notation ident := ident.ident.

  Global Strategy -1000 [base.base_interp ident.gen_interp].

  Module Import invert_expr.
    Export Language.Compilers.invert_expr.
    Module ident.
      Definition invert_Literal {t} (idc : ident t) : option (type.interp base.interp t)
        := match idc with
           | ident.Literal _ n => Some n
           | _ => None
           end.

      Global Instance InvertIdent : @InvertIdentT base.type.base base.base_interp ident
        := {
            invert_ident_Literal := @invert_Literal
            ; is_nil t idc := match idc with ident.nil _ => true | _ => false end
            ; is_cons t idc := match idc with ident.cons _ => true | _ => false end
            ; is_Some t idc := match idc with ident.Some _ => true | _ => false end
            ; is_None t idc := match idc with ident.None _ => true | _ => false end
            ; is_pair t idc := match idc with ident.pair _ _ => true | _ => false end
            ; is_tt t idc := match idc with ident.tt => true | _ => false end
          }.

      Global Instance buildInvertIdentCorrect : @BuildInvertIdentCorrectT base.type.base base.base_interp ident _ _.
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
    End ident.
  End invert_expr.

  Module DefaultValue.
    Export Language.Compilers.DefaultValue.
    (** This module provides "default" inhabitants for the
        interpretation of PHOAS types and for the PHOAS [expr] type.
        These values are used for things like [nth_default] and in
        other places where we need to provide a dummy value in cases
        that will never actually be reached in correctly used code. *)
    Module type.
      Export Language.Compilers.DefaultValue.type.
      Module base.
        Export Language.Compilers.DefaultValue.type.base.
        Local Ltac inhabit := (constructor; fail) + (constructor; inhabit).
        Local Ltac build_base_default base base_interp :=
          constr:(ltac:(let t := fresh "t" in
                        intro t; destruct t; hnf; inhabit)
                  : @DefaultT base base_interp).
        Local Ltac make_base_default base base_interp := let res := build_base_default base base_interp in refine res.
        Global Instance base_default : @DefaultT base.type.base base.base_interp
          := ltac:(make_base_default base.type.base base.base_interp).
      End base.
    End type.
  End DefaultValue.

  Module expr.
    Global Hint Extern 1 (@expr.Reified_of _ ident _ _ ?t ?v ?e)
    => solve [ let rv := expr.Reify (Language.Compilers.base.type base.type.base) ident ltac:(base.reify) ltac:(ident.reify) v in unify e rv; reflexivity | idtac "ERROR: Failed to reify" v "(of type" t "); try setting Reify.debug_level to see output" ]
       : typeclass_instances.
  End expr.

  Module Classes.
    Export Language.Compilers.Classes.
    Global Instance exprInfo : ExprInfoT :=
      {
        base := base.type.base;
        ident := ident.ident;
        base_interp := base.base_interp;
        ident_gen_interp := ident.gen_interp
      }.

    Definition exprExtraInfo : ExprExtraInfoT.
    Proof.
      econstructor; typeclasses eauto.
    Defined.
  End Classes.
End Compilers.
