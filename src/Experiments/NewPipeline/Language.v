Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.DebugPrint.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Module Reify.
    (** Change this with [Ltac reify_debug_level ::= constr:(1).] to get
        more debugging. *)
    Ltac debug_level := constr:(0%nat).

    Tactic Notation "debug_enter_reify_idtac" ident(funname) uconstr(e)
      := idtac funname ": Attempting to reify:" e.
    Tactic Notation "debug_leave_reify_success_idtac" ident(funname) uconstr(e) uconstr(ret)
      := idtac funname ": Success in reifying:" e "as" ret.
    Tactic Notation "debug_leave_reify_failure_idtac" ident(funname) uconstr(e)
      := idtac funname ": Failure in reifying:" e.
    Ltac check_debug_level_then_Set _ :=
      let lvl := debug_level in
      lazymatch type of lvl with
      | nat => constr:(Set)
      | ?T => constr_run_tac ltac:(fun _ => idtac "Error: debug_level should have type nat but instead has type" T)
      end.
    Ltac debug0 tac :=
      constr_run_tac tac.
    Ltac debug1 tac :=
      let lvl := debug_level in
      lazymatch lvl with
      | S _ => constr_run_tac tac
      | _ => check_debug_level_then_Set ()
      end.
    Ltac debug2 tac :=
      let lvl := debug_level in
      lazymatch lvl with
      | S (S _) => constr_run_tac tac
      | _ => check_debug_level_then_Set ()
      end.
    Ltac debug3 tac :=
      let lvl := debug_level in
      lazymatch lvl with
      | S (S (S _)) => constr_run_tac tac
      | _ => check_debug_level_then_Set ()
      end.
    Ltac debug_enter_reify_base_type e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_base_type e).
    Ltac debug_enter_reify_type e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_type e).
    Ltac debug_enter_reify_in_context e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_in_context e).
    Ltac debug_leave_reify_in_context_success e ret := debug3 ltac:(fun _ => debug_leave_reify_success_idtac reify_in_context e ret).
    Ltac debug_leave_reify_in_context_failure e
      := let dummy := debug0 ltac:(fun _ => debug_leave_reify_failure_idtac reify_in_context e) in
         constr:(I : I).
    Ltac debug_leave_reify_base_type_failure e
      := let dummy := debug0 ltac:(fun _ => debug_leave_reify_failure_idtac reify_base_type e) in
         constr:(I : I).
    Tactic Notation "idtac_reify_in_context_case" ident(case) :=
      idtac "reify_in_context:" case.
    Ltac debug_reify_in_context_case tac :=
      debug3 tac.
    Ltac debug_enter_reify_abs e := debug2 ltac:(fun _ => debug_enter_reify_idtac reify_abs e).
  End Reify.

  Module type.
    Inductive type (base_type : Type) := base (t : base_type) | arrow (s d : type base_type).
    Global Arguments base {_}.
    Global Arguments arrow {_} s d.

    Fixpoint final_codomain {base_type} (t : type base_type) : base_type
      := match t with
         | base t
           => t
         | arrow s d => @final_codomain base_type d
         end.

    Fixpoint uncurried_domain {base_type} prod s (t : type base_type) : type base_type
      := match t with
         | base t
           => s
         | arrow s' d => @uncurried_domain base_type prod (prod s s') d
         end.

    Fixpoint for_each_lhs_of_arrow {base_type} (f : type base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => unit
         | arrow s d => f s * @for_each_lhs_of_arrow _ f d
         end.

    (** Denote [type]s into their interpretation in [Type]/[Set] *)
    Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => base_interp t
         | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
         end.

    Fixpoint app_curried {base_type} {f : base_type -> Type} {t : type base_type}
      : interp f t -> for_each_lhs_of_arrow (interp f) t -> f (final_codomain t)
      := match t with
         | base t => fun v _ => v
         | arrow s d => fun F x_xs => @app_curried _ f d (F (fst x_xs)) (snd x_xs)
         end.

    Fixpoint app_curried_gen {base_type} {f : type base_type -> Type} (app : forall s d, f (arrow s d) -> f s -> f d)
             {t : type base_type}
      : f t -> for_each_lhs_of_arrow f t -> f (base (final_codomain t))
      := match t with
         | base t => fun v _ => v
         | arrow s d => fun F x_xs => @app_curried_gen _ f app d (app _ _ F (fst x_xs)) (snd x_xs)
         end.

    Fixpoint map_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
             (F : forall t, f t -> g t)
             {t}
      : for_each_lhs_of_arrow f t -> for_each_lhs_of_arrow g t
      := match t with
         | base t => fun 'tt => tt
         | arrow s d => fun '(x, xs) => (F s x, @map_for_each_lhs_of_arrow _ f g F d xs)
         end.

    Fixpoint andb_bool_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
             (R : forall t, f t -> g t -> bool)
             {t}
      : for_each_lhs_of_arrow f t -> for_each_lhs_of_arrow g t -> bool
      := match t with
         | base t => fun _ _ => true
         | arrow s d => fun x_xs y_ys => R s (fst x_xs) (fst y_ys) && @andb_bool_for_each_lhs_of_arrow _ f g R d (snd x_xs) (snd y_ys)
         end%bool.

    Section interpM.
      Context {base_type} (M : Type -> Type) (base_interp : base_type -> Type).
      (** half-monadic denotation function; denote [type]s into their
          interpretation in [Type]/[Set], wrapping the codomain of any
          arrow in [M]. *)
      Fixpoint interpM (t : type base_type) : Type
        := match t with
           | base t => base_interp t
           | arrow s d => @interpM s -> M (@interpM d)
           end.
      Fixpoint interpM_final' (withM : bool) (t : type base_type)
        := match t with
           | base t => if withM then M (base_interp t) else base_interp t
           | arrow s d => interpM_final' false s -> interpM_final' true d
           end.
      Definition interpM_final := interpM_final' true.

      Fixpoint interpM_return (t : type base_type) : M (base_interp (final_codomain t)) -> interpM_final t
        := match t with
           | base t => fun v => v
           | arrow s d => fun v _ => @interpM_return d v
           end.
    End interpM.

    Definition domain {base_type} (default : base_type) (t : type base_type)
      : type base_type
      := match t with
         | arrow s d => s
         | base _ => base default
         end.

    Definition codomain {base_type} (t : type base_type) : type base_type
      := match t with
         | arrow s d => d
         | t => t
         end.

    Section transport_cps.
      Context {base_type}
              (try_make_transport_base_type_cps : forall (P : base_type -> Type) t1 t2, ~> option (P t1 -> P t2)).

      Fixpoint try_make_transport_cps (P : type base_type -> Type) (t1 t2 : type base_type)
        : ~> option (P t1 -> P t2)
        := match t1, t2 with
           | base t1, base t2 => try_make_transport_base_type_cps (fun t => P (base t)) t1 t2
           | arrow s1 d1, arrow s2 d2
             => (trs <-- try_make_transport_cps (fun s => P (arrow s _)) _ _;
                  trd <-- try_make_transport_cps (fun d => P (arrow _ d)) _ _;
                return (Some (fun v => trd (trs v))))
           | base _, _
           | arrow _ _, _
             => (return None)
           end%cps.

      Definition try_transport_cps (P : type base_type -> Type) (t1 t2 : type base_type) (v : P t1) : ~> option (P t2)
        := (tr <-- try_make_transport_cps P t1 t2;
            return (Some (tr v)))%cps.

      Definition try_transport (P : type base_type -> Type) (t1 t2 : type base_type) (v : P t1) : option (P t2)
        := try_transport_cps P t1 t2 v _ id.
    End transport_cps.

    (*
    Fixpoint try_transport {base_type}
             (try_transport_base_type : forall (P : base_type -> Type) t1 t2, P t1 -> option (P t2))
             (P : type base_type -> Type) (t1 t2 : type base_type) : P t1 -> option (P t2)
      := match t1, t2 return P t1 -> option (P t2) with
         | base t1, base t2
           => try_transport_base_type (fun t => P (base t)) t1 t2
         | arrow s d, arrow s' d'
           => fun v
             => (v <- (try_transport
                       try_transport_base_type (fun s => P (arrow s d))
                       s s' v);
                  (try_transport
                     try_transport_base_type (fun d => P (arrow s' d))
                     d d' v))%option
         | base _, _
         | arrow _ _, _
           => fun _ => None
         end.
*)

    Ltac reify base_reify base_type ty :=
      let __ := Reify.debug_enter_reify_type ty in
      let reify_rec t := reify base_reify base_type t in
      lazymatch eval cbv beta in ty with
      | ?A -> ?B
        => let rA := reify_rec A in
           let rB := reify_rec B in
           constr:(@arrow base_type rA rB)
      | @interp _ _ ?T => T
      | _ => let rt := base_reify ty in
             constr:(@base base_type rt)
      end.
  End type.
  Notation type := type.type.
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.type.
  Infix "->" := type.arrow : etype_scope.
  Module base.
    Local Notation einterp := type.interp.
    Module type.
      Inductive base := unit | Z | bool | nat. (* Not Variant because COQBUG(https://github.com/coq/coq/issues/7738) *)
      Inductive type := type_base (t : base) | prod (A B : type) | list (A : type).
      Global Coercion type_base : base >-> type.
    End type.
    Global Coercion type.type_base : type.base >-> type.type.
    Notation type := type.type.
    Definition base_interp (ty : type.base)
      := match ty with
         | type.unit => Datatypes.unit
         | type.Z => BinInt.Z
         | type.bool => Datatypes.bool
         | type.nat => Datatypes.nat
         end.
    Fixpoint interp (ty : type)
      := match ty with
         | type.type_base t => base_interp t
         | type.prod A B => interp A * interp B
         | type.list A => Datatypes.list (interp A)
         end%type.

    Definition try_make_base_transport_cps
               (P : type.base -> Type) (t1 t2 : type.base)
      : ~> option (P t1 -> P t2)
      := match t1, t2 with
         | type.unit, type.unit
         | type.Z, type.Z
         | type.bool, type.bool
         | type.nat, type.nat
           => (return (Some id))
         | type.unit, _
         | type.Z, _
         | type.bool, _
         | type.nat, _
           => (return None)
         end%cps.
    Fixpoint try_make_transport_cps
             (P : type -> Type) (t1 t2 : type)
      : ~> option (P t1 -> P t2)
      := match t1, t2 with
         | type.type_base t1, type.type_base t2
           => try_make_base_transport_cps (fun t => P (type.type_base t)) t1 t2
         | type.prod A B, type.prod A' B'
           => (trA <-- try_make_transport_cps (fun A => P (type.prod A _)) _ _;
                trB <-- try_make_transport_cps (fun B => P (type.prod _ B)) _ _;
              return (Some (fun v => trB (trA v))))
         | type.list A, type.list A' => try_make_transport_cps (fun A => P (type.list A)) A A'
         | type.type_base _, _
         | type.prod _ _, _
         | type.list _, _
           => (return None)
         end%cps.

    Definition try_transport_cps (P : type -> Type) (t1 t2 : type) (v : P t1) : ~> option (P t2)
      := (tr <-- try_make_transport_cps P t1 t2;
            return (Some (tr v)))%cps.

    Definition try_transport (P : type -> Type) (t1 t2 : type) (v : P t1) : option (P t2)
      := try_transport_cps P t1 t2 v _ id.
    (*
    Fixpoint try_transport
             (P : type -> Type) (t1 t2 : type) : P t1 -> option (P t2)
      := match t1, t2 return P t1 -> option (P t2) with
         | type.unit, type.unit
         | type.Z, type.Z
         | type.bool, type.bool
         | type.nat, type.nat
           => @Some _
         | type.list A, type.list A'
           => @try_transport (fun A => P (type.list A)) A A'
         | type.prod s d, type.prod s' d'
           => fun v
              => (v <- (try_transport (fun s => P (type.prod s d)) s s' v);
                    (try_transport (fun d => P (type.prod s' d)) d d' v))%option

         | type.unit, _
         | type.Z, _
         | type.bool, _
         | type.nat, _
         | type.prod _ _, _
         | type.list _, _
           => fun _ => None
         end.
     *)

    Ltac reify_base ty :=
      let __ := Reify.debug_enter_reify_base_type ty in
      lazymatch eval cbv beta in ty with
      | Datatypes.unit => type.unit
      | Datatypes.nat => type.nat
      | Datatypes.bool => type.bool
      | BinInt.Z => type.Z
      | interp (type.type_base ?T) => T
      | @einterp type interp (@Compilers.type.base type (type.type_base ?T)) => T
      | _ => let __ := match goal with
                      | _ => fail 1 "Unrecognized type:" ty
                      end in
            constr:(I : I)
      end.
    Ltac reify ty :=
      let __ := Reify.debug_enter_reify_base_type ty in
      lazymatch eval cbv beta in ty with
      | Datatypes.prod ?A ?B
        => let rA := reify A in
          let rB := reify B in
          constr:(type.prod rA rB)
      | Datatypes.list ?T
        => let rT := reify T in
          constr:(type.list rT)
      | interp ?T => T
      | @einterp type interp (@Compilers.type.base type ?T) => T
      | ?ty => let rT := reify_base ty in
              constr:(@type.type_base rT)
      end.
    Notation reify_base t := (ltac:(let rt := reify_base t in exact rt)) (only parsing).
    Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
    Notation reify_norm_base t := (ltac:(let t' := eval cbv in t in let rt := reify_base t' in exact rt)) (only parsing).
    Notation reify_norm t := (ltac:(let t' := eval cbv in t in let rt := reify t' in exact rt)) (only parsing).
    Notation reify_base_type_of e := (reify_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_base_type_of e := (reify_norm_base ((fun t (_ : t) => t) _ e)) (only parsing).
    Notation reify_norm_type_of e := (reify_norm ((fun t (_ : t) => t) _ e)) (only parsing).
  End base.
  Global Coercion base.type.type_base : base.type.base >-> base.type.type.
  Bind Scope etype_scope with base.type.
  Infix "*" := base.type.prod : etype_scope.
  Notation "()" := (base.type.type_base base.type.unit) : etype_scope.

  Module expr.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.

      Inductive expr : type -> Type :=
      | Ident {t} (idc : ident t) : expr t
      | Var {t} (v : var t) : expr t
      | Abs {s d} (f : var s -> expr d) : expr (s -> d)
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
      .
    End with_var.

    Fixpoint interp {base_type ident} {interp_base_type : base_type -> Type}
             (interp_ident : forall t, ident t -> type.interp interp_base_type t)
             {t} (e : @expr base_type ident (type.interp interp_base_type) t)
      : type.interp interp_base_type t
      := match e in expr t return type.interp _ t with
         | Ident t idc => interp_ident _ idc
         | Var t v => v
         | Abs s d f => fun x => @interp _ _ _ interp_ident _ (f x)
         | App s d f x => (@interp _ _ _ interp_ident _ f)
                            (@interp _ _ _ interp_ident _ x)
         | LetIn A B x f
           => dlet y := @interp _ _ _ interp_ident _ x in
               @interp _ _ _ interp_ident _ (f y)
         end.

    Definition Expr {base_type ident} t := forall var, @expr base_type ident var t.
    Definition APP {base_type ident s d} (f : Expr (s -> d)) (x : Expr s) : Expr d
      := fun var => @App base_type ident var s d (f var) (x var).

    Definition Interp {base_type ident interp_base_type} interp_ident {t} (e : @Expr base_type ident t)
      : type.interp interp_base_type t
      := @interp base_type ident interp_base_type interp_ident t (e _).

    (** [Interp (APP _ _)] is the same thing as Gallina application of
        the [Interp]retations of the two arguments to [APP]. *)
    Definition Interp_APP {base_type ident interp_base_type interp_ident} {s d} (f : @Expr base_type ident (s -> d)) (x : @Expr base_type ident s)
      : @Interp base_type ident interp_base_type interp_ident _ (APP f x)
        = Interp interp_ident f (Interp interp_ident x)
      := eq_refl.

    (** Same as [Interp_APP], but for any reflexive relation, not just
        [eq] *)
    Definition Interp_APP_rel_reflexive {base_type ident interp_base_type interp_ident} {s d} {R} {H:Reflexive R}
               (f : @Expr base_type ident (s -> d)) (x : @Expr base_type ident s)
      : R (@Interp base_type ident interp_base_type interp_ident _ (APP f x))
          (Interp interp_ident f (Interp interp_ident x))
      := H _.

    Module var_context.
      Inductive list {base_type} {var : type base_type -> Type} :=
      | nil
      | cons {T t} (gallina_v : T) (v : var t) (ctx : list).
    End var_context.

    (* cf COQBUG(https://github.com/coq/coq/issues/5448) , COQBUG(https://github.com/coq/coq/issues/6315) , COQBUG(https://github.com/coq/coq/issues/6559) , COQBUG(https://github.com/coq/coq/issues/6534) , https://github.com/mit-plv/fiat-crypto/issues/320 *)
    Ltac require_same_var n1 n2 :=
      (*idtac n1 n2;*)
      let c1 := constr:(fun n1 n2 : Set => ltac:(exact n1)) in
      let c2 := constr:(fun n1 n2 : Set => ltac:(exact n2)) in
      (*idtac c1 c2;*)
      first [ constr_eq c1 c2 | fail 1 "Not the same var:" n1 "and" n2 "(via constr_eq" c1 c2 ")" ].
    Ltac is_same_var n1 n2 :=
      match goal with
      | _ => let check := match goal with _ => require_same_var n1 n2 end in
             true
      | _ => false
      end.
    Ltac is_underscore v :=
      let v' := fresh v in
      let v' := fresh v' in
      is_same_var v v'.
    Ltac refresh n fresh_tac :=
      let n_is_underscore := is_underscore n in
      let n' := lazymatch n_is_underscore with
                | true => fresh
                | false => fresh_tac n
                end in
      let n' := fresh_tac n' in
      n'.

    Ltac type_of_first_argument_of f :=
      let f_ty := type of f in
      lazymatch eval hnf in f_ty with
      | forall x : ?T, _ => T
      end.

    (** Forms of abstraction in Gallina that our reflective language
        cannot handle get handled by specializing the code "template"
        to each particular application of that abstraction. In
        particular, type arguments (nat, Z, (λ _, nat), etc) get
        substituted into lambdas and treated as a integral part of
        primitive operations (such as [@List.app T], [@list_rect (λ _,
        nat)]).  During reification, we accumulate them in a
        right-associated tuple, using [tt] as the "nil" base case.
        When we hit a λ or an identifier, we plug in the template
        parameters as necessary. *)
    Ltac require_template_parameter parameter_type :=
      first [ unify parameter_type Prop
            | unify parameter_type Set
            | unify parameter_type Type
            | lazymatch eval hnf in parameter_type with
              | forall x : ?T, @?P x
                => let check := constr:(fun x : T
                                        => ltac:(require_template_parameter (P x);
                                                 exact I)) in
                   idtac
              end ].
    Ltac is_template_parameter parameter_type :=
      is_success_run_tactic ltac:(fun _ => require_template_parameter parameter_type).
    Ltac plug_template_ctx f template_ctx :=
      lazymatch template_ctx with
      | tt => f
      | (?arg, ?template_ctx')
        =>
        let T := type_of_first_argument_of f in
        let x_is_template_parameter := is_template_parameter T in
        lazymatch x_is_template_parameter with
        | true
          => plug_template_ctx (f arg) template_ctx'
        | false
          => constr:(fun x : T
                     => ltac:(let v := plug_template_ctx (f x) template_ctx in
                              exact v))
        end
      end.

    Ltac reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx :=
      let reify_rec_gen term value_ctx template_ctx := reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx in
      let reify_rec term := reify_rec_gen term value_ctx template_ctx in
      let reify_rec_not_head term := reify_rec_gen term value_ctx tt in
      let do_reify_ident term else_tac
          := reify_ident
               term
               ltac:(fun idc => constr:(@Ident base_type ident var _ idc))
                      reify_rec
                      else_tac in
      let __ := Reify.debug_enter_reify_in_context term in
      lazymatch value_ctx with
      | context[@var_context.cons _ _ ?T ?rT term ?v _]
        => constr:(@Var base_type ident var rT v)
      | _
        =>
        lazymatch term with
        | match ?b with true => ?t | false => ?f end
          => let T := type of term in
             reify_rec (@bool_rect (fun _ => T) t f b)
        | match ?x with Datatypes.pair a b => ?f end
          => let x' := fresh in
             let T := type of x in
             reify_rec ((fun x' : T
                         => match Datatypes.fst x, Datatypes.snd x return _ with
                            | a, b => f
                            end) x)
        | match ?x with nil => ?N | cons a b => @?C a b end
          => let T := type of term in
             reify_rec (@list_case _ (fun _ => T) N C x)
        | let x := ?a in @?b x
          => let A := type of a in
             let B := lazymatch type of b with forall x, @?B x => B end in
             reify_rec (b a) (*(@Let_In A B a b)*)
        | @Let_In ?A ?B ?a ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             lazymatch rb with
             | @Abs _ _ _ ?s ?d ?f
               => constr:(@LetIn base_type ident var s d ra f)
             | ?rb => let __ := match goal with
                                | _ => fail 1 "Invalid non-Abs function reification of" b "to" rb
                                end in
                      constr:(I : I)
             end
        | (fun x : ?T => ?f)
          =>
          let x_is_template_parameter := is_template_parameter T in
          lazymatch x_is_template_parameter with
          | true
            =>
            lazymatch template_ctx with
            | (?arg, ?template_ctx)
              => (* we pull a trick with [match] to plug in [arg] without running cbv β *)
              lazymatch type of term with
              | forall y, ?P
                => reify_rec_gen (match arg as y return P with x => f end) value_ctx template_ctx
              end
            end
          | false
            =>
            let rT := type.reify reify_base_type base_type T in
            let not_x := fresh (* could be [refresh x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
            let not_x2 := fresh (* could be [refresh not_x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
            let not_x3 := fresh (* could be [refresh not_x2 ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
            (*let __ := match goal with _ => idtac "reify_in_context: λ case:" term "using vars:" not_x not_x2 not_x3 end in*)
            let rf0 :=
                constr:(
                  fun (x : T) (not_x : var rT)
                  => match f, @var_context.cons base_type var T rT x not_x value_ctx return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
                     | not_x2, not_x3
                       => ltac:(
                            let f := (eval cbv delta [not_x2] in not_x2) in
                            let var_ctx := (eval cbv delta [not_x3] in not_x3) in
                            (*idtac "rec call" f "was" term;*)
                            let rf := reify_rec_gen f var_ctx template_ctx in
                            exact rf)
                     end) in
            lazymatch rf0 with
            | (fun _ => ?rf)
              => constr:(@Abs base_type ident var rT _ rf)
            | _
              => (* This will happen if the reified term still
                    mentions the non-var variable.  By chance, [cbv
                    delta] strips type casts, which are only places
                    that I can think of where such dependency might
                    remain.  However, if this does come up, having a
                    distinctive error message is much more useful for
                    debugging than the generic "no matching clause" *)
              let __ := match goal with
                        | _ => fail 1 "Failure to eliminate functional dependencies of" rf0
                        end in
              constr:(I : I)
            end
          end
        | _
          =>
          do_reify_ident
            term
            ltac:(
            fun _
            =>
              lazymatch term with
              | ?f ?x
                =>
                let ty := type_of_first_argument_of f in
                let x_is_template_parameter := is_template_parameter ty in
                lazymatch x_is_template_parameter with
                | true
                  => (* we can't reify things of type [Type], so we save it for later to plug in *)
                  reify_rec_gen f value_ctx (x, template_ctx)
                | false
                  => let rx := reify_rec_gen x value_ctx tt in
                     let rf := reify_rec_gen f value_ctx template_ctx in
                     constr:(App (base_type:=base_type) (ident:=ident) (var:=var) rf rx)
                end
              | _
                => let term' := plug_template_ctx term template_ctx in
                   do_reify_ident
                     term'
                     ltac:(fun _
                           =>
                             (*let __ := match goal with _ => idtac "Attempting to unfold" term end in*)
                             let term
                                 := match constr:(Set) with
                                    | _ => (eval cbv delta [term] in term) (* might fail, so we wrap it in a match to give better error messages *)
                                    | _
                                      => let __ := match goal with
                                                   | _ => fail 2 "Unrecognized term:" term'
                                                   end in
                                         constr:(I : I)
                                    end in
                             reify_rec term)
              end)
        end
      end.
    Ltac reify base_type ident reify_base_type reify_ident var term :=
      reify_in_context base_type ident reify_base_type reify_ident var term (@var_context.nil base_type var) tt.
    Ltac Reify base_type ident reify_base_type reify_ident term :=
      constr:(fun var : type base_type -> Type
              => ltac:(let r := reify base_type ident reify_base_type reify_ident var term in
                       exact r)).
    Ltac Reify_rhs base_type ident reify_base_type reify_ident base_interp interp_ident _ :=
      let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
      let R := Reify base_type ident reify_base_type reify_ident RHS in
      transitivity (@Interp base_type ident base_interp interp_ident _ R);
      [ | reflexivity ].

    Module Export Notations.
      Delimit Scope expr_scope with expr.
      Delimit Scope Expr_scope with Expr.
      Delimit Scope expr_pat_scope with expr_pat.
      Bind Scope expr_scope with expr.
      Bind Scope Expr_scope with Expr.
      Infix "@" := App : expr_scope.
      Infix "@" := APP : Expr_scope.
      Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
      Notation "'λ' x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
      Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
      Notation "'$' x" := (Var x) (at level 10, format "'$' x") : expr_scope.
      Notation "### x" := (Ident x) : expr_scope.
    End Notations.
  End expr.
  Export expr.Notations.
  Notation expr := expr.expr.

  Module ident.
    Local Notation type := (type base.type).
    Local Notation ttype := type.
    Module fancy.
      Section with_base.
        Let type_base (x : base.type) : type := type.base x.
        Local Coercion type_base : base.type >-> type.
        Section with_scope.
          Import base.type.
          Notation type := ttype.

          Inductive ident_with_wordmax {log2wordmax : BinInt.Z} : base.type -> base.type -> Set :=
          | add (imm : BinInt.Z) : ident_with_wordmax (Z * Z) (Z * Z)
          | addc (imm : BinInt.Z) : ident_with_wordmax (Z * Z * Z) (Z * Z)
          | sub (imm : BinInt.Z) : ident_with_wordmax (Z * Z) (Z * Z)
          | subb (imm : BinInt.Z) : ident_with_wordmax (Z * Z * Z) (Z * Z)
          | mulll : ident_with_wordmax (Z * Z) Z
          | mullh : ident_with_wordmax (Z * Z) Z
          | mulhl : ident_with_wordmax (Z * Z) Z
          | mulhh : ident_with_wordmax (Z * Z) Z
          | selm : ident_with_wordmax (Z * Z * Z) Z
          | rshi : BinInt.Z -> ident_with_wordmax (Z * Z) Z
          .

          Inductive ident : base.type -> base.type -> Set :=
          | with_wordmax (log2wordmax : BinInt.Z) {s d} (idc : @ident_with_wordmax log2wordmax s d) : ident s d
          | selc : ident (Z * Z * Z) Z
          | sell : ident (Z * Z * Z) Z
          | addm : ident (Z * Z * Z) Z
          .

          Section interp_with_wordmax.
            Context (log2wordmax : BinInt.Z).
            Let wordmax := 2 ^ log2wordmax.
            Let half_bits := log2wordmax / 2.
            Let wordmax_half_bits := 2 ^ half_bits.

            Local Notation low x := (Z.land x (wordmax_half_bits - 1)).
            Local Notation high x := (x >> half_bits).
            Local Notation shift x imm := ((x << imm) mod wordmax).

            Definition interp_with_wordmax {s d} (idc : @ident_with_wordmax log2wordmax s d) : base.interp s -> base.interp d :=
              match idc with
              | add imm => fun x => Z.add_get_carry_full wordmax (fst x) (shift (snd x) imm)
              | addc imm => fun x => Z.add_with_get_carry_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
              | sub imm => fun x => Z.sub_get_borrow_full wordmax (fst x) (shift (snd x) imm)
              | subb imm => fun x => Z.sub_with_get_borrow_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
              | mulll => fun x => low (fst x) * low (snd x)
              | mullh => fun x => low (fst x) * high (snd x)
              | mulhl => fun x => high (fst x) * low (snd x)
              | mulhh => fun x => high (fst x) * high (snd x)
              | rshi n => fun x => Z.rshi wordmax (fst x) (snd x) n
              | selm => fun x => Z.zselect (Z.cc_m wordmax (fst (fst x))) (snd (fst x)) (snd x)
              end.
          End interp_with_wordmax.

          Definition interp {s d} (idc : @ident s d) : base.interp s -> base.interp d :=
            match idc with
            | with_wordmax lwm s d idc => interp_with_wordmax lwm idc
            | selc => fun x => Z.zselect (fst (fst x)) (snd (fst x)) (snd x)
            | sell => fun x => Z.zselect (Z.land (fst (fst x)) 1) (snd (fst x)) (snd x)
            | addm => fun x => Z.add_modulo (fst (fst x)) (snd (fst x)) (snd x)
            end.
        End with_scope.
      End with_base.
      Global Coercion with_wordmax : ident_with_wordmax >-> ident.
      Global Arguments interp_with_wordmax {_ s d} idc.
      Global Arguments interp {s d} idc.
    End fancy.

    Section with_base.
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Section with_scope.
        Import base.type.
        Notation type := ttype.

        (* N.B. [ident] must have essentially flat structure for the
           python script constructing [pattern.ident] to work *)
        Inductive ident : type -> Type :=
        | Literal {t:base.type.base} (v : base.interp t) : ident t
        | Nat_succ : ident (nat -> nat)
        | Nat_pred : ident (nat -> nat)
        | Nat_max : ident (nat -> nat -> nat)
        | Nat_mul : ident (nat -> nat -> nat)
        | Nat_add : ident (nat -> nat -> nat)
        | Nat_sub : ident (nat -> nat -> nat)
        | nil {t} : ident (list t)
        | cons {t:base.type} : ident (t -> list t -> list t)
        | pair {A B:base.type} : ident (A -> B -> A * B)
        | fst {A B} : ident (A * B -> A)
        | snd {A B} : ident (A * B -> B)
        | pair_rect {A B T:base.type} : ident ((A -> B -> T) -> A * B -> T)
        | bool_rect {T:base.type} : ident ((unit -> T) -> (unit -> T) -> bool -> T)
        | nat_rect {P:base.type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | list_rect {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | list_case {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P) -> list A -> P)
        | List_length {T} : ident (list T -> nat)
        | List_seq : ident (nat -> nat -> list nat)
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
        | Z_add : ident (Z -> Z -> Z)
        | Z_mul : ident (Z -> Z -> Z)
        | Z_pow : ident (Z -> Z -> Z)
        | Z_sub : ident (Z -> Z -> Z)
        | Z_opp : ident (Z -> Z)
        | Z_div : ident (Z -> Z -> Z)
        | Z_modulo : ident (Z -> Z -> Z)
        | Z_eqb : ident (Z -> Z -> bool)
        | Z_leb : ident (Z -> Z -> bool)
        | Z_of_nat : ident (nat -> Z)
        | Z_shiftr (offset : BinInt.Z) : ident (Z -> Z)
        | Z_shiftl (offset : BinInt.Z) : ident (Z -> Z)
        | Z_land (mask : BinInt.Z) : ident (Z -> Z)
        | Z_mul_split : ident (Z -> Z -> Z -> Z * Z)
        | Z_mul_split_concrete (s:BinInt.Z) : ident (Z -> Z -> Z * Z)
        | Z_add_get_carry : ident (Z -> Z -> Z -> (Z * Z))
        | Z_add_get_carry_concrete (s:BinInt.Z) : ident (Z -> Z -> (Z * Z))
        | Z_add_with_carry : ident (Z -> Z -> Z -> Z)
        | Z_add_with_get_carry : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_add_with_get_carry_concrete (s:BinInt.Z) : ident (Z -> Z -> Z -> Z * Z)
        | Z_sub_get_borrow : ident (Z -> Z -> Z -> (Z * Z))
        | Z_sub_get_borrow_concrete (s:BinInt.Z) : ident (Z -> Z -> Z * Z)
        | Z_sub_with_get_borrow : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_sub_with_get_borrow_concrete (s:BinInt.Z) : ident (Z -> Z -> Z -> Z * Z)
        | Z_zselect : ident (Z -> Z -> Z -> Z)
        | Z_add_modulo : ident (Z -> Z -> Z -> Z)
        | Z_rshi : ident (Z -> Z -> Z -> Z -> Z)
        | Z_rshi_concrete (s offset:BinInt.Z) : ident (Z -> Z -> Z)
        | Z_cc_m : ident (Z -> Z -> Z)
        | Z_cc_m_concrete (s:BinInt.Z) : ident (Z -> Z)
        | Z_neg_snd : ident ((Z * Z) -> Z * Z) (** TODO(jadep): This is only here for demonstration purposes; remove it once you no longer need it as a template; N.B. the type signature here says "given any amount of information about a thing of type [ℤ * ℤ], we promise to return a concrete pair of some amount of information about a thing of type ℤ and a thing of type ℤ" *)
        | Z_cast (range : zrange) : ident (Z -> Z)
        | Z_cast2 (range : zrange * zrange) : ident ((Z * Z) -> (Z * Z))
        | fancy_add (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z -> Z * Z)
        | fancy_addc (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z * Z -> Z * Z)
        | fancy_sub (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z -> Z * Z)
        | fancy_subb (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z * Z -> Z * Z)
        | fancy_mulll (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mullh (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mulhl (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mulhh (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_rshi (log2wordmax : BinInt.Z) : BinInt.Z -> ident (Z * Z -> Z)
        | fancy_selc : ident (Z * Z * Z -> Z)
        | fancy_selm (log2wordmax : BinInt.Z) : ident (Z * Z * Z -> Z)
        | fancy_sell : ident (Z * Z * Z -> Z)
        | fancy_addm : ident (Z * Z * Z -> Z)
        .

        Definition to_fancy {s d : base.type} (idc : ident (s -> d)) : option (fancy.ident s d)
          := match idc in ident t return option match t with
                                                | type.base s -> type.base d => fancy.ident s d
                                                | _ => Datatypes.unit
                                                end%etype with
             | fancy_add log2wordmax imm => Some (fancy.with_wordmax log2wordmax (fancy.add imm))
             | fancy_addc log2wordmax imm => Some (fancy.with_wordmax log2wordmax (fancy.addc imm))
             | fancy_sub log2wordmax imm => Some (fancy.with_wordmax log2wordmax (fancy.sub imm))
             | fancy_subb log2wordmax imm => Some (fancy.with_wordmax log2wordmax (fancy.subb imm))
             | fancy_mulll log2wordmax => Some (fancy.with_wordmax log2wordmax fancy.mulll)
             | fancy_mullh log2wordmax => Some (fancy.with_wordmax log2wordmax fancy.mullh)
             | fancy_mulhl log2wordmax => Some (fancy.with_wordmax log2wordmax fancy.mulhl)
             | fancy_mulhh log2wordmax => Some (fancy.with_wordmax log2wordmax fancy.mulhh)
             | fancy_rshi log2wordmax x => Some (fancy.with_wordmax log2wordmax (fancy.rshi x))
             | fancy_selc => Some fancy.selc
             | fancy_selm log2wordmax => Some (fancy.with_wordmax log2wordmax fancy.selm)
             | fancy_sell => Some fancy.sell
             | fancy_addm => Some fancy.addm
             | _ => None
             end.
      End with_scope.

      Section gen.
        Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

        Definition cast (r : zrange) (x : BinInt.Z)
          := if (lower r <=? x) && (x <=? upper r)
             then x
             else cast_outside_of_range r x.

        Local Notation wordmax log2wordmax := (2 ^ log2wordmax).
        Local Notation half_bits log2wordmax := (log2wordmax / 2).
        Local Notation wordmax_half_bits log2wordmax := (2 ^ (half_bits log2wordmax)).

        Local Notation low log2wordmax x := (Z.land x ((wordmax_half_bits log2wordmax) - 1)).
        Local Notation high log2wordmax x := (x >> (half_bits log2wordmax)).
        Local Notation shift log2wordmax x imm := ((x << imm) mod (wordmax log2wordmax)).

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
             | nil t => Datatypes.nil
             | cons t => Datatypes.cons
             | pair A B => Datatypes.pair
             | fst A B => Datatypes.fst
             | snd A B => Datatypes.snd
             | pair_rect A B T => fun f '((a, b) : base.interp A * base.interp B) => f a b
             | bool_rect T
               => fun t f => Datatypes.bool_rect _ (t tt) (f tt)
             | nat_rect P
               => fun O_case S_case => Datatypes.nat_rect _ (O_case tt) S_case
             | list_rect A P
               => fun N_case C_case => Datatypes.list_rect _ (N_case tt) C_case
             | list_case A P
               => fun N_case C_case => ListUtil.list_case _ (N_case tt) C_case
             | List_length T => @List.length _
             | List_seq => List.seq
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
             | Z_add => Z.add
             | Z_mul => Z.mul
             | Z_pow => Z.pow
             | Z_sub => Z.sub
             | Z_opp => Z.opp
             | Z_div => Z.div
             | Z_modulo => Z.modulo
             | Z_eqb => Z.eqb
             | Z_leb => Z.leb
             | Z_of_nat => Z.of_nat
             | Z_shiftr offset => fun v => Z.shiftr v offset
             | Z_shiftl offset => fun v => Z.shiftl v offset
             | Z_land mask => fun v => Z.land v mask
             | Z_mul_split => Z.mul_split
             | Z_mul_split_concrete s => Z.mul_split s
             | Z_add_get_carry => Z.add_get_carry_full
             | Z_add_get_carry_concrete s => Z.add_get_carry_full s
             | Z_add_with_carry => Z.add_with_carry
             | Z_add_with_get_carry => Z.add_with_get_carry_full
             | Z_add_with_get_carry_concrete s => Z.add_with_get_carry_full s
             | Z_sub_get_borrow => Z.sub_get_borrow_full
             | Z_sub_get_borrow_concrete s => Z.sub_get_borrow_full s
             | Z_sub_with_get_borrow => Z.sub_with_get_borrow_full
             | Z_sub_with_get_borrow_concrete s => Z.sub_with_get_borrow_full s
             | Z_zselect => Z.zselect
             | Z_add_modulo => Z.add_modulo
             | Z_rshi => Z.rshi
             | Z_rshi_concrete s offset => fun x y => Z.rshi s x y offset
             | Z_cc_m => Z.cc_m
             | Z_cc_m_concrete s => Z.cc_m s
             | Z_neg_snd => fun '(x, y) => (x, -y) (** TODO(jadep): This is only here for demonstration purposes; remove it once you no longer need it as a template *)
             | Z_cast r => cast r
             | Z_cast2 (r1, r2) => fun '(x1, x2) => (cast r1 x1, cast r2 x2)
             | fancy_add _ _ as idc
             | fancy_addc _ _ as idc
             | fancy_sub _ _ as idc
             | fancy_subb _ _ as idc
             | fancy_mulll _ as idc
             | fancy_mullh _ as idc
             | fancy_mulhl _ as idc
             | fancy_mulhh _ as idc
             | fancy_rshi _ _ as idc
             | fancy_selc as idc
             | fancy_selm _ as idc
             | fancy_sell as idc
             | fancy_addm as idc
               => fancy.interp (invert_Some (to_fancy idc))
             end.
      End gen.

      Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
      Proof. exact v. Qed.

      (** Interpret identifiers where [Z_cast] is an opaque identity
         function when the value is not inside the range *)
      Definition interp {t} (idc : ident t) : type.interp base.interp t
        := @gen_interp cast_outside_of_range t idc.
      Global Arguments interp _ !_ / .
    End with_base.
    Notation LiteralUnit := (@Literal base.type.unit).
    Notation LiteralZ := (@Literal base.type.Z).
    Notation LiteralBool := (@Literal base.type.bool).
    Notation LiteralNat := (@Literal base.type.nat).

    (** TODO: MOVE ME? *)
    Module Thunked.
      Definition pair_rect {A B} P (f : A -> B -> P) (x : A * B) : P
        := let '(a, b) := x in f a b.
      Definition bool_rect P (t f : Datatypes.unit -> P) (b : bool) : P
        := Datatypes.bool_rect (fun _ => P) (t tt) (f tt) b.
      Definition list_rect {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P -> P) (ls : list A) : P
        := Datatypes.list_rect (fun _ => P) (N tt) C ls.
      Definition list_case {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P) (ls : list A) : P
        := ListUtil.list_case (fun _ => P) (N tt) C ls.
      Definition nat_rect P (O_case : unit -> P) (S_case : nat -> P -> P) (n : nat) : P
        := Datatypes.nat_rect (fun _ => P) (O_case tt) S_case n.
    End Thunked.

    Ltac require_primitive_const term :=
      lazymatch term with
      | S ?n => require_primitive_const n
      | O => idtac
      | true => idtac
      | false => idtac
      | tt => idtac
      | Z0 => idtac
      | Zpos ?p => require_primitive_const p
      | Zneg ?p => require_primitive_const p
      | xI ?p => require_primitive_const p
      | xO ?p => require_primitive_const p
      | xH => idtac
      | ?term => fail 0 "Not a known const:" term
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
        | Nat.mul => then_tac Nat_mul
        | Nat.max => then_tac Nat_max
        | Nat.pred => then_tac Nat_pred
        | S => then_tac Nat_succ
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
        | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse
          => reify_rec (@Thunked.bool_rect T (fun _ : Datatypes.unit => Ptrue) (fun _ : Datatypes.unit => Pfalse))
        | @Thunked.bool_rect ?T
          => let rT := base.reify T in
             then_tac (@ident.bool_rect rT)
        | @Datatypes.nat_rect (fun _ => ?T) ?P0
          => reify_rec (@Thunked.nat_rect T (fun _ : Datatypes.unit => P0))
        | @Thunked.nat_rect ?T
          => let rT := base.reify T in
             then_tac (@ident.nat_rect rT)
        | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil
          => reify_rec (@Thunked.list_rect A T (fun _ : Datatypes.unit => Pnil))
        | @Thunked.list_rect ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.list_rect rA rT)
        | @ListUtil.list_case ?A (fun _ => ?T) ?Pnil
          => reify_rec (@Thunked.list_case A T (fun _ : Datatypes.unit => Pnil))
        | @Thunked.list_case ?A ?T
          => let rA := base.reify A in
             let rT := base.reify T in
             then_tac (@ident.list_case rA rT)
        | @List.length ?A =>
          let rA := base.reify A in
          then_tac (@ident.List_length rA)
        | List.seq => then_tac ident.List_seq
        | @repeat ?A
          => let rA := base.reify A in
             then_tac (@ident.List_repeat rA)
        | @combine ?A ?B
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
        | Z.add => then_tac ident.Z_add
        | Z.mul => then_tac ident.Z_mul
        | Z.pow => then_tac ident.Z_pow
        | Z.sub => then_tac ident.Z_sub
        | Z.opp => then_tac ident.Z_opp
        | Z.div => then_tac ident.Z_div
        | Z.modulo => then_tac ident.Z_modulo
        | Z.eqb => then_tac ident.Z_eqb
        | Z.leb => then_tac ident.Z_leb
        | Z.of_nat => then_tac ident.Z_of_nat
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
        | _ => else_tac ()
        end
      end.

    Fixpoint smart_Literal {var} {t:base.type} : base.interp t -> @expr.expr base.type ident var (type.base t)
      := match t with
         | base.type.type_base t => fun v => expr.Ident (ident.Literal v)
         | base.type.prod A B
           => fun '((a, b) : base.interp A * base.interp B)
              => expr.Ident ident.pair @ (@smart_Literal var A a) @ (@smart_Literal var B b)
         | base.type.list A
           => fun v : list (base.interp A)
              => fold_right
                   (fun x xs => expr.Ident ident.cons @ x @ xs)
                   (expr.Ident ident.nil)
                   (List.map (@smart_Literal var A) v)
         end%expr.

    Module Export Notations.
      Delimit Scope ident_scope with ident.
      Bind Scope ident_scope with ident.
      Global Arguments expr.Ident {base_type%type ident%function var%function t%etype} idc%ident.
      Notation "## x" := (Literal x) (only printing) : ident_scope.
      Notation "## x" := (Literal (t:=base.reify_base_type_of x) x) (only parsing) : ident_scope.
      Notation "## x" := (expr.Ident (Literal x)) (only printing) : expr_scope.
      Notation "## x" := (smart_Literal (t:=base.reify_type_of x) x) (only parsing) : expr_scope.
      Notation "# x" := (expr.Ident x) : expr_pat_scope.
      Notation "# x" := (@expr.Ident base.type _ _ _ x) : expr_scope.
      Notation "x @ y" := (expr.App x%expr_pat y%expr_pat) : expr_pat_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#pair) .. (expr.App (expr.App (#pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
      Notation "( x , y , .. , z )" := (expr.App (expr.App (#pair)%expr_pat .. (expr.App (expr.App (#pair)%expr_pat x%expr_pat) y%expr_pat) .. ) z%expr_pat) : expr_pat_scope.
      Notation "x :: y" := (#cons @ x @ y)%expr : expr_scope.
      Notation "[ ]" := (#nil)%expr : expr_scope.
      Notation "x :: y" := (#cons @ x @ y)%expr_pat : expr_pat_scope.
      Notation "[ ]" := (#nil)%expr_pat : expr_pat_scope.
      Notation "[ x ]" := (x :: [])%expr : expr_scope.
      Notation "[ x ; y ; .. ; z ]" := (#cons @ x @ (#cons @ y @ .. (#cons @ z @ #nil) ..))%expr : expr_scope.
      Notation "ls [[ n ]]"
        := ((#(List_nth_default) @ _ @ ls @ #(Literal n%nat))%expr)
           : expr_scope.
      Notation "xs ++ ys" := (#List_app @ xs @ ys)%expr : expr_scope.
      Notation "x - y" := (#Z_sub @ x @ y)%expr : expr_scope.
      Notation "x + y" := (#Z_add @ x @ y)%expr : expr_scope.
      Notation "x / y" := (#Z_div @ x @ y)%expr : expr_scope.
      Notation "x * y" := (#Z_mul @ x @ y)%expr : expr_scope.
      Notation "x >> y" := (#(Z_shiftr y) @ x)%expr : expr_scope.
      Notation "x << y" := (#(Z_shiftl y) @ x)%expr : expr_scope.
      Notation "x 'mod' y" := (#Z_modulo @ x @ y)%expr : expr_scope.
      Notation "- x" := (#Z_opp @ x)%expr : expr_scope.
    End Notations.
  End ident.
  Export ident.Notations.
  Notation ident := ident.ident.

  Global Strategy -1000 [expr.Interp expr.interp ident.interp type.interp base.interp base.base_interp ident.gen_interp].
  Ltac reify var term :=
    expr.reify base.type ident ltac:(base.reify) ident.reify var term.
  Ltac Reify term :=
    expr.Reify base.type ident ltac:(base.reify) ident.reify term.
  Ltac Reify_rhs _ :=
    expr.Reify_rhs base.type ident ltac:(base.reify) ident.reify (@base.interp) (@ident.interp) ().

  Module Import invert_expr.
    Module ident.
      Definition invert_Literal_cps {t} (idc : ident t) : ~> option (type.interp base.interp t)
        := fun T => match idc with
                    | ident.Literal _ n => fun k => k (Some n)
                    | _ => fun k => k None
                    end.

      Definition invert_Literal {t} (idc : ident t) : option (type.interp base.interp t)
        := match idc with
           | ident.Literal _ n => Some n
           | _ => None
           end.
    End ident.

    Section with_var_gen.
      Context {base_type} {ident var : type base_type -> Type}.
      Local Notation expr := (@expr base_type ident var).
      Local Notation if_arrow f t
        := (match t return Type with
            | type.arrow s d => f s d
            | type.base _ => unit
            end) (only parsing).
      Definition invert_Ident {t} (e : expr t)
        : option (ident t)
        := match e with
           | expr.Ident t idc => Some idc
           | _ => None
           end.
      Definition invert_App {t} (e : expr t)
        : option { s : _ & expr (s -> t) * expr s }%type
        := match e with
           | expr.App A B f x => Some (existT _ A (f, x))
           | _ => None
           end.
      Definition invert_Abs {s d} (e : expr (s -> d))
        : option (var s -> expr d)%type
        := match e in expr.expr t return option (if_arrow (fun s d => var s -> expr d) t) with
           | expr.Abs s d f => Some f
           | _ => None
           end.
      Definition invert_App2 {t} (e : expr t)
        : option { ss' : _ & expr (fst ss' -> snd ss' -> t) * expr (fst ss') * expr (snd ss') }%type
        := (e <- invert_App e;
              let '(existT s' (f', x')) := e in
              f' <- invert_App f';
                let '(existT s (f, x)) := f' in
                Some (existT _ (s, s') (f, x, x')))%option.
      Definition invert_AppIdent {t} (e : expr t)
        : option { s : _ & ident (s -> t) * expr s }%type
        := (e <- invert_App e;
              let '(existT s (f, x)) := e in
              f' <- invert_Ident f;
                Some (existT _ s (f', x)))%option.
      Definition invert_AppIdent2 {t} (e : expr t)
        : option { ss' : _ & ident (fst ss' -> snd ss' -> t) * expr (fst ss') * expr (snd ss') }%type
        := (e <- invert_App2 e;
              let '(existT ss' (f, x, x')) := e in
              f' <- invert_Ident f;
                Some (existT _ ss' (f', x, x')))%option.
      Definition invert_Var {t} (e : expr t)
        : option (var t)
        := match e with
           | expr.Var t v => Some v
           | _ => None
           end.

      Fixpoint App_curried {t} : expr t -> type.for_each_lhs_of_arrow expr t -> expr (type.base (type.final_codomain t))
        := match t with
           | type.base t => fun e _ => e
           | type.arrow s d => fun e x => @App_curried d (e @ (fst x)) (snd x)
           end.
      Fixpoint smart_App_curried {t} (e : expr t) : type.for_each_lhs_of_arrow var t -> expr (type.base (type.final_codomain t))
        := match e in expr.expr t return type.for_each_lhs_of_arrow var t -> expr (type.base (type.final_codomain t)) with
           | expr.Abs s d f
             => fun v => @smart_App_curried d (f (fst v)) (snd v)
           | e
             => fun v => @App_curried _ e (type.map_for_each_lhs_of_arrow (fun _ v => expr.Var v) v)
           end.
    End with_var_gen.

    Section with_var.
      Context {var : type base.type -> Type}.
      Local Notation expr := (@expr base.type ident var).
      Local Notation try_transportP P := (@type.try_transport base.type (@base.try_make_transport_cps) P _ _).
      Local Notation try_transport := (try_transportP _).
      Let type_base (v : base.type) : type.type base.type := type.base v.
      Coercion type_base : base.type >-> type.type.

      Definition invert_Z_opp {t} (e : expr t)
        : option (expr t)
        := match e in expr.expr t return option (expr t) with
           | expr.App (type.base base.type.Z) (type.base base.type.Z) (#ident.Z_opp) v => Some v
           | _ => None
           end%expr_pat%expr.

      Definition invert_Z_cast (e : expr base.type.Z)
        : option (zrange * expr base.type.Z)
        := match e with
           | expr.App (type.base base.type.Z) _ (#(ident.Z_cast r)) v => Some (r, v)
           | _ => None
           end%core%expr_pat%expr.

      Definition invert_Z_cast2 (e : expr (base.type.Z * base.type.Z))
        : option ((zrange * zrange) * expr (base.type.Z * base.type.Z))
        := match e with
           | expr.App (type.base (base.type.Z * base.type.Z)) _ (#(ident.Z_cast2 r)) v => Some (r, v)
           | _ => None
           end%etype%core%expr_pat%expr.

      Definition invert_pair {A B} (e : expr (A * B))
        : option (expr A * expr B)
        := match e with
           | (a, b)
             => a <- try_transport a; b <- try_transport b; Some (a, b)%core
           | _ => None
           end%expr_pat%expr%option.
      Definition invert_Literal {t} (e : expr t)
        : option (type.interp base.interp t)
        := match e with
           | expr.Ident _ idc => ident.invert_Literal idc
           | _ => None
           end%expr_pat%expr.
    End with_var.

    Definition reify_list {var} {t : base.type} (ls : list (@expr.expr base.type ident var (type.base t))) : expr (type.base (base.type.list t))
      := fold_right
           (fun x xs => x :: xs)%expr
           []%expr
           ls.

    Fixpoint reflect_list_cps' {var t} (e : @expr.expr base.type ident var t) {struct e}
      : ~> option (list (@expr.expr base.type ident var (type.base match t return base.type with
                                                                   | type.base (base.type.list t) => t
                                                                   | _ => base.type.unit
                                                                   end)))
      := match e in expr.expr t return ~> option (list (@expr.expr base.type ident var (type.base match t return base.type with
                                                                                                  | type.base (base.type.list t) => t
                                                                                                  | _ => base.type.unit
                                                                                                  end)))
         with
         | [] => (return (Some nil))
         | x :: xs
           => (x' <-- type.try_transport_cps base.try_make_transport_cps (@expr.expr base.type ident var) _ _ x;
                xs' <-- @reflect_list_cps' var _ xs;
                xs' <-- type.try_transport_cps base.try_make_transport_cps (fun t => list (@expr.expr _ _ _ (type.base match t return base.type with
                                                                                                                  | type.base (base.type.list t) => t
                                                                                                                  | _ => base.type.unit
                                                                                                                  end))) _ _ xs';
              return (Some (x' :: xs')%list))
         | _ => (return None)
         end%expr_pat%expr%cps.

    Definition reflect_list_cps {var t} (e : @expr.expr base.type ident var (type.base (base.type.list t)))
      : ~> option (list (@expr.expr base.type ident var (type.base t)))
      := reflect_list_cps' e.
    Global Arguments reflect_list_cps {var t} e [T] k.

    Definition reflect_list {var t} (e : @expr.expr base.type ident var (type.base (base.type.list t)))
      : option (list (@expr.expr base.type ident var (type.base t)))
      := reflect_list_cps e id.
  End invert_expr.

  Module DefaultValue.
    (** This module provides "default" inhabitants for the
        interpretation of PHOAS types and for the PHOAS [expr] type.
        These values are used for things like [nth_default] and in
        other places where we need to provide a dummy value in cases
        that will never actually be reached in correctly used code. *)
    Module type.
      Module base.
        Fixpoint default {t : base.type} : base.interp t
          := match t with
             | base.type.unit => tt
             | base.type.Z => (-1)%Z
             | base.type.nat => 0%nat
             | base.type.bool => true
             | base.type.list _ => nil
             | base.type.prod A B
               => (@default A, @default B)
             end.
      End base.
      Fixpoint default {t} : type.interp base.interp t
        := match t with
           | type.base x => @base.default x
           | type.arrow s d => fun _ => @default d
           end.
    End type.

    Module expr.
      Module base.
        Section with_var.
          Context {var : type.type base.type -> Type}.
          Fixpoint default {t : base.type} : @expr base.type ident var (type.base t)
            := match t with
               | base.type.prod A B
                 => (@default A, @default B)
               | base.type.list A => #ident.nil
               | base.type.unit as t
               | base.type.Z as t
               | base.type.nat as t
               | base.type.bool as t
                 => ##(@type.base.default t)
               end%expr.
        End with_var.

        Definition Default {t : base.type} : expr.Expr (type.base t) := fun _ => default.
      End base.

      Section with_var.
        Context {var : type base.type -> Type}.
        Fixpoint default {t : type base.type} : @expr base.type ident var t
          := match t with
             | type.base x => base.default
             | type.arrow s d => λ _, @default d
             end%expr.
      End with_var.

      Definition Default {t} : expr.Expr t := fun _ => default.
    End expr.
  End DefaultValue.

  Module Import defaults.
    Notation expr := (@expr base.type ident).
    Notation Expr := (@expr.Expr base.type ident).
    Notation type := (type base.type).
    Global Coercion type_base (t : base.type) : type := type.base t.
    Global Arguments type_base _ / .
    Notation interp := (@expr.interp base.type ident base.interp (@ident.interp)).
    Notation Interp := (@expr.Interp base.type ident base.interp (@ident.interp)).
    Ltac reify_type ty := type.reify ltac:(base.reify) base.type ty.
    Notation reify_type t := (ltac:(let rt := reify_type t in exact rt)) (only parsing).
    Notation reify_type_of e := (reify_type ((fun t (_ : t) => t) _ e)) (only parsing).
  End defaults.

  Section gallina_reify.
    Context {var : type -> Type}.
    Definition reify_list {t} (ls : list (@expr var (type.base t))) : @expr var (base.type.list t)
      := (list_rect
            (fun _ => _)
            (#ident.nil)
            (fun x _ xs => x :: xs)
            ls)%expr.
  End gallina_reify.

  Lemma interp_reify_list {t} ls
    : interp (@reify_list _ t ls) = List.map interp ls.
  Proof.
    unfold reify_list.
    induction ls as [|x xs IHxs]; cbn in *; [ reflexivity | ].
    rewrite IHxs; reflexivity.
  Qed.

  Module GallinaReify.
    Module base.
      Fixpoint value (t : base.type) : Set
        := match t with
           | base.type.unit as t
           | base.type.Z as t
           | base.type.bool as t
           | base.type.nat as t
             => base.interp t
           | base.type.prod A B => value A * value B
           | base.type.list A => list (value A)
           end%type.

      Section reify.
        Context {var : type -> Type}.
        Fixpoint reify {t : base.type} {struct t}
          : value t -> @expr var t
          := match t return value t -> expr t with
             | base.type.prod A B as t
               => fun '((a, b) : value A * value B)
                  => (@reify A a, @reify B b)%expr
             | base.type.list A as t
               => fun x : list (value A)
                  => reify_list (List.map (@reify A) x)
             | base.type.unit as t
             | base.type.Z as t
             | base.type.bool as t
             | base.type.nat as t
               => fun x : base.interp t
                  => (##x)%expr
             end.
      End reify.

      Definition Reify_as (t : base.type) (v : value t) : Expr t
        := fun var => reify v.

      (** [Reify] does Ltac type inference to get the type *)
      Notation Reify v
        := (Reify_as (base.reify_type_of v) (fun _ => v)) (only parsing).
    End base.

    Section value.
      Context (var : type -> Type).
      Fixpoint value (t : type)
        := match t return Type with
           | type.arrow s d => var s -> value d
           | type.base t => base.value t
           end%type.
    End value.

    Section reify.
      Context {var : type -> Type}.
      Fixpoint reify {t : type} {struct t}
        : value var t -> @expr var t
        := match t return value var t -> expr t with
           | type.arrow s d
             => fun (f : var s -> value var d)
                => (λ x , @reify d (f x))%expr
           | type.base t
             => @base.reify var t
           end.
    End reify.

    Definition Reify_as (t : type) (v : forall var, value var t) : Expr t
      := fun var => reify (v _).

    (** [Reify] does Ltac type inference to get the type *)
    Notation Reify v
      := (Reify_as (reify_type_of v) (fun _ => v)) (only parsing).
  End GallinaReify.

  Module GeneralizeVar.
    (** In both lazy and cbv evaluation strategies, reduction under
        lambdas is only done at the very end.  This means that if we
        have a computation which returns a PHOAS syntax tree, and we
        plug in two different values for [var], the computation is run
        twice.  This module provides a way of computing a
        representation of terms which does not suffer from this issue.
        By computing a flat representation, and then going back to
        PHOAS, the cbv strategy will fully compute the preceeding
        PHOAS passes only once, and the lazy strategy will share
        computation among the various uses of [var] (because there are
        no lambdas to get blocked on) and thus will also compute the
        preceeding PHOAS passes only once. *)
    Module Flat.
      Inductive expr : type -> Set :=
      | Ident {t} (idc : ident t) : expr t
      | Var (t : type) (n : positive) : expr t
      | Abs (s : type) (n : positive) {d} (f : expr d) : expr (s -> d)
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | LetIn {A B} (n : positive) (ex : expr A) (eC : expr B) : expr B.
    End Flat.

    Definition ERROR {T} (v : T) : T. exact v. Qed.

    Fixpoint to_flat' {t} (e : @expr (fun _ => PositiveMap.key) t)
             (cur_idx : PositiveMap.key)
      : Flat.expr t
      := match e in expr.expr t return Flat.expr t with
         | expr.Var t v => Flat.Var t v
         | expr.App s d f x => Flat.App
                                 (@to_flat' _ f cur_idx)
                                 (@to_flat' _ x cur_idx)
         | expr.Ident t idc => Flat.Ident idc
         | expr.Abs s d f
           => Flat.Abs s cur_idx
                       (@to_flat'
                          d (f cur_idx)
                          (Pos.succ cur_idx))
         | expr.LetIn A B ex eC
           => Flat.LetIn
                cur_idx
                (@to_flat' A ex cur_idx)
                (@to_flat'
                   B (eC cur_idx)
                   (Pos.succ cur_idx))
         end.

    Fixpoint from_flat {t} (e : Flat.expr t)
      : forall var, PositiveMap.t { t : type & var t } -> @expr var t
      := match e in Flat.expr t return forall var, _ -> expr t with
         | Flat.Var t v
           => fun var ctx
              => match (tv <- PositiveMap.find v ctx;
                          type.try_transport base.try_make_transport_cps var _ _ (projT2 tv))%option with
                 | Some v => expr.Var v
                 | None => ERROR DefaultValue.expr.default
                 end
         | Flat.Ident t idc => fun var ctx => expr.Ident idc
         | Flat.App s d f x
           => let f' := @from_flat _ f in
              let x' := @from_flat _ x in
              fun var ctx => expr.App (f' var ctx) (x' var ctx)
         | Flat.Abs s cur_idx d f
           => let f' := @from_flat d f in
              fun var ctx
              => expr.Abs (fun v => f' var (PositiveMap.add cur_idx (existT _ s v) ctx))
         | Flat.LetIn A B cur_idx ex eC
           => let ex' := @from_flat A ex in
              let eC' := @from_flat B eC in
              fun var ctx
              => expr.LetIn
                   (ex' var ctx)
                   (fun v => eC' var (PositiveMap.add cur_idx (existT _ A v) ctx))
         end.

    Definition to_flat {t} (e : expr t) : Flat.expr t
      := to_flat' e 1%positive.
    Definition ToFlat {t} (E : Expr t) : Flat.expr t
      := to_flat (E _).
    Definition FromFlat {t} (e : Flat.expr t) : Expr t
      := let e' := @from_flat t e in
         fun var => e' var (PositiveMap.empty _).
    Definition GeneralizeVar {t} (e : @expr (fun _ => PositiveMap.key) t) : Expr t
      := FromFlat (to_flat e).
  End GeneralizeVar.
End Compilers.
