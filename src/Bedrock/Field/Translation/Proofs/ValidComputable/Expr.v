Require Import Coq.derive.Derive.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.UniquePose.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations.
Import Inversion.Compilers.

Section Expr.
  Context {p : Types.parameters} {p_ok : @ok p}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Ltac intros_do_revert tac :=
    lazymatch goal with
    | [ |- forall x : _, _ ] => let x' := fresh in intro x'; intros_do_revert tac; revert x'
    | _ => tac ()
    end.

  Ltac split_lists :=
    refine (@nth_error_true_fold_left_orb_true _ _ _ _);
    [ > cbn [nth_error];
      repeat lazymatch goal with
             | [ |- nth_error (_ :: _) ?n = Some true ]
               => is_evar n;
                  let n' := open_constr:(S _) in
                  unify n n';
                  cbn [nth_error]
             | [ |- nth_error ?ev ?n = Some true ]
               => let ev := head ev in
                  is_evar ev; is_evar n;
                  let EV := fresh in
                  pose ev as EV;
                  instantiate (1:=ltac:(intros_do_revert ltac:(fun _ => refine (cons _ _)))) in (value of EV); clear EV; cbv beta;
                  unify n O;
                  cbn [nth_error]; apply f_equal
             end .. ].

  Ltac get_last ls :=
    lazymatch ls with
    | cons _ ?ls => get_last ls
    | _ => ls
    end.
  Ltac handle_first_var lhs :=
    lazymatch lhs with
    | ?ev ?x ?y => handle_first_var (ev x)
    | ?ev ?e
      => is_evar ev;
         (tryif is_var e
           then instantiate (1:=ltac:(intro)); cbv beta
           else instantiate (1:=ltac:(let e := fresh "e" in intro e; case e; clear e)); cbv beta iota in * )
    end.
  Ltac split_recr valid_expr_bool :=
    lazymatch goal with
    | [ H : valid_expr_bool _ _ _ = true |- _ ]
      => instantiate (1:=ltac:(let e := fresh "e" in intro e; refine (andb _ _); revert e));
         cbv beta; refine (andb_true_intro _); split;
         [ clear H; split_recr valid_expr_bool | clear -H ]
    | _ => instantiate (1:=fun _ => true); reflexivity
    end.
  Ltac get_first_arg f :=
    lazymatch f with
    | ?f ?x
      => lazymatch f with
         | ?f' _ => get_first_arg f
         | _ => x
         end
    end.
  Ltac terms_intersect x y :=
    match x with
    | context[?x'] => match y with
                      | context[x'] => constr:(true)
                      end
    | _ => constr:(false)
    end.
  Ltac destruct_to_instantiate_with valid_expr_bool H x :=
    repeat lazymatch goal with
           | [ |- ?lhs = true ]
             => let x' := get_first_arg lhs in
                let inter := terms_intersect x x' in
                lazymatch inter with
                | false => instantiate (1:=ltac:(intro)); cbv beta
                | true => handle_first_var lhs
                end
           end;
    (instantiate (1:=ltac:(refine (valid_expr_bool _ _ _); clear valid_expr_bool)));
    refine H.
  Ltac instantiate_non_recr valid_expr_bool :=
    clear dependent valid_expr_bool;
    repeat match goal with
             [ H : valid_expr _ _ |- _ ] => clear H
           end;
    repeat lazymatch goal with
           | [ |- ?lhs = true ]
             => handle_first_var lhs
           end;
    repeat lazymatch goal with
           | [ H : _ |- _ ]
             => lazymatch type of H with
                | _ = true
                  => refine (andb_true_intro _); split;
                     [ clear H
                     | refine H ]
                | ?T
                  => lazymatch type of T with
                     | Prop
                       => refine (andb_true_intro _); split;
                          [ clear H
                          | solve [ refine (unreflect_bool H) ]
                            || (idtac "could not reflect:" T; fail) ]
                     | _ => clear H
                     end
                end
           | _ => instantiate (1:=true); reflexivity
           end.
  Ltac unfold_valid_expr_bool valid_expr_bool :=
    cbv [valid_expr_bool]; fold valid_expr_bool; clearbody valid_expr_bool.
  Ltac finish_non_recr_instantiation valid_expr_bool :=
    instantiate (1:=ltac:(let e := fresh "e" in
                          intro e;
                          refine (andb _ _);
                          [ clear valid_expr_bool
                          | ];
                          revert e));
    cbv beta;
    (refine (andb_true_intro _); split;
     [ instantiate_non_recr valid_expr_bool; shelve
     | split_recr valid_expr_bool ]).
  Ltac finish_recr_instantiation valid_expr_bool :=
    lazymatch goal with
    | [ H : valid_expr_bool _ _ ?x = true |- _ ]
      => destruct_to_instantiate_with valid_expr_bool H x
    end.
  Ltac get_valid_expr_bool :=
    lazymatch reverse goal with
    | [ valid_expr_bool : forall t, bool -> API.expr t -> bool |- _ ]
      => valid_expr_bool
    end.
  Ltac get_valid_expr_bool_correct valid_expr_bool :=
    lazymatch goal with
    | [ valid_expr_bool_correct : forall t rc e, valid_expr_bool t rc e = true -> valid_expr rc e |- _ ] => valid_expr_bool_correct
    end.
  Ltac fill_valid_expr_bool_after_split_lists :=
    unshelve (
        let valid_expr_bool := get_valid_expr_bool in
        finish_non_recr_instantiation valid_expr_bool;
        finish_recr_instantiation valid_expr_bool
      );
    try (intros; exact false).
  Ltac fill_valid_expr_bool :=
    (let valid_expr_bool := get_valid_expr_bool in
     unfold_valid_expr_bool valid_expr_bool);
    split_lists;
    fill_valid_expr_bool_after_split_lists.

  Ltac early_safe_step1 :=
    first [ progress cbn [andb] in *
          | match goal with
            | [ |- false = true -> _ ] => intro
            | [ |- true = false -> _ ] => intro
            | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
            | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
            end ].
  Ltac early_safe_step2 :=
    first [ match goal with
            | [ |- context[match ?e with _ => _ end] ] => is_var e; destruct e
            | [ H : context[match ?e with _ => _ end] |- _ ] => is_var e; destruct e
            | [ veb := _ : bool |- _ ] => clearbody veb
            end ].
  Ltac early_safe_step := first [ early_safe_step1 | early_safe_step2 ].
  Ltac early_step valid_expr_bool valid_expr_bool_correct :=
    first [ early_safe_step1
          | match goal with
            | [ |- context[valid_expr_bool ?t ?rc ?e] ]
              => unique pose proof (valid_expr_bool_correct t rc e);
                 let veb := fresh "veb" in
                 set (veb := valid_expr_bool t rc e) in *
            | [ |- context[?e] ]
              => lazymatch e with
                 | context[valid_expr_bool]
                   => match e with
                      | context[match ?e with _ => _ end] => is_var e; destruct e
                      end
                 end
            end
          | early_safe_step2 ].

  Definition valid_expr_bool_package
    : { valid_expr_bool_step
        : ((forall {t} (rc : bool) (e : API.expr t), bool)
           -> (forall {t} (rc : bool) (e : API.expr t), bool))
          & { valid_expr_bool
              : (forall {t} (rc : bool) (e : API.expr t), bool)
                & (forall {t} (rc : bool) (e : API.expr t),
                  (*reflect (valid_expr rc e) (valid_expr_bool t rc e)*)
                  valid_expr rc e -> valid_expr_bool t rc e = true)
                  * (forall {t} (rc : bool) (e : API.expr t),
                        @valid_expr_bool t rc e = @valid_expr_bool_step (@valid_expr_bool) t rc e) }%type }.
  Proof using Type.
    clear p_ok.
    unshelve
      (simple refine (let valid_expr_bool_step
                          : (forall {t} (rc : bool) (e : API.expr t), bool)
                            -> (forall {t} (rc : bool) (e : API.expr t), bool)
                          := fun valid_expr_bool t rc e
                             => fold_left orb _ false in
                      let valid_expr_bool := (fix valid_expr_bool {t} (rc : bool) (e : API.expr t) {struct e} : bool := valid_expr_bool_step (@valid_expr_bool) t rc e) in
                      let valid_expr_bool_eta : forall t rc e, @valid_expr_bool t rc e = valid_expr_bool_step (@valid_expr_bool) t rc e
                          := _ in
                      (*let valid_expr_bool_step_correct'
                          : (forall (t : API.type) (rc : bool) (e : API.expr t),
                                @valid_expr_bool t rc e = true -> valid_expr rc e)
                            -> forall (t : API.type) (rc : bool) (e : API.expr t),
                              valid_expr_bool_step (@valid_expr_bool) t rc e = true -> valid_expr rc e
                          := _ in
                      let valid_expr_bool_step_correct := _ in*)
                      let valid_expr_bool_correct := _ in
                      existT
                        _ (@valid_expr_bool_step)
                        (existT
                           _ (@valid_expr_bool)
                           ((fun t rc e
                             => (*iff_reflect
                                  _ _
                                  (conj*) (valid_expr_bool_correct t rc e)
                                        (*((fix valid_expr_bool_correct' {t} (rc : bool) (e : API.expr t) {struct e} := valid_expr_bool_step_correct (@valid_expr_bool_correct') t rc e) t rc e))*)),
                            valid_expr_bool_eta)));
       [ revert valid_expr_bool t rc e
       | clear -p; intros ? ? e; destruct e; cbn [valid_expr_bool]; reflexivity
       (*| clearbody valid_expr_bool_eta
       | clearbody valid_expr_bool_eta valid_expr_bool_step_correct';
         let H := fresh in
         intro H; specialize (valid_expr_bool_step_correct' H);
         intros t rc e;
         pose e as e';
         destruct e;
         let e' := (eval cbv delta [e'] in e') in
         refine (valid_expr_bool_step_correct' _ rc e')*)
       | (*clear valid_expr_bool_step_correct' valid_expr_bool_step_correct;*)
         clearbody valid_expr_bool_eta;
         intros t rc e H;
         induction H;
         rewrite valid_expr_bool_eta; clear valid_expr_bool_eta;
         clearbody valid_expr_bool;
         cbv [valid_expr_bool_step];
         clear valid_expr_bool_step;
         split_lists;
         lazymatch goal with
         | [ |- ?ev ?veb ?t ?rc ?e = true ]
           => let subcall := fresh "subcall" in
              let ty := type of ev in
              let H := fresh in
              let rcv := lazymatch rc with
                         | true => constr:(Some true)
                         | false => constr:(Some false)
                         | _ => constr:(@None bool)
                         end in
              simple refine (let subcall : ty := _ in
                             let H : subcall veb t rc e = true := _ in
                             _);
              [ clear -p;
                let t := fresh "t" in
                let rc := fresh "rc" in
                let e := fresh "e" in
                intros valid_expr_bool t rc e;
                lazymatch rcv with
                | Some true => refine (andb rc _)
                | Some false => refine (andb (negb rc) _)
                | None => idtac
                end;
                revert e; shelve
              | subst subcall; cbv beta;
                lazymatch goal with
                | [ |- andb _ _ = true ] => apply andb_true_intro; split; [ reflexivity | ]
                | [ |- _ = true ] => idtac
                end;
                fill_valid_expr_bool_after_split_lists
              | let T := type of subcall in
                let subcall' := fresh "subcall'" in
                simple refine (let subcall' : T := _ in
                               _);
                [ clear -subcall;
                  let subcall_body := (eval cbv beta iota delta [subcall] in subcall) in
                  clear subcall;
                  transparent_abstract (exact subcall_body)
                | let subcallv := (eval cbv delta [subcall'] in subcall') in
                  instantiate (1:=subcallv);
                  replace subcallv with subcall by reflexivity;
                  refine H ] ]
         end ]).
    intros; exact nil.
  Defined.

  Definition valid_expr_bool_step
    : forall (valid_expr_bool : forall {t} (rc : bool) (e : API.expr t), bool)
             {t} (rc : bool) (e : API.expr t), bool
    := Eval cbv [projT1 valid_expr_bool_package] in projT1 valid_expr_bool_package.

  Fixpoint valid_expr_bool {t} (rc : bool) (e : API.expr t) {struct e} : bool
    := @valid_expr_bool_step (@valid_expr_bool) t rc e.

  Lemma valid_expr_bool_eta {t} (rc : bool) (e : API.expr t)
    : valid_expr_bool rc e = @valid_expr_bool_step (@valid_expr_bool) t rc e.
  Proof using Type. now destruct e. Qed.

  Lemma valid_expr_bool_impl2
    : forall {t} (rc : bool) (e : API.expr t),
      valid_expr rc e -> valid_expr_bool rc e = true.
  Proof using Type. exact (fst (projT2 (projT2 valid_expr_bool_package))). Qed.

  Definition valid_expr_bool_impl1_step
             (valid_expr_bool_correct
              : forall {t} (rc : bool) (e : API.expr t),
                 valid_expr_bool rc e = true -> valid_expr rc e)
             {t} (rc : bool) (e : API.expr t)
    : valid_expr_bool rc e = true -> valid_expr rc e.
  Proof using Type.
    clear p_ok.
    rewrite valid_expr_bool_eta.
    cbv [valid_expr_bool_step].
    lazymatch goal with
    | [ |- fold_left orb ?ls ?b = true -> _ ]
      => induction_fold_left_orb_true ls b
    end.
    all: lazymatch goal with
         | [ |- false = true -> _ ]
           => let H := fresh in
              intro H; exfalso; clear -H; discriminate
         | [ |- ?lhs = true -> valid_expr _ _ ]
           => let h := head lhs in
              cbv [h]
         end.
    Time
      all: intro;
  repeat match goal with
         | [ H : andb _ _ = true |- _ ] => apply andb_prop in H; destruct H
    end.
    Time all: let valid_expr_bool_correct := get_valid_expr_bool_correct (@valid_expr_bool) in
              repeat (let H := match goal with
                               | [ H : ?lhs = true |- _ ]
                                 => let __ := match lhs with context[valid_expr_bool] => idtac end in
                                    H
                               end in
                      let H' := fresh in
                      eassert (H' : _);
                     [ instantiate (1:=ltac:(clear H));
                     repeat match goal with
                            | [ H' : _ |- _ ] => tryif first [ constr_eq H H' | constr_eq H' valid_expr_bool_correct ] then fail else clear H'
                            end;
                     repeat match type of H with
                            | context[match ?e with _ => _ end]
                              => is_var e;
                     instantiate (1:=ltac:(destruct e)); destruct e
                     | false = true => refine (_ : False); clear -H; discriminate
                       end;
                     lazymatch type of H with
                     | @valid_expr_bool _ _ _ = true
                       => refine (valid_expr_bool_correct _ _ _ H)
                     | ?T => fail 1 "Leftover:" T
                     end
                     | clear H ]).
    all: clear valid_expr_bool_correct.
    Time all:
      time
        abstract (
          time repeat early_safe_step;
        time repeat first [ early_safe_step
                          | progress subst
                          | match goal with
                            | [ H : negb ?x = ?y |- _ ]
                              => let H' := fresh in
                                 assert (H' : x = negb y) by (clear -H; now destruct x, y);
                          cbn [negb] in H'; clear H
                            end
                          | expr.invert_match_step
                          | match goal with
                            | [ H : context[match ?x with _ => _ end ] |- _ ]
                              => is_var x;
                          lazymatch type of x with
                          | ?F ?t
                            => lazymatch type of t with
                               | API.type
                                 => type.invert_one x; subst; inversion_type
                            end
                            end
                            end
                          | match goal with
                            | [ H : ?x = ?x |- _ ] => clear H
                            | [ H : ?x = ?v |- _ ]
                              => let b := lazymatch v with true => x | false => constr:(negb x) end in
                                 lazymatch constr:(@id (reflect _ b) _) with
                                 | @id (reflect (?x = ?x) _) _
                                   => clear H
                                 | @id (reflect ?P _) ?lem
                                   => unique assert P;
                          [ let H' := fresh in
                            pose proof lem as H'; rewrite H in H'; cbn [negb] in H';
                          inversion H'; assumption
                          | ]
                            end
                            end ];
    (* Tactic call ran for 2.641 secs (2.628u,0.011s) (success)
Tactic call ran for 23.769 secs (23.632u,0.135s) (success)
Tactic call ran for 1.041 secs (1.029u,0.012s) (success)
Tactic call ran for 1.06 secs (1.048u,0.011s) (success)
Tactic call ran for 1.602 secs (1.598u,0.003s) (success)
Tactic call ran for 0.002 secs (0.002u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 8.624 secs (8.58u,0.043s) (success)
Tactic call ran for 5.875 secs (5.843u,0.031s) (success)
Tactic call ran for 5.916 secs (5.916u,0.s) (success)
Tactic call ran for 18.244 secs (18.244u,0.s) (success)
Tactic call ran for 17.057 secs (17.057u,0.s) (success)
Tactic call ran for 6.049 secs (6.049u,0.s) (success)
Tactic call ran for 12.284 secs (12.284u,0.s) (success)
Tactic call ran for 0.887 secs (0.887u,0.s) (success)
Tactic call ran for 0.649 secs (0.649u,0.s) (success)

Finished transaction in 105.706 secs (105.453u,0.252s) (successful)
     *)
        constructor; solve [ eauto ]
        ).
    (* Tactic call ran for 282.124 secs (281.901u,0.224s) (success) *)
    Time Defined.
  (*Finished transaction in 76.9 secs (76.9u,0.s) (successful)*)

  Time Fixpoint valid_expr_bool_impl1 {t} (rc : bool) (e : API.expr t) {struct e}
    : valid_expr_bool rc e = true -> valid_expr rc e
    := @valid_expr_bool_impl1_step (@valid_expr_bool_impl1) t rc e.
  (* Finished transaction in 0.387 secs (0.387u,0.s) (successful) *)

  Definition is_fst_snd_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.fst base_Z base_Z => true
    | ident.snd base_Z base_Z => true
    | _ => false
    end.

  Definition valid_expr_App1_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App type_range (type.arrow type_Z type_Z) f r =>
      is_cast_ident_expr f && is_cast_literal r
    | expr.App type_range2 (type.arrow type_ZZ type_ZZ) f r =>
      is_cast_ident_expr f && is_cast2_literal r
    | expr.Ident (type.arrow type_ZZ type_Z) i =>
      negb require_casts && is_fst_snd_ident i
    | _ => false
    end.

  Definition is_mul_high_ident {t} (i : ident.ident t) : bool :=
    match i with
    | ident.Z_mul_high => true
    | _ => false
    end.
  Definition is_mul_high_ident_expr {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident (type.arrow type_Z
                             (type.arrow type_Z
                                         (type.arrow type_Z type_Z)))
                 i => is_mul_high_ident i
    | _ => false
    end.

  Definition valid_expr_binop_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z s)) =>
      (is_mul_high_ident_expr f)
        && (negb require_casts)
        && (Z.eqb s (2 ^ Semantics.width))
    | expr.Ident (type.arrow type_Z (type.arrow type_Z type_Z)) i =>
      match translate_binop i with
      | None => false
      | Some _ => negb require_casts
      end
    | _ => false
    end.

  Definition is_shiftl_ident {t} (i : ident.ident t) :=
    match i with
    | ident.Z_truncating_shiftl => true
    | _ => false
    end.
  Definition is_shiftl_ident_expr
             {t} (e : @API.expr (fun _ => unit) t) :=
    match e with
    | expr.Ident
        (type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)))
        i => is_shiftl_ident i
    | _ => false
    end.
  Definition valid_expr_shift_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z s)) =>
      (is_shiftl_ident_expr f)
        && (negb require_casts)
        && Z.eqb s Semantics.width
    | expr.Ident _ ident.Z_shiftr =>
      negb require_casts
    | expr.Ident _ ident.Z_shiftl =>
      negb require_casts
    | _ => false
    end.

  Definition valid_shifter {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z n) =>
      is_bounded_by_bool n width_range
    | _ => false
    end.

  Definition is_lnot_modulo_ident {t} (i : ident.ident t) :=
    match i with
    | ident.Z_lnot_modulo => true
    | _ => false
    end.
  Definition is_lnot_modulo_ident_expr
             {t} (e : @API.expr (fun _ => unit) t) :=
    match e with
    | expr.Ident
        (type.arrow type_Z (type.arrow type_Z type_Z))
        i => is_lnot_modulo_ident i
    | _ => false
    end.
  Definition valid_expr_lnot_modulo_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow type_Z (type.arrow type_Z type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z m)) =>
      (is_lnot_modulo_ident_expr f)
        && (negb require_casts)
        && Z.eqb (2^Z.log2 m) m
    | _ => false
    end.

  Definition valid_expr_nth_default_App3_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.List_nth_default base_Z) =>
      true
    | _ => false
    end.
  Definition valid_expr_nth_default_App2_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_Z (type.arrow
                  type_listZ
                  (type.arrow type_nat type_Z))
        f (expr.Ident _ (ident.Literal base.type.Z d)) =>
      valid_expr_nth_default_App3_bool f && is_bounded_by_bool d max_range
    | _ => false
    end.
  Definition valid_expr_nth_default_App1_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App type_listZ (type.arrow type_nat type_Z)
               f (expr.Var _ l) =>
      valid_expr_nth_default_App2_bool f
    | _ => false
    end.
  Definition valid_expr_nth_default_bool {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.App
        type_nat type_Z
        f (expr.Ident _ (ident.Literal base.type.nat i)) =>
      valid_expr_nth_default_App1_bool f
    | _ => false
    end.

  Definition is_literalz {t}
             (e : @API.expr (fun _ => unit) t) (z : Z) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z x) => Z.eqb x z
    | _ => false
    end.
  Definition valid_expr_select_bool {t}
             rc (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ ident.Z_zselect => negb rc
    | _ => false
    end.

  Definition valid_expr_lnot_modulo_bool {t} (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ ident.Z_lnot_modulo =>
      negb require_casts
    | _ => false
    end.
  Definition valid_lnot_modulus {t}
           (e : @API.expr (fun _ => unit) t) : bool :=
    match e with
    | expr.Ident _ (ident.Literal base.type.Z n) =>
      (is_bounded_by_bool n max_range) && (n =? 2 ^ Z.log2 n)
    | _ => false
    end.

  (* opp is the only unary operation we accept *)
  Definition is_opp_ident {t} (i : ident t) : bool :=
    match i with
    | ident.Z_opp => true
    | _ => false
    end.
  Definition is_opp_ident_expr
             {t} (e : @API.expr (fun _ => unit) t) :=
    match e with
    | expr.Ident (type.arrow type_Z type_Z) i => is_opp_ident i
    | _ => false
    end.

  (* Because some operations are only valid if the arguments obey certain
     constraints, and to make the inductive logic work out, it helps to be able
     to call valid_expr_bool' recursively but have it return false for anything
     other than a specific kind of operation. This lets us, on encountering the
     very last application in a multi-argument function, take a sneak peek ahead
     to see if the rest of the applications match a certain kind of operation,
     and then enforce any constraints on the last argument. *)
  Inductive PartialMode := NotPartial | Binop | Shift | Select | Lnot.

  Fixpoint valid_expr_bool' {t}
           (mode : PartialMode) (require_casts : bool)
           (e : @API.expr (fun _ => unit) t) {struct e} : bool :=
    match mode with
    | Binop =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_binop_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Shift =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_shift_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Select =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_bool' Select require_casts f)
          && is_literalz x 0
      | expr.App type_Z
                 (type.arrow type_Z
                             (type.arrow type_Z type_Z)) f x =>
        (valid_expr_select_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | Lnot =>
      match e with
      | expr.App type_Z (type.arrow type_Z type_Z) f x =>
        (valid_expr_lnot_modulo_bool require_casts f)
          && valid_expr_bool' NotPartial true x
      | _ => false
      end
    | NotPartial =>
        match e with
        | expr.App type_nat _ f x =>
          (* only thing accepting nat is nth_default *)
          if require_casts
          then false
          else valid_expr_nth_default_bool (expr.App f x)
        | expr.App type_Z type_Z f x =>
          if valid_expr_bool' Binop require_casts f
          then (* f is a binop applied to one valid argument;
                check that x (second argument) is also valid *)
            valid_expr_bool' NotPartial true x
          else if valid_expr_bool' Shift require_casts f
               then (* f is a shift applied to one valid
                       argument; check that x (shifting index) is a
                       valid shifter *)
                 valid_shifter x
               else if valid_expr_bool' Select require_casts f
                    then (* f is a select; make sure x = 2^w-1 *)
                      is_literalz x (2^Semantics.width-1)
                    else
                      if valid_expr_bool' Lnot require_casts f
                      then (* f is lnot_modulo; make sure argument is a valid
                              modulus *)
                        (negb require_casts)
                          && valid_lnot_modulus x
                      else
                        if is_opp_ident_expr f
                        then (* f is opp *)
                          (negb require_casts)
                            && valid_expr_bool' NotPartial true x
                        else (* must be a cast *)
                          (valid_expr_App1_bool require_casts f)
                            && valid_expr_bool' NotPartial false x
        | expr.App type_ZZ type_Z f x =>
          (* fst or snd *)
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' NotPartial true x
        | expr.App type_ZZ type_ZZ f x =>
          (valid_expr_App1_bool require_casts f)
            && valid_expr_bool' NotPartial false x
        | expr.Ident _ (ident.Literal base.type.Z z) =>
          is_bounded_by_bool z max_range || negb require_casts
        | expr.Ident _ (ident.Literal base.type.nat n) =>
          negb require_casts
        | expr.Var type_Z v => true
        | expr.Var type_listZ v => true
        | _ => false
        end
    end.

  Definition valid_expr_bool {t} := @valid_expr_bool' t NotPartial.

  Lemma valid_expr_App1_bool_type {t} rc (e : API.expr t) :
    valid_expr_App1_bool rc e = true ->
    (exists d,
        t = type.arrow type_Z d
        \/ t = type.arrow type_ZZ d).
  Proof.
    cbv [valid_expr_App1_bool].
    destruct e;
      match goal with
      | idc : ident.ident _ |- _ =>
        destruct idc; try congruence;
          break_match; try congruence; intros;
            eexists; right; reflexivity
      | v: unit, t : API.type |- _ =>
        destruct t; congruence
      | f : API.expr (?s -> ?d) |- _ =>
        destruct d;
          break_match; try congruence;
        try (eexists; right; reflexivity);
        eexists; left; reflexivity
      | |- forall (_: false = true), _ => congruence
      | |- context [@expr.LetIn _ _ _ _ ?B] =>
        destruct B; congruence
      | _ => idtac
      end.
  Qed.

  Lemma is_mul_high_ident_expr_type {t} (f : API.expr t) :
    is_mul_high_ident_expr f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z
                               (type.arrow type_Z type_Z)).
  Proof.
    cbv [is_mul_high_ident_expr].
    break_match; congruence.
  Qed.

  Lemma valid_expr_shift_bool_type {t} rc (f : API.expr t) :
    valid_expr_shift_bool rc f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z type_Z).
  Proof.
    cbv [valid_expr_shift_bool].
    break_match; congruence.
  Qed.

  Lemma valid_expr_binop_bool_type {t} rc (f : API.expr t) :
    valid_expr_binop_bool rc f = true ->
    t = type.arrow type_Z
                   (type.arrow type_Z type_Z).
  Proof.
    cbv [valid_expr_binop_bool translate_binop].
    destruct f;
      match goal with
      | idc : ident.ident _ |- _ =>
        destruct idc; try congruence;
          break_match; congruence
      | |- forall (_: false = true), _ => congruence
      | _ => idtac
      end; [ ].
    break_match; congruence.
  Qed.

  Lemma valid_expr_nth_default_App2_bool_type {t}
        (f : API.expr t) :
    valid_expr_nth_default_App2_bool f = true ->
    match t with
    | type.arrow type_listZ
                 (type.arrow type_nat type_Z) =>
      True
    | _ => False
    end.
  Proof.
    cbv [valid_expr_nth_default_App2_bool].
    break_match; try congruence; [ ].
    tauto.
  Qed.

  Lemma valid_expr_nth_default_App1_bool_type {t}
        (f : API.expr t) :
    valid_expr_nth_default_App1_bool f = true ->
    match t with
    | type.arrow type_nat type_Z =>
      True
    | _ => False
    end.
  Proof.
    cbv [valid_expr_nth_default_App1_bool].
    break_match; try congruence; [ ].
    tauto.
  Qed.

  Lemma valid_expr_nth_default_App3_bool_impl1 {t}
        (f : API.expr t) n l d :
    valid_expr_nth_default_App3_bool f = true ->
    is_bounded_by_bool d max_range = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z
                  (type.arrow type_listZ (type.arrow type_nat type_Z)) =>
       fun f =>
         valid_expr
           false (expr.App
                    (expr.App
                       (expr.App
                          f
                          (expr.Ident
                             (ident.Literal (t:=base.type.Z) d)))
                       (expr.Var l))
                 (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App3_bool].
    break_match; try congruence; [ ].
    intros. constructor.
    cbv [is_bounded_by_bool upper lower max_range] in *.
    repeat match goal with
           | H : _ && _ = true |- _ =>
             apply andb_true_iff in H; destruct H
           end.
    Z.ltb_to_lt; lia.
  Qed.

  Lemma valid_expr_nth_default_App2_bool_impl1 {t}
        (f : API.expr t) n l :
    valid_expr_nth_default_App2_bool f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_listZ (type.arrow type_nat type_Z) =>
       fun f =>
         valid_expr
           false
           (expr.App
              (expr.App f (expr.Var l))
              (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App2_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : valid_expr_nth_default_App3_bool _ = true |- _ =>
               eapply valid_expr_nth_default_App3_bool_impl1 in H;
                 eassumption
             end.
  Qed.

  Lemma valid_expr_nth_default_App1_bool_impl1 {t}
        (f : API.expr t) n :
    valid_expr_nth_default_App1_bool f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_nat type_Z =>
       fun f =>
         valid_expr
           false (expr.App f
                        (expr.Ident (ident.Literal (t:=base.type.nat) n)))
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_nth_default_App1_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             end;
      match goal with
      | H : valid_expr_nth_default_App2_bool _ = true |- _ =>
        eapply valid_expr_nth_default_App2_bool_impl1 in H
      end.
    break_match_hyps; try tauto; [ ].
    eassumption.
  Qed.

  Lemma is_fst_snd_ident_impl1 {t} (i : ident.ident t) :
    is_fst_snd_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_ZZ type_Z =>
       fun i =>
         forall x : API.expr type_ZZ,
           valid_expr true x ->
           valid_expr false (expr.App (expr.Ident i) x)
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_fst_snd_ident].
    break_match; try congruence; [ | ];
      intros; constructor; eauto.
  Qed.

  Lemma is_cast_literal_ident_eq {t} (i : ident.ident t) :
    is_cast_literal_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type_range =>
       fun i => i = ident.Literal (t:=base.type.zrange) max_range
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_cast_literal_ident].
    break_match; try congruence; [ ].
    cbv [range_good].
    intros; progress reflect_beq_to_eq zrange_beq; subst.
    reflexivity.
  Qed.

  Lemma is_cast_literal_eq {t} (r : API.expr t) :
    is_cast_literal r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range =>
       fun r =>
         r = expr.Ident (ident.Literal (t:=base.type.zrange) max_range)
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast_literal].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_cast_literal_ident _ = true |- _ =>
        apply is_cast_literal_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma is_pair_range_eq {t} (i : ident.ident t) :
    is_pair_range i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_range (type.arrow type_range type_range2) =>
       fun i => i = ident.pair
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_pair_range].
    break_match; congruence.
  Qed.

  Lemma is_cast2_literal_App2_eq {t} (r : API.expr t) :
    is_cast2_literal_App2 r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type.arrow type_range (type.arrow type_range type_range2) =>
       fun r => r = expr.Ident ident.pair
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal_App2].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_pair_range _ = true |- _ =>
        apply is_pair_range_eq in H
      end.
    congruence.
  Qed.

  Lemma is_cast2_literal_App1_eq {t} (r : API.expr t) :
    is_cast2_literal_App1 r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type.arrow type_range type_range2 =>
       fun r =>
         r = expr.App
               (expr.Ident ident.pair)
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) max_range))
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal_App1].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : is_cast_literal _ = true |- _ =>
               apply is_cast_literal_eq in H; subst
             | H : is_cast2_literal_App2 _ = true |- _ =>
               apply is_cast2_literal_App2_eq in H; subst
             end.
    congruence.
  Qed.

  Lemma is_cast2_literal_eq {t} (r : API.expr t) :
    is_cast2_literal r = true ->
    (match t as t0 return @API.expr (fun _ => unit) t0 -> Prop with
     | type_range2 =>
       fun r =>
         r = expr.App
               (expr.App
                  (expr.Ident ident.pair)
                  (expr.Ident
                     (ident.Literal (t:=base.type.zrange) max_range)))
               (expr.Ident
                  (ident.Literal (t:=base.type.zrange) max_range))
     | _ => fun _ => False
     end) r.
  Proof.
    cbv [is_cast2_literal].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : is_cast_literal _ = true |- _ =>
               apply is_cast_literal_eq in H; subst
             | H : is_cast2_literal_App1 _ = true |- _ =>
               apply is_cast2_literal_App1_eq in H; subst
             end.
    congruence.
  Qed.

  Lemma is_cast_ident_expr_impl1 {t} rc (f : API.expr t) :
    is_cast_ident_expr f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_range (type.arrow type_Z type_Z) =>
       fun f =>
         forall
           (r : API.expr type_range)
           (x : API.expr type_Z),
           is_cast_literal r = true ->
           valid_expr false x ->
           valid_expr rc (expr.App (expr.App f r) x)
     | type.arrow type_range2 (type.arrow type_ZZ type_ZZ) =>
       fun f =>
         forall
           (r : API.expr type_range2)
           (x : API.expr type_ZZ),
           is_cast2_literal r = true ->
           valid_expr false x ->
           valid_expr rc (expr.App (expr.App f r) x)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_cast_ident_expr is_cast_ident].
    break_match; try congruence; [ | ];
      intros;
      match goal with
      | H : is_cast_literal _ = true |- _ =>
        apply is_cast_literal_eq in H; subst
      | H : is_cast2_literal _ = true |- _ =>
        apply is_cast2_literal_eq in H; subst
      end.
    { constructor;
        cbv [range_good]; auto using zrange_lb. }
    { constructor;
        cbv [range_good]; auto using zrange_lb. }
  Qed.

  Lemma valid_expr_App1_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_App1_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z _ =>
       fun f =>
         forall x : API.expr type_Z,
           valid_expr false x ->
           valid_expr rc (expr.App f x)
     | type.arrow type_ZZ type_Z =>
       fun f =>
         forall x : API.expr type_ZZ,
           valid_expr true x ->
           valid_expr rc (expr.App f x)
     | type.arrow type_ZZ type_ZZ =>
       fun f =>
         forall x : API.expr type_ZZ,
           valid_expr false x ->
           valid_expr rc (expr.App f x)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_App1_bool].
    remember t.
    destruct t; try congruence.
    { intros; exfalso.
      break_match_hyps; congruence. }
    { break_match; try congruence; [ | | ]; intros;
        repeat match goal with
               | H : _ && _ = true |- _ =>
                 apply andb_true_iff in H; destruct H
               | H : negb ?rc = true |- _ =>
                 destruct rc; cbn [negb] in *; try congruence; [ ]
               | H : is_fst_snd_ident _ = true |- _ =>
                 apply is_fst_snd_ident_impl1 in H; solve [eauto]
               | H : is_cast_ident_expr _ = true |- _ =>
                 eapply is_cast_ident_expr_impl1 in H;
                   apply H; solve [eauto]
               end. }
  Qed.

  Lemma valid_expr_nth_default_bool_impl1 {t}
        (e : API.expr t) :
    (exists b, t = type.base b) ->
    valid_expr_nth_default_bool e = true ->
    valid_expr false e.
  Proof.
    cbv [valid_expr_nth_default_bool].
    intro; destruct e; try congruence; [ ].
    match goal with
      | _ : API.expr (type.arrow _ ?d) |- _ =>
        destruct d
    end;
      break_match; try congruence; intros; [ ].
    match goal with
    | H : valid_expr_nth_default_App1_bool _ = true |- _ =>
      eapply valid_expr_nth_default_App1_bool_impl1 in H
    end.
    eassumption.
  Qed.

  Lemma is_mul_high_ident_eq {t} (i : ident.ident t) :
    is_mul_high_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun i => i = ident.Z_mul_high
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_mul_high_ident].
    break_match; congruence.
  Qed.

  Lemma is_mul_high_ident_expr_eq {t} (f : API.expr t) :
    is_mul_high_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f => f = expr.Ident ident.Z_mul_high
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_mul_high_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_mul_high_ident _ = true |- _ =>
        apply is_mul_high_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_expr_binop_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_binop_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_expr true y ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_binop_bool].
    break_match; try congruence; [ | ];
      intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : is_mul_high_ident_expr _ = true |- _ =>
               apply is_mul_high_ident_expr_eq in H; subst
             end; [ | ].
    { constructor; eauto; congruence. }
    { constructor; eauto; Z.ltb_to_lt; congruence. }
  Qed.

  Lemma is_shiftl_ident_eq {t} (i : ident.ident t) :
    is_shiftl_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun i => i = ident.Z_truncating_shiftl
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_shiftl_ident].
    break_match; congruence.
  Qed.

  Lemma is_shiftl_ident_expr_eq {t} (f : API.expr t) :
    is_shiftl_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f => f = expr.Ident ident.Z_truncating_shiftl
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_shiftl_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_shiftl_ident _ = true |- _ =>
        apply is_shiftl_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_shifter_eq {t} (x : API.expr t) :
    valid_shifter x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun x =>
         exists n,
           is_bounded_by_bool n width_range = true /\
           x = expr.Ident (ident.Literal (t:=base.type.Z) n)
     | _ => fun _ => False
     end) x.
  Proof.
    cbv [valid_shifter].
    break_match; try congruence; [ ].
    intros; eexists; eauto.
  Qed.

  Lemma valid_expr_shift_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_shift_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_shifter y = true ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_shift_bool].
    break_match; try congruence; [ | | ];
      intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : is_bounded_by_bool _ width_range = true |- _ =>
               cbv [is_bounded_by_bool upper lower width_range] in H
             | H : is_shiftl_ident_expr _ = true |- _ =>
               apply is_shiftl_ident_expr_eq in H; subst
             | H : valid_shifter _ = true |- _ =>
               apply valid_shifter_eq in H;
                 destruct H as [? [? ?] ]; subst
             end.
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
    { Z.ltb_to_lt.
      constructor; eauto; lia. }
  Qed.

  Lemma is_literalz_impl1 {t} (e : API.expr t) (x : Z) :
    is_literalz e x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun e => e = expr.Ident (ident.Literal (t:=base.type.Z) x)
     | _ => fun _ => False
     end) e.
  Proof.
    cbv [is_literalz].
    break_match; try congruence; intros.
    Z.ltb_to_lt; subst; congruence.
  Qed.

  Lemma is_opp_ident_eq {t} (i : ident.ident t) :
    is_opp_ident i = true ->
    (match t as t0 return ident.ident t0 -> Prop with
     | type.arrow type_Z type_Z => fun i => i = ident.Z_opp
     | _ => fun _ => False
     end) i.
  Proof.
    cbv [is_opp_ident]. break_match; congruence.
  Qed.

  Lemma is_opp_ident_expr_eq {t} (f : API.expr t) :
    is_opp_ident_expr f = true ->
    (match t as t0 return API.expr t0 -> Prop with
     | type.arrow type_Z type_Z =>
       fun f => f = expr.Ident ident.Z_opp
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [is_opp_ident_expr].
    break_match; try congruence; [ ].
    intros;
      match goal with
      | H : is_opp_ident _ = true |- _ =>
        apply is_opp_ident_eq in H
      end.
    congruence.
  Qed.

  Lemma valid_expr_select_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_select_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z (type.arrow type_Z type_Z)) =>
       fun f =>
         forall c x y : API.expr type_Z,
           valid_expr true c ->
           is_literalz x 0 = true ->
           is_literalz y (2^Semantics.width-1) = true ->
           valid_expr rc
                      (expr.App
                         (expr.App
                            (expr.App f c) x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_select_bool].
    break_match; try congruence; [ ]; intros.
    repeat match goal with
           | H : negb ?rc = true |- _ =>
             destruct rc; cbn [negb] in *; try congruence; [ ]
           | H : is_literalz _ _ = true |- _ =>
             apply is_literalz_impl1 in H
           end.
    subst; constructor; eauto.
  Qed.

  Lemma valid_lnot_modulus_eq {t} (x : API.expr t) :
    valid_lnot_modulus x = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type_Z =>
       fun x =>
         exists n,
           is_bounded_by_bool n max_range = true
           /\ n = 2 ^ Z.log2 n
           /\ x = expr.Ident (ident.Literal (t:=base.type.Z) n)
     | _ => fun _ => False
     end) x.
  Proof.
    cbv [valid_lnot_modulus].
    break_match; try congruence; [ ].
    intros; eexists; repeat split; eauto.
  Qed.

  Lemma valid_expr_lnot_modulo_bool_impl1 {t}
        rc (f : API.expr t) :
    valid_expr_lnot_modulo_bool rc f = true ->
    (match t as t0 return expr.expr t0 -> Prop with
     | type.arrow type_Z (type.arrow type_Z type_Z) =>
       fun f =>
         forall x y : API.expr type_Z,
           valid_expr true x ->
           valid_lnot_modulus y = true ->
           valid_expr rc (expr.App (expr.App f x) y)
     | _ => fun _ => False
     end) f.
  Proof.
    cbv [valid_expr_lnot_modulo_bool].
    break_match; try congruence; [ ].
    intros;
      repeat match goal with
             | H : _ && _ = true |- _ =>
               apply andb_true_iff in H; destruct H
             | H : negb ?rc = true |- _ =>
               destruct rc; cbn [negb] in *; try congruence; [ ]
             | H : valid_lnot_modulus _ = true |- _ =>
               apply valid_lnot_modulus_eq in H;
                 destruct H as [? [? [? ?] ] ]; subst
             end.
    constructor; eauto.
  Qed.

  Lemma valid_expr_bool'_impl1 {t} (e : API.expr t) :
    forall mode rc,
      valid_expr_bool' mode rc e = true ->
      match mode with
      | Binop =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_expr true x ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | Shift =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_shifter x = true ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | Select =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               is_literalz x (2^Semantics.width-1) = true ->
               valid_expr rc (expr.App f x)
         | type.arrow type_Z (type.arrow type_Z type_Z) =>
           fun f =>
             forall x y,
               is_literalz x 0 = true ->
               is_literalz y (2^Semantics.width-1) = true ->
               valid_expr rc (expr.App (expr.App f x) y)
         | type.arrow
             type_Z
             (type.arrow type_Z (type.arrow type_Z type_Z)) =>
           fun f =>
             forall c x y,
               valid_expr true c ->
               valid_expr_select_bool rc f = true ->
               is_literalz x 0 = true ->
               is_literalz y (2^Semantics.width-1) = true ->
               valid_expr rc (expr.App (expr.App (expr.App f c) x) y)
         | _ => fun _ => False
         end) e
      | Lnot =>
        (match t as t0 return expr.expr t0 -> Prop with
         | type.arrow type_Z type_Z =>
           fun f =>
             forall x,
               valid_lnot_modulus x = true ->
               valid_expr rc (expr.App f x)
         | _ => fun _ => False
         end) e
      | NotPartial => (exists b, t = type.base b) -> valid_expr rc e
      end.
  Proof.
    induction e; intros;
      cbn [valid_expr_bool'] in *;
      [ | | | | ].
    { break_match_hyps; try congruence.
      { constructor.
        repeat match goal with
               | _ => progress cbn [orb]
               | H : _ || _ = true |- _ =>
                 apply orb_true_iff in H; destruct H
               | H : _ = true |- _ => rewrite H
               | _ => rewrite Bool.orb_true_r
               | _ => reflexivity
               end. }
      { destruct rc; cbn [negb] in *; try congruence.
        constructor. } }
    { break_match_hyps; try congruence.
      { constructor. }
      { constructor. } }
    { break_match_hyps; congruence. }
    { remember s.
      remember d.
      break_match_hyps; try congruence;
          repeat match goal with
                 | H : _ && _ = true |- _ =>
                   apply andb_true_iff in H; destruct H
                 | H: valid_expr_App1_bool _ _ = true |- _ =>
                   apply valid_expr_App1_bool_type in H;
                     destruct H; destruct H; congruence
                 | IH : forall mode _ _,
                     match mode with
                     | NotPartial => _
                     | Binop => False
                     | Shift => False
                     | Select => False
                     | Lnot => False
                     end |- _ =>
                   specialize (IH NotPartial); (cbn match in IH)
                 end.
      { (* fully-applied binop case *)
        intros. apply (IHe1 Binop); eauto. }
      { (* fully-applied shift case *)
        intros. apply (IHe1 Shift); eauto. }
      { (* fully-applied select case *)
        intros.  apply (IHe1 Select); eauto. }
      { (* fully-applied lnot_modulo case *)
        intros.  apply (IHe1 Lnot); eauto. }
      { (* opp case *)
        intros.
        repeat match goal with
               | H : is_opp_ident_expr _ = true |- _ =>
                 apply is_opp_ident_expr_eq in H; subst
               | H : negb ?rc = true |- _ =>
                 destruct rc; cbn [negb] in *; try congruence; [ ]
               end.
        econstructor.
        eauto. }
      { (* cast Z case *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_Z -> type_Z)); eauto. }
      { (* nth_default case *)
        eauto using valid_expr_nth_default_bool_impl1. }
      { (* fst/snd *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_ZZ -> type_Z)); eauto. }
      { (* cast ZZ *)
        intros.
        apply (valid_expr_App1_bool_impl1
                 (t := type_ZZ -> type_ZZ)); eauto. }
      { (* partially-applied binop case *)
        intros.
        apply (valid_expr_binop_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied shift case *)
        intros.
        apply (valid_expr_shift_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied select case (last 2 arguments) *)
        intros. apply (IHe1 Select); eauto. }
      { (* partially-applied select case (all 3 arguments) *)
        intros.
        apply (valid_expr_select_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z -> type_Z)); eauto. }
      { (* partially-applied lnot_modulo case *)
        intros.
        apply (valid_expr_lnot_modulo_bool_impl1
                 (t:=type_Z -> type_Z -> type_Z)); eauto. } }
    { break_match; try congruence. }
  Qed.

  Lemma valid_expr_bool_impl1 {t} (e : API.expr t) :
    (exists b, t = type.base b) ->
    forall rc,
      valid_expr_bool rc e = true -> valid_expr rc e.
  Proof.
    cbv [valid_expr_bool]; intros.
    match goal with H : _ = true |- _ =>
                    apply valid_expr_bool'_impl1 in H end.
    eauto.
  Qed.

  Lemma valid_expr_bool_impl2 {t} (e : API.expr t) :
    forall rc,
      valid_expr rc e ->
      valid_expr_bool rc e = true.
  Proof.
    cbv [valid_expr_bool].
    induction 1; intros; subst; cbn;
      repeat match goal with
             | _ => progress cbn [andb]
             | H : valid_expr_bool' _ _ _ = true |- _ =>
               rewrite H
             | _ => rewrite Z.eqb_refl
             end;
      auto using
           Bool.andb_true_iff, Bool.orb_true_iff,
      is_bounded_by_bool_max_range,
      is_bounded_by_bool_width_range; [ | | ].
    { (* lnot_modulo *)
      apply Bool.andb_true_iff; split;
        Z.ltb_to_lt; auto. }
    { (* select *)
      break_match;
        repeat match goal with
               | H : (_ && _)%bool = true  |- _ =>
                 apply Bool.andb_true_iff in H; destruct H
               end; congruence. }
    { (* binop *)
      match goal with
      | H : translate_binop ?i <> None
        |- context [match translate_binop ?i with _ => _ end] =>
        destruct (translate_binop i)
      end; cbn [andb]; congruence. }
  Qed.



  Lemma valid_expr_bool_iff {t} (e : API.expr (type.base t)) :
    forall rc,
      valid_expr_bool rc e = true <-> valid_expr rc e.
  Proof.
    split; eauto using valid_expr_bool_impl1, valid_expr_bool_impl2.
  Qed.
End Expr.
