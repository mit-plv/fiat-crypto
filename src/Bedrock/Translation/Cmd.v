Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

(** Tactics ***)
Ltac cleanup :=
  repeat first [ progress cbn [fst snd eq_rect] in *
               | progress destruct_head'_and
               | match goal with H : exists _, _ |- _ => destruct H end
               | match goal with H : ?x = ?x |- _ => clear H end ].
(* borrowed from Fancy/Compiler.v *)
(* TODO : replace calls to this with simpler/faster tactics *)
Ltac hammer_wf :=
  repeat first [ progress subst
               | progress cbn [eq_rect fst snd projT1 projT2] in *
               | progress destruct_head'_False
               | progress inversion_wf_one_constr
               | progress Inversion.Compilers.expr.invert_subst
               | progress destruct_head'_and
               | progress destruct_head'_sig
               | progress Inversion.Compilers.expr.inversion_expr
               | break_innermost_match_hyps_step
               | match goal with
                 | H : existT _ _ _ = existT _ _ _ |- _ =>
                   apply Eqdep_dec.inj_pair2_eq_dec in H;
                   [ | solve [ apply Inversion.Compilers.type.type_eq_Decidable] ]
                 end ]; cleanup.

Section Cmd.
  Context {p : Types.parameters}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  (* TODO: think about whether this is really the best way to handle
     the situation where one fiat-crypto LetIn translates to two bedrock2
     commands; perhaps a preprocessing step to make the compilation
     1-to-1 is better *)
  (* TODO: whatever strategy is decided upon, use it for mul_split as well *)
  Section Carries.
    Local Notation AddGetCarry r1 r2 s x y :=
      (expr.App
         (s:=type_ZZ) (d:=type_ZZ)
         (* cast *)
         (expr.App
            (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
            (expr.Ident ident.Z_cast2)
            (expr.App
               (s:=type_range) (d:=type_range2)
               (expr.App
                  (s:=type_range) (d:=type.arrow type_range type_range2)
                  (expr.Ident ident.pair)
                  (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
               (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (* add-get-carry expression *)
         (expr.App (s:=type_Z)
                   (expr.App (s:=type_Z)
                             (expr.App
                                (expr.Ident ident.Z_add_get_carry)
                                (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                             x) y)).
    Local Notation AddWithGetCarry r1 r2 s c x y :=
      (expr.App
         (s:=type_ZZ) (d:=type_ZZ)
         (* cast *)
         (expr.App
            (s:=type_range2) (d:=type.arrow type_ZZ type_ZZ)
            (expr.Ident ident.Z_cast2)
            (expr.App
               (s:=type_range) (d:=type_range2)
               (expr.App
                  (s:=type_range) (d:=type.arrow type_range type_range2)
                  (expr.Ident ident.pair)
                  (expr.Ident (ident.Literal (t:=base.type.zrange) r1)))
               (expr.Ident (ident.Literal (t:=base.type.zrange) r2))))
         (* add-with-get-carry expression *)
         (expr.App (s:=type_Z)
                   (expr.App (s:=type_Z)
                             (expr.App (s:=type_Z)
                                       (expr.App
                                          (expr.Ident ident.Z_add_with_get_carry)
                                          (expr.Ident (ident.Literal (t:=base.type.Z) s)))
                                       c) x) y)).

    Definition translate_add_get_carry (sum carry : Syntax.varname)
               r1 r2 s (x y : API.expr type_Z) : Syntax.cmd.cmd :=
      if (range_good r1 && range_good r2)%bool
      then if Z.eqb s maxint
           then
             let sum_expr := Syntax.expr.op Syntax.bopname.add
                                            (translate_expr true x) (translate_expr true y) in
             (* Given (0 <= x < w) and (0 <= y < w), carry bit = (x + y) mod w
                <? x: if (x + y) mod w < x, then clearly the sum must have
                overflowed (since 0 <= y) if the sum overflowed, then (x + y)
                mod w = x + y - w < x *)
             let carry_expr := Syntax.expr.op Syntax.bopname.ltu
                                              (Syntax.expr.var sum) (translate_expr true x) in
             Syntax.cmd.seq (Syntax.cmd.set sum sum_expr) (Syntax.cmd.set carry carry_expr)
           else Syntax.cmd.skip
      else Syntax.cmd.skip.

    Definition translate_add_with_get_carry (sum carry : Syntax.varname)
               r1 r2 s (c x y : API.expr type_Z) : Syntax.cmd.cmd :=
      if (range_good r1 && range_good r2)%bool
      then if Z.eqb s maxint
           then
             let sum_cx := Syntax.expr.op Syntax.bopname.add
                                          (translate_expr true c) (translate_expr true x) in
             let sum_cxy := Syntax.expr.op Syntax.bopname.add
                                           (Syntax.expr.var sum) (translate_expr true y) in
             (* compute the carry by adding together the carries of both
                additions, using the same strategy as in Z_add_get_carry *)
             let carry_cx := Syntax.expr.op Syntax.bopname.ltu
                                            (Syntax.expr.var sum) (translate_expr true x) in
             let carry_cxy := Syntax.expr.op Syntax.bopname.ltu
                                             (Syntax.expr.var sum) (translate_expr true y) in
             let carry_expr := Syntax.expr.op Syntax.bopname.add (Syntax.expr.var carry) carry_cxy in
             (* sum := c + x
                carry := (sum <? x)
                sum +=y
                carry += (sum <? y) *)
             (Syntax.cmd.seq
                (Syntax.cmd.seq
                   (Syntax.cmd.seq
                      (Syntax.cmd.set sum sum_cx)
                      (Syntax.cmd.set carry carry_cx))
                   (Syntax.cmd.set sum sum_cxy))
                (Syntax.cmd.set carry carry_expr))
           else Syntax.cmd.skip
      else Syntax.cmd.skip.


    Definition translate_carries {t} (e : @API.expr ltype t) (nextn : nat)
      : option (nat * ltype t * Syntax.cmd.cmd) :=
      let sum := varname_gen nextn in
      let carry := varname_gen (S nextn) in
      match e with
      | AddGetCarry r1 r2 s x y =>
        Some (2%nat, (sum,carry), translate_add_get_carry sum carry r1 r2 s x y)
      | AddWithGetCarry r1 r2 s c x y =>
        Some (2%nat, (sum,carry), translate_add_with_get_carry sum carry r1 r2 s c x y)
      | _ => None
      end.
  End Carries.

  Fixpoint assign {t : base.type} (nextn : nat)
    : base_rtype t -> (nat * base_ltype t * Syntax.cmd.cmd) :=
    match t with
    | base.type.prod a b =>
      fun rhs =>
        let assign1 := assign nextn (fst rhs) in
        let assign2 := assign (nextn + fst (fst assign1)) (snd rhs) in
        ((fst (fst assign1) + fst (fst assign2))%nat,
         (snd (fst assign1), snd (fst assign2)),
         Syntax.cmd.seq (snd assign1) (snd assign2))
    | base.type.list (base.type.type_base base.type.Z) =>
      fun _ =>
        (* not allowed to assign to a list; return garbage *)
        (0%nat, dummy_base_ltype _, Syntax.cmd.skip)
    | base.type.list _ | base.type.option _ | base.type.unit
    | base.type.type_base _ =>
      fun rhs =>
        let v := varname_gen nextn in
        (1%nat, v, Syntax.cmd.set v rhs)
    end.

  Fixpoint translate_cmd {t} (e : @API.expr ltype (type.base t)) (nextn : nat)
    : nat (* number of variable names used *)
      * base_ltype t (* variables in which return values are stored *)
      * Syntax.cmd.cmd (* actual program *) :=
    match e in expr.expr t0 return (nat * ltype t0 * Syntax.cmd.cmd) with
    | expr.LetIn (type.base t1) (type.base t2) x f =>
      let trx :=
          match translate_carries x nextn with
          | Some trx => trx
          | None => assign nextn (translate_expr true x)
          end in
      let trf := translate_cmd (f (snd (fst trx))) (nextn + fst (fst trx)) in
      ((fst (fst trx) + fst (fst trf))%nat,
       snd (fst trf),
       Syntax.cmd.seq (snd trx) (snd trf))
    | expr.App
        type_listZ type_listZ
        (expr.App type_Z _ (expr.Ident _ (ident.cons _)) x) l =>
      let trx := assign nextn (translate_expr true x) in
      let trl := translate_cmd l (S nextn) in
      ((fst (fst trx) + fst (fst trl))%nat,
       snd (fst trx) :: snd (fst trl),
       Syntax.cmd.seq (snd trx) (snd trl))
    | expr.App _ (type.base t) f x =>
      let v := translate_expr true (expr.App f x) in
      assign nextn v
    | expr.Ident type_listZ (ident.nil _) =>
      (0%nat, [], Syntax.cmd.skip)
    | expr.Ident (type.base _) x =>
      let v := translate_expr true (expr.Ident x) in
      assign nextn v
    | expr.Var (type.base _) x =>
      let v := translate_expr true (expr.Var x) in
      assign nextn v
    | _ => (0%nat, dummy_ltype _, Syntax.cmd.skip)
    end.

  Section Proofs.
    Context {p_ok : @ok p}.
    Context (call : Syntax.funname ->
                    Semantics.trace ->
                    Interface.map.rep (map:=Semantics.mem) ->
                    list Interface.word.rep ->
                    (Semantics.trace -> Interface.map.rep (map:=Semantics.mem) ->
                     list Interface.word.rep -> Prop) ->
                    Prop).
    Context (Proper_call :
               Morphisms.pointwise_relation
                 Syntax.funname
                 (Morphisms.pointwise_relation
                    Semantics.trace
                    (Morphisms.pointwise_relation
                       Interface.map.rep
                       (Morphisms.pointwise_relation
                          (list Interface.word.rep)
                          (Morphisms.respectful
                             (Morphisms.pointwise_relation
                                Semantics.trace
                                (Morphisms.pointwise_relation
                                   Interface.map.rep
                                   (Morphisms.pointwise_relation
                                      (list Interface.word.rep) Basics.impl)))
                             Basics.impl)))) call call).

    (* TODO: are these all needed? *)
    Local Instance sem_ok : Semantics.parameters_ok semantics
      := semantics_ok.
    Local Instance mem_ok : Interface.map.ok Semantics.mem
      := Semantics.mem_ok.
    Local Instance varname_eqb_spec x y : BoolSpec _ _ _
      := Semantics.varname_eqb_spec x y.

    (* TODO : fill this in *)
    Axiom valid_carry_expr :
      forall {t}, @API.expr (fun _ => unit) t -> Prop.

    Inductive valid_cmd : forall {t}, @API.expr (fun _ => unit) (type.base t) -> Prop :=
    | valid_LetIn_carry :
        forall {b} x f,
          valid_carry_expr x -> valid_cmd (f tt) ->
          valid_cmd (expr.LetIn (A:=type_ZZ) (B:=type.base b) x f)
    (* N.B. LetIn is split into cases so that only pairs of type_base and type_base are
      allowed; this is primarily because we don't want lists on the LHS *)
    | valid_LetIn_prod :
        forall {a b c} x f,
          valid_expr true x -> valid_cmd (f tt) ->
          valid_cmd (expr.LetIn
                        (A:=type.base (base.type.prod
                                         (base.type.type_base a) (base.type.type_base b)))
                        (B:=type.base c) x f)
    | valid_LetIn_base :
        forall {a b} x f,
          valid_expr true x -> valid_cmd (f tt) ->
          valid_cmd (expr.LetIn (A:=type.base (base.type.type_base a)) (B:=type.base b) x f)
    | valid_cons :
        forall x l,
          valid_expr true x ->
          valid_cmd l ->
          valid_cmd
            (expr.App
               (expr.App
                  (expr.Ident
                     (ident.cons (t:=base.type.type_base base.type.Z))) x) l)
    | valid_nil :
        valid_cmd (expr.Ident (ident.nil (t:=base.type.type_base base.type.Z)))
    | valid_inner : forall {t} e,
        valid_expr true e -> valid_cmd (t:=t) e
    .

    (* General-purpose lemmas about maps that should be later moved to coqutil *)
    (* TODO: move *)
    Section Maps.
      Lemma only_differ_trans {key value} {map: Interface.map.map key value}
            m1 m2 m3 ks1 ks2 :
        Interface.map.only_differ m2 ks1 m1 ->
        Interface.map.only_differ m3 ks2 m2 ->
        Interface.map.only_differ m3 (PropSet.union ks1 ks2) m1.
      Admitted.

      (* TODO: move *)
      Lemma only_differ_sameset {key value} {map: Interface.map.map key value}
            m1 m2 ks1 ks2 :
        PropSet.sameset ks1 ks2 ->
        Interface.map.only_differ m2 ks1 m1 ->
        Interface.map.only_differ m2 ks2 m1.
      Admitted.

      Lemma sameset_iff {E} (s1 s2 : PropSet.set E) :
        PropSet.sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
      Proof.
        cbv [PropSet.sameset PropSet.subset PropSet.elem_of]. split.
        { destruct 1; split; eauto. }
        { intro Hiff; split; apply Hiff; eauto. }
      Qed.
    End Maps.

    (* Reasoning about various collections of variable names *)
    Section Varnames.
      Fixpoint varname_set {t} : base_ltype t -> PropSet.set Syntax.varname :=
        match t with
        | base.type.prod a b =>
          fun x => PropSet.union (varname_set (fst x)) (varname_set (snd x))
        | base.type.list (base.type.type_base base.type.Z) =>
          PropSet.of_list
        | _ => fun x => PropSet.singleton_set x
        end.

      Definition used_varnames nextn nvars : PropSet.set Syntax.varname :=
        PropSet.of_list (map varname_gen (seq nextn nvars)).

      Lemma used_varnames_iff nextn nvars v :
        used_varnames nextn nvars v <->
        (exists n,
            v = varname_gen n /\ nextn <= n < nextn + nvars)%nat.
      Admitted.

      Lemma used_varnames_le nextn nvars n :
        (nextn + nvars <= n)%nat ->
        ~ used_varnames nextn nvars (varname_gen n).
      Admitted.

      Definition varname_not_in_context {var1}
                 (v : Syntax.varname)
                 (x : {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
        : Prop :=
        match x with
        | existT (type.base b) (w, x, y) =>
          ~ (varname_set y) v
        | existT (type.arrow _ _) _ => False (* no functions allowed *)
        end.

      Lemma equivalent_not_varname_set {t}
            locals1 locals2 vset (varnames : base_ltype t) x :
        Interface.map.only_differ locals1 vset locals2 ->
        (forall v : Syntax.varname, vset v -> ~ varname_set varnames v) ->
        forall mem,
          equivalent x (rtype_of_ltype varnames) locals1 mem ->
          equivalent x (rtype_of_ltype varnames) locals2 mem.
      Proof.
        (* TODO : clean up this proof *)
        intros Hdiffer Hexcl.
        induction t;
          cbn [fst snd rtype_of_ltype varname_set
                   equivalent rep.Z rep.listZ_local rep.equiv]; intros;
          BreakMatch.break_match; DestructHead.destruct_head'_and; try tauto.
        { (* base case *)
          cbv [PropSet.singleton_set
                 PropSet.elem_of
                 varname_set
                 WeakestPrecondition.expr
                 WeakestPrecondition.expr_body
                 WeakestPrecondition.get ] in *.
          specialize (Hexcl varnames); intros;
            destruct (Hdiffer varnames) as [? | Heq];
              [ tauto | rewrite <-Heq; eauto ]. }
        { (* prod case *)
          cbn [varname_set] in Hexcl; cbv [PropSet.union PropSet.elem_of] in Hexcl.
          eapply SeparationLogic.Proper_sep_impl1;
            cbv [Lift1Prop.impl1]; intros; [ | | eassumption ];
              [ apply IHt1 | apply IHt2]; auto;
                let x := fresh in
                let y := fresh in
                intros x y; specialize (Hexcl x y); tauto. }
        { (* list case *)
          split; [ assumption | ].
          cbn [varname_set] in Hexcl; cbv [PropSet.union PropSet.of_list] in Hexcl.
          cbn [Language.Compilers.base.interp Compilers.base_interp base_rtype] in *. (* simplify types *)
          cbn [rep.rtype rep.Z] in *.
          apply Forall2_forall_iff with (d1:=0) (d2:=Syntax.expr.literal 0); auto.
          match goal with H : _ |- _ =>
                          intros i Hi;
                            rewrite Forall2_forall_iff
                              with (d1:=0) (d2:=Syntax.expr.literal 0) in H by auto;
                            specialize (H i Hi); revert H
          end.
          apply nth_default_preserves_properties_length_dep; try lia.
          cbn [equivalent base_ltype rep.Z rep.listZ_local rep.ltype rep.equiv
                          rep.rtype_of_ltype rtype_of_ltype] in *.
          intros *. rewrite in_map_iff. intros; cleanup. subst.
          apply IHt; intros; auto.
          match goal with H : vset _ |- _ => apply Hexcl in H end.
          congruence. }
      Qed.

      Lemma equivalent_not_in_context {var1} locals1 locals2 vset x :
        Interface.map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> varname_not_in_context v x) ->
        equiv3 (var1:=var1) locals1 x ->
        equiv3 locals2 x.
      Proof.
        intros; cbv [equiv3 varname_not_in_context locally_equivalent] in *.
        destruct x as [x [ [? ?] ?] ]; destruct x; [ | tauto ].
        eauto using equivalent_not_varname_set.
      Qed.

      Lemma equivalent_not_in_context_forall {var1} locals1 locals2 vset G :
        Interface.map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> Forall (varname_not_in_context v) G) ->
        Forall (equiv3 (var1:=var1) locals1) G ->
        Forall (equiv3 locals2) G.
      Proof.
        intros Hdiffer Hexcl; induction G; intros; constructor;
          match goal with
          | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
        { eapply equivalent_not_in_context; eauto.
          intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
        { apply IHG; auto.
          intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
      Qed.

      Lemma only_differ_step nvars nvars' nextn l1 l2 l3 :
        Interface.map.only_differ l1 (used_varnames nextn nvars) l2 ->
        Interface.map.only_differ l2 (used_varnames (nextn + nvars) nvars') l3 ->
        Interface.map.only_differ l1 (used_varnames nextn (nvars + nvars')) l3.
      Proof.
        cbv [Interface.map.only_differ used_varnames PropSet.of_list
                                       PropSet.elem_of].
        let H1 := fresh in
        let H2 := fresh in
        let x := fresh "x" in
        intros H1 H2 x; specialize (H1 x); specialize (H2 x).
        repeat match goal with
               | _ => progress cleanup
               | _ => progress subst
               | H : _ \/ _ |- _ => destruct H
               | |- context [In _ (map _ _)] => rewrite in_map_iff
               | H : In _ (map _ _) |- _ => apply in_map_iff in H
               | H : In _ (seq _ _) |- _ => apply in_seq in H
               | H : varname_gen _ = varname_gen _ |- _ =>
                 apply varname_gen_unique in H
               | _ => solve [right; congruence]
               | _ => solve [left; eexists;
                             rewrite in_seq, varname_gen_unique; split;
                             eauto with lia ]
               end.
      Qed.

      (* if two maps only differ on some keys, and we get a key that
         is not in the differing set, then any proposition that holds
         on one result should hold on the other. *)
      Lemma get_untouched m1 m2 ks k P :
        Interface.map.only_differ m2 ks m1 ->
        ~ ks k ->
        WeakestPrecondition.get m1 k P <-> WeakestPrecondition.get m2 k P.
      Admitted.

      Lemma expr_untouched mem1 mem2 l1 l2 vars v P :
        Interface.map.only_differ l2 vars l1 ->
        ~ vars v ->
        WeakestPrecondition.expr mem1 l1 (Syntax.expr.var v) P <->
        WeakestPrecondition.expr mem2 l2 (Syntax.expr.var v) P.
      Proof.
        intros.
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
        rewrite get_untouched; eauto; reflexivity.
      Qed.
    End Varnames.

    Lemma translate_carries_Some {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_carry_expr x1 ->
      exists cmdx,
        translate_carries (t:=type.base t) x3 nextn = Some cmdx.
    Admitted.

    (* valid expressions can't possibly be valid carry commands *)
    Lemma translate_carries_None {t : base.type}
          G x1 x2 x3 nextn :
      wf3 (var2:=API.interp_type) G x1 x2 x3 ->
      valid_expr true x1 ->
      translate_carries (t:=type.base t) x3 nextn = None.
    Admitted.

    (* N.B. technically, x2 and f2 are not needed in the following
       lemmas, it just makes things easier *)
    Lemma translate_cmd_carry {t1 t2 : base.type}
          G x1 x2 x3 f1 f2 f3 nextn
          (trx : nat * base_ltype t1 * Syntax.cmd.cmd) :
      wf3 G x1 x2 x3 ->
      (forall v1 v2 v3,
          wf3
            (existT (fun t => (unit * API.interp_type t * ltype t)%type)
                    (type.base t1) (v1, v2, v3) :: G)
              (f1 v1) (f2 v2) (f3 v3)) ->
      valid_cmd (f1 tt) ->
      translate_carries (t:=type.base t1) x3 nextn = Some trx ->
      let trf := translate_cmd (f3 (snd (fst trx))) (nextn + fst (fst trx)) in
      let nvars := (fst (fst trx) + fst (fst trf))%nat in
      translate_cmd (expr.LetIn (A:=type.base t1) (B:=type.base t2) x3 f3) nextn =
      (nvars, snd (fst trf), Syntax.cmd.seq (snd trx) (snd trf)).
    Proof.
      intros. subst nvars trf. cbn [translate_cmd].
      match goal with H : _ = Some _ |- _ => rewrite H end.
      reflexivity.
    Qed.

    Lemma translate_carries_correct {t}
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t)) :
      (* e1 is a valid input to translate_carries_correct *)
      valid_carry_expr e1 ->
      forall G nextn
             (trx : nat * base_ltype t * Syntax.cmd.cmd),
        wf3 G e1 e2 e3 ->
        translate_carries e3 nextn = Some trx ->
        forall (tr : Semantics.trace)
               (mem locals : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          context_equiv G locals ->
          WeakestPrecondition.cmd
            call (snd trx) tr mem locals
            (fun tr' mem' locals' =>
               tr = tr'
               (* translate_carries never stores anything -- mem unchanged *)
               /\ mem = mem'
               (* return values match the number of variables used *)
               /\ PropSet.sameset (varname_set (snd (fst trx)))
                                  (used_varnames nextn (fst (fst trx)))
               (* new locals only differ in the values of LHS variables *)
               /\ Interface.map.only_differ locals (varname_set (snd (fst trx))) locals'
               (* information stored in LHS variables is equivalent to interp *)
               /\ sep
                    (emp (locally_equivalent
                            (API.interp e2) (rtype_of_ltype (snd (fst trx))) locals'))
                    R mem').
    Admitted.

    (* TODO: it's always the case that
         varname_set (snd (fst a)) = { nextn,  ..., nextn + fst (fst a) - 1}
       consider which representation is easier to work with *)
    Lemma assign_correct {t} :
      forall (x : base.interp t)
             (rhs : base_rtype t)
             (nextn : nat)
             (tr : Semantics.trace)
             (mem locals : Interface.map.rep)
             (R : Interface.map.rep -> Prop),
        (* rhs == x *)
        locally_equivalent x rhs locals ->
        let a := assign nextn rhs in
        WeakestPrecondition.cmd
          call (snd a)
          tr mem locals
          (fun tr' mem' locals' =>
             tr = tr'
             (* assign never stores anything -- mem unchanged *)
             /\ mem = mem'
             (* return values match the number of variables used *)
             /\ PropSet.sameset (varname_set (snd (fst a)))
                                (used_varnames nextn (fst (fst a)))
             (* new locals only differ in the values of LHS variables *)
             /\ Interface.map.only_differ locals (varname_set (snd (fst a))) locals'
             (* evaluating lhs == x *)
             /\ sep (emp (locally_equivalent x (rtype_of_ltype (snd (fst a))) locals')) R mem').
    Admitted.

    (* if e is a valid_expr, it will hit the cases that call translate_expr *)
    Lemma translate_cmd_valid_expr {t}
          (e1 : @API.expr (fun _ => unit) (type.base t))
          (e2 : @API.expr API.interp_type (type.base t))
          (e3 : @API.expr ltype (type.base t))
          G nextn :
      valid_expr true e1 ->
      wf3 G e1 e2 e3 ->
      translate_cmd e3 nextn = assign nextn (translate_expr true e3).
    Proof.
      inversion 1; hammer_wf; try reflexivity;
        inversion 1; hammer_wf; reflexivity.
    Qed.

    Lemma translate_cmd_correct {t'} (t:=type.base t')
          (* three exprs, representing the same Expr with different vars *)
          (e1 : @API.expr (fun _ => unit) t)
          (e2 : @API.expr API.interp_type t)
          (e3 : @API.expr ltype t)
          (* e1 is valid input to translate_cmd *)
          (e1_valid : valid_cmd e1)
          (* context list *)
          (G : list _) :
      (* exprs are all related *)
      wf3 G e1 e2 e3 ->
      forall (locals : Interface.map.rep)
             (nextn : nat),
        (* ret := fiat-crypto interpretation of e2 *)
        let ret1 : base.interp t' := API.interp e2 in
        (* out := translation output for e3 *)
        let out := translate_cmd e3 nextn in
        let nvars := fst (fst out) in
        let ret2 := rtype_of_ltype (snd (fst out)) in
        let body := snd out in
        (* G doesn't contain variables we could accidentally overwrite *)
        (forall n,
            (nextn <= n)%nat ->
            Forall (varname_not_in_context (varname_gen n)) G) ->
        forall (tr : Semantics.trace)
               (mem : Interface.map.rep)
               (R : Interface.map.rep -> Prop),
          (* contexts are equivalent; for every variable in the context list G,
             the fiat-crypto and bedrock2 results match *)
          context_equiv G locals ->
          (* TODO: does this need to be a separation-logic condition? *)
          R mem ->
          (* executing translation output is equivalent to interpreting e *)
          WeakestPrecondition.cmd
            call body tr mem locals
            (fun tr' mem' locals' =>
               tr = tr' /\
               mem = mem' /\
               Interface.map.only_differ
                 locals (used_varnames nextn nvars) locals' /\
          sep (emp (locally_equivalent ret1 ret2 locals')) R mem').
    Proof.
      revert e2 e3 G.
      subst t.
      induction e1_valid; try (inversion 1; [ ]); cbv zeta in *; intros.
      all:hammer_wf. (* get rid of the wf nonsense *)

      { (* carry let-in *)
        (* posit the existence of a return value from translate_carries and use
           it to rewrite translate_expr *)
        match goal with H : valid_carry_expr _ |- _ =>
                        pose proof H;
                        eapply translate_carries_Some in H;
                        [ destruct H | eassumption .. ]
        end.
        erewrite @translate_cmd_carry by eassumption.
        cleanup.

        (* simplify fiat-crypto step *)
        intros; cbn [expr.interp type.app_curried] in *.
        cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

        (* simplify bedrock2 step *)
        cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].
        (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
        2 : eapply translate_carries_correct with (R0:=R); try eassumption.

        (* use inductive hypothesis *)
        cleanup.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [ eapply Proper_call | repeat intro | ].

        2: { eapply IHe1_valid with (R:=R);
             clear IHe1_valid;
             try match goal with H : _ |- _ => solve [apply H] end;
             repeat match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
             cleanup; eauto with lia.

             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context].
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               eauto using used_varnames_le. }
             { (* proof that context_list_equiv continues to hold *)
               cbv [context_equiv] in *; apply Forall_cons; [ eassumption | ].
               eapply equivalent_not_in_context_forall; eauto. intro.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               rewrite used_varnames_iff. intros; cleanup.
               subst. eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* let-in (product of base types) *)
      (* simplify one translation step *)
      cbn [translate_cmd].
      erewrite translate_carries_None by eassumption.
      cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.
             { (* proof that new context doesn't contain variables that could be
                  overwritten in the future *)
               intros; apply Forall_cons; eauto with lia; [ ].
               cbn [varname_not_in_context ltype base_ltype] in *.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               eauto using used_varnames_le. }
             { (* proof that context_list_equiv continues to hold *)
               cbv [context_equiv] in *; apply Forall_cons; eauto; [ ].
               eapply equivalent_not_in_context_forall; eauto. intro.
               match goal with H : PropSet.sameset _ _ |- _ =>
                               rewrite sameset_iff in H; rewrite H end.
               rewrite used_varnames_iff. intros; cleanup.
               subst. eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* let-in (base type) *)
      (* simplify one translation step *)
      cbn [translate_cmd].
      erewrite translate_carries_None by eassumption.
      cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R);
           clear IHe1_valid;
           try match goal with H : _ |- _ => solve [apply H] end;
           match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end;
           cleanup; eauto with lia.

           { (* proof that new context doesn't contain variables that could be
                overwritten in the future *)
             intros; apply Forall_cons; eauto with lia; [ ].
             cbn [assign fst] in *.
             cbn [varname_not_in_context varname_set fst snd].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             setoid_rewrite varname_gen_unique.
             lia. }
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_equiv] in *; apply Forall_cons; eauto; [ ].
             eapply equivalent_not_in_context_forall; eauto.
             cbn [assign snd fst varname_set].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             intros; subst; eauto. } }
        { intros; cleanup; subst; repeat split; try tauto; [ ].
          (* remaining case : only_differ *)
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. } }
    { (* cons *)

      (* repeatedly do inversion until the cons is exposed *)
      repeat match goal with
             | H : wf3 _ _ _ _ |- _ =>
               match type of H with context [Compilers.ident.cons] =>
                                    inversion H; hammer_wf
               end
             end.

      (* simplify one translation step *)
      cbn [translate_cmd]. cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried Compilers.ident_interp] in *.
      cbv [Rewriter.Util.LetIn.Let_In] in *. cleanup.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      (* use inductive hypothesis *)
      cleanup.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      2: { eapply IHe1_valid with (R:=R); clear IHe1_valid.
           all:try match goal with H : _ |- _ => solve [apply H] end.
           all: match goal with
                  H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
           all:cleanup.
           all: try solve [eauto with lia].
           { (* proof that context_list_equiv continues to hold *)
             cbv [context_equiv] in *.
             eapply equivalent_not_in_context_forall; eauto.
             cbn [assign snd fst varname_set].
             cbv [PropSet.union PropSet.singleton_set PropSet.elem_of].
             intros; subst; eauto. } }
      { intros; cleanup; subst; repeat split; try tauto; [ | ].
        all:cbn [assign fst snd varname_set] in *.
        { (* only_differ *)
          rewrite <-(Nat.add_1_r nextn) in *.
          eapply only_differ_step; try eassumption; [ ].
          eapply only_differ_sameset; eauto. }
        { (* equivalence of output holds *)
          clear IHe1_valid.
          apply sep_emp_l.
          repeat match goal with H : sep (emp _) _ _ |- _ => apply sep_emp_l in H end.
          destruct_head'_and.
          match goal with H : locally_equivalent _ _ _ |- _ =>
                          cbv [locally_equivalent] in *;
                            (* plug in just anything for locally_equivalent mem *)
                            specialize (H ltac:(auto))
          end.
          cbn [fst snd rtype_of_ltype rep.rtype_of_ltype rep.equiv rep.listZ_local
                   locally_equivalent equivalent] in *.
          cleanup.
          rewrite ?map_length in *.
          repeat split; cbn [length]; [ congruence | | assumption ].
          apply Forall2_cons; [|eassumption].

          cbn [rep.equiv rep.Z] in *.
          let mem := fresh "mem" in
          intros ? mem; eapply expr_untouched with (mem2:=mem); eauto; [ ].
          cbv [used_varnames PropSet.of_list PropSet.elem_of].
          rewrite in_map_iff. intro; cleanup.
          match goal with H : varname_gen ?x = varname_gen _ |- _ =>
                          apply varname_gen_unique in H; subst x end.
          match goal with H : In _ (seq _ _) |- _ =>
                          apply in_seq in H end.
          lia. } } }
    { (* nil *)
      (* simplify one translation step *)
      cbn [translate_cmd assign fst snd]. cleanup.

      (* simplify fiat-crypto step *)
      intros; cbn [expr.interp type.app_curried Compilers.ident_interp] in *.

      (* simplify bedrock2 step *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

      repeat split; eauto; [ | ].
      { cbv [Interface.map.only_differ]. right; reflexivity. }
      { apply sep_emp_l. cbv [locally_equivalent].
        cbn [equivalent rep.Z rep.listZ_local rep.equiv
                        rep.rtype_of_ltype rtype_of_ltype map].
        eauto. } }
    { (* valid expr *)
      erewrite translate_cmd_valid_expr by eauto.

      (* simplify bedrock2 cmd *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ eapply Proper_call | repeat intro | ].
      (* N.B. putting below line in the [ | | ] above makes eassumption fail *)
      2 : eapply assign_correct; try eassumption; [ ];
        eapply translate_expr_correct; eassumption.

      cleanup. repeat split; eauto.
      eapply only_differ_sameset; eauto. }
    Qed.
  End Proofs.
End Cmd.