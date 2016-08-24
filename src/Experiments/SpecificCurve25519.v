Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Crypto.Assembly.Evaluables.

Section Definitions.
  Context {T: Type} {E: Evaluable T}.

  Inductive type := TN | TT | Prod : type -> type -> type.

  Fixpoint interp_type (t:type): Type :=
    match t with
    | TT => T
    | TN => nat
    | Prod a b => prod (interp_type a) (interp_type b)
    end.

  Inductive binop : type -> type -> type -> Type := 
    | OPadd : binop TT TT TT
    | OPsub : binop TT TT TT
    | OPmul : binop TT TT TT
    | OPmask : binop TT TN TT
    | OPshiftr : binop TT TN TT.
    (* TODO: should [Pair] be a [binop]? *)

  Definition interp_binop {t1 t2 t} (op:binop t1 t2 t) : interp_type t1 -> interp_type t2 -> interp_type t :=
    match op with
    | OPadd    => @eadd T E 
    | OPsub    => @esub T E
    | OPmul    => @emul T E
    | OPmask   => @emask T E
    | OPshiftr => @eshiftr T E
    end.

End Definitions.


Module Input.
  Section Language.
    Context {T: Type}.
    Context {E: Evaluable T}.

    Section expr.
        Context {var : type -> Type}.

        Inductive expr : type -> Type :=
        | ConstT : @interp_type T TT -> expr TT
        | ConstN : @interp_type T TN -> expr TN
        | Var : forall {t}, var t -> expr t
        | Binop : forall {t1 t2}, binop t1 t2 TT -> expr t1 -> expr t2 -> expr TT
        | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
        | Pair : forall {t1}, expr t1 -> forall {t2}, expr t2 -> expr (Prod t1 t2)
        | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
    End expr.

    Local Notation ZConst z := (@ConstT Z ZEvaluable _ z%Z).

    Definition Expr t : Type := forall var, @expr var t.

    Fixpoint interp {t} (e: @expr interp_type t) : interp_type t :=
        match e in @expr _ t return interp_type t with
        | ConstT n => n
        | ConstN n => n
        | Var _ n => n
        | Binop _ _ op e1 e2 => interp_binop op (interp e1) (interp e2)
        | Let _ ex _ eC => let x := interp ex in interp (eC x)
        | Pair _ e1 _ e2 => (interp e1, interp e2)
        | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
        end.


    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  Definition ZInterp {t} E := @Interp Z ZEvaluable t E.

  Example example_Expr : Expr TT := fun var => (
    Let (ConstT 7) (fun a =>
      Let (Let (Binop OPadd (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p =>
        MatchPair (Var p) (fun x y =>
          Binop OPadd (Var x) (Var y)))))%Z.

  Example interp_example_Expr : ZInterp example_Expr = 28%Z. reflexivity. Qed.

  (* Reification assumes the argument type is Z *)

  Ltac reify_type t :=
    lazymatch t with
    | nat => constr:(TN)
    | BinInt.Z => constr:(TT)
    | prod ?l ?r =>
        let l := reify_type l in
        let r := reify_type r in
        constr:(Prod l r)
    end.

  Ltac reify_binop op :=
    lazymatch op with
    | Z.add    => constr:(OPadd)
    | Z.sub    => constr:(OPsub)
    | Z.mul    => constr:(OPmul)
    | Z.land   => constr:(OPmask)
    | Z.shiftr => constr:(OPshiftr)
    end.

  Class reify {varT} (var:varT) {eT} (e:eT) {T:Type} := Build_reify : T.
  Definition reify_var_for_in_is {T} (x:T) (t:type) {eT} (e:eT) := False.

  Ltac reify var e :=
    lazymatch e with
    | let x := ?ex in @?eC x =>
      let ex := reify var ex in
      let eC := reify var eC in
      constr:(Let (T := Z) (var:=var) ex eC)
    | match ?ep with (v1, v2) => @?eC v1 v2 end =>
      let ep := reify var ep in
      let eC := reify var eC in
      constr:(MatchPair (T := Z) (var:=var) ep eC)
    | pair ?a ?b =>
      let a := reify var a in
      let b := reify var b in
      constr:(Pair (T := Z) (var:=var) a b)
    | ?op ?a ?b =>
      let op := reify_binop op in
      let b := reify var b in
      let a := reify var a in
      constr:(Binop (T := Z) (var:=var) op a b)
    | (fun x : ?T => ?C) =>
      let t := reify_type T in
      (* Work around Coq 8.5 and 8.6 bug *)
      (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
      (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
      (* even if its Gallina name matches a Ltac in this tactic. *)
      let maybe_x := fresh x in
      let not_x := fresh x in
      lazymatch constr:(fun (x : T) (not_x : var t) (_:reify_var_for_in_is x t not_x) =>
                          (_ : reify var C)) (* [C] here is an open term that references "x" by name *)
      with fun _ v _ => @?C v => C end
    | ?x =>
      lazymatch goal with
      | _:reify_var_for_in_is x ?t ?v |- _ => constr:(@Var Z var t v)
      | _ => (* let t := match type of x with ?t => reify_type t end in *)
        match type of x with
        | nat => constr:(@ConstN Z var x)
        | _ => constr:(@ConstT Z var x)
        end
      end
    end.
  Hint Extern 0 (reify ?var ?e) => (let e := reify var e in eexact e) : typeclass_instances.

  Ltac Reify e :=
    lazymatch constr:(fun (var:type->Type) => (_:reify var e)) with
      (fun var => ?C) => constr:(fun (var:type->Type) => C) (* copy the term but not the type cast *)
    end.

  Definition zinterp_type := @interp_type Z.
  Transparent zinterp_type.

  Goal forall (x : Z) (v : zinterp_type TT) (_:reify_var_for_in_is x TT v), reify(T:=Z) zinterp_type ((fun x => x+x) x)%Z.
    intros.
    let A := (reify zinterp_type (x + x)%Z) in pose A.
  Abort.

  Goal False.
    let z := reify zinterp_type (let x := 0 in x)%Z in pose z.
  Abort.
  
  Ltac lhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(LHS) end.
  Ltac rhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(RHS) end.

  Ltac Reify_rhs :=
    let rhs := rhs_of_goal in
    let RHS := Reify rhs in
    transitivity (ZInterp RHS);
    [|cbv iota beta delta [ZInterp Interp interp_type interp_binop interp]; reflexivity].

  Goal (0 = let x := 1+2 in x*3)%Z.
    Reify_rhs.
  Abort.

  Goal (0 = let x := 1 in let y := 2 in x * y)%Z.
    Reify_rhs.
  Abort.

  Section wf.
    Context {T : Type} {var1 var2 : type -> Type}.

    Local Notation "x ≡ y" := (existT _ _ (x, y)).

    Definition Texpr var t := @expr T var t.

    Inductive wf : list (sigT (fun t => var1 t * var2 t))%type -> forall {t}, Texpr var1 t -> Texpr var2 t -> Prop :=
    | WfConstT : forall G n, wf G (ConstT n) (ConstT n)
    | WfConstN : forall G n, wf G (ConstN n) (ConstN n)
    | WfVar : forall G t x x', In (x ≡ x') G -> @wf G t (Var x) (Var x')
    | WfBinop : forall G {t1} {t2} (e1:Texpr var1 t1) (e2:Texpr var1 t2)
                       (e1':Texpr var2 t1) (e2':Texpr var2 t2) op,
        wf G e1 e1'
        -> wf G e2 e2'
        -> wf G (Binop (T := T) op e1 e2) (Binop (T := T) op e1' e2')
    | WfLet : forall G t1 t2 e1 e1' (e2 : _ t1 -> Texpr _ t2) e2',
        wf G e1 e1'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (e2 x1) (e2' x2))
        -> wf G (Let (T := T) e1 e2) (Let (T := T) e1' e2')
    | WfPair : forall G {t1} {t2} (e1: Texpr var1 t1) (e2: Texpr var1 t2)
                      (e1': Texpr var2 t1) (e2': Texpr var2 t2),
        wf G e1 e1'
        -> wf G e2 e2'
        -> wf G (Pair (T := T) e1 e2) (Pair (T := T) e1' e2')
    | WfMatchPair : forall G t1 t2 tC ep ep' (eC : _ t1 -> _ t2 -> Texpr _ tC) eC',
        wf G ep ep'
        -> (forall x1 x2 y1 y2, wf ((x1 ≡ x2) :: (y1 ≡ y2) :: G) (eC x1 y1) (eC' x2 y2))
        -> wf G (MatchPair (T := T) ep eC) (MatchPair (T := T) ep' eC').
  End wf.
        
  Definition Wf {T: Type} {t} (E : @Expr T t) := forall var1 var2, wf nil (E var1) (E var2).

  Example example_Expr_Wf : Wf example_Expr.
  Proof.
    unfold Wf; repeat match goal with
    | [ |- wf _ _ _ ] => constructor
    | [ |- In ?x (cons ?x _) ] => constructor 1; reflexivity
    | [ |- In _ _ ] => constructor 2
    | _ => intros
    end.
  Qed.

  Axiom Wf_admitted : forall {t} (E:Expr t), @Wf Z t E.
  Ltac admit_Wf := apply Wf_admitted.
End Input.

Module Output.

  Section Language.
    Context {T: Type}.
    Context {E: Evaluable T}.

    (* A very restricted language where binary operations are restricted
    to returning [T] and must appear in [let] binders, and all pairs
    must be constructed in the return clause.  No matching on pairs is
    allowed *)

    Section expr.
      Context {var : Type}.

      Inductive arg : type -> Type :=
        | ConstT : @interp_type T TT -> arg TT
        | ConstN : @interp_type T TN -> arg TN
        | Var : var -> arg TT
        | Pair : forall {t1}, arg t1 -> forall {t2}, arg t2 -> arg (Prod t1 t2).

      Inductive expr : type -> Type :=
        | LetBinop : forall {t1 t2}, binop t1 t2 TT -> arg t1 -> arg t2 ->
                                    forall {tC}, (var -> expr tC) -> expr tC
        | Return : forall {t}, arg t -> expr t.
    End expr.

    Arguments arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Definition Expr t : Type := forall var, expr var t.

    Fixpoint interp_arg {t} (e: arg T t) : interp_type t :=
      match e with
      | ConstT n => n
      | ConstN n => n
      | Var n => n
      | Pair _ e1 _ e2 => (interp_arg e1, interp_arg e2)
      end.

    Fixpoint interp {t} (e:expr T t) : interp_type t :=
      match e with
      | LetBinop _ _ op a b _ eC =>
        let x := interp_binop op (interp_arg a) (interp_arg b) in interp (eC x)
        | Return _ a => interp_arg a
        end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E T).
  End Language.

  Example example_expr :
    (@interp Z ZEvaluable _
      (LetBinop OPadd (ConstT 7%Z) (ConstT 8%Z) (fun v => Return (Var v))) = 15)%Z.
  Proof. reflexivity. Qed.

  Section under_lets.
    Context {T var: Type}.

    Arguments arg _ _ _ : clear implicits.
    Arguments expr _ _ _ : clear implicits.

    Fixpoint under_lets {t} (e: expr T var t) {struct e} :
      forall {tC} (C:arg T var t -> expr T var tC), expr T var tC :=
      match e with
      | LetBinop _ _ op a b tC eC => fun tC C => LetBinop op a b (fun v => @under_lets _ (eC v) _ C)
      | Return t a => fun _ C => C a
      end.
  End under_lets.

  Lemma under_lets_correct {T} {E: Evaluable T} {t} (e: @expr T _ t) {tC}
    (C: @arg T _ t -> @expr T _ tC)
    (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 -> interp (C a1) = interp (C a2)) :
    forall a, interp_arg a = interp e -> interp (under_lets e C) = interp (C a).
  Proof. induction e; repeat (intuition (congruence || eauto) + simpl + rewrite_hyp !*). Qed.

  Section match_arg.
    Context {T var:Type}.

    Arguments arg _ _ _ : clear implicits.
    Arguments expr _ _ _ : clear implicits.

    Definition match_arg_Prod' {t1} {t2} (a:arg T var (Prod t1 t2)) : option (arg T var t1 * arg T var t2) :=
      match a in arg _ _ t
        return option (match t with | Prod _ _ => _ | _ => False end) with
      | Pair _ a1 _ a2 => Some (a1, a2)
      | _ => None
      end.

    Definition match_arg_Prod {t1} {t2} (a:arg T var (Prod t1 t2)) : (arg T var t1 * arg T var t2).
      refine match match_arg_Prod' a with
      | Some (a1, a2) => (a1, a2)
      | None => _ (* impossible *)
      end.
    Proof.
      intros; constructor;
        abstract (repeat match goal with
        | [a: interp_type _ |- _] => destruct a; constructor; assumption
        | [a: arg _ _ (Prod _ _) |- _] => inversion_clear a; try assumption
        end).
    Defined.

    Global Arguments match_arg_Prod / : simpl nomatch.

    Definition match_arg_Prod_Pair {t1 t2} (a1:arg T var t1) (a2:arg T var t2) :
      match_arg_Prod (Pair a1 a2) = (a1, a2) := eq_refl.
    
    Lemma match_arg_Prod_correct_helper {t} (a:arg T var t) :
      match t return arg T var t -> Prop with
      | Prod _ _ => fun a => forall a1 a2, match_arg_Prod a = (a1, a2) <-> a = Pair a1 a2
      | _ => fun _ => True
      end a.
    Proof.
      unfold match_arg_Prod; destruct a;
        repeat match goal with
        | _ => split
        | _ => intro
        | _ => progress simpl in *
        | _ => break_match
        | _ => intuition congruence
        | H: _ |- _ => eapply (f_equal match_arg_Prod) in H
        end.
    Qed.

    Lemma match_arg_Prod_correct {t1 t2} (a:arg T _ (Prod t1 t2)) (a1:arg T _ t1) (a2:arg T _ t2) :
      match_arg_Prod a = (a1, a2) <-> a = (Pair a1 a2).
    Proof.
      pose proof (match_arg_Prod_correct_helper a) as H; simpl in H; rewrite H; reflexivity.
    Qed.

    Lemma Pair_eq t0 t1 x0 x1 x0' x1' : @Pair T var t0 x0 t1 x1 = @Pair T var t0 x0' t1 x1' <-> (x0, x1) = (x0', x1').
    Proof.
      split; intro H; try congruence.
      apply (f_equal match_arg_Prod) in H; assumption.
    Qed.
  End match_arg.

  Fixpoint uninterp_arg {t} {struct t} : interp_type t -> @arg Z Z t :=
    match t with
    | TT => ConstT | TN => ConstN
    | Prod t1 t2 => fun x => let (x1, x2) := x in
        Pair (@uninterp_arg t1 x1) (@uninterp_arg t2 x2)
    end.

  Lemma interp_arg_uninterp_arg : forall t (a:interp_type t), interp_arg (uninterp_arg a) = a.
  Proof.
    induction t; simpl; intros; try reflexivity.
    break_match; subst; simpl; intuition congruence.
  Qed.

  Lemma interp_under_lets {_: Evaluable Z} {t: type} {tC: type}
        (e: @expr Z _ t)
        (C: @arg Z _ t -> @expr Z _ tC)
        (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 ->
              interp (C a1) = interp (C a2)) :
    interp (under_lets e C) = interp (C (@uninterp_arg t (interp e))).
  Proof.
    intros; apply under_lets_correct;
    [ assumption
    | rewrite interp_arg_uninterp_arg; reflexivity ].
  Qed.
End Output.

Section compile.
  Context {ivar : type -> Type}.
  Context {ovar : Type}.

  Fixpoint compile {t} (e:@Input.expr Z (@Output.arg Z ovar) t) : @Output.expr Z ovar t :=
    match e with
    | Input.ConstT n => Output.Return (Output.ConstT n)
    | Input.ConstN n => Output.Return (Output.ConstN n)
    | Input.Var _ arg => Output.Return arg
    | Input.Binop t1 t2 op e1 e2 =>
       Output.under_lets (@compile _ e1) (fun arg1 =>
          Output.under_lets (@compile _ e2) (fun arg2 =>
             Output.LetBinop op arg1 arg2 (fun v => Output.Return (Output.Var v))))
    | Input.Let _ ex _ eC =>
       Output.under_lets (@compile _ ex) (fun arg => @compile _ (eC arg))
    | Input.Pair _ e1 _ e2 =>
       Output.under_lets (@compile _ e1) (fun arg1 =>
          Output.under_lets (@compile _ e2) (fun arg2 =>
             Output.Return (Output.Pair arg1 arg2)))
    | Input.MatchPair _ _ ep _ eC =>
        Output.under_lets (@compile _ ep) (fun arg =>
          let (a1, a2) := Output.match_arg_Prod arg in @compile _ (eC a1 a2))
    end.
  End compile.

Definition Compile {t} (e:Input.Expr t) : Output.Expr t := fun var =>
  compile (e (@Output.arg Z var)).

Lemma compile_correct {_: Evaluable Z} {t} e1 e2 G (wf:Input.wf G e1 e2) :
  List.Forall (fun v => let 'existT _ (x, a) := v in Output.interp_arg a = x) G ->
    Output.interp (compile e2) = Input.interp e1 :> interp_type t.
Proof.
  induction wf;
    repeat match goal with
    | [HIn:In ?x ?l, HForall:Forall _ ?l |- _ ] =>
      (pose proof (proj1 (Forall_forall _ _) HForall _ HIn); clear HIn)
    | [ H : Output.match_arg_Prod _ = (_, _) |- _ ] =>
      apply Output.match_arg_Prod_correct in H
    | [ H : Output.Pair _ _ = Output.Pair _ _ |- _ ] =>
      apply Output.Pair_eq in H
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress subst
    | _ => progress specialize_by assumption
    | _ => progress break_match
    | _ => rewrite !Output.interp_under_lets
    | _ => rewrite !Output.interp_arg_uninterp_arg
    | _ => progress erewrite_hyp !*
    | _ => apply Forall_cons
    | _ => solve [intuition (congruence || eauto)]
    end.
Qed.

Lemma Compile_correct {_: Evaluable Z} {t} (E:Input.Expr t) (WfE:Input.Wf E) :
  Output.Interp (Compile E) = Input.Interp E. 
Proof. eapply compile_correct; eauto. Qed.

Import Input.

Section Curve25519.
  Local Infix ">>" := Z.shiftr.
  Local Infix "&" := (fun x y => Z.land x (Z.of_nat (Z.to_nat y))).
  Local Open Scope Z_scope.
  Require Import Crypto.Spec.ModularArithmetic.
  Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
  Require Import Crypto.Specific.GF25519.
  Require Import Crypto.Experiments.SpecEd25519.

  (* Computing the length first is necessary to make this run in tolerable time on 8.6 *)
  Definition twice_d' := Eval cbv [length params25519 ModularBaseSystemOpt.limb_widths_from_len ModularBaseSystem.encode ModularBaseSystemList.encode PseudoMersenneBaseParams.limb_widths] in ModularBaseSystem.encode(modulus:=q) (d + d)%F.
  Definition twice_d : fe25519 := Eval vm_compute in twice_d'.

  Definition ge25519_add' :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In twice_d] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ge25519_add_sig P Q : { r | r = ge25519_add' P Q }.
    (* python -c "print ('\n'.join('let \'(' + ', '.join('(' + ', '.join('%s_%s_%d'%(P,c,i) for i in range(10)) + ')' for c in 'XYZT') + ') := %s in'%P for P in 'PQ'))" *)
    refine (
let '((P_X_0, P_X_1, P_X_2, P_X_3, P_X_4, P_X_5, P_X_6, P_X_7, P_X_8, P_X_9), (P_Y_0, P_Y_1, P_Y_2, P_Y_3, P_Y_4, P_Y_5, P_Y_6, P_Y_7, P_Y_8, P_Y_9), (P_Z_0, P_Z_1, P_Z_2, P_Z_3, P_Z_4, P_Z_5, P_Z_6, P_Z_7, P_Z_8, P_Z_9), (P_T_0, P_T_1, P_T_2, P_T_3, P_T_4, P_T_5, P_T_6, P_T_7, P_T_8, P_T_9)) := P in
let '((Q_X_0, Q_X_1, Q_X_2, Q_X_3, Q_X_4, Q_X_5, Q_X_6, Q_X_7, Q_X_8, Q_X_9), (Q_Y_0, Q_Y_1, Q_Y_2, Q_Y_3, Q_Y_4, Q_Y_5, Q_Y_6, Q_Y_7, Q_Y_8, Q_Y_9), (Q_Z_0, Q_Z_1, Q_Z_2, Q_Z_3, Q_Z_4, Q_Z_5, Q_Z_6, Q_Z_7, Q_Z_8, Q_Z_9), (Q_T_0, Q_T_1, Q_T_2, Q_T_3, Q_T_4, Q_T_5, Q_T_6, Q_T_7, Q_T_8, Q_T_9)) := Q in
_).
    repeat match goal with
             [x:?T |- _] =>
             lazymatch T with
             | Z => fail
             | _ => clear x
             end
           end.

    eexists.
    cbv beta delta [ge25519_add'].
    
    Reify_rhs.
    (* Finished transaction in 14.664 secs (14.639u,0.026s) (successful) in coqc version Coq 8.6 from July 2016, slow interactively *)

    rewrite <-Compile_correct by admit_Wf.
    (* Finished transaction in 0.282 secs (0.283u,0.s) (successful), slow interactively *)

    let E := match goal with |- _ = Output.Interp ?E => E end in
    set (vm_E := E); vm_compute in vm_E; subst vm_E. 
    (* Finished transaction in 0.427 secs (0.423u,0.003s) (successful), very slow interactively *)

    cbv iota beta delta [Output.Interp Output.interp Output.interp_arg interp_binop interp_type].

    Set Printing Depth 999999.
    reflexivity.
  Defined.
End Curve25519.