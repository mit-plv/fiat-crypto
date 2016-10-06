Require Import Crypto.Assembly.PhoasCommon.

Module HL.
  Section Language.
    Context {T: Type}.
    Context {E: Evaluable T}.

    Section expr.
        Context {var : type -> Type}.

        Inductive expr : type -> Type :=
          | Const : @interp_type T TT -> expr TT
          | Var : forall {t}, var t -> expr t
          | Binop : forall {t1 t2 t3}, binop t1 t2 t3 -> expr t1 -> expr t2 -> expr t3
          | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
          | Pair : forall {t1}, expr t1 -> forall {t2}, expr t2 -> expr (Prod t1 t2)
          | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
    End expr.

    Local Notation ZConst z := (@Const Z ZEvaluable _ z%Z).

    Definition Expr t : Type := forall var, @expr var t.

    Fixpoint interp {t} (e: @expr interp_type t) : interp_type t :=
        match e in @expr _ t return interp_type t with
        | Const n => n
        | Var _ n => n
        | Binop _ _ _ op e1 e2 => interp_binop op (interp e1) (interp e2)
        | Let _ ex _ eC => let x := interp ex in interp (eC x)
        | Pair _ e1 _ e2 => (interp e1, interp e2)
        | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
        end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  Definition typeMap {A B t} (f: A -> B) (x: @interp_type A t): @interp_type B t.
  Proof.
    induction t; [refine (f x)|].
    destruct x as [x1 x2].
    refine (IHt1 x1, IHt2 x2).
  Defined.

  Definition zinterp {t} E := @interp Z ZEvaluable t E.

  Definition ZInterp {t} E := @Interp Z ZEvaluable t E.

  Definition wordInterp {n t} E := @interp (word n) (@WordEvaluable n) t E.

  Definition WordInterp {n t} E := @Interp (word n) (@WordEvaluable n) t E.

  Definition rangeInterp {n t} E: @interp_type (option (Range N)) t :=
    typeMap rangeEval (@interp (@WordRangeOpt n) (@WordRangeOptEvaluable n) t E).

  Definition RangeInterp {n t} E: @interp_type (option (Range N)) t :=
    typeMap rangeEval (@Interp (@WordRangeOpt n) (@WordRangeOptEvaluable n) t E).

  Example example_Expr : Expr TT := fun var => (
    Let (Const 7) (fun a =>
      Let (Let (Binop OPadd (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p =>
        MatchPair (Var p) (fun x y =>
          Binop OPadd (Var x) (Var y)))))%Z.

  Example interp_example_Expr : ZInterp example_Expr = 28%Z.
  Proof. reflexivity. Qed.

  (* Reification assumes the argument type is Z *)

  Ltac reify_type t :=
    lazymatch t with
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
    | Z.land   => constr:(OPand)
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
        constr:(@Const Z var x)
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
    | WfConst : forall G n, wf G (Const n) (Const n)
    | WfVar : forall G t x x', In (x ≡ x') G -> @wf G t (Var x) (Var x')
    | WfBinop : forall G {t1} {t2} {t3} (e1:Texpr var1 t1) (e2:Texpr var1 t2)
                  (e1':Texpr var2 t1) (e2':Texpr var2 t2)
                  (op: binop t1 t2 t3),
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

End HL.
