(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Definition runtime_mul := Z.mul.
Definition runtime_add := Z.add.
Delimit Scope runtime_scope with RT.
Infix "*" := runtime_mul : runtime_scope.
Infix "+" := runtime_add : runtime_scope.

Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right Z.add 0%Z (map (fun t => fst t * snd t) p).

  Lemma eval_nil : eval nil = 0.
  Proof. trivial.                                             Qed.
  Lemma eval_cons p q : eval (p::q) = fst p * snd p + eval q.
  Proof. trivial.                                             Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof. induction p; rewrite <-?List.app_comm_cons;
           rewrite ?eval_nil, ?eval_cons; nsatz.              Qed.

  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof. induction p; push; nsatz.                            Qed.
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', (snd t * snd t')%RT))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; cbv [mul]; push; nsatz.                 Qed.
  Hint Rewrite eval_mul : push_eval.

  Example base10_2digit_mul (a0:Z) (a1:Z) (b0:Z) (b1:Z) :
    {ab| eval ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)]}.
    eexists ?[ab].
    (* Goal: eval ?ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)] *)
    rewrite <-eval_mul.
    (* Goal: eval ?ab = eval (mul [(10,a1);(1,a0)] [(10,b1);(1,b0)]) *)
    cbv -[runtime_mul eval].
    (* Goal: eval ?ab = eval [(100,(a1*b1));(10,a1*b0);(10,a0*b1);(1,a0*b0)]%RT *)
    trivial.                                              Defined.

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Lemma eval_split s p (s_nz:s<>0) :
    eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
  Proof. cbv [split]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
  Hint Rewrite eval_reduce : push_eval.

  Section Carries.
    Context {modulo div : Z -> Z -> Z}.
    Context {div_mod : forall a b:Z, b <> 0 ->
                                     a = b * (div a b) + modulo a b}.

    Definition carryterm (w fw:Z) (t:Z * Z) :=
      if (Z.eqb (fst t) w)
      then dlet_nd t2 := snd t in
           dlet_nd d2 := div t2 fw in
           dlet_nd m2 := modulo t2 fw in
           [(w * fw, d2);(w,m2)]
      else [t].

    Lemma eval_carryterm w fw (t:Z * Z) (fw_nonzero:fw<>0):
      eval (carryterm w fw t) = eval [t].
    Proof using Type*.
      cbv [carryterm Let_In]; break_match; push; [|trivial].
      specialize (div_mod (snd t) fw fw_nonzero).
      rewrite Z.eqb_eq in *.
      nsatz.
    Qed. Hint Rewrite eval_carryterm using auto : push_eval.

    Definition carry (w fw:Z) (p:list (Z * Z)):=
      flat_map (carryterm w fw) p.

    Lemma eval_carry w fw p (fw_nonzero:fw<>0):
      eval (carry w fw p) = eval p.
    Proof using Type*. cbv [carry]; induction p; push; nsatz. Qed.
    Hint Rewrite eval_carry using auto : push_eval.
  End Carries.
End Associational.

Module Positional. Section Positional.
  Context (weight : nat -> Z)
          (weight_0 : weight 0%nat = 1)
          (weight_nz : forall i, weight i <> 0).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Lemma eval_to_associational n x :
    Associational.eval (@to_associational n x) = eval n x.
  Proof. trivial.                                             Qed.

  (* SKIP over this: zeros, add_to_nth *)
  Local Ltac push := autorewrite with push_eval push_map distr_length
    push_flat_map push_fold_right push_nth_default cancel_pair natsimplify.
  Definition zeros n : list Z
    := List.repeat 0 n.
  Lemma eval_zeros n : eval n (zeros n) = 0.
  Proof.
    cbv [eval Associational.eval to_associational zeros].
    rewrite <- (seq_length n 0) at 2.
    generalize dependent (List.seq 0 n); intro xs.
    induction xs; simpl; nsatz.                               Qed.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => runtime_add x y) ls.
  Lemma eval_add_to_nth (n:nat) (i:nat) (x:Z) (xs:list Z) (H:(i<length xs)%nat)
        (Hn : length xs = n) (* N.B. We really only need [i < Nat.min n (length xs)] *) :
    eval n (add_to_nth i x xs) = weight i * x + eval n xs.
  Proof.
    subst n.
    cbv [eval to_associational add_to_nth runtime_add].
    rewrite ListUtil.combine_update_nth_r at 1.
    rewrite <-(update_nth_id i (List.combine _ _)) at 2.
    rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _
      (weight 0, 0)) by (push; lia); cbv [ListUtil.splice_nth id].
    repeat match goal with
           | _ => progress push
           | _ => progress break_match
           | _ => progress (apply Zminus_eq; ring_simplify)
           | _ => rewrite <-ListUtil.map_nth_default_always
           end; lia.                                          Qed.
  Hint Rewrite @eval_add_to_nth eval_zeros : push_eval.

  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => (nat * Z)%type)
      ((O, fst t * snd t)%RT)
      (fun i' place_i'
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in (c * snd t)%RT)
          else place_i')
      i.

  Lemma place_in_range (t:Z*Z) (n:nat) : (fst (place t n) < S n)%nat.
  Proof. induction n; cbv [place nat_rect] in *; break_match; autorewrite with cancel_pair; try omega. Qed.
  Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
  Proof. induction i; cbv [place nat_rect] in *; break_match; push;
    repeat match goal with |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(auto) ltac:(auto))
           end; nsatz.                                        Qed.
  Hint Rewrite weight_place : push_eval.

  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      let p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Lemma eval_from_associational {n} p (n_nz:n<>O \/ p = nil) :
    eval n (from_associational n p) = Associational.eval p.
  Proof. destruct n_nz; [ induction p | subst p ];
  cbv [from_associational] in *; push; try
  pose proof place_in_range a (pred n); try omega; try nsatz;
  apply fold_right_invariant; cbv [zeros add_to_nth];
  intros; rewrite ?map_length, ?List.repeat_length, ?seq_length, ?length_update_nth;
  try omega.                                                  Qed.
  Hint Rewrite @eval_from_associational : push_eval.

  Section mulmod.
    Context (m:Z) (m_nz:m <> 0) (s:Z) (s_nz:s <> 0)
            (c:list (Z*Z)) (Hm:m = s - Associational.eval c).
    Definition mulmod (n:nat) (a b:list Z) : list Z
      := let a_a := to_associational n a in
         let b_a := to_associational n b in
         let ab_a := Associational.mul a_a b_a in
         let abm_a := Associational.reduce s c ab_a in
         from_associational n abm_a.
    Lemma eval_mulmod n (f g:list Z)
          (Hf : length f = n) (Hg : length g = n) :
      eval n (mulmod n f g) mod m = (eval n f * eval n g) mod m.
    Proof. cbv [mulmod]; rewrite Hm in *; push; trivial.
    destruct f, g; simpl in *; [ right; subst n | left; try omega.. ].
    clear; cbv -[Associational.reduce].
    induction c as [|?? IHc]; simpl; trivial.                 Qed.
  End mulmod.

  Section Carries.
    Context {modulo div: Z -> Z -> Z}.
    Context {div_mod : forall a b:Z, b <> 0 ->
                                     a = b * (div a b) + modulo a b}.

    Definition carry {n m} (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry modulo div (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Lemma eval_carry {n m} i p: (n <> 0%nat) -> (m <> 0%nat) ->
                              weight (S i) / weight i <> 0 ->
      eval m (carry (n:=n) (m:=m) i p) = eval n p.
    Proof.
      cbv [carry]; intros; push; [|tauto].
      rewrite @Associational.eval_carry by eauto.
      apply eval_to_associational.
    Qed. Hint Rewrite @eval_carry : push_eval.

    Definition carry_reduce {n} (s:Z) (c:list (Z * Z))
               (index:nat) (p : list Z) :=
      from_associational
        n (Associational.reduce
             s c (to_associational (S n) (@carry n (S n) index p))).

    Lemma eval_carry_reduce {n} s c index p :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (weight (S index) / weight index <> 0) ->
      eval n (@carry_reduce n s c index p) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof.
      cbv [carry_reduce]; intros; push; auto.
      rewrite eval_to_associational; push; auto.
    Qed. Hint Rewrite @eval_carry_reduce : push_eval.

    (* N.B. It is important to reverse [idxs] here, because fold_right is
      written such that the first terms in the list are actually used
      last in the computation. For example, running:

      `Eval cbv - [Z.add] in (fun a b c d => fold_right Z.add d [a;b;c]).`

      will produce [fun a b c d => (a + (b + (c + d)))].*)
    Definition chained_carries {n} s c p (idxs : list nat) :=
      fold_right (fun a b => @carry_reduce n s c a b) p (rev idxs).

    Lemma eval_chained_carries {n} s c p idxs :
      (s <> 0) -> (s - Associational.eval c <> 0) -> (n <> 0%nat) ->
      (forall i, In i idxs -> weight (S i) / weight i <> 0) ->
      eval n (@chained_carries n s c p idxs) mod (s - Associational.eval c)
      = eval n p mod (s - Associational.eval c).
    Proof using Type*.
      cbv [chained_carries]; intros; push.
      apply fold_right_invariant; [|intro; rewrite <-in_rev];
        destruct n; intros; push; auto.
    Qed. Hint Rewrite @eval_chained_carries : push_eval.

  End Carries.

End Positional. End Positional.

Module Compilers.
  Module type.
    Variant primitive := unit | Z | nat | bool.
    Inductive type := type_primitive (_:primitive) | prod (A B : type) | arrow (s d : type) | list (A : type).
    Module Export Coercions.
      Global Coercion type_primitive : primitive >-> type.
    End Coercions.

    Fixpoint interp (t : type)
      := match t with
         | unit => Datatypes.unit
         | prod A B => interp A * interp B
         | arrow A B => interp A -> interp B
         | list A => Datatypes.list (interp A)
         | nat => Datatypes.nat
         | type_primitive Z => BinInt.Z
         | bool => Datatypes.bool
         end%type.

    Ltac reify_primitive ty :=
      lazymatch eval cbv beta in ty with
      | Datatypes.unit => unit
      | Datatypes.nat => nat
      | Datatypes.bool => bool
      | BinInt.Z => Z
      end.

    Ltac reify ty :=
      lazymatch eval cbv beta in ty with
      | Datatypes.prod ?A ?B
        => let rA := reify A in
           let rB := reify B in
           constr:(prod rA rB)
      | ?A -> ?B
        => let rA := reify A in
           let rB := reify B in
           constr:(arrow rA rB)
      | Datatypes.list ?T
        => let rT := reify T in
           constr:(list rT)
      | type.interp ?T => T
      | _ => let rt := reify_primitive ty in
             constr:(type_primitive rt)
      end.

    Module Export Notations.
      Export Coercions.
      Delimit Scope ctype_scope with ctype.
      Bind Scope ctype_scope with type.
      Notation "()" := unit : ctype_scope.
      Notation "A * B" := (prod A B) : ctype_scope.
      Notation "A -> B" := (arrow A B) : ctype_scope.
      Notation type := type.
    End Notations.
  End type.
  Export type.Notations.

  Module Uncurried.
    Module expr.
      Inductive expr {ident : type -> type -> Type} {var : type -> Type} : type -> Type :=
      | Var {t} (v : var t) : expr t
      | TT : expr type.unit
      | AppIdent {s d} (idc : ident s d) (args : expr s) : expr d
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
      | Abs {s d} (f : var s -> expr d) : expr (s -> d).

      Module Export Notations.
        Bind Scope expr_scope with expr.
        Delimit Scope expr_scope with expr.

        Infix "@" := App : expr_scope.
        Infix "@@" := AppIdent : expr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
        Notation "( )" := TT : expr_scope.
        Notation "()" := TT : expr_scope.
        Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
      End Notations.

      Definition Expr {ident : type -> type -> Type} t := forall var, @expr ident var t.

      Section unexpr.
        Context {ident : type -> type -> Type}
                {var : type -> Type}.

        Fixpoint unexpr {t} (e : @expr ident (@expr ident var) t) : @expr ident var t
          := match e in expr t return expr t with
             | Var t v => v
             | TT => TT
             | AppIdent s d idc args => AppIdent idc (unexpr args)
             | App s d f x => App (unexpr f) (unexpr x)
             | Pair A B a b => Pair (unexpr a) (unexpr b)
             | Abs s d f => Abs (fun x => unexpr (f (Var x)))
             end.
      End unexpr.

      Section with_ident.
        Context {ident : type -> type -> Type}
                (interp_ident : forall s d, ident s d -> type.interp s -> type.interp d).

        Fixpoint interp {t} (e : @expr ident type.interp t) : type.interp t
          := match e with
             | Var t v => v
             | TT => tt
             | AppIdent s d idc args => interp_ident s d idc (@interp s args)
             | App s d f x => @interp _ f (@interp _ x)
             | Pair A B a b => (@interp A a, @interp B b)
             | Abs s d f => fun v => interp (f v)
             end.

        Definition Interp {t} (e : Expr t) := interp (e _).
      End with_ident.

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

      Module var_context.
        Inductive list {var : type -> Type} :=
        | nil
        | cons {t} (gallina_v : type.interp t) (v : var t) (ctx : list).
      End var_context.

      (* cf COQBUG(https://github.com/coq/coq/issues/5448) , COQBUG(https://github.com/coq/coq/issues/6315) , COQBUG(https://github.com/coq/coq/issues/6559) *)
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
      cannot handle get handled by specializing the code "template" to
      each particular application of that abstraction. In particular,
      type arguments (nat, Z, (λ _, nat), etc) get substituted into
      lambdas and treated as a integral part of primitive operations
      (such as [@List.app T], [@list_rect (λ _, nat)]).  During
      reification, we accumulate them in a right-associated tuple,
      using [tt] as the "nil" base case.  When we hit a λ or an
      identifier, we plug in the template parameters as necessary. *)
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

      Ltac reify_in_context ident reify_ident var term value_ctx template_ctx :=
        let reify_rec_gen term value_ctx template_ctx := reify_in_context ident reify_ident var term value_ctx template_ctx in
        let reify_rec term := reify_rec_gen term value_ctx template_ctx in
        let reify_rec_not_head term := reify_rec_gen term value_ctx tt in
        let mkAppIdent idc args
            := let rargs := reify_rec_not_head args in
               constr:(@AppIdent ident var _ _ idc rargs) in
        let do_reify_ident term else_tac
            := let term_is_primitive_const := is_primitive_const term in
               reify_ident
                 mkAppIdent
                 term_is_primitive_const
                 term
                 else_tac in
        (*let dummy := match goal with _ => idtac "reify_in_context: attempting to reify:" term end in*)
        lazymatch value_ctx with
        | context[@var_context.cons _ ?rT term ?v _]
          => constr:(@Var ident var rT v)
        | _
          =>
          lazymatch term with
          | match ?b with true => ?t | false => ?f end
            => let T := type of t in
               reify_rec (@bool_rect (fun _ => T) t f b)
          | match ?x with Datatypes.pair a b => ?f end
            => reify_rec (match Datatypes.fst x, Datatypes.snd x return _ with
                          | a, b => f
                          end)
          | let x := ?a in @?b x
            => let A := type of a in
               let B := lazymatch type of b with forall x, @?B x => B end in
               reify_rec (b a) (*(@Let_In A B a b)*)
          | Datatypes.pair ?x ?y
            => let rx := reify_rec x in
               let ry := reify_rec y in
               constr:(Pair (ident:=ident) (var:=var) rx ry)
          | tt
            => constr:(@TT ident var)
          | (fun x : ?T => ?f)
            =>
            let x_is_template_parameter := is_template_parameter T in
            lazymatch x_is_template_parameter with
            | true
              =>
              lazymatch template_ctx with
              | (?arg, ?template_ctx)
                => (* we pull a trick with [match] to plug in [arg] without running cbv β *)
                reify_rec_gen (match arg with x => f end) value_ctx template_ctx
              end
            | false
              =>
              let rT := type.reify T in
              let not_x := refresh x ltac:(fun n => fresh n) in
              let not_x2 := refresh not_x ltac:(fun n => fresh n) in
              let not_x3 := refresh not_x2 ltac:(fun n => fresh n) in
              (*let dummy := match goal with _ => idtac "reify_in_context: λ case:" term "using vars:" not_x not_x2 not_x3 end in*)
              let rf0 :=
                  constr:(
                    fun (x : T) (not_x : var rT)
                    => match f, @var_context.cons var rT x not_x value_ctx return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
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
                => constr:(@Abs ident var rT _ rf)
              | _
                => (* This will happen if the reified term still
              mentions the non-var variable.  By chance, [cbv delta]
              strips type casts, which are only places that I can
              think of where such dependency might remain.  However,
              if this does come up, having a distinctive error message
              is much more useful for debugging than the generic "no
              matching clause" *)
                let dummy := match goal with
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
                       constr:(App (ident:=ident) (var:=var) rf rx)
                  end
                | _
                  => let term := plug_template_ctx term template_ctx in
                     do_reify_ident
                       term
                       ltac:(fun _
                             => let dummy := match goal with
                                             | _ => fail 1 "Unrecognized term:" term
                                             end in
                                constr:(I : I))
                end)
          end
        end.
      Ltac reify ident reify_ident var term :=
        reify_in_context ident reify_ident var term (@var_context.nil var) tt.
      Ltac Reify ident reify_ident term :=
        constr:(fun var : type -> Type
                => ltac:(let r := reify ident reify_ident var term in
                         exact r)).
      Ltac Reify_rhs ident reify_ident interp_ident _ :=
        let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
        let R := Reify ident reify_ident RHS in
        transitivity (@Interp ident interp_ident _ R);
        [ | cbv beta iota delta [Interp interp interp_ident Let_In type.interp bool_rect];
            reflexivity ].

      Module for_reification.
        Module ident.
          Import type.
          Inductive ident : type -> type -> Set :=
          | primitive {t:type.primitive} (v : interp t) : ident () t
          | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
          | Nat_succ : ident nat nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident (T * T * bool) T
          | nat_rect {P} : ident (P * (nat * P -> P) * nat) P
          | pred : ident nat nat
          | List_seq : ident (nat * nat) (list nat)
          | List_repeat {A} : ident (A * nat) (list A)
          | List_combine {A B} : ident (list A * list B) (list (A * B))
          | List_map {A B} : ident ((A -> B) * list A) (list B)
          | List_flat_map {A B} : ident ((A -> list B) * list A) (list B)
          | List_partition {A} : ident ((A -> bool) * list A) (list A * list A)
          | List_app {A} : ident (list A * list A) (list A)
          | List_rev {A} : ident (list A) (list A)
          | List_fold_right {A B} : ident ((B * A -> A) * A * list B) A
          | List_update_nth {T} : ident (nat * (T -> T) * list T) (list T)
          | List_nth_default {T} : ident (T * list T * nat) T
          | Z_runtime_mul : ident (Z * Z) Z
          | Z_runtime_add : ident (Z * Z) Z
          | Z_add : ident (Z * Z) Z
          | Z_mul : ident (Z * Z) Z
          | Z_pow : ident (Z * Z) Z
          | Z_opp : ident Z Z
          | Z_div : ident (Z * Z) Z
          | Z_modulo : ident (Z * Z) Z
          | Z_eqb : ident (Z * Z) bool
          | Z_of_nat : ident nat Z.

          Notation curry0 f
            := (fun 'tt => f).
          Notation curry2 f
            := (fun '(a, b) => f a b).
          Notation curry3 f
            := (fun '(a, b, c) => f a b c).
          Notation uncurry2 f
            := (fun a b => f (a, b)).
          Notation curry3_1 f
            := (fun '(a, b, c) => f (uncurry2 a) b c).
          Notation curry3_2 f
            := (fun '(a, b, c) => f a (uncurry2 b) c).

          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := match idc in ident s d return type.interp s -> type.interp d with
               | primitive _ v => curry0 v
               | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
               | Nat_succ => Nat.succ
               | nil t => curry0 (@Datatypes.nil (type.interp t))
               | cons t => curry2 (@Datatypes.cons (type.interp t))
               | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
               | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
               | bool_rect T => curry3 (@Datatypes.bool_rect (fun _ => type.interp T))
               | nat_rect P => curry3_2 (@Datatypes.nat_rect (fun _ => type.interp P))
               | pred => Nat.pred
               | List_seq => curry2 List.seq
               | List_combine A B => curry2 (@List.combine (type.interp A) (type.interp B))
               | List_map A B => curry2 (@List.map (type.interp A) (type.interp B))
               | List_repeat A => curry2 (@List.repeat (type.interp A))
               | List_flat_map A B => curry2 (@List.flat_map (type.interp A) (type.interp B))
               | List_partition A => curry2 (@List.partition (type.interp A))
               | List_app A => curry2 (@List.app (type.interp A))
               | List_rev A => @List.rev (type.interp A)
               | List_fold_right A B => curry3_1 (@List.fold_right (type.interp A) (type.interp B))
               | List_update_nth T => curry3 (@update_nth (type.interp T))
               | List_nth_default T => curry3 (@List.nth_default (type.interp T))
               | Z_runtime_mul => curry2 runtime_mul
               | Z_runtime_add => curry2 runtime_add
               | Z_add => curry2 Z.add
               | Z_mul => curry2 Z.mul
               | Z_pow => curry2 Z.pow
               | Z_modulo => curry2 Z.modulo
               | Z_opp => Z.opp
               | Z_div => curry2 Z.div
               | Z_eqb => curry2 Z.eqb
               | Z_of_nat => Z.of_nat
               end.

          Ltac reify
               mkAppIdent
               term_is_primitive_const
               term
               else_tac :=
            (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
            lazymatch term with
            | Nat.succ ?x => mkAppIdent Nat_succ x
            | S ?x => mkAppIdent Nat_succ x
            | @Datatypes.nil ?T
              => let rT := type.reify T in
                 mkAppIdent (@ident.nil rT) tt
            | @Datatypes.cons ?T ?x ?xs
              => let rT := type.reify T in
                 mkAppIdent (@ident.cons rT) (x, xs)
            | @Datatypes.fst ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.fst rA rB) x
            | @Datatypes.snd ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.snd rA rB) x
            | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
              => let rT := type.reify T in
                 mkAppIdent (@ident.bool_rect rT) (Ptrue, Pfalse, b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT) (P0,
                                                  (fun pat : Datatypes.nat * T
                                                   => let '(n', Pn) := pat in PS),
                                                  n)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
              => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                 constr:(I : I)
            | Nat.pred ?x => mkAppIdent ident.pred x
            | List.seq ?x ?y  => mkAppIdent ident.List_seq (x, y)
            | @List.repeat ?A ?x ?y
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_repeat rA) (x, y)
            | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.Let_In rA rB) (x, f)
            | @LetIn.Let_In ?A ?B ?x ?f
              => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                 constr:(I : I)
            | @combine ?A ?B ?ls1 ?ls2
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_combine rA rB) (ls1, ls2)
            | @List.map ?A ?B ?f ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_map rA rB) (f, ls)
            | @List.flat_map ?A ?B ?f ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.List_flat_map rA rB) (f, ls)
            | @List.partition ?A ?f ?ls
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_partition rA) (f, ls)
            | @List.app ?A ?ls1 ?ls2
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_app rA) (ls1, ls2)
            | @List.rev ?A ?ls
              => let rA := type.reify A in
                 mkAppIdent (@ident.List_rev rA) ls
            | @List.fold_right ?A ?B (fun b a => ?f) ?a0 ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.List_fold_right rA rB) ((fun pat : B * A => let '(b, a) := pat in f), a0, ls)
            | @List.fold_right ?A ?B ?f ?a0 ?ls
              => let dummy := match goal with _ => fail 1 "List.fold_right function argument is not syntactically a function of two arguments:" f end in
                 constr:(I : I)
            | @update_nth ?T ?n ?f ?ls
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_update_nth rT) (n, f, ls)
            | @List.nth_default ?T ?d ?ls ?n
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
            | runtime_mul ?x ?y => mkAppIdent ident.Z_runtime_mul (x, y)
            | runtime_add ?x ?y => mkAppIdent ident.Z_runtime_add (x, y)
            | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
            | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
            | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
            | Z.opp ?x => mkAppIdent ident.Z_opp x
            | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
            | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
            | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
            | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
            | _
              => lazymatch term_is_primitive_const with
                 | true
                   =>
                   let assert_const := match goal with
                                       | _ => require_primitive_const term
                                       end in
                   let T := type of term in
                   let rT := type.reify_primitive T in
                   mkAppIdent (@ident.primitive rT term) tt
                 | false => else_tac ()
                 end
            end.

          Module List.
            Notation seq := List_seq.
            Notation repeat := List_repeat.
            Notation combine := List_combine.
            Notation map := List_map.
            Notation flat_map := List_flat_map.
            Notation partition := List_partition.
            Notation app := List_app.
            Notation rev := List_rev.
            Notation fold_right := List_fold_right.
            Notation update_nth := List_update_nth.
            Notation nth_default := List_nth_default.
          End List.

          Module Z.
            Notation runtime_mul := Z_runtime_mul.
            Notation runtime_add := Z_runtime_add.
            Notation add := Z_add.
            Notation mul := Z_mul.
            Notation pow := Z_pow.
            Notation opp := Z_opp.
            Notation div := Z_div.
            Notation modulo := Z_modulo.
            Notation eqb := Z_eqb.
            Notation of_nat := Z_of_nat.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
          End Nat.

          Module Export Notations.
            Notation ident := ident.
          End Notations.
        End ident.

        Module Notations.
          Include ident.Notations.
          Notation expr := (@expr ident).
          Notation Expr := (@Expr ident).
          Notation interp := (@interp ident (@ident.interp)).
          Notation Interp := (@Interp ident (@ident.interp)).

          (*Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.*)
          Notation "'expr_let' x := A 'in' b" := (AppIdent ident.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.
          Notation "[ ]" := (AppIdent ident.nil _) : expr_scope.
          Notation "x :: xs" := (AppIdent ident.cons (Pair x%expr xs%expr)) : expr_scope.
          Notation "x" := (AppIdent (ident.primitive x) _) (only printing, at level 9) : expr_scope.
          Notation "ls [[ n ]]"
            := (AppIdent ident.List.nth_default (_, ls, AppIdent (ident.primitive n%nat) _)%expr)
               : expr_scope.

          Module Reification.
            Ltac reify var term := expr.reify ident ident.reify var term.
            Ltac Reify term := expr.Reify ident ident.reify term.
            Ltac Reify_rhs _ :=
              expr.Reify_rhs ident ident.reify ident.interp ().
          End Reification.
          Include Reification.
        End Notations.
        Include Notations.
      End for_reification.

      Module Export default.
        Module ident.
          Import type.
          Inductive ident : type -> type -> Set :=
          | primitive {t : type.primitive} (v : interp t) : ident () t
          | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
          | Nat_succ : ident nat nat
          | nil {t} : ident () (list t)
          | cons {t} : ident (t * list t) (list t)
          | fst {A B} : ident (A * B) A
          | snd {A B} : ident (A * B) B
          | bool_rect {T} : ident (T * T * bool) T
          | nat_rect {P} : ident (P * (nat * P -> P) * nat) P
          | pred : ident nat nat
          | list_rect {A P} : ident (P * (A * list A * P -> P) * list A) P
          | List_nth_default {T} : ident (T * list T * nat) T
          | Z_runtime_mul : ident (Z * Z) Z
          | Z_runtime_add : ident (Z * Z) Z
          | Z_add : ident (Z * Z) Z
          | Z_mul : ident (Z * Z) Z
          | Z_pow : ident (Z * Z) Z
          | Z_opp : ident Z Z
          | Z_div : ident (Z * Z) Z
          | Z_modulo : ident (Z * Z) Z
          | Z_eqb : ident (Z * Z) bool
          | Z_of_nat : ident nat Z.

          Notation curry0 f
            := (fun 'tt => f).
          Notation curry2 f
            := (fun '(a, b) => f a b).
          Notation curry3 f
            := (fun '(a, b, c) => f a b c).
          Notation uncurry2 f
            := (fun a b => f (a, b)).
          Notation uncurry3 f
            := (fun a b c => f (a, b, c)).
          Notation curry3_23 f
            := (fun '(a, b, c) => f a (uncurry3 b) c).
          Notation curry3_2 f
            := (fun '(a, b, c) => f a (uncurry2 b) c).

          Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
            := match idc in ident s d return type.interp s -> type.interp d with
               | primitive _ v => curry0 v
               | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
               | Nat_succ => Nat.succ
               | nil t => curry0 (@Datatypes.nil (type.interp t))
               | cons t => curry2 (@Datatypes.cons (type.interp t))
               | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
               | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
               | bool_rect T => curry3 (@Datatypes.bool_rect (fun _ => type.interp T))
               | nat_rect P => curry3_2 (@Datatypes.nat_rect (fun _ => type.interp P))
               | pred => Nat.pred
               | list_rect A P => curry3_23 (@Datatypes.list_rect (type.interp A) (fun _ => type.interp P))
               | List_nth_default T => curry3 (@List.nth_default (type.interp T))
               | Z_runtime_mul => curry2 runtime_mul
               | Z_runtime_add => curry2 runtime_add
               | Z_add => curry2 Z.add
               | Z_mul => curry2 Z.mul
               | Z_pow => curry2 Z.pow
               | Z_modulo => curry2 Z.modulo
               | Z_opp => Z.opp
               | Z_div => curry2 Z.div
               | Z_eqb => curry2 Z.eqb
               | Z_of_nat => Z.of_nat
               end.

          Ltac reify
               mkAppIdent
               term_is_primitive_const
               term
               else_tac :=
            (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
            lazymatch term with
            | Nat.succ ?x => mkAppIdent Nat_succ x
            | S ?x => mkAppIdent Nat_succ x
            | @Datatypes.nil ?T
              => let rT := type.reify T in
                 mkAppIdent (@ident.nil rT) tt
            | @Datatypes.cons ?T ?x ?xs
              => let rT := type.reify T in
                 mkAppIdent (@ident.cons rT) (x, xs)
            | @Datatypes.fst ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.fst rA rB) x
            | @Datatypes.snd ?A ?B ?x
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.snd rA rB) x
            | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
              => let rT := type.reify T in
                 mkAppIdent (@ident.bool_rect rT) (Ptrue, Pfalse, b)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
              => let rT := type.reify T in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 mkAppIdent (@ident.nat_rect rT) (P0,
                                                  (fun pat : Datatypes.nat * T
                                                   => let '(n', Pn) := pat in PS),
                                                  n)
            | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
              => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                 constr:(I : I)
            | Nat.pred ?x => mkAppIdent ident.pred x
            | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
              => let rA := type.reify A in
                 let rB := type.reify B in
                 mkAppIdent (@ident.Let_In rA rB) (x, f)
            | @LetIn.Let_In ?A ?B ?x ?f
              => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                 constr:(I : I)
            | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil (fun x xs rec => ?Pcons) ?ls
              => let rA := type.reify A in
                 let rB := type.reify B in
                 let pat := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) *)
                 let pat' := fresh "pat" in (* fresh for COQBUG(https://github.com/coq/coq/issues/6562) (must also not overlap with [rec], but I think [fresh] handles that correctly, at least) *)
                 mkAppIdent (@ident.list_rect rA rB)
                            (Pnil,
                             (fun pat : A * Datatypes.list A * B
                              => let '(pat', rec) := pat in
                                 let '(x, xs) := pat' in
                                 Pcons),
                             ls)
            | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil ?Pcons ?ls
              => let dummy := match goal with _ => fail 1 "list_rect cons case is not syntactically a function of three arguments:" Pcons end in
                 constr:(I : I)
            | @List.nth_default ?T ?d ?ls ?n
              => let rT := type.reify T in
                 mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
            | runtime_mul ?x ?y => mkAppIdent ident.Z_runtime_mul (x, y)
            | runtime_add ?x ?y => mkAppIdent ident.Z_runtime_add (x, y)
            | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
            | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
            | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
            | Z.opp ?x => mkAppIdent ident.Z_opp x
            | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
            | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
            | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
            | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
            | _
              => lazymatch term_is_primitive_const with
                 | true
                   =>
                   let assert_const := match goal with
                                       | _ => require_primitive_const term
                                       end in
                   let T := type of term in
                   let rT := type.reify_primitive T in
                   mkAppIdent (@ident.primitive rT term) tt
                 | _ => else_tac ()
                 end
            end.

          Module List.
            Notation nth_default := List_nth_default.
          End List.

          Module Z.
            Notation runtime_mul := Z_runtime_mul.
            Notation runtime_add := Z_runtime_add.
            Notation add := Z_add.
            Notation mul := Z_mul.
            Notation pow := Z_pow.
            Notation opp := Z_opp.
            Notation div := Z_div.
            Notation modulo := Z_modulo.
            Notation eqb := Z_eqb.
            Notation of_nat := Z_of_nat.
          End Z.

          Module Nat.
            Notation succ := Nat_succ.
          End Nat.

          Module Export Notations.
            Notation ident := ident.
          End Notations.
        End ident.

        Module Notations.
          Include ident.Notations.
          Notation expr := (@expr ident).
          Notation Expr := (@Expr ident).
          Notation interp := (@interp ident (@ident.interp)).
          Notation Interp := (@Interp ident (@ident.interp)).

          (*Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.*)
          Notation "'expr_let' x := A 'in' b" := (AppIdent ident.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.
          Notation "[ ]" := (AppIdent ident.nil _) : expr_scope.
          Notation "x :: xs" := (AppIdent ident.cons (Pair x%expr xs%expr)) : expr_scope.
          Notation "x" := (AppIdent (ident.primitive x) _) (only printing, at level 9) : expr_scope.
          Notation "ls [[ n ]]"
            := (AppIdent ident.List.nth_default (_, ls, AppIdent (ident.primitive n%nat) _)%expr)
               : expr_scope.

          Ltac reify var term := expr.reify ident ident.reify var term.
          Ltac Reify term := expr.Reify ident ident.reify term.
          Ltac Reify_rhs _ :=
            expr.Reify_rhs ident ident.reify ident.interp ().
        End Notations.
        Include Notations.
      End default.
    End expr.

    Module canonicalize_list_recursion.
      Import expr.
      Import expr.default.
      Module ident.
        Local Ltac SmartApp term :=
          lazymatch term with
          | Abs (fun x : @expr ?var ?T => ?f)
            => eval cbv [unexpr] in (fun x : @expr var T => @unexpr ident.ident var _ f)
          | Abs (fun x : ?T => ?f)
            => let dummy := match goal with _ => fail 1 "Invalid var type:" T end in
               constr:(I : I)
          end.

        Definition transfer {var} {s d} (idc : for_reification.ident s d) : @expr var s -> @expr var d
          := let List_app A :=
                 list_rect
                   (fun _ => list (type.interp A) -> list (type.interp A))
                   (fun m => m)
                   (fun a l1 app_l1 m => a :: app_l1 m) in
             match idc in for_reification.ident s d return @expr var s -> @expr var d with
             | for_reification.ident.Let_In tx tC
               => AppIdent ident.Let_In
             | for_reification.ident.Nat_succ
               => AppIdent ident.Nat_succ
             | for_reification.ident.nil t
               => AppIdent ident.nil
             | for_reification.ident.cons t
               => AppIdent ident.cons
             | for_reification.ident.fst A B
               => AppIdent ident.fst
             | for_reification.ident.snd A B
               => AppIdent ident.snd
             | for_reification.ident.bool_rect T
               => AppIdent ident.bool_rect
             | for_reification.ident.nat_rect P
               => AppIdent ident.nat_rect
             | for_reification.ident.pred
               => AppIdent ident.pred
             | for_reification.ident.primitive t v
               => AppIdent (ident.primitive v)
             | for_reification.ident.Z_runtime_mul
               => AppIdent ident.Z.runtime_mul
             | for_reification.ident.Z_runtime_add
               => AppIdent ident.Z.runtime_add
             | for_reification.ident.Z_add
               => AppIdent ident.Z.add
             | for_reification.ident.Z_mul
               => AppIdent ident.Z.mul
             | for_reification.ident.Z_pow
               => AppIdent ident.Z.pow
             | for_reification.ident.Z_opp
               => AppIdent ident.Z.opp
             | for_reification.ident.Z_div
               => AppIdent ident.Z.div
             | for_reification.ident.Z_modulo
               => AppIdent ident.Z.modulo
             | for_reification.ident.Z_eqb
               => AppIdent ident.Z.eqb
             | for_reification.ident.Z_of_nat
               => AppIdent ident.Z.of_nat
             | for_reification.ident.List_seq
               => ltac:(
                    let v
                        :=
                        reify
                          (@expr var)
                          (fun start_len : nat * nat
                           => nat_rect
                                (fun _ => nat -> list nat)
                                (fun _ => nil)
                                (fun len seq_len start => cons start (seq_len (S start)))
                                (snd start_len) (fst start_len)) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_repeat A
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun (xn : type.interp A * nat)
                                => nat_rect
                                     (fun _ => list (type.interp A))
                                     nil
                                     (fun k repeat_k => cons (fst xn) repeat_k)
                                     (snd xn)) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_combine A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((ls1, ls2) : list (type.interp A) * list (type.interp B))
                                => list_rect
                                     (fun _ => list (type.interp B) -> list (type.interp A * type.interp B))
                                     (fun l' => nil)
                                     (fun x tl combine_tl rest
                                      => list_rect
                                           (fun _ => list (type.interp A * type.interp B))
                                           nil
                                           (fun y tl' _
                                            => (x, y) :: combine_tl tl')
                                           rest)
                                     ls1
                                     ls2) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_map A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> type.interp B) * Datatypes.list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp B))
                                     nil
                                     (fun a t map_t => f a :: map_t)
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_flat_map A B
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app B)) in
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> list (type.interp B)) * list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp B))
                                     nil
                                     (fun x t flat_map_t => List_app (f x) flat_map_t)
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_partition A
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, ls) : (type.interp A -> bool) * list (type.interp A))
                                => list_rect
                                     (fun _ => list (type.interp A) * list (type.interp A))%type
                                     (nil, nil)
                                     (fun x tl partition_tl
                                      => let g := fst partition_tl in
                                         let d := snd partition_tl in
                                         if f x then (x :: g, d) else (g, x :: d))
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_app A
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app A)) in
                    let v := reify (@expr var) (fun '(ls1, ls2) => List_app ls1 ls2) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_rev A
               => ltac:(
                    let List_app := (eval cbv [List_app] in (List_app A)) in
                    let v := reify
                               (@expr var)
                               (fun ls
                                => list_rect
                                     (fun _ => list (type.interp A))
                                     nil
                                     (fun x l' rev_l' => List_app rev_l' [x])
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_fold_right A B
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((f, a0, ls)
                                      : (type.interp B * type.interp A -> type.interp A) * type.interp A * list (type.interp B))
                                => list_rect
                                     (fun _ => type.interp A)
                                     a0
                                     (fun b t fold_right_t => f (b, fold_right_t))
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_update_nth T
               => ltac:(
                    let v := reify
                               (@expr var)
                               (fun '((n, f, ls) : nat * (type.interp T -> type.interp T) * list (type.interp T))
                                => nat_rect
                                     (fun _ => list (type.interp T) -> list (type.interp T))
                                     (fun ls
                                      => list_rect
                                           (fun _ => list (type.interp T))
                                           nil
                                           (fun x' xs' __ => f x' :: xs')
                                           ls)
                                     (fun n' update_nth_n' ls
                                      => list_rect
                                           (fun _ => list (type.interp T))
                                           nil
                                           (fun x' xs' __ => x' :: update_nth_n' xs')
                                           ls)
                                     n
                                     ls) in
                    let v := SmartApp v in exact v)
             | for_reification.ident.List_nth_default T
               => AppIdent ident.List_nth_default
             (*ltac:(
                  let v := reify
                             var
                             (fun (default : type.interp T) (l : list (type.interp T)) (n : nat)
                              => nat_rect
                                   (fun _ => list (type.interp T) -> type.interp T)
                                   (list_rect
                                      (fun _ => type.interp T)
                                      default
                                      (fun x __ __ => x))
                                   (fun n nth_error_n
                                    => list_rect
                                         (fun _ => type.interp T)
                                         default
                                         (fun __ l __ => nth_error_n l))
                                   n
                                   l) in
                  exact v)*)
             end%expr.
      End ident.

      Module expr.
        Section with_var.
          Context {var : type -> Type}.

          Fixpoint transfer {t} (e : @for_reification.Notations.expr var t)
            : @expr var t
            := match e  with
               | Var t v => Var v
               | TT => TT
               | Pair A B a b => Pair (@transfer A a) (@transfer B b)
               | AppIdent s d idc args => @ident.transfer var s d idc (@transfer _ args)
               | App s d f x => App (@transfer _ f) (@transfer _ x)
               | Abs s d f => Abs (fun x => @transfer d (f x))
               end.
        End with_var.

        Definition Transfer {t} (e : for_reification.Notations.Expr t) : Expr t
          := fun var => transfer (e _).
      End expr.
    End canonicalize_list_recursion.
    Notation canonicalize_list_recursion := canonicalize_list_recursion.expr.Transfer.
    Export expr.
    Export expr.default.
  End Uncurried.

  Module CPS.
    Import Uncurried.
    Module Import Output.
      Module type.
        Import Compilers.type.
        Inductive type := type_primitive (_:primitive) | prod (A B : type) | continuation (A : type) | list (A : type).
        Module Export Coercions.
          Global Coercion type_primitive : primitive >-> type.
        End Coercions.

        Module Export Notations.
          Export Coercions.
          Delimit Scope cpstype_scope with cpstype.
          Bind Scope cpstype_scope with type.
          Notation "()" := unit : cpstype_scope.
          Notation "A * B" := (prod A B) : cpstype_scope.
          Notation "A --->" := (continuation A) : cpstype_scope.
          Notation type := type.
        End Notations.

        Section interp.
          Context (R : Type).
          Fixpoint interp (t : type)
            := match t return Type with
               | type_primitive t => Compilers.type.interp t
               | prod A B => interp A * interp B
               | continuation A => interp A -> R
               | list A => Datatypes.list (interp A)
               end%type.
        End interp.
      End type.
      Export type.Notations.

      Module expr.
        Section expr.
          Context {ident : type -> Type} {var : type -> Type} {R : type}.

          Inductive expr :=
          | Halt (v : var R)
          | App {A} (f : var (A --->)) (x : var A)
          | Bind {A} (x : primop A) (f : var A -> expr)
          with
          primop : type -> Type :=
          | Var {t} (v : var t) : primop t
          | Abs {t} (f : var t -> expr) : primop (t --->)
          | Pair {A B} (x : var A) (y : var B) : primop (A * B)
          | Fst {A B} (x : var (A * B)) : primop A
          | Snd {A B} (x : var (A * B)) : primop B
          | TT : primop ()
          | Ident {t} (idc : ident t) : primop t.
        End expr.
        Global Arguments expr {ident var} R.
        Global Arguments primop {ident var} R _.

        Definition Expr {ident : type -> Type} R := forall var, @expr ident var R.

        Section with_ident.
          Context {ident : type -> Type}
                  (r : type)
                  (R : Type)
                  (interp_ident
                   : forall t, ident t -> type.interp R t).

          Fixpoint interp (e : @expr ident (type.interp R) r) (k : type.interp R r -> R)
                   {struct e}
            : R
            := match e with
               | Halt v => k v
               | App A f x => f x
               | Bind A x f => interp (f (@interp_primop _ x k)) k
               end
          with interp_primop {t} (e : @primop ident (type.interp R) r t) (k : type.interp R r -> R)
                             {struct e}
               : type.interp R t
               := match e with
                  | Var t v => v
                  | Abs t f => fun x : type.interp _ t => interp (f x) k
                  | Pair A B x y => (x, y)
                  | Fst A B x => fst x
                  | Snd A B x => snd x
                  | TT => tt
                  | Ident t idc => interp_ident t idc
                  end.

          Definition Interp (e : Expr r) (k : type.interp R r -> R) : R := interp (e _) k.
        End with_ident.

        Module Export Notations.
          Delimit Scope cpsexpr_scope with cpsexpr.
          Bind Scope cpsexpr_scope with expr.
          Bind Scope cpsexpr_scope with primop.

          Infix "@" := App : cpsexpr_scope.
          Notation "v <- x ; f" := (Bind x (fun v => f)) : cpsexpr_scope.
          Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%cpsexpr)) ..)) : cpsexpr_scope.
          Notation "( x , y , .. , z )" := (Pair .. (Pair x%cpsexpr y%cpsexpr) .. z%cpsexpr) : cpsexpr_scope.
        Notation "( )" := TT : cpsexpr_scope.
        Notation "()" := TT : cpsexpr_scope.
        End Notations.
      End expr.
      Export expr.Notations.
    End Output.

    Module type.
      Section translate.
        Fixpoint translate (t : Compilers.type.type) : type
          := match t with
             | A * B => (translate A * translate B)%cpstype
             | s -> d => (translate s * (translate d --->) --->)%cpstype
             | Compilers.type.list A => type.list (translate A)
             | Compilers.type.type_primitive t
               => t
             end%ctype.
        Fixpoint untranslate (R : Compilers.type.type) (t : type)
          : Compilers.type.type
          := match t with
             | type.type_primitive t => t
             | A * B => (untranslate R A * untranslate R B)%ctype
             | (t --->)
               => (untranslate R t -> R)%ctype
             | type.list A => Compilers.type.list (untranslate R A)
             end%cpstype.
      End translate.
    End type.

    Module expr.
      Import Output.expr.
      Import Output.expr.Notations.
      Import Compilers.type.
      Import Compilers.Uncurried.expr.
      Section with_ident.
        Context {ident : Output.type.type -> Type}
                {ident' : type -> type -> Type}
                {var : Output.type.type -> Type}
                (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d))).
        Notation var' := (fun t => var (type.translate t)).
        Local Notation oexpr := (@Output.expr.expr ident var).

        Section splice.
          Context {r1 r2 : Output.type.type}.
          Fixpoint splice  (e1 : oexpr r1) (e2 : var r1 -> oexpr r2)
                   {struct e1}
            : oexpr r2
            := match e1 with
               | Halt v => e2 v
               | f @ x => f @ x
               | Bind A x f => v <- @splice_primop _ x e2; @splice (f v) e2
               end%cpsexpr
          with
          splice_primop {t} (f : @primop ident var r1 t) (e2 : var r1 -> oexpr r2)
                        {struct f}
          : @primop ident var r2 t
          := match f with
             | Output.expr.Var t v => Output.expr.Var v
             | Output.expr.Pair A B x y as e => Output.expr.Pair x y
             | Output.expr.Fst A B x => Output.expr.Fst x
             | Output.expr.Snd A B x => Output.expr.Snd x
             | Output.expr.TT => Output.expr.TT
             | Output.expr.Ident t idc => Output.expr.Ident idc
             | Output.expr.Abs t f
               => Output.expr.Abs (fun x => @splice (f x) e2)
             end.
        End splice.

        Local Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

        Fixpoint translate {t}
                 (e : @Compilers.Uncurried.expr.expr ident' var' t)
          : @Output.expr.expr ident var (type.translate t)
          := match e with
             | Var t v => Halt v
             | TT => x <- () ; Halt x
             | AppIdent s d idc args
               => (args' <-- @translate _ args;
                     k <- Output.expr.Abs (fun r => Halt r);
                     p <- (args', k);
                     f <- Output.expr.Ident (translate_ident s d idc);
                     f @ p)
             | Pair A B a b
               => (a' <-- @translate _ a;
                     b' <-- @translate _ b;
                     p <- (a', b');
                     Halt p)
             | App s d e1 e2
               => (f <-- @translate _ e1;
                     x <-- @translate _ e2;
                     k <- Output.expr.Abs (fun r => Halt r);
                     p <- (x, k);
                     f @ p)
             | Abs s d f
               => f <- (Output.expr.Abs
                          (fun p
                           => x <- Fst p;
                                k <- Snd p;
                                r <-- @translate _ (f x);
                                k @ r));
                    Halt f
             end%cpsexpr.
      End with_ident.

      Definition Translate
                 {ident : Output.type.type -> Type}
                 {ident' : type -> type -> Type}
                 (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d)))
                 {t} (e : @Compilers.Uncurried.expr.Expr ident' t)
        : @Output.expr.Expr ident (type.translate t)
        := fun var => translate translate_ident (e _).

      Section call_with_cont.
        Context {ident' : Output.type.type -> Type}
                {ident : type -> type -> Type}
                {var : type -> Type}
                {r : Output.type.type}
                {R : type}.
        Notation ucexpr := (@Compilers.Uncurried.expr.expr ident var).
        Notation ucexprut t := (ucexpr (type.untranslate R t)) (only parsing).
        Notation var' := (fun t => ucexprut t).
        Context (untranslate_ident : forall t, ident' t -> ucexprut t)
                (ifst : forall A B, ident (A * B)%ctype A)
                (isnd : forall A B, ident (A * B)%ctype B).

        Fixpoint call_with_continuation
                 (e : @Output.expr.expr ident' var' r)
                 (k : ucexprut r -> ucexpr R)
                 {struct e}
          : ucexpr R
          := match e with
             | Halt v => k v
             | expr.App A f x
               => @App _ _ (type.untranslate R A) R
                       f x
             | Bind A x f
               => @call_with_continuation
                    (f (@call_primop_with_continuation A x k))
                    k
             end%expr
        with
        call_primop_with_continuation
          {t}
          (e : @Output.expr.primop ident' var' r t)
          (k : ucexprut r -> ucexpr R)
          {struct e}
        : ucexprut t
        := match e in Output.expr.primop _ t return ucexprut t with
           | expr.Var t v => v
           | expr.Abs t f => Abs (fun x : var (type.untranslate _ _)
                                  => @call_with_continuation
                                       (f (Var x)) k)
           | expr.Pair A B x y => (x, y)
           | Fst A B x => ifst (type.untranslate _ A) (type.untranslate _ B)
                               @@ x
           | Snd A B x => isnd (type.untranslate _ A) (type.untranslate _ B)
                               @@ x
           | expr.TT => TT
           | Ident t idc => untranslate_ident t idc
           end%expr.
      End call_with_cont.

      Definition CallWithContinuation
                 {ident' : Output.type.type -> Type}
                 {ident : type -> type -> Type}
                 {R : type}
                 (untranslate_ident : forall t, ident' t -> @Compilers.Uncurried.expr.Expr ident (type.untranslate R t))
                 (ifst : forall A B, ident (A * B)%ctype A)
                 (isnd : forall A B, ident (A * B)%ctype B)
                 {t} (e : @Output.expr.Expr ident' t)
                 (k : forall var, @Uncurried.expr.expr ident var (type.untranslate R t) -> @Uncurried.expr.expr ident var R)
        : @Compilers.Uncurried.expr.Expr ident R
        := fun var => call_with_continuation
                        (fun t idc => untranslate_ident t idc _) ifst isnd (e _) (k _).
    End expr.

    Module ident.
      Import CPS.Output.type.
      Inductive ident : type -> Set :=
      | wrap {s d} (idc : Uncurried.expr.default.ident s d) : ident (type.translate (s -> d)).

      Notation cps_of f
        := (fun x k => k (f x)).
      Notation curry0 f
        := (fun 'tt => f).
      Notation curry2 f
        := (fun '(a, b) => f a b).
      Notation curry3 f
        := (fun '(a, b, c) => f a b c).
      Notation uncurry2 f
        := (fun a b => f (a, b)).
      Notation uncurry3 f
        := (fun a b c => f (a, b, c)).
      Notation curry3_23 f
        := (fun '(a, b, c) => f a (uncurry3 b) c).
      Notation curry3_2 f
        := (fun '(a, b, c) => f a (uncurry2 b) c).

      Definition interp {R} {t} (idc : ident t) : type.interp R t
        := match idc in ident t return type.interp R t with
           | wrap s d idc
             => fun '((x, k) : type.interp R (type.translate s) * (type.interp R (type.translate d) -> R))
                =>
                  match idc in Uncurried.expr.default.ident s d return type.interp R (type.translate s) -> (type.interp R (type.translate d) -> R) -> R with
                  | ident.primitive _ _ as idc
                  | ident.Nat_succ as idc
                  | ident.pred as idc
                  | ident.Z_runtime_mul as idc
                  | ident.Z_runtime_add as idc
                  | ident.Z_add as idc
                  | ident.Z_mul as idc
                  | ident.Z_pow as idc
                  | ident.Z_opp as idc
                  | ident.Z_div as idc
                  | ident.Z_modulo as idc
                  | ident.Z_eqb as idc
                  | ident.Z_of_nat as idc
                    => cps_of (Uncurried.expr.default.ident.interp idc)
                  | ident.Let_In tx tC
                    => fun '((x, f) : (interp R (type.translate tx)
                                       * (interp R (type.translate tx) * (interp R (type.translate tC) -> R) -> R)))
                           (k : interp R (type.translate tC) -> R)
                       => @LetIn.Let_In
                            (type.interp R (type.translate tx)) (fun _ => R)
                            x
                            (fun v => f (v, k))
                  | ident.nil t
                    => cps_of (curry0 (@Datatypes.nil (interp R (type.translate t))))
                  | ident.cons t
                    => cps_of (curry2 (@Datatypes.cons (interp R (type.translate t))))
                  | ident.fst A B
                    => cps_of (@Datatypes.fst (interp R (type.translate A)) (interp R (type.translate B)))
                  | ident.snd A B
                    => cps_of (@Datatypes.snd (interp R (type.translate A)) (interp R (type.translate B)))
                  | ident.bool_rect T
                    => fun '((tc, fc, b) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) type.interp R (type.translate T) * type.interp R (type.translate T) * bool)
                           k
                       => @Datatypes.bool_rect
                            (fun _ => R)
                            (k tc)
                            (k fc)
                            b
                  | ident.nat_rect P
                    => fun '((PO, PS, n) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) interp R (type.translate P) * (nat * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * nat)
                           k
                       => @Datatypes.nat_rect
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => k PO)
                            (fun n' rec k
                             => rec (fun rec => PS (n', rec, k)))
                            n
                            k
                  | ident.list_rect A P
                    => fun '((Pnil, Pcons, ls) :
                               (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) interp R (type.translate P) * (interp R (type.translate A) * Datatypes.list (interp R (type.translate A)) * interp R (type.translate P) * (interp R (type.translate P) -> R) -> R) * Datatypes.list (interp R (type.translate A)))
                           k
                       => @Datatypes.list_rect
                            (interp R (type.translate A))
                            (fun _ => (interp R (type.translate P) -> R) -> R)
                            (fun k => k Pnil)
                            (fun x xs rec k
                             => rec (fun rec => Pcons (x, xs, rec, k)))
                            ls
                            k
                  | ident.List_nth_default T
                    => cps_of (curry3 (@List.nth_default (interp R (type.translate T))))
                  end x k
           end.

      Local Notation var_eta x := (ident.fst @@ x, ident.snd @@ x)%core%expr.

      Definition untranslate {R} {t} (idc : ident t)
        : @Compilers.Uncurried.expr.Expr Uncurried.expr.default.ident (type.untranslate R t)
        := fun var
           => match idc in ident t return Compilers.Uncurried.expr.expr (type.untranslate _ t) with
              | wrap s d idc
                =>
                match idc in default.ident s d return Compilers.Uncurried.expr.expr (type.untranslate _ (type.translate (s -> d))) with
                | ident.primitive t v
                  => λ (_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (() * (t -> R))%ctype) ,
                     (ident.snd @@ (Var _k))
                       @ (ident.primitive v @@ TT)
                | ident.Let_In tx tC
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tC) -> R) -> R) * (type.untranslate _ (type.translate tC) -> R))%ctype) ,
                     ident.Let_In
                       @@ (ident.fst @@ (ident.fst @@ (Var xyk)),
                           (λ (x :
                                 (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate tx))) ,
                            (ident.snd @@ (ident.fst @@ (Var xyk)))
                              @ (Var x, ident.snd @@ Var xyk)))
                | ident.nat_rect P
                  => λ (PO_PS_n_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate P) * (type.nat * type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate P) -> R) -> R) * type.nat * (type.untranslate _ (type.translate P) -> R))%ctype) ,
                     let (PO_PS_n, k) := var_eta (Var PO_PS_n_k) in
                     let (PO_PS, n) := var_eta PO_PS_n in
                     let (PO, PS) := var_eta PO_PS in
                     ((@ident.nat_rect ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ k , Var k @ PO),
                            (λ n'rec k ,
                             let (n', rec) := var_eta (Var n'rec) in
                             rec @ (λ rec , PS @ (n', Var rec, Var k))),
                            n))
                       @ k
                | ident.list_rect A P
                  => λ (Pnil_Pcons_ls_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate A) * Compilers.type.list (type.untranslate _ (type.translate A)) * type.untranslate _ (type.translate P) * (type.untranslate _ (type.translate P) -> R) -> R) * Compilers.type.list (type.untranslate _ (type.translate A)) * (type.untranslate _ (type.translate P) -> R))%ctype) ,
                     let (Pnil_Pcons_ls, k) := var_eta (Var Pnil_Pcons_ls_k) in
                     let (Pnil_Pcons, ls) := var_eta Pnil_Pcons_ls in
                     let (Pnil, Pcons) := var_eta Pnil_Pcons in
                     ((@ident.list_rect
                         (type.untranslate _ (type.translate A))
                         ((type.untranslate _ (type.translate P) -> R) -> R))
                        @@ ((λ k, Var k @ Pnil),
                            (λ x_xs_rec k,
                             let (x_xs, rec) := var_eta (Var x_xs_rec) in
                             let (x, xs) := var_eta x_xs in
                             rec @ (λ rec , Pcons @ (x, xs, Var rec, Var k))),
                            ls))
                       @ k
                | ident.List_nth_default T
                  => λ (xyzk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate T) * Compilers.type.list (type.untranslate _ (type.translate T)) * type.nat * (type.untranslate _ (type.translate T) -> R))%ctype) ,
                     (ident.snd @@ Var xyzk)
                       @ (ident.List_nth_default @@ (ident.fst @@ Var xyzk))
                | ident.bool_rect T
                  => λ (xyzk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate T) * type.untranslate _ (type.translate T) * type.bool * (type.untranslate _ (type.translate T) -> R))%ctype) ,
                     ident.bool_rect
                       @@ ((ident.snd @@ (Var xyzk))
                             @ (ident.fst @@ (ident.fst @@ (ident.fst @@ (Var xyzk)))),
                           (ident.snd @@ (Var xyzk))
                             @ (ident.snd @@ (ident.fst @@ (ident.fst @@ (Var xyzk)))),
                           ident.snd @@ (ident.fst @@ (Var xyzk)))
                | ident.nil t
                  => λ (_k :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (() * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                     (ident.snd @@ (Var _k))
                       @ (ident.nil @@ TT)
                | ident.cons t
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate t) * Compilers.type.list (type.untranslate _ (type.translate t)) * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ (ident.cons
                            @@ (ident.fst @@ (Var xyk)))
                | ident.fst A B
                  => λ (xk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate A) -> R))%ctype) ,
                     (ident.snd @@ (Var xk))
                       @ (ident.fst
                            @@ (ident.fst @@ (Var xk)))
                | ident.snd A B
                  => λ (xk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate B) -> R))%ctype) ,
                     (ident.snd @@ (Var xk))
                       @ (ident.snd
                            @@ (ident.fst @@ (Var xk)))
                | ident.Nat_succ as idc
                | ident.pred as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.nat * (type.nat -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.nat)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_opp as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_runtime_mul as idc
                | ident.Z_runtime_add as idc
                | ident.Z_add as idc
                | ident.Z_mul as idc
                | ident.Z_pow as idc
                | ident.Z_div as idc
                | ident.Z_modulo as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_eqb as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.Z * type.Z * (type.bool -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.bool)
                            @@ (ident.fst @@ (Var xyk)))
                | ident.Z_of_nat as idc
                  => λ (xyk :
                          (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (type.nat * (type.Z -> R))%ctype) ,
                     (ident.snd @@ (Var xyk))
                       @ ((idc : default.ident _ type.Z)
                            @@ (ident.fst @@ (Var xyk)))
                end%expr
              end.
    End ident.
    Notation ident := ident.ident.

    Module default.
      Notation expr := (@Output.expr.expr ident).
      Notation Expr := (@Output.expr.Expr ident).

      Definition Translate
                 {t} (e : @Compilers.Uncurried.expr.default.Expr t)
        : Expr (type.translate t)
        := expr.Translate (@ident.wrap) e.

      Definition call_with_continuation
                 {var}
                 {R : Compilers.type.type}
                 {t} (e : @expr _ t)
                 (k : @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.expr var R
        := expr.call_with_continuation (fun t idc => @ident.untranslate _ t idc _) (@ident.fst) (@ident.snd) e k.

      Definition CallWithContinuation
                 {R : Compilers.type.type}
                 {t} (e : Expr t)
                 (k : forall var, @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
        : @Compilers.Uncurried.expr.default.Expr R
        := expr.CallWithContinuation (@ident.untranslate _) (@ident.fst) (@ident.snd) e k.

      Definition CallFunWithIdContinuation'
                 {R}
                 {s d} (e : Expr (type.translate (s -> d)))
                 (k : forall var, var (type.untranslate R (type.translate d)) -> var R)
        : @Compilers.Uncurried.expr.default.Expr (type.untranslate R (type.translate s) -> R)
        := fun var
           => Abs (fun x => @call_with_continuation
                              var R _ (e _)
                              (fun e : expr.default.expr (type.untranslate _ (type.translate s) * (type.untranslate _ (type.translate d) -> _) -> _)
                               => e @ (Var x, λ v , Var (k _ v)))%expr).
      Notation CallFunWithIdContinuation e
        := (@CallFunWithIdContinuation'
              ((fun s d (e' : Expr (type.translate (s -> d))) => d) _ _ e)
              _ _
              e
              (fun _ => id))
             (only parsing).
    End default.
    Include default.
  End CPS.

  Import Uncurried.
  Section invert.
    Context {var : type -> Type}.

    Definition invert_Var {t} (e : @expr var t) : option (var t)
      := match e with
         | Var t v => Some v
         | _ => None
         end.

    Local Notation if_arrow f
      := (fun t => match t return Type with
                   | type.arrow s d => f s d
                   | _ => True
                   end) (only parsing).
    Local Notation if_arrow_s f := (if_arrow (fun s d => f s)) (only parsing).
    Local Notation if_arrow_d f := (if_arrow (fun s d => f d)) (only parsing).
    Local Notation if_prod f
      := (fun t => match t return Type with
                   | type.prod A B => f A B
                   | _ => True
                   end).

    Definition invert_Abs {s d} (e : @expr var (type.arrow s d)) : option (var s -> @expr var d)
      := match e in expr.expr t return option (if_arrow (fun _ _ => _) t) with
         | Abs s d f => Some f
         | _ => None
         end.

    Definition invert_App {d} (e : @expr var d) : option { s : _ & @expr var (s -> d) * @expr var s }%type
      := match e with
         | App s d f x => Some (existT _ s (f, x))
         | _ => None
         end.

    Definition invert_AppIdent {d} (e : @expr var d) : option { s : _ & @ident s d * @expr var s }%type
      := match e with
         | AppIdent s d idc args
           => Some (existT _ s (idc, args))
         | _ => None
         end.

    Definition invert_App2 {d} (e : @expr var d) : option { s1s2 : _ * _ & @expr var (fst s1s2 -> snd s1s2 -> d) * @expr var (fst s1s2) * @expr var (snd s1s2) }%type
      := match invert_App e with
         | Some (existT s (f, y))
           => match invert_App f with
              | Some (existT s' (f', x))
                => Some (existT _ (s', s) (f', x, y))
              | None => None
              end
         | None => None
         end.

    Local Notation expr_prod
      := (fun t => match t return Type with
                   | type.prod A B => prod (expr A) (expr B)
                   | _ => True
                   end) (only parsing).

    Definition invert_Pair {A B} (e : @expr var (type.prod A B)) : option (@expr var A * @expr var B)
      := match e in expr.expr t return option (if_prod (fun A B => expr A * expr B)%type t) with
         | Pair A B a b
           => Some (a, b)
         | _ => None
         end.

    (* if we want more code for the below, I would suggest [reify_base_type] and [reflect_base_type] *)
    Definition reify_primitive {t} (v : type.interp (type.type_primitive t)) : @expr var (type.type_primitive t)
      := AppIdent (ident.primitive v) TT.
    Definition reflect_primitive {t} (e : @expr var (type.type_primitive t)) : option (type.interp (type.type_primitive t))
      := match invert_AppIdent e with
         | Some (existT s (idc, args))
           => match idc in ident _ t return option (type.interp t) with
              | ident.primitive _ v => Some v
              | _ => None
              end
         | None => None
         end.

    Local Notation list_expr
      := (fun t => match t return Type with
                   | type.list T => list (expr T)
                   | _ => True
                   end) (only parsing).

    (* oh, the horrors of not being able to use non-linear deep pattern matches.  c.f. COQBUG(https://github.com/coq/coq/issues/6320) *)
    Fixpoint reflect_list {t} (e : @expr var (type.list t))
      : option (list (@expr var t))
      := match e in expr.expr t return option (list_expr t) with
         | AppIdent s (type.list t) idc x_xs
           => match x_xs in expr.expr s return ident s (type.list t) -> option (list (expr t)) with
              | Pair A (type.list B) x xs
                => match @reflect_list B xs with
                   | Some xs
                     => fun idc
                        => match idc in ident s d
                                 return if_prod (fun A B => expr A) s
                                        -> if_prod (fun A B => list_expr B) s
                                        -> option (list_expr d)
                           with
                           | ident.cons A
                             => fun x xs => Some (cons x xs)
                           | _ => fun _ _ => None
                           end x xs
                   | None => fun _ => None
                   end
              | _
                => fun idc
                   => match idc in ident _ t return option (list_expr t) with
                      | ident.nil _ => Some nil
                      | _ => None
                      end
              end idc
         | _ => None
         end.
  End invert.

  Section gallina_reify.
    Context {var : type -> Type}.
    Definition reify_list {t} (ls : list (@expr var t)) : @expr var (type.list t)
      := list_rect
           (fun _ => _)
           (ident.nil @@ TT)%expr
           (fun x _ xs => ident.cons @@ (x, xs))%expr
           ls.
  End gallina_reify.

  Module partial.
    Section value.
      Context (var : type -> Type).
      Definition value_prestep (value : type -> Type) (t : type)
        := match t return Type with
           | type.prod A B as t => value A * value B
           | type.arrow s d => value s -> value d
           | type.list A => list (value A)
           | type.type_primitive _ as t
             => type.interp t
           end%type.
      Definition value_step (value : type -> Type) (t : type)
        := match t return Type with
           | type.arrow _ _ as t
             => value_prestep value t
           | type.prod _ _ as t
           | type.list _ as t
           | type.type_primitive _ as t
             => @expr var t + value_prestep value t
           end%type.
      Fixpoint value (t : type)
        := value_step value t.
    End value.

    Module expr.
      Section reify.
        Context {var : type -> Type}.
        Fixpoint reify {t : type} {struct t}
          : value var t -> @expr var t
          := match t return value var t -> expr t with
             | type.prod A B as t
               => fun x : expr t + value var A * value var B
                  => match x with
                     | inl v => v
                     | inr (a, b) => (@reify A a, @reify B b)%expr
                     end
             | type.arrow s d
               => fun (f : value var s -> value var d)
                  => Abs (fun x
                          => @reify d (f (@reflect s (Var x))))
             | type.list A as t
               => fun x : expr t + list (value var A)
                  => match x with
                     | inl v => v
                     | inr v => reify_list (List.map (@reify A) v)
                     end
             | type.type_primitive _ as t
               => fun x : expr t + type.interp t
                  => match x with
                     | inl v => v
                     | inr v => ident.primitive v @@ TT
                     end%expr
             end
        with reflect {t : type}
             : @expr var t -> value var t
             := match t return expr t -> value var t with
                | type.arrow s d
                  => fun (f : expr (s -> d)) (x : value var s)
                     => @reflect d (App f (@reify s x))
                | type.prod A B as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match invert_Pair v with
                        | Some (a, b)
                          => inr (@reflect A a, @reflect B b)
                        | None
                          => inl v
                        end
                | type.list A as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match reflect_list v with
                        | Some ls
                          => inr (List.map (@reflect A) ls)
                        | None
                          => inl v
                        end
                | type.type_primitive _ as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match reflect_primitive v with
                        | Some v => inr v
                        | None => inl v
                        end
                end.
      End reify.
    End expr.

    Module ident.
      Section interp.
        Context {var : type -> Type}.
        Definition interp_let_in {tC tx : type} : value var tx -> (value var tx -> value var tC) -> value var tC
          := match tx return value var tx -> (value var tx -> value var tC) -> value var tC with
             | type.arrow _ _
             | type.prod _ _
             | type.list _
               => fun x f => f x
             | type.type_primitive _ as t
               => fun (x : expr t + type.interp t) (f : expr t + type.interp t -> value var tC)
                  => match x with
                     | inl e
                       => match invert_Var e with
                          | Some v => f (inl (Var v))
                          | None => partial.expr.reflect (expr_let y := e in partial.expr.reify (f (inl (Var y))))%expr
                          end
                     | inr v => f (inr v) (* FIXME: do not substitute [S (big stuck term)] *)
                     end
             end.
        Definition interp {s d} (idc : ident s d) : value var (s -> d)
          := match idc in ident s d return value var (s -> d) with
             | ident.Let_In tx tC as idc
               => fun (xf : expr (tx * (tx -> tC)) + value var tx * value var (tx -> tC))
                  => match xf with
                     | inr (x, f) => interp_let_in x f
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=tx * (tx -> tC)) xf))
                     end
             | ident.nil t
               => fun _ => inr (@nil (value var t))
             | ident.primitive t v
               => fun _ => inr v
             | ident.cons t as idc
               => fun (x_xs : expr (t * type.list t) + value var t * (expr (type.list t) + list (value var t)))
                  => match x_xs return expr (type.list t) + list (value var t) with
                     | inr (x, inr xs) => inr (cons x xs)
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=t * type.list t) x_xs))
                     end
             | ident.fst A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => fst x
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=A*B) x))
                     end
             | ident.snd A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => snd x
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=A*B) x))
                     end
             | ident.bool_rect T as idc
               => fun (true_case_false_case_b : expr (T * T * type.bool) + (expr (T * T) + value var T * value var T) * (expr type.bool + bool))
                  => match true_case_false_case_b with
                     | inr (inr (true_case, false_case), inr b)
                       => @bool_rect (fun _ => value var T) true_case false_case b
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=T*T*type.bool) true_case_false_case_b))
                     end
             | ident.nat_rect P as idc
               => fun (O_case_S_case_n : expr (P * (type.nat * P -> P) * type.nat) + (expr (P * (type.nat * P -> P)) + value var P * value var (type.nat * P -> P)) * (expr type.nat + nat))
                  => match O_case_S_case_n with
                     | inr (inr (O_case, S_case), inr n)
                       => @nat_rect (fun _ => value var P)
                                    O_case
                                    (fun n' rec => S_case (inr (inr n', rec)))
                                    n
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=P * (type.nat * P -> P) * type.nat) O_case_S_case_n))
                     end
             | ident.list_rect A P as idc
               => fun (nil_case_cons_case_ls : expr (P * (A * type.list A * P -> P) * type.list A) + (expr (P * (A * type.list A * P -> P)) + value var P * value var (A * type.list A * P -> P)) * (expr (type.list A) + list (value var A)))
                  => match nil_case_cons_case_ls with
                     | inr (inr (nil_case, cons_case), inr ls)
                       => @list_rect
                            (value var A)
                            (fun _ => value var P)
                            nil_case
                            (fun x xs rec => cons_case (inr (inr (x, inr xs), rec)))
                            ls
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=P * (A * type.list A * P -> P) * type.list A) nil_case_cons_case_ls))
                     end
             | ident.List.nth_default A as idc
               => fun (default_ls_idx : expr (A * type.list A * type.nat) + (expr (A * type.list A) + value var A * (expr (type.list A) + list (value var A))) * (expr type.nat + nat))
                  => match default_ls_idx with
                     | inr (inr (default, inr ls), inr idx)
                       => List.nth_default default ls idx
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=A * type.list A * type.nat) default_ls_idx))
                     end
             | ident.pred as idc
             | ident.Nat_succ as idc
             | ident.Z_of_nat as idc
             | ident.Z_opp as idc
               => fun x : expr _ + type.interp _
                  => match x return expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | inl x => expr.reflect (AppIdent idc x)
                     end
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_pow as idc
             | ident.Z_div as idc
             | ident.Z_modulo as idc
             | ident.Z_eqb as idc
               => fun (x_y : expr (_ * _) + (expr _ + type.interp _) * (expr _ + type.interp _))
                  => match x_y return expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | _ => expr.reflect (AppIdent idc (expr.reify (t:=_*_) x_y))
                     end
             | ident.Z_runtime_mul as idc
               => fun (x_y : expr (_ * _) + (expr _ + type.interp _) * (expr _ + type.interp _))
                  => let default := expr.reflect (AppIdent idc (expr.reify (t:=_*_) x_y)) in
                     match x_y return expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl e)
                     | inr (inl e, inr x)
                       => if Z.eqb x 0
                          then inr 0%Z
                          else if Z.eqb x 1
                               then inl e
                               else default
                     | inr (inl _, inl _) | inl _ => default
                     end
             | ident.Z_runtime_add as idc
               => fun (x_y : expr (_ * _) + (expr _ + type.interp _) * (expr _ + type.interp _))
                  => let default := expr.reflect (AppIdent idc (expr.reify (t:=_*_) x_y)) in
                     match x_y return expr _ + type.interp _ with
                     | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                     | inr (inr x, inl e)
                     | inr (inl e, inr x)
                       => if Z.eqb x 0
                          then inl e
                          else default
                     | inr (inl _, inl _) | inl _ => default
                     end
             end.
      End interp.
    End ident.
  End partial.

  Section partial_reduce.
    Context {var : type -> Type}.

    Fixpoint partial_reduce' {t} (e : @expr (partial.value var) t)
      : partial.value var t
      := match e in expr.expr t return partial.value var t with
         | Var t v => v
         | TT => inr tt
         | AppIdent s d idc args => partial.ident.interp idc (@partial_reduce' _ args)
         | Pair A B a b => inr (@partial_reduce' A a, @partial_reduce' B b)
         | App s d f x => @partial_reduce' _ f (@partial_reduce' _ x)
         | Abs s d f => fun x => @partial_reduce' d (f x)
         end.

    Definition partial_reduce {t} (e : @expr (partial.value var) t) : @expr var t
      := partial.expr.reify (@partial_reduce' t e).
  End partial_reduce.

  Definition PartialReduce {t} (e : Expr t) : Expr t
    := fun var => @partial_reduce var t (e _).

End Compilers.
Import Associational Positional Compilers.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.

(* TODO: is this the right way to do things? *)
Definition expand_list_helper {A} (default : A) (ls : list A) (n : nat) (idx : nat) : list A
  := nat_rect
       (fun _ => nat -> list A)
       (fun _ => nil)
       (fun n' rec_call idx
        => cons (List.nth_default default ls idx) (rec_call (S idx)))
       n
       idx.
Definition expand_list {A} (default : A) (ls : list A) (n : nat) : list A
  := expand_list_helper default ls n 0.
Require Import Coq.micromega.Lia.
(* TODO: MOVE ME *)
Lemma expand_list_helper_correct {A} (default : A) (ls : list A) (n idx : nat) (H : (idx + n <= length ls)%nat)
  : expand_list_helper default ls n idx
    = List.firstn n (List.skipn idx ls).
Proof.
  cbv [expand_list_helper]; revert idx H.
  induction n as [|n IHn]; cbn; intros.
  { reflexivity. }
  { rewrite IHn by omega.
    erewrite (@skipn_nth_default _ idx ls) by omega.
    reflexivity. }
Qed.

Lemma expand_list_correct (n : nat) {A} (default : A) (ls : list A) (H : List.length ls = n)
  : expand_list default ls n = ls.
Proof.
  subst; cbv [expand_list]; rewrite expand_list_helper_correct by reflexivity.
  rewrite skipn_0, firstn_all; reflexivity.
Qed.

Delimit Scope RT_expr_scope with RT_expr.
Import Uncurried.
Import expr.
Import for_reification.Notations.Reification.

Notation "x + y"
  := (AppIdent ident.Z.runtime_add (x%RT_expr, y%RT_expr)%expr)
     : RT_expr_scope.
Notation "x * y"
  := (AppIdent ident.Z.runtime_mul (x%RT_expr, y%RT_expr)%expr)
     : RT_expr_scope.
Notation "x + y"
  := (AppIdent ident.Z.runtime_add (x%RT_expr, y%RT_expr)%expr)
     : expr_scope.
Notation "x * y"
  := (AppIdent ident.Z.runtime_mul (x%RT_expr, y%RT_expr)%expr)
     : expr_scope.
Notation "x" := (Var x) (only printing, at level 9) : expr_scope.
Open Scope RT_expr_scope.

Require Import AdmitAxiom.


Example test1 : True.
Proof.
  let v := Reify ((fun x => 2^x) 255)%Z in
  pose v as E.
  vm_compute in E.
  pose (PartialReduce (canonicalize_list_recursion E)) as E'.
  vm_compute in E'.
  lazymatch (eval cbv delta [E'] in E') with
  | (fun var => AppIdent (ident.primitive ?v) TT) => idtac
  end.
  constructor.
Qed.
Example test2 : True.
Proof.
  let v := Reify (fun y : Z
                  => (fun k : Z * Z -> Z * Z
                      => dlet_nd x := (y * y)%RT in
                          dlet_nd z := (x * x)%RT in
                          k (z, z))
                       (fun v => v)) in
  pose v as E.
  vm_compute in E.
  pose (PartialReduce (canonicalize_list_recursion E)) as E'.
  vm_compute in E'.
  lazymatch (eval cbv delta [E'] in E') with
  | (fun var : type -> Type =>
       (λ x : var (type.type_primitive type.Z),
              expr_let x0 := (Var x * Var x)%RT_expr in
            expr_let x1 := (Var x0 * Var x0)%RT_expr in
            (Var x1, Var x1))%expr) => idtac
  end.
  constructor.
Qed.
Example test3 : True.
Proof.
  let v := Reify (fun y : Z
                  => dlet_nd x := dlet_nd x := (y * y)%RT in
                      (x * x)%RT in
                      dlet_nd z := dlet_nd z := (x * x)%RT in
                      (z * z)%RT in
                      (z * z)%RT) in
  pose v as E.
  vm_compute in E.
  pose (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E))) as E'.
  vm_compute in E'.
  pose (PartialReduce E') as E''.
  lazy in E''.
  lazymatch (eval cbv delta [E''] in E'') with
  | (fun var : type -> Type =>
       (λ x : var (type.type_primitive type.Z),
              expr_let x0 := Var x * Var x in
            expr_let x1 := Var x0 * Var x0 in
            expr_let x2 := Var x1 * Var x1 in
            expr_let x3 := Var x2 * Var x2 in
            Var x3 * Var x3)%RT_expr%expr)
    => idtac
  end.
  constructor.
Qed.

Axiom admit : forall {T}, T.

Derive carry_mul_gen
       SuchThat (forall (w : nat -> Z)
                        (fg : list Z * list Z)
                        (f := fst fg) (g := snd fg)
                        (n : nat)
                        (Hf : length f = n)
                        (Hg : length g = n)
                        (s : Z)
                        (c : list (Z * Z))
                        (len_c : nat)
                        (Hc : length c = len_c)
                        (idxs : list nat)
                        (len_idxs : nat)
                        (Hidxs : length idxs = len_idxs)
                        (Hw0_1 : w 0%nat = 1)
                        (Hw_nz : forall i : nat, w i <> 0)
                        (Hw_div_nz : forall i : nat, w (S i) / w i <> 0)
                        (Hsc_nz : s - Associational.eval c <> 0)
                        (Hs_nz : s <> 0)
                        (Hn_nz : n <> 0%nat),
                    let fg' := carry_mul_gen w fg n s c len_c idxs len_idxs in
                    (eval w n fg') mod (s - Associational.eval c)
                    = (eval w n f * eval w n g) mod (s - Associational.eval c))
       As carry_mul_gen_correct.
Proof.
  intros; subst carry_mul_gen.
  erewrite <-eval_mulmod with (s:=s) (c:=c)
    by (try assumption; try reflexivity).
  (*   eval w n (fg' w fg n s c len_c) mod (s - Associational.eval c) =
       eval w n (mulmod w s c n f g) mod (s - Associational.eval c) *)
  etransitivity;
    [ | rewrite <- eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs) (modulo:=fun x y => Z.modulo x y) (div:=fun x y => Z.div x y)
        by (try assumption; auto using Z.div_mod); reflexivity ].
  eapply f_equal2; [|trivial]. eapply f_equal.
  erewrite <- (expand_list_correct _ (-1)%Z f),
  <- (expand_list_correct _ (-1)%Z g),
  <- (expand_list_correct _ 0%nat idxs),
  <- (expand_list_correct _ (-1,-1)%Z c)
    by eassumption.
  pose (idxs, len_idxs, n, s, c, len_c, w, fg) as args.
  subst f g.
  change fg with (snd args).
  change w with (snd (fst args)).
  change len_c with (snd (fst (fst args))).
  change c with (snd (fst (fst (fst args)))).
  change s with (snd (fst (fst (fst (fst args))))).
  change n with (snd (fst (fst (fst (fst (fst args)))))).
  change len_idxs with (snd (fst (fst (fst (fst (fst (fst args))))))).
  change idxs with (fst (fst (fst (fst (fst (fst (fst args))))))).
  remember args as args' eqn:Hargs.
  etransitivity.
  Focus 2.
  { subst fg'.
    repeat match goal with H : _ |- _ => clear H end; revert args'.
    lazymatch goal with
    | [ |- forall args, ?ev = @?RHS args ]
      => refine (fun args => f_equal (fun F => F args) (_ : _ = RHS))
    end.
    cbv [expand_list expand_list_helper].
    cbv delta [chained_carries carry carry_reduce Associational.carry carryterm mulmod to_associational mul to_associational reduce from_associational add_to_nth zeros place split].
    Reify_rhs ().
    reflexivity.
  } Unfocus.
  cbv beta.
  let e := match goal with |- _ = expr.Interp _ ?e _ => e end in
  set (E := e).
  Time let E' := constr:(PartialReduce (CPS.CallFunWithIdContinuation (CPS.Translate (canonicalize_list_recursion E)))) in
       let E' := (eval lazy in E') in
       pose E' as E''.
  transitivity (Interp E'' (fst (fst args'), (fun '((i, k) : nat * (Z -> list Z)) => k (w i)), snd args')); [ clear E | exact admit ].
  subst args' args; cbn [fst snd].
  subst fg'.
  reflexivity.
Qed.

(*Definition w (i:nat) : Z := 2^Qceiling((25+1/2)*i).*)
Definition w (i:nat) : Z := 2^Qceiling(51*i).
Derive base_51_carry_mul
       SuchThat (forall
                    (*(f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : Z)
        (f:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)
        (g:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)*)
                    (fg : list Z * list Z)
                    (f := fst fg) (g := snd fg)
                    (n:=5%nat)
                    (Hf : length f = n) (Hg : length g = n)
                    (fg' := base_51_carry_mul fg),
                    (eval w n fg') mod (2^255-19)
                    = (eval w n f * eval w n g) mod (2^255-19))
       As base_51_carry_mul_correct.
Proof.
  intros; subst f g fg'.
  erewrite <- carry_mul_gen_correct with (s:=2^255) (c:=[(1, 19)]) (idxs:=(seq 0 n ++ [0; 1])%list%nat)
    by (cbn [length seq n List.app]; try reflexivity; try assumption;
        try (intros; eapply pow_ceil_mul_nat_divide_nonzero);
        try eapply pow_ceil_mul_nat_nonzero;
        (apply dec_bool; vm_compute; reflexivity)).
  cbn [length seq n List.app].
  cbv [w Qceiling Qfloor Qopp Qnum Qdiv Qplus inject_Z Qmult Qinv Qden Pos.mul].
  cbv [Associational.eval fold_right map fst snd].
  apply f_equal2; [ | reflexivity ]; apply f_equal.
  cbv [carry_mul_gen n].
  lazymatch goal with
  | [ |- ?ev = expr.Interp (@ident.interp) ?e (?args, fg) ]
    => let rargs := Reify args in
       let rargs := constr:(canonicalize_list_recursion rargs) in
       transitivity (expr.Interp
                       (@ident.interp)
                       (fun var
                        => λ (FG : var (type.list type.Z * type.list type.Z)%ctype),
                           (e var @ (rargs var, Var FG)))%expr fg)
  end.
  2:cbv [expr.interp expr.Interp ident.interp]; exact admit.
  let e := match goal with |- _ = expr.Interp _ ?e _ => e end in
  set (E := e).
  cbv [canonicalize_list_recursion canonicalize_list_recursion.expr.transfer canonicalize_list_recursion.ident.transfer] in E.
  Time let E' := constr:(PartialReduce E) in
       let E' := (eval lazy in E') in
       pose E' as E''.
  transitivity (Interp E'' fg); [ clear E | exact admit ].
  subst base_51_carry_mul.
  reflexivity.
Qed.

Import ident.
Print base_51_carry_mul.
(*   = fun (fg : list Z * list Z) (_ : length (Datatypes.fst fg) = 5%nat)
         (_ : length (Datatypes.snd fg) = 5%nat) =>
       expr.Interp (@interp)
         (fun var : type -> Type =>
          (λ x : var (type.list type.Z * type.list type.Z)%ctype,
           expr_let y := (fst @@ x [[0]] * snd @@ x [[4]])%expr +
                         ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                          ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                           ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                            (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y, 2251799813685248) in
           expr_let y2 := (fst @@ x [[0]] * snd @@ x [[3]])%expr +
                          ((fst @@ x [[1]] * snd @@ x [[2]])%expr +
                           ((fst @@ x [[2]] * snd @@ x [[1]])%expr +
                            ((fst @@ x [[3]] * snd @@ x [[0]])%expr +
                             (19 * (fst @@ x [[4]] * snd @@ x [[4]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y2, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y2, 2251799813685248) in
           expr_let y5 := (fst @@ x [[0]] * snd @@ x [[2]])%expr +
                          ((fst @@ x [[1]] * snd @@ x [[1]])%expr +
                           ((fst @@ x [[2]] * snd @@ x [[0]])%expr +
                            ((19 * (fst @@ x [[3]] * snd @@ x [[4]])%expr)%expr +
                             (19 * (fst @@ x [[4]] * snd @@ x [[3]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y5, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y5, 2251799813685248) in
           expr_let y8 := (fst @@ x [[0]] * snd @@ x [[1]])%expr +
                          ((fst @@ x [[1]] * snd @@ x [[0]])%expr +
                           ((19 * (fst @@ x [[2]] * snd @@ x [[4]])%expr)%expr +
                            ((19 * (fst @@ x [[3]] * snd @@ x [[3]])%expr)%expr +
                             (19 * (fst @@ x [[4]] * snd @@ x [[2]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y8, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y8, 2251799813685248) in
           expr_let y11 := (fst @@ x [[0]] * snd @@ x [[0]])%expr +
                           ((19 * (fst @@ x [[1]] * snd @@ x [[4]])%expr)%expr +
                            ((19 * (fst @@ x [[2]] * snd @@ x [[3]])%expr)%expr +
                             ((19 * (fst @@ x [[3]] * snd @@ x [[2]])%expr)%expr +
                              (19 * (fst @@ x [[4]] * snd @@ x [[1]])%expr)%expr)%expr)%expr)%expr in
           expr_let y12 := Z.div @@ (y11, 2251799813685248) in
           expr_let y13 := Z.modulo @@ (y11, 2251799813685248) in
           expr_let y14 := (fst @@ x [[0]] * snd @@ x [[4]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                             ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                              (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y14, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y14, 2251799813685248) in
           expr_let y17 := (fst @@ x [[0]] * snd @@ x [[3]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[2]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[1]])%expr +
                             ((fst @@ x [[3]] * snd @@ x [[0]])%expr +
                              (19 * (fst @@ x [[4]] * snd @@ x [[4]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y17, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y17, 2251799813685248) in
           expr_let y20 := (fst @@ x [[0]] * snd @@ x [[2]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[1]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[0]])%expr +
                             ((19 * (fst @@ x [[3]] * snd @@ x [[4]])%expr)%expr +
                              (19 * (fst @@ x [[4]] * snd @@ x [[3]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y20, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y20, 2251799813685248) in
           expr_let y23 := y12 +
                           ((fst @@ x [[0]] * snd @@ x [[1]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[0]])%expr +
                             ((19 * (fst @@ x [[2]] * snd @@ x [[4]])%expr)%expr +
                              ((19 * (fst @@ x [[3]] * snd @@ x [[3]])%expr)%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[2]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y24 := Z.div @@ (y23, 2251799813685248) in
           expr_let y25 := Z.modulo @@ (y23, 2251799813685248) in
           expr_let _ := Z.div @@ (y13, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y13, 2251799813685248) in
           expr_let y28 := (fst @@ x [[0]] * snd @@ x [[4]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                             ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                              (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y28, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y28, 2251799813685248) in
           expr_let y31 := (fst @@ x [[0]] * snd @@ x [[3]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[2]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[1]])%expr +
                             ((fst @@ x [[3]] * snd @@ x [[0]])%expr +
                              (19 * (fst @@ x [[4]] * snd @@ x [[4]])%expr)%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y31, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y31, 2251799813685248) in
           expr_let y34 := y24 +
                           ((fst @@ x [[0]] * snd @@ x [[2]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[1]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[0]])%expr +
                              ((19 * (fst @@ x [[3]] * snd @@ x [[4]])%expr)%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[3]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y35 := Z.div @@ (y34, 2251799813685248) in
           expr_let y36 := Z.modulo @@ (y34, 2251799813685248) in
           expr_let _ := Z.div @@ (y25, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y25, 2251799813685248) in
           expr_let _ := Z.div @@ (y13, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y13, 2251799813685248) in
           expr_let y41 := (fst @@ x [[0]] * snd @@ x [[4]])%expr +
                           ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                            ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                             ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                              (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr in
           expr_let _ := Z.div @@ (y41, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y41, 2251799813685248) in
           expr_let y44 := y35 +
                           ((fst @@ x [[0]] * snd @@ x [[3]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[2]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[1]])%expr +
                              ((fst @@ x [[3]] * snd @@ x [[0]])%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[4]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y45 := Z.div @@ (y44, 2251799813685248) in
           expr_let y46 := Z.modulo @@ (y44, 2251799813685248) in
           expr_let _ := Z.div @@ (y36, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y36, 2251799813685248) in
           expr_let _ := Z.div @@ (y25, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y25, 2251799813685248) in
           expr_let _ := Z.div @@ (y13, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y13, 2251799813685248) in
           expr_let y53 := y45 +
                           ((fst @@ x [[0]] * snd @@ x [[4]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                              ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                               (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr)%expr in
           expr_let y54 := Z.div @@ (y53, 2251799813685248) in
           expr_let y55 := Z.modulo @@ (y53, 2251799813685248) in
           expr_let _ := Z.div @@ (y46, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y46, 2251799813685248) in
           expr_let _ := Z.div @@ (y36, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y36, 2251799813685248) in
           expr_let _ := Z.div @@ (y25, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y25, 2251799813685248) in
           expr_let _ := Z.div @@ (y13, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y13, 2251799813685248) in
           expr_let _ := Z.div @@ (y55, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y55, 2251799813685248) in
           expr_let _ := Z.div @@ (y46, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y46, 2251799813685248) in
           expr_let _ := Z.div @@ (y36, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y36, 2251799813685248) in
           expr_let _ := Z.div @@ (y25, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y25, 2251799813685248) in
           expr_let y72 := y13 + (19 * y54)%expr in
           expr_let y73 := Z.div @@ (y72, 2251799813685248) in
           expr_let y74 := Z.modulo @@ (y72, 2251799813685248) in
           expr_let _ := Z.div @@ (y55, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y55, 2251799813685248) in
           expr_let _ := Z.div @@ (y46, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y46, 2251799813685248) in
           expr_let _ := Z.div @@ (y36, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y36, 2251799813685248) in
           expr_let y81 := y73 + y25 in
           expr_let y82 := Z.div @@ (y81, 2251799813685248) in
           expr_let y83 := Z.modulo @@ (y81, 2251799813685248) in
           expr_let _ := Z.div @@ (y74, 2251799813685248) in
           expr_let _ := Z.modulo @@ (y74, 2251799813685248) in
           y74 :: y83 :: y82 + y36 :: y46 :: y55 :: [])%expr) fg
     : forall fg : list Z * list Z,
       length (Datatypes.fst fg) = 5%nat ->
       length (Datatypes.snd fg) = 5%nat -> list Z
*)

(* after manual dead code elimination: *)
(*    = fun (fg : list Z * list Z) (_ : length (Datatypes.fst fg) = 5%nat)
         (_ : length (Datatypes.snd fg) = 5%nat) =>
       expr.Interp (@interp)
         (fun var : type -> Type =>
          (λ x : var (type.list type.Z * type.list type.Z)%ctype,
           expr_let y11 := (fst @@ x [[0]] * snd @@ x [[0]])%expr +
                           ((19 * (fst @@ x [[1]] * snd @@ x [[4]])%expr)%expr +
                            ((19 * (fst @@ x [[2]] * snd @@ x [[3]])%expr)%expr +
                             ((19 * (fst @@ x [[3]] * snd @@ x [[2]])%expr)%expr +
                              (19 * (fst @@ x [[4]] * snd @@ x [[1]])%expr)%expr)%expr)%expr)%expr in
           expr_let y12 := Z.div @@ (y11, 2251799813685248) in
           expr_let y13 := Z.modulo @@ (y11, 2251799813685248) in
           expr_let y23 := y12 +
                           ((fst @@ x [[0]] * snd @@ x [[1]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[0]])%expr +
                             ((19 * (fst @@ x [[2]] * snd @@ x [[4]])%expr)%expr +
                              ((19 * (fst @@ x [[3]] * snd @@ x [[3]])%expr)%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[2]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y24 := Z.div @@ (y23, 2251799813685248) in
           expr_let y25 := Z.modulo @@ (y23, 2251799813685248) in
           expr_let y34 := y24 +
                           ((fst @@ x [[0]] * snd @@ x [[2]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[1]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[0]])%expr +
                              ((19 * (fst @@ x [[3]] * snd @@ x [[4]])%expr)%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[3]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y35 := Z.div @@ (y34, 2251799813685248) in
           expr_let y36 := Z.modulo @@ (y34, 2251799813685248) in
           expr_let y44 := y35 +
                           ((fst @@ x [[0]] * snd @@ x [[3]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[2]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[1]])%expr +
                              ((fst @@ x [[3]] * snd @@ x [[0]])%expr +
                               (19 * (fst @@ x [[4]] * snd @@ x [[4]])%expr)%expr)%expr)%expr)%expr)%expr in
           expr_let y45 := Z.div @@ (y44, 2251799813685248) in
           expr_let y46 := Z.modulo @@ (y44, 2251799813685248) in
           expr_let y53 := y45 +
                           ((fst @@ x [[0]] * snd @@ x [[4]])%expr +
                            ((fst @@ x [[1]] * snd @@ x [[3]])%expr +
                             ((fst @@ x [[2]] * snd @@ x [[2]])%expr +
                              ((fst @@ x [[3]] * snd @@ x [[1]])%expr +
                               (fst @@ x [[4]] * snd @@ x [[0]])%expr)%expr)%expr)%expr)%expr in
           expr_let y54 := Z.div @@ (y53, 2251799813685248) in
           expr_let y55 := Z.modulo @@ (y53, 2251799813685248) in
           expr_let y72 := y13 + (19 * y54)%expr in
           expr_let y73 := Z.div @@ (y72, 2251799813685248) in
           expr_let y74 := Z.modulo @@ (y72, 2251799813685248) in
           expr_let y81 := y73 + y25 in
           expr_let y82 := Z.div @@ (y81, 2251799813685248) in
           expr_let y83 := Z.modulo @@ (y81, 2251799813685248) in
           y74 :: y83 :: y82 + y36 :: y46 :: y55 :: [])%expr) fg
*)
