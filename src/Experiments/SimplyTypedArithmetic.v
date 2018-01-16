(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.RunTacticAsConstr.
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
      then dlet t2 := snd t in
           dlet d2 := div t2 fw in
           dlet m2 := modulo t2 fw in
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
  Definition add_to_nth i x : list Z -> list Z
    := ListUtil.update_nth i (runtime_add x).
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
    List.fold_right (fun t =>
      let p := place t (pred n) in
      add_to_nth (fst p) (snd p)    ) (zeros n) p.
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
      fold_right (@carry_reduce n s c) p (rev idxs).

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
    Variant opaque := unit | Z | nat | bool.
    Inductive type := type_opaque (_:opaque) | prod (A B : type) | arrow (s d : type) | list (A : type).
    Module Export Coercions.
      Global Coercion type_opaque : opaque >-> type.
    End Coercions.

    Fixpoint final_codomain (t : type) : type
      := match t with
         | arrow _ d => final_codomain d
         | t => t
         end.

    Fixpoint under_arrows (t : type) (f : type -> type) : type
      := match t with
         | arrow s d => arrow s (under_arrows d f)
         | t => f t
         end.

    Fixpoint interp (t : type)
      := match t with
         | unit => Datatypes.unit
         | prod A B => interp A * interp B
         | arrow A B => interp A -> interp B
         | list A => Datatypes.list (interp A)
         | nat => Datatypes.nat
         | type_opaque Z => BinInt.Z
         | bool => Datatypes.bool
         end%type.

    Ltac reify_opaque ty :=
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
      | _ => let rt := reify_opaque ty in
             constr:(type_opaque rt)
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

  Module expr.
    Inductive expr {ident : type -> Type} {var : type -> Type} : type -> Type :=
    | Var {t} (v : var t) : expr t
    | Ident {t} (idc : ident t) : expr t
    | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
    | Abs {s d} (f : var s -> expr d) : expr (s -> d).

    Module Export Notations.
      Bind Scope expr_scope with expr.
      Delimit Scope expr_scope with expr.

      Infix "@" := App : expr_scope.
      Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
    End Notations.

    Definition Expr {ident : type -> Type} t := forall var, @expr ident var t.

    Section with_ident.
      Context {ident : type -> Type}
              (interp_ident : forall t, ident t -> type.interp t).

      Fixpoint interp {t} (e : @expr ident type.interp t) : type.interp t
        := match e with
           | Var t v => v
           | Ident t idc => interp_ident t idc
           | App s d f x => interp f (interp x)
           | Abs s d f => fun v => interp (f v)
           end.

      Definition Interp {t} (e : Expr t) := interp (e _).
    End with_ident.

    Ltac is_opaque_const_cps2 term on_success on_failure :=
      let recurse term := is_opaque_const_cps2 term on_success on_failure in
      lazymatch term with
      | S ?n => recurse n
      | O => on_success ()
      | true => on_success ()
      | false => on_success ()
      | tt => on_success ()
      | Z0 => on_success ()
      | Zpos ?p => recurse p
      | Zneg ?p => recurse p
      | xI ?p => recurse p
      | xO ?p => recurse p
      | xH => on_success ()
      | ?term => on_failure term
      end.
    Ltac require_opaque_const term :=
      is_opaque_const_cps2 term ltac:(fun _ => idtac) ltac:(fun term => fail 0 "Not a known const:" term).
    Ltac is_opaque_const term :=
      is_opaque_const_cps2 term ltac:(fun _ => true) ltac:(fun _ => false).

    Module var_context.
      Inductive list {var : type -> Type} :=
      | nil
      | cons {t} (gallina_v : type.interp t) (v : var t) (ctx : list).
    End var_context.

    (* cf COQBUG(https://github.com/coq/coq/issues/5448) , COQBUG(https://github.com/coq/coq/issues/6315) *)
    Ltac refresh n :=
      let n' := fresh n in
      let n' := fresh n in
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

    Ltac reify_helper ident reify_ident var term value_ctx template_ctx :=
      let reify_rec_gen term value_ctx template_ctx := reify_helper ident reify_ident var term value_ctx template_ctx in
      let reify_rec term := reify_rec_gen term value_ctx template_ctx in
      (*let dummy := match goal with _ => idtac "reify_helper: attempting to reify:" term end in*)
      lazymatch value_ctx with
      | context[@var_context.cons _ ?rT term ?v _]
        => constr:(@Var ident var rT v)
      | _
        =>
        let term_is_opaque_const := is_opaque_const term in
        lazymatch term_is_opaque_const with
        | true
          => let rv := reify_ident term in
             constr:(Ident (var:=var) rv)
        | false
          =>
          lazymatch term with
          | match ?b with true => ?t | false => ?f end
            => let T := type of t in
               reify_rec (@bool_rect (fun _ => T) t f b)
          | let x := ?a in @?b x
            => let A := type of a in
               let B := lazymatch type of b with forall x, @?B x => B end in
               reify_rec (@Let_In A B a b)
          | ?f ?x
            =>
            let ty := type_of_first_argument_of f in
            let x_is_template_parameter := is_template_parameter ty in
            lazymatch x_is_template_parameter with
            | true
              => (* we can't reify things of type [Type], so we save it for later to plug in *)
              reify_rec_gen f value_ctx (x, template_ctx)
            | false
              =>
              let rx := reify_rec_gen x value_ctx tt in
              let rf := reify_rec_gen f value_ctx template_ctx in
              constr:(App (var:=var) rf rx)
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
                reify_rec_gen (match arg with x => f end) value_ctx template_ctx
              end
            | false
              =>
              let rT := type.reify T in
              let not_x := refresh x in
              let not_x2 := refresh not_x in
              let not_x3 := refresh not_x2 in
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
            => let term := plug_template_ctx term template_ctx in
               let idc := reify_ident term in
               constr:(Ident (var:=var) idc)
          end
        end
      end.
    Ltac reify ident reify_ident var term :=
      reify_helper ident reify_ident var term (@var_context.nil var) tt.
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
        Inductive ident : type -> Set :=
        | opaque {t:type.opaque} (v : interp t) : ident t
        | Let_In {tx tC} : ident (tx -> (tx -> tC) -> tC)
        | Nat_succ : ident (nat -> nat)
        | nil {t} : ident (list t)
        | cons {t} : ident (t -> list t -> list t)
        | pair {A B} : ident (A -> B -> A * B)
        | fst {A B} : ident (A * B -> A)
        | snd {A B} : ident (A * B -> B)
        | bool_rect {T} : ident (T -> T -> bool -> T)
        | nat_rect {P} : ident (P -> (nat -> P -> P) -> nat -> P)
        | pred : ident (nat -> nat)
        | List_seq : ident (nat -> nat -> list nat)
        | List_repeat {A} : ident (A -> nat -> list A)
        | List_combine {A B} : ident (list A -> list B -> list (A * B))
        | List_map {A B} : ident ((A -> B) -> list A -> list B)
        | List_flat_map {A B} : ident ((A -> list B) -> list A -> list B)
        | List_partition {A} : ident ((A -> bool) -> list A -> list A * list A)
        | List_app {A} : ident (list A -> list A -> list A)
        | List_rev {A} : ident (list A -> list A)
        | List_fold_right {A B} : ident ((B -> A -> A) -> A -> list B -> A)
        | List_update_nth {T} : ident (nat -> (T -> T) -> list T -> list T)
        | List_nth_default {T} : ident (T -> list T -> nat -> T)
        | Z_runtime_mul : ident (Z -> Z -> Z)
        | Z_runtime_add : ident (Z -> Z -> Z)
        | Z_add : ident (Z -> Z -> Z)
        | Z_mul : ident (Z -> Z -> Z)
        | Z_pow : ident (Z -> Z -> Z)
        | Z_opp : ident (Z -> Z)
        | Z_div : ident (Z -> Z -> Z)
        | Z_modulo : ident (Z -> Z -> Z)
        | Z_eqb : ident (Z -> Z -> bool)
        | Z_of_nat : ident (nat -> Z).

        Definition interp {t} (idc : ident t) : type.interp t
          := match idc in ident t return type.interp t with
             | opaque _ v => v
             | Let_In tx tC => @LetIn.Let_In (type.interp tx) (fun _ => type.interp tC)
             | Nat_succ => Nat.succ
             | nil t => @Datatypes.nil (type.interp t)
             | cons t => @Datatypes.cons (type.interp t)
             | pair A B => @Datatypes.pair (type.interp A) (type.interp B)
             | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
             | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
             | bool_rect T => @Datatypes.bool_rect (fun _ => type.interp T)
             | nat_rect P => @Datatypes.nat_rect (fun _ => type.interp P)
             | pred => Nat.pred
             | List_seq => List.seq
             | List_combine A B => @List.combine (type.interp A) (type.interp B)
             | List_map A B => @List.map (type.interp A) (type.interp B)
             | List_repeat A => @List.repeat (type.interp A)
             | List_flat_map A B => @List.flat_map (type.interp A) (type.interp B)
             | List_partition A => @List.partition (type.interp A)
             | List_app A => @List.app (type.interp A)
             | List_rev A => @List.rev (type.interp A)
             | List_fold_right A B => @List.fold_right (type.interp A) (type.interp B)
             | List_update_nth T => @update_nth (type.interp T)
             | List_nth_default T => @List.nth_default (type.interp T)
             | Z_runtime_mul => runtime_mul
             | Z_runtime_add => runtime_add
             | Z_add => Z.add
             | Z_mul => Z.mul
             | Z_pow => Z.pow
             | Z_modulo => Z.modulo
             | Z_opp => Z.opp
             | Z_div => Z.div
             | Z_eqb => Z.eqb
             | Z_of_nat => Z.of_nat
             end.

        Ltac reify term :=
          (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
          lazymatch term with
          | Nat.succ => Nat_succ
          | S => Nat_succ
          | @Datatypes.nil ?T
            => let rT := type.reify T in
               constr:(@ident.nil rT)
          | @Datatypes.cons ?T
            => let rT := type.reify T in
               constr:(@ident.cons rT)
          | @Datatypes.pair ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.pair rA rB)
          | @Datatypes.fst ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.fst rA rB)
          | @Datatypes.snd ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.snd rA rB)
          | @Datatypes.bool_rect (fun _ => ?T)
            => let rT := type.reify T in
               constr:(@ident.bool_rect rT)
          | @Datatypes.nat_rect (fun _ => ?T)
            => let rT := type.reify T in
               constr:(@ident.nat_rect rT)
          | Nat.pred => ident.pred
          | List.seq => ident.List_seq
          | @List.repeat ?A
            => let rA := type.reify A in
               constr:(@ident.List_repeat rA)
          | @LetIn.Let_In ?A ?B
            => let B := lazymatch (eval cbv beta in B) with fun _ => ?B => B end in
               let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.Let_In rA rB)
          | @combine ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.List_combine rA rB)
          | @List.map ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.List_map rA rB)
          | @List.flat_map ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.List_flat_map rA rB)
          | @List.partition ?A
            => let rA := type.reify A in
               constr:(@ident.List_partition rA)
          | @List.app ?A
            => let rA := type.reify A in
               constr:(@ident.List_app rA)
          | @List.rev ?A
            => let rA := type.reify A in
               constr:(@ident.List_rev rA)
          | @List.fold_right ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.List_fold_right rA rB)
          | @update_nth ?T
            => let rT := type.reify T in
               constr:(@ident.List_update_nth rT)
          | @List.nth_default ?T
            => let rT := type.reify T in
               constr:(@ident.List_nth_default rT)
          | runtime_mul => ident.Z_runtime_mul
          | runtime_add => ident.Z_runtime_add
          | Z.add => ident.Z_add
          | Z.mul => ident.Z_mul
          | Z.pow => ident.Z_pow
          | Z.opp => ident.Z_opp
          | Z.div => ident.Z_div
          | Z.modulo => ident.Z_modulo
          | Z.eqb => ident.Z_eqb
          | Z.of_nat => ident.Z_of_nat
          | _
            => let assert_const := match goal with
                                   | _ => require_opaque_const term
                                   end in
               let T := type of term in
               let rT := type.reify_opaque T in
               constr:(@ident.opaque rT term)
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

        Notation Pair x y := (App (App (Ident ident.pair) x) y).

        Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
        Notation "'expr_let' x := A 'in' b" := (App (App (Ident ident.Let_In) A%expr) (Abs (fun x => b%expr))) : expr_scope.
        Notation "[ ]" := (Ident ident.nil) : expr_scope.
        Notation "x :: xs" := (App (App (Ident ident.cons) x%expr) xs%expr) : expr_scope.
        Notation "x" := (Ident (ident.opaque x)) (only printing, at level 9) : expr_scope.
        Notation "ls [[ n ]]"
          := (App (App (App (Ident ident.List.nth_default) _) ls%expr) (Ident (ident.opaque n%nat)))
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
        Inductive ident : type -> Set :=
        | opaque {t : type.opaque} (v : interp t) : ident t
        | Let_In {tx tC} : ident (tx -> (tx -> tC) -> tC)
        | Nat_succ : ident (nat -> nat)
        | nil {t} : ident (list t)
        | cons {t} : ident (t -> list t -> list t)
        | pair {A B} : ident (A -> B -> A * B)
        | fst {A B} : ident (A * B -> A)
        | snd {A B} : ident (A * B -> B)
        | bool_rect {T} : ident (T -> T -> bool -> T)
        | nat_rect {P} : ident (P -> (nat -> P -> P) -> nat -> P)
        | pred : ident (nat -> nat)
        | list_rect {A P} : ident (P -> (A -> list A -> P -> P) -> list A -> P)
        | List_nth_default {T} : ident (T -> list T -> nat -> T)
        | Z_runtime_mul : ident (Z -> Z -> Z)
        | Z_runtime_add : ident (Z -> Z -> Z)
        | Z_add : ident (Z -> Z -> Z)
        | Z_mul : ident (Z -> Z -> Z)
        | Z_pow : ident (Z -> Z -> Z)
        | Z_opp : ident (Z -> Z)
        | Z_div : ident (Z -> Z -> Z)
        | Z_modulo : ident (Z -> Z -> Z)
        | Z_eqb : ident (Z -> Z -> bool)
        | Z_of_nat : ident (nat -> Z).

        Definition interp {t} (idc : ident t) : type.interp t
          := match idc in ident t return type.interp t with
             | opaque _ v => v
             | Let_In tx tC => @LetIn.Let_In (type.interp tx) (fun _ => type.interp tC)
             | Nat_succ => Nat.succ
             | nil t => @Datatypes.nil (type.interp t)
             | cons t => @Datatypes.cons (type.interp t)
             | pair A B => @Datatypes.pair (type.interp A) (type.interp B)
             | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
             | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
             | bool_rect T => @Datatypes.bool_rect (fun _ => type.interp T)
             | nat_rect P => @Datatypes.nat_rect (fun _ => type.interp P)
             | pred => Nat.pred
             | list_rect A P => @Datatypes.list_rect (type.interp A) (fun _ => type.interp P)
             | List_nth_default T => @nth_default (type.interp T)
             | Z_runtime_mul => runtime_mul
             | Z_runtime_add => runtime_add
             | Z_add => Z.add
             | Z_mul => Z.mul
             | Z_pow => Z.pow
             | Z_modulo => Z.modulo
             | Z_opp => Z.opp
             | Z_div => Z.div
             | Z_eqb => Z.eqb
             | Z_of_nat => Z.of_nat
             end.

        Ltac reify term :=
          (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
          lazymatch term with
          | Nat.succ => ident.Nat_succ
          | S => ident.Nat_succ
          | @Datatypes.nil ?T
            => let rT := type.reify T in
               constr:(@ident.nil rT)
          | @Datatypes.cons ?T
            => let rT := type.reify T in
               constr:(@ident.cons rT)
          | @Datatypes.pair ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.pair rA rB)
          | @Datatypes.fst ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.fst rA rB)
          | @Datatypes.snd ?A ?B
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.snd rA rB)
          | @Datatypes.bool_rect (fun _ => ?T)
            => let rT := type.reify T in
               constr:(@ident.bool_rect rT)
          | @Datatypes.nat_rect (fun _ => ?T)
            => let rT := type.reify T in
               constr:(@ident.nat_rect rT)
          | Nat.pred => ident.pred
          | @LetIn.Let_In ?A ?B
            => let B := lazymatch (eval cbv beta in B) with fun _ => ?B => B end in
               let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.Let_In rA rB)
          | @Datatypes.list_rect ?A (fun _ => ?B)
            => let rA := type.reify A in
               let rB := type.reify B in
               constr:(@ident.list_rect rA rB)
          | @nth_default ?T
            => let rT := type.reify T in
               constr:(@ident.List_nth_default rT)
          | runtime_mul => ident.Z_runtime_mul
          | runtime_add => ident.Z_runtime_add
          | Z.add => ident.Z_add
          | Z.mul => ident.Z_mul
          | Z.pow => ident.Z_pow
          | Z.opp => ident.Z_opp
          | Z.div => ident.Z_div
          | Z.modulo => ident.Z_modulo
          | Z.eqb => ident.Z_eqb
          | Z.of_nat => ident.Z_of_nat
          | _
            => let assert_const := match goal with
                                   | _ => require_opaque_const term
                                   end in
               let T := type of term in
               let rT := type.reify_opaque T in
               constr:(@ident.opaque rT term)
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

        Notation Pair x y := (App (App (Ident ident.pair) x) y).

        Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
        Notation "'expr_let' x := A 'in' b" := (App (App (Ident ident.Let_In) A%expr) (Abs (fun x => b%expr))) : expr_scope.
        Notation "[ ]" := (Ident ident.nil) : expr_scope.
        Notation "x :: xs" := (App (App (Ident ident.cons) x%expr) xs%expr) : expr_scope.
        Notation "x" := (Ident (ident.opaque x)) (only printing, at level 9) : expr_scope.
        Notation "ls [[ n ]]"
          := (App (App (App (Ident ident.List.nth_default) _) ls%expr) (Ident (ident.opaque n%nat)))
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
      Definition transfer {var} {t} (idc : for_reification.ident t) : @expr var t
        := let List_app A :=
               list_rect
                 (fun _ => list (type.interp A) -> list (type.interp A))
                 (fun m => m)
                 (fun a l1 app_l1 m => a :: app_l1 m) in
           match idc with
           | for_reification.ident.Let_In tx tC
             => Ident ident.Let_In
           | for_reification.ident.Nat_succ
             => Ident ident.Nat_succ
           | for_reification.ident.nil t
             => Ident ident.nil
           | for_reification.ident.cons t
             => Ident ident.cons
           | for_reification.ident.pair A B
             => Ident ident.pair
           | for_reification.ident.fst A B
             => Ident ident.fst
           | for_reification.ident.snd A B
             => Ident ident.snd
           | for_reification.ident.bool_rect T
             => Ident ident.bool_rect
           | for_reification.ident.nat_rect P
             => Ident ident.nat_rect
           | for_reification.ident.pred
             => Ident ident.pred
           | for_reification.ident.opaque t v
             => Ident (ident.opaque v)
           | for_reification.ident.Z_runtime_mul
             => Ident ident.Z.runtime_mul
           | for_reification.ident.Z_runtime_add
             => Ident ident.Z.runtime_add
           | for_reification.ident.Z_add
             => Ident ident.Z.add
           | for_reification.ident.Z_mul
             => Ident ident.Z.mul
           | for_reification.ident.Z_pow
             => Ident ident.Z.pow
           | for_reification.ident.Z_opp
             => Ident ident.Z.opp
           | for_reification.ident.Z_div
             => Ident ident.Z.div
           | for_reification.ident.Z_modulo
             => Ident ident.Z.modulo
           | for_reification.ident.Z_eqb
             => Ident ident.Z.eqb
           | for_reification.ident.Z_of_nat
             => Ident ident.Z.of_nat
           | for_reification.ident.List_seq
             => ltac:(
                  let v := reify
                             var
                             (fun start len : nat
                              => nat_rect
                                   (fun _ => nat -> list nat)
                                   (fun _ => nil)
                                   (fun len seq_len start => cons start (seq_len (S start)))
                                   len start)
                  in exact v)
           | for_reification.ident.List_repeat A
             => ltac:(
                  let v := reify
                             var
                             (fun (x : type.interp A)
                              => nat_rect
                                   (fun _ => list (type.interp A))
                                   nil
                                   (fun k repeat_k => cons x repeat_k)) in
                  exact v)
           | for_reification.ident.List_combine A B
             => ltac:(
                  let v := reify
                             var
                             (list_rect
                                (fun _ => list (type.interp B) -> list (type.interp A * type.interp B))
                                (fun l' => nil)
                                (fun x tl combine_tl
                                 => list_rect
                                      (fun _ => list (type.interp A * type.interp B))
                                      nil
                                      (fun y tl' REIFICATION_STACK_OVERFLOWS_IF_THIS_IS_NAMED_UNDERSCORE (* CODBUG(https://github.com/coq/coq/issues/5448) *)
                                       => (x, y) :: combine_tl tl'))) in
                  exact v)
           | for_reification.ident.List_map A B
             => ltac:(
                  let v := reify
                             var
                             (fun f : type.interp A -> type.interp B
                              => list_rect
                                   (fun _ => list (type.interp B))
                                   nil
                                   (fun a t map_t => f a :: map_t)) in
                  exact v)
           | for_reification.ident.List_flat_map A B
             => ltac:(
                  let List_app := (eval cbv [List_app] in (List_app B)) in
                  let v := reify
                             var
                             (fun f : type.interp A -> list (type.interp B)
                              => list_rect
                                   (fun _ => list (type.interp B))
                                   nil
                                   (fun x t flat_map_t => List_app (f x) flat_map_t)) in
                  exact v)
           | for_reification.ident.List_partition A
             => ltac:(
                  let v := reify
                             var
                             (fun f : type.interp A -> bool
                              => list_rect
                                   (fun _ => list (type.interp A) * list (type.interp A))%type
                                   (nil, nil)
                                   (fun x tl partition_tl
                                    => let g := fst partition_tl in
                                       let d := snd partition_tl in
                                       if f x then (x :: g, d) else (g, x :: d))) in
                  exact v)
           | for_reification.ident.List_app A
             => ltac:(
                  let List_app := (eval cbv [List_app] in (List_app A)) in
                  let v := reify var List_app in
                  exact v)
           | for_reification.ident.List_rev A
             => ltac:(
                  let List_app := (eval cbv [List_app] in (List_app A)) in
                  let v := reify
                             var
                             (list_rect
                                (fun _ => list (type.interp A))
                                nil
                                (fun x l' rev_l' => List_app rev_l' [x])) in
                  exact v)
           | for_reification.ident.List_fold_right A B
             => ltac:(
                  let v := reify
                             var
                             (fun (f : type.interp B -> type.interp A -> type.interp A) (a0 : type.interp A)
                              => list_rect
                                   (fun _ => type.interp A)
                                   a0
                                   (fun b t fold_right_t => f b fold_right_t)) in
                  exact v)
           | for_reification.ident.List_update_nth T
             => ltac:(
                  let v := reify
                             var
                             (fun (n : nat) (f : type.interp T -> type.interp T)
                              => nat_rect
                                   (fun _ => list (type.interp T) -> list (type.interp T))
                                   (list_rect
                                      (fun _ => list (type.interp T))
                                      nil
                                      (fun x' xs' __ => f x' :: xs'))
                                   (fun n' update_nth_n'
                                    => list_rect
                                         (fun _ => list (type.interp T))
                                         nil
                                         (fun x' xs' __ => x' :: update_nth_n' xs'))
                                   n) in
                  exact v)
           | for_reification.ident.List_nth_default T
             => Ident ident.List_nth_default
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
             | Ident t idc => @ident.transfer var t idc
             | App s d f x => App (@transfer _ f) (@transfer _ x)
             | Abs s d f => Abs (fun x => @transfer d (f x))
             end.
      End with_var.

      Definition Transfer {t} (e : for_reification.Notations.Expr t) : Expr t
        := fun var => transfer (e _).
    End expr.
  End canonicalize_list_recursion.
  Notation canonicalize_list_recursion := canonicalize_list_recursion.expr.Transfer.
  Import expr.
  Import expr.default.

  Module CPS.
    Module type.
      Import Compilers.type.
      Section translate.
        Context (R : type).
        Fixpoint translate (t : type) : type
          := match t with
             | A * B => translate A * translate B
             | s -> d => translate s -> (translate d -> R) -> R
             | list A => list (translate A)
             | type_opaque _ as t
               => t
             end%ctype.
      End translate.
    End type.

    Module ident.
      Section with_var.
        Context {var : type -> Type}.
        Let Ident' := @Ident ident var.
        Local Coercion Ident' : ident >-> expr.

        Definition translate {t} {R}
                 (idc : ident t)
                 (k : @expr var (type.translate R t) -> @expr var R)
          : @expr var R
          := match idc in ident.ident t return (expr (type.translate R t) -> expr R) -> expr R with
             | ident.opaque _ _ as idc
               => fun k => k idc
             | ident.nil t
               => fun k => k (@ident.nil (type.translate R t))
             | ident.Let_In tx tC as idc
               => fun k
                  => k (λ (x : var (type.translate R tx))
                          (xk :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (((type.translate _ tx -> ((type.translate _ tC -> R) -> R)) -> ((type.translate _ tC -> R) -> R)) -> R)) ,
                        Var xk @ (λ f fk,
                                  ident.Let_In
                                    @ Var x
                                    @ (λ x, Var f @ Var x @ Var fk)))
             | ident.Nat_succ as idc
             | ident.pred as idc
             | ident.Z_opp as idc
             | ident.Z_of_nat as idc
               => fun k
                  => k (λ x k, Var k @ (idc @ Var x))
             | ident.cons t as idc
               => fun k
                  => k (λ (x : var (type.translate R t))
                          (xk :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((type.list (type.translate _ t) -> ((type.list (type.translate _ t) -> R) -> R)) -> R)),
                        Var xk @ (λ xs k,
                                  Var k @ (ident.cons @ Var x @ Var xs)))
             | ident.pair A B
               => fun k
                  => k (λ (x : var (type.translate R A))
                          (xk :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((type.translate _ B -> ((type.translate _ A * type.translate _ B -> R) -> R)) -> R)),
                        Var xk @ (λ y k,
                                  Var k @ (Var x, Var y)))
             | ident.fst A B
               => fun k
                  => k (λ (x : var (type.translate R A * type.translate R B))
                          (k : var (type.translate _ A -> R)),
                        Var k @ (ident.fst @ Var x))
             | ident.snd A B
               => fun k
                  => k (λ (x : var (type.translate R A * type.translate R B))
                          (k : var (type.translate _ B -> R)),
                        Var k @ (ident.snd @ Var x))
             | ident.bool_rect T
               => fun k
                  => k (λ (true_case : var (type.translate R T))
                          (k0 :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((type.translate R T -> ((type.bool -> (type.translate R T -> R) -> R) -> R) -> R) -> R)),
                        Var k0 @ (λ false_case k1,
                                  Var k1 @ (λ b k,
                                            ident.bool_rect
                                              @ (Var k @ Var true_case)
                                              @ (Var k @ Var false_case)
                                              @ Var b)))
             | ident.nat_rect P
               => fun k
                  => k (λ (O_case : var (type.translate R P))
                          (k0 :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (((type.nat -> ((type.translate R P -> (type.translate R P -> R) -> R) -> R) -> R) -> ((type.nat -> (type.translate R P -> R) -> R) -> R) -> R) -> R)),
                        Var k0 @ (λ S_case k1,
                                  Var k1 @ (λ n k,
                                            (@ident.nat_rect ((type.translate R P -> R) -> R))
                                              @ (λ k, Var k @ Var O_case)
                                              @ (λ n' rec k,
                                                 (Var rec)
                                                   @ (λ rec,
                                                      (Var S_case)
                                                        @ (Var n')
                                                        @ (λ K, Var K @ Var rec @ Var k)))
                                              @ (Var n)
                                              @ (Var k))))
             | ident.list_rect A P
               => fun k
                  => k (λ (nil_case : var (type.translate R P))
                          (k0 :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var (((type.translate R A -> ((type.list (type.translate R A) -> ((type.translate R P -> (type.translate R P -> R) -> R) -> R) -> R) -> R) -> R) -> ((type.list (type.translate R A) -> (type.translate R P -> R) -> R) -> R) -> R) -> R)),
                        (Var k0)
                          @ (λ cons_case k1,
                             (Var k1)
                               @ (λ ls k,
                                  (@ident.list_rect _ ((type.translate R P -> R) -> R))
                                    @ (λ k, Var k @ Var nil_case)
                                    @ (λ x xs rec k,
                                       (Var rec)
                                         @ (λ rec,
                                            (Var cons_case)
                                              @ (Var x)
                                              @ (λ K,
                                                 (Var K)
                                                   @ (Var xs)
                                                   @ (λ K, Var K @ Var rec @ Var k))))
                                    @ (Var ls)
                                    @ (Var k))))
             | ident.List_nth_default A
               => fun k
                  => k (λ (default : var (type.translate R A))
                          (k0 :
                             (* ignore this line; it's to work around lack of fixpoint refolding in type inference *) var ((type.list (type.translate R A) -> ((type.nat -> (type.translate R A -> R) -> R) -> R) -> R) -> R)),
                        (Var k0)
                          @ (λ ls k1,
                             (Var k1)
                               @ (λ n k,
                                  Var k @ (ident.List.nth_default @ Var default @ Var ls @ Var n))))
             | ident.Z_runtime_mul as idc
             | ident.Z_runtime_add as idc
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_pow as idc
             | ident.Z_div as idc
             | ident.Z_modulo as idc
             | ident.Z_eqb as idc
               => fun k
                  => k (λ x xk,
                        (Var xk)
                          @ (λ y yk,
                             (Var yk @ (idc @ Var x @ Var y))))
             end%expr k.
      End with_var.
    End ident.

    Module expr.
      Section with_var.
        Context {var : type -> Type}.
        Notation var' R := (fun t => var (type.translate R t)).
        Section with_R.
          Context {R : type}.

          Fixpoint translate {t}
                   (e : @expr (var' R) t)
                   (k : @expr var (type.translate R t) -> @expr var R)
                   {struct e}
            : @expr var R
            := match e in expr.expr t return (expr (type.translate R t) -> expr R) -> expr R with
               | Var t v
                 => fun k => k (Var v)
               | Ident t idc => ident.translate idc
               | App s d f x
                 => fun k
                    => @translate
                         _ f
                         (fun fv
                          => @translate
                               _ x
                               (fun xv
                                => App (App fv xv) (Abs (fun v => k (Var v)))))
               | Abs s d f
                 => fun k
                    => k (Abs (fun (x : var (type.translate R s))
                               => Abs (fun (k : var (type.translate _ _ -> _))
                                       => @translate
                                            _ (f x)
                                            (fun v => App (Var k) v))))
               end k.

          Fixpoint collect_translation_function_types t
            := match t return Type with
               | type.arrow s d
                 => collect_translation_function_types d
                    * (var s -> var (type.translate R s))
               | _ => unit
               end%type.
        End with_R.

        Fixpoint translate_under_binders {t}
                 (R:=type.final_codomain t)
                 (e : @expr (var' R) t)
                 (k_vars : @collect_translation_function_types (type.final_codomain t) t)
                 (k : @expr var (type.translate R (type.final_codomain t)) -> @expr var R)
                 {struct t}
          : @expr var t
          := match t return @expr (var' (type.final_codomain t)) t -> (collect_translation_function_types t) -> (expr (type.translate _ (type.final_codomain t)) -> expr (type.final_codomain t)) -> expr t with
             | type.arrow s d
               => fun e '((k_vars, ks) : collect_translation_function_types d * _) k
                  => Abs (fun x : var s
                          => @translate_under_binders d (e @ Var (ks x))%expr k_vars k)
             | t
               => fun e _ k
                  => @translate (type.final_codomain t) t e k
             end e k_vars k.
      End with_var.

      Definition Translate {R t} (e : Expr t) (k : forall var, @expr var (type.translate R t) -> @expr var R)
        : Expr R
        := fun var => @translate var R t (e _) (k _).

      Definition TranslateUnderBinders {t} (e : Expr t)
                 (k : forall var,
                     @collect_translation_function_types var (type.final_codomain t) t
                     * (@expr var (type.translate (type.final_codomain t) (type.final_codomain t)) -> @expr var (type.final_codomain t)))
        : Expr t
        := fun var => @translate_under_binders var t (e _) (fst (k _)) (snd (k _)).
    End expr.
  End CPS.

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

    Definition invert_Ident {t} (e : @expr var t) : option (ident t)
      := match e with
         | Ident t idc => Some idc
         | _ => None
         end.

    Definition invert_AppIdent {d} (e : @expr var d) : option { s : _ & @ident (s -> d) * @expr var s }%type
      := match invert_App e with
         | Some (existT s (f, x))
           => match invert_Ident f with
              | Some f' => Some (existT _ s (f', x))
              | None => None
              end
         | None => None
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
      := match invert_App2 e with
         | Some (existT (s1, s2) (f, x, y))
           => match invert_Ident f with
              | Some idc
                => match idc in ident t
                         return if_arrow_s expr t
                                -> if_arrow_d (if_arrow_s expr) t
                                -> option (if_arrow_d (if_arrow_d expr_prod) t)
                   with
                   | ident.pair A B => fun x y => Some (x, y)
                   | _ => fun _ _ => None
                   end x y
              | None => None
              end
         | None => None
         end.

    (* if we want more code for the below, I would suggest [reify_base_type] and [reflect_base_type] *)
    Definition reify_opaque {t} (v : type.interp (type.type_opaque t)) : @expr var (type.type_opaque t)
      := Ident (ident.opaque v).
    Definition reflect_opaque {t} (e : @expr var (type.type_opaque t)) : option (type.interp (type.type_opaque t))
      := match invert_Ident e with
         | Some idc
           => match idc in ident t return option (type.interp t) with
              | ident.opaque _ v => Some v
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
         | Ident t idc
           => match idc in ident t return option (list_expr t) with
              | ident.nil _ => Some nil
              | _ => None
              end
         | App (type.list s) d f xs
               (* WHY reflect xs before x? *)
           => match @reflect_list s xs return _ with
              | Some xs
                => match invert_AppIdent f return option (list_expr d) with
                   | Some (existT s' (idc, x))
                     => match idc in ident t
                              return if_arrow_s expr t
                                     -> if_arrow_d (if_arrow_s list_expr) t
                                     -> option (if_arrow_d (if_arrow_d list_expr) t)
                        with
                        | ident.cons A => fun x xs => Some (cons x xs)
                        | _ => fun _ _ => None
                        end x xs
                   | _ => None
                   end
              | None => None
              end
         | _ => None
         end.
  End invert.

  Section gallina_reify.
    Context {var : type -> Type}.
    Definition reify_list {t} (ls : list (@expr var t)) : @expr var (type.list t)
      := list_rect
           (fun _ => _)
           (Ident ident.nil)
           (fun x _ xs => App (App (Ident ident.cons) x) xs)
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
           | type.type_opaque _ as t
             => type.interp t
           end%type.
      Definition value_step (value : type -> Type) (t : type)
        := match t return Type with
           | type.arrow _ _ as t
             => value_prestep value t
           | type.prod _ _ as t
           | type.list _ as t
           | type.type_opaque _ as t
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
             | type.type_opaque _ as t
               => fun x : expr t + type.interp t
                  => match x with
                     | inl v => v
                     | inr v => Ident (ident.opaque v)
                     end
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
                | type.type_opaque _ as t
                  => fun v : expr t
                     => let inr := @inr (expr t) (value_prestep (value var) t) in
                        let inl := @inl (expr t) (value_prestep (value var) t) in
                        match reflect_opaque v with
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
             | type.type_opaque _ as t
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
        Definition interp {t} (idc : ident t) : value var t
          := match idc in ident t return value var t with
             | ident.Let_In tx tC
               => interp_let_in
             | ident.nil t
               => inr (@nil (value var t))
             | ident.opaque t v
               => inr v
             | ident.cons t as idc
               => fun x (xs : expr (type.list t) + list (value var t))
                  => match xs return expr (type.list t) + list (value var t) with
                     | inr xs => inr (cons x xs)
                     | _ => expr.reflect (Ident idc) x xs
                     end
             | ident.pair A B as idc
               => fun x y => @inr _ (value var A * value var B) (x, y)
             | ident.fst A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => fst x
                     | _ => expr.reflect (Ident idc) x
                     end
             | ident.snd A B as idc
               => fun x : expr (A * B) + value var A * value var B
                  => match x with
                     | inr x => snd x
                     | _ => expr.reflect (Ident idc) x
                     end
             | ident.bool_rect T as idc
               => fun true_case false_case (b : expr type.bool + bool)
                  => match b with
                     | inr b => @bool_rect (fun _ => value var T) true_case false_case b
                     | _ => expr.reflect (Ident idc) true_case false_case b
                     end
             | ident.nat_rect P as idc
               => fun (O_case : value var P)
                      (S_case : expr type.nat + nat -> value var P -> value var P)
                      (n : expr type.nat + nat)
                  => match n with
                     | inr n => @nat_rect (fun _ => value var P)
                                          O_case
                                          (fun n' => S_case (inr n'))
                                          n
                     | _ => expr.reflect (Ident idc) O_case S_case n
                     end
             | ident.list_rect A P as idc
               => fun (nil_case : value var P)
                      (cons_case : value var A -> expr (type.list A) + list (value var A) -> value var P -> value var P)
                      (ls : expr (type.list A) + list (value var A))
                  => match ls with
                     | inr ls => @list_rect
                                   (value var A)
                                   (fun _ => value var P)
                                   nil_case
                                   (fun x xs rec => cons_case x (inr xs) rec)
                                   ls
                     | _ => expr.reflect (Ident idc) nil_case cons_case ls
                     end
             | ident.List.nth_default A as idc
               => fun (default : value var A)
                      (ls : expr _ + list (value var A))
                      (idx : expr _ + nat)
                  => match ls, idx return value var A with
                     | inr ls, inr idx => List.nth_default default ls idx
                     | _, _ => expr.reflect (Ident idc) default ls idx
                     end
             | ident.pred as idc
             | ident.Nat_succ as idc
             | ident.Z_of_nat as idc
             | ident.Z_opp as idc
               => fun x : expr _ + type.interp _
                  => match x return expr _ + type.interp _ with
                     | inr x => inr (ident.interp idc x)
                     | _ => expr.reflect (Ident idc) x
                     end
             | ident.Z_add as idc
             | ident.Z_mul as idc
             | ident.Z_pow as idc
             | ident.Z_div as idc
             | ident.Z_modulo as idc
             | ident.Z_eqb as idc
               => fun (x y : expr _ + type.interp _)
                  => match x, y return expr _ + type.interp _ with
                     | inr x, inr y => inr (ident.interp idc x y)
                     | _, _ => expr.reflect (Ident idc) x y
                     end
             | ident.Z_runtime_mul as idc
               => fun (x y : expr _ + type.interp _)
                  => let default := expr.reflect (Ident idc) x y in
                     match x, y return expr _ + type.interp _ with
                     | inr x, inr y => inr (ident.interp idc x y)
                     | inr x, inl e
                     | inl e, inr x
                       => if Z.eqb x 0
                          then inr 0%Z
                          else if Z.eqb x 1
                               then inl e
                               else default
                     | inl _, inl _ => default
                     end
             | ident.Z_runtime_add as idc
               => fun (x y : expr _ + type.interp _)
                  => let default := expr.reflect (Ident idc) x y in
                     match x, y return expr _ + type.interp _ with
                     | inr x, inr y => inr (ident.interp idc x y)
                     | inr x, inl e
                     | inl e, inr x
                       => if Z.eqb x 0
                          then inl e
                          else default
                     | inl _, inl _ => default
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
         | Ident t idc => partial.ident.interp idc
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
Definition w (i:nat) : Z := 2^Qceiling((25+1/2)*i).

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
Import expr.
Import for_reification.Notations.Reification.

Notation "x + y"
  := (App (App (Ident ident.Z.runtime_add) x%RT_expr) y%RT_expr)
     : RT_expr_scope.
Notation "x * y"
  := (App (App (Ident ident.Z.runtime_mul) x%RT_expr) y%RT_expr)
     : RT_expr_scope.
Notation "x + y"
  := (App (App (Ident ident.Z.runtime_add) x%RT_expr) y%RT_expr)
     : expr_scope.
Notation "x * y"
  := (App (App (Ident ident.Z.runtime_mul) x%RT_expr) y%RT_expr)
     : expr_scope.
Notation "x" := (Var x) (only printing, at level 9) : expr_scope.
Open Scope RT_expr_scope.

Require Import AdmitAxiom.

Example base_51_carry_mul (*(f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : Z)
        (f:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)
        (g:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)*) (f g : list Z)
        (n:=5%nat)
        (Hf : length f = n) (Hg : length g = n)
  : { fg : list Z | (eval w n fg) mod (2^255-19)
                    = (eval w n f * eval w n g) mod (2^255-19) }.
  (* manually assign names to limbs for pretty-printing *)
  eexists ?[fg].
  erewrite <-eval_mulmod with (s:=2^255) (c:=[(1,19)])
    by (try assumption; try eapply pow_ceil_mul_nat_nonzero; vm_decide).
(*   eval w ?fg mod (2 ^ 255 - 19) = *)
(*   eval w *)
(*     (mulmod w (2^255) [(1, 19)] (f9,f8,f7,f6,f5,f4,f3,f2,f1,f0) *)
(*        (g9,g8,g7,g6,g5,g4,g3,g2,g1,g0)) mod (2^255 - 19) *)
  etransitivity; (* work around [rewrite] being stupid about evars *)
    [
    | rewrite <- eval_chained_carries with (s:=2^255) (c:=[(1,19)]) (idxs:=(seq 0 (pred n) ++ [0; 1])%list%nat) (modulo:=Z.modulo) (div:=Z.div)
      by (try assumption; auto using Z.div_mod; try (intros; eapply pow_ceil_mul_nat_divide_nonzero); try eapply pow_ceil_mul_nat_nonzero; try vm_decide);
      reflexivity ].
  eapply f_equal2; [|trivial]. eapply f_equal.
(*   ?fg = *)
(*   mulmod w (2 ^ 255) [(1, 19)] (f9, f8, f7, f6, f5, f4, f3, f2, f1, f0) *)
(*     (g9, g8, g7, g6, g5, g4, g3, g2, g1, g0) *)
  (*cbv [f g].*)
  cbv [w Qceiling Qfloor Qopp Qnum Qdiv Qplus inject_Z Qmult Qinv Qden Pos.mul].
  let ev := match goal with |- ?ev = _ => ev end in
  set (e := ev).
  rewrite <- (expand_list_correct n (-1)%Z f), <- (expand_list_correct n (-1)%Z g) by assumption; subst e.
  etransitivity.
  Focus 2.
  {
    repeat match goal with H : _ |- _ => clear H end; revert f g.
    lazymatch goal with
    | [ |- forall f g, ?ev = @?RHS f g ]
      => refine (fun f g => f_equal (fun F => F f g) (_ : _ = RHS))
    end.
    cbv [n expand_list expand_list_helper].
    cbv delta [chained_carries carry carry_reduce Associational.carry carryterm mulmod w to_associational mul to_associational reduce from_associational add_to_nth zeros place split].
    Locate Ltac Reify.
    assert True.
    { let v := Reify ((fun x => 2^x) 255)%Z in
      pose v as E.
      vm_compute in E.
      pose (PartialReduce (canonicalize_list_recursion E)) as E'.
      vm_compute in E'.
      lazymatch (eval cbv delta [E'] in E') with
      | (fun var => Ident (ident.opaque ?v)) => idtac
      end.
      constructor. }
    assert True.
    { let v := Reify (fun y : Z
                      => (fun k : Z * Z -> Z * Z
                          => let x := (y * y)%RT in
                             let z := (x * x)%RT in
                             k (z, z))
                           (fun v => v)) in
      pose v as E.
      vm_compute in E.
      pose (PartialReduce (canonicalize_list_recursion E)) as E'.
      vm_compute in E'.
      lazymatch (eval cbv delta [E'] in E') with
      | (fun var : type -> Type =>
           (λ x : var (type.type_opaque type.Z),
                  expr_let x0 := (Var x * Var x)%RT_expr in
                expr_let x1 := (Var x0 * Var x0)%RT_expr in
                (Var x1, Var x1))%expr) => idtac
      end.
      constructor. }
    assert True.
    { let v := Reify (fun y : Z
                      => let x := let x := (y * y)%RT in
                                  (x * x)%RT in
                         let z := let z := (x * x)%RT in
                                  (z * z)%RT in
                         (z * z)%RT) in
      pose v as E.
      vm_compute in E.
      pose (PartialReduce (CPS.expr.TranslateUnderBinders (canonicalize_list_recursion E) (fun var => (tt, id, id)))) as E'.
      vm_compute in E'.
      lazymatch (eval cbv delta [E'] in E') with
      | (fun var : type -> Type =>
           (λ x : var (type.type_opaque type.Z),
                  expr_let x0 := Var x * Var x in
                expr_let x1 := Var x0 * Var x0 in
                expr_let x2 := Var x1 * Var x1 in
                expr_let x3 := Var x2 * Var x2 in
                Var x3 * Var x3)%RT_expr%expr)
        => idtac
      end.
      constructor. }
    Reify_rhs ().
    reflexivity.
  } Unfocus.
  cbv beta.
  let e := match goal with |- _ = expr.Interp _ ?e _ _ => e end in
  set (E := e).
  Time let E' := constr:(PartialReduce (CPS.expr.TranslateUnderBinders (canonicalize_list_recursion E) (fun var => (tt, id, id, id)))) in
       let E' := (eval lazy in E') in
       pose E' as E''.
  transitivity (Interp E'' f g); [ clear E | admit ].
  reflexivity.
  (*cbv -[runtime_mul runtime_add]; cbv [runtime_mul runtime_add].
  ring_simplify_subterms.*)
(* ?fg =
 (f0*g9+ f1*g8+    f2*g7+    f3*g6+    f4*g5+    f5*g4+    f6*g3+    f7*g2+    f8*g1+    f9*g0,
  f0*g8+ 2*f1*g7+  f2*g6+    2*f3*g5+  f4*g4+    2*f5*g3+  f6*g2+    2*f7*g1+  f8*g0+    38*f9*g9,
  f0*g7+ f1*g6+    f2*g5+    f3*g4+    f4*g3+    f5*g2+    f6*g1+    f7*g0+    19*f8*g9+ 19*f9*g8,
  f0*g6+ 2*f1*g5+  f2*g4+    2*f3*g3+  f4*g2+    2*f5*g1+  f6*g0+    38*f7*g9+ 19*f8*g8+ 38*f9*g7,
  f0*g5+ f1*g4+    f2*g3+    f3*g2+    f4*g1+    f5*g0+    19*f6*g9+ 19*f7*g8+ 19*f8*g7+ 19*f9*g6,
  f0*g4+ 2*f1*g3+  f2*g2+    2*f3*g1+  f4*g0+    38*f5*g9+ 19*f6*g8+ 38*f7*g7+ 19*f8*g6+ 38*f9*g5,
  f0*g3+ f1*g2+    f2*g1+    f3*g0+    19*f4*g9+ 19*f5*g8+ 19*f6*g7+ 19*f7*g6+ 19*f8*g5+ 19*f9*g4,
  f0*g2+ 2*f1*g1+  f2*g0+    38*f3*g9+ 19*f4*g8+ 38*f5*g7+ 19*f6*g6+ 38*f7*g5+ 19*f8*g4+ 38*f9*g3,
  f0*g1+ f1*g0+    19*f2*g9+ 19*f3*g8+ 19*f4*g7+ 19*f5*g6+ 19*f6*g5+ 19*f7*g4+ 19*f8*g3+ 19*f9*g2,
  f0*g0+ 38*f1*g9+ 19*f2*g8+ 38*f3*g7+ 19*f4*g6+ 38*f5*g5+ 19*f6*g4+ 38*f7*g3+ 19*f8*g2+ 38*f9*g1) *)
  (*trivial.*)
Defined.
Eval cbv [proj1_sig base_51_carry_mul] in (fun f g Hf Hg => proj1_sig (base_51_carry_mul f g Hf Hg)).
(*     = fun (f g : list Z) (_ : length f = 5%nat) (_ : length g = 5%nat) =>
       expr.Interp (@ident.interp)
         (fun var : type -> Type =>
          (λ x x0 : var (type.list type.Z),
           expr_let y := x [[0]] * x0 [[4]] +
                         (2 * (x [[1]] * x0 [[3]]) +
                          (67108864 * (x [[1]] * x0 [[4]]) +
                           (x [[2]] * x0 [[2]] +
                            (67108864 * (x [[2]] * x0 [[3]]) +
                             (2251799813685248 * (x [[2]] * x0 [[4]]) +
                              (2 * (x [[3]] * x0 [[1]]) +
                               (67108864 * (x [[3]] * x0 [[2]]) +
                                (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                 (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                  (x [[4]] * x0 [[0]] +
                                   (67108864 * (x [[4]] * x0 [[1]]) +
                                    (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                     (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                      5070602400912917605986812821504 * (x [[4]] * x0 [[4]])))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y @ 67108864 in
           expr_let y2 := x [[0]] * x0 [[3]] +
                          (x [[1]] * x0 [[2]] + (x [[2]] * x0 [[1]] + x [[3]] * x0 [[0]])) in
           expr_let _ := Ident ident.Z.div @ y2 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y2 @ 67108864 in
           expr_let y5 := x [[0]] * x0 [[2]] + (2 * (x [[1]] * x0 [[1]]) + x [[2]] * x0 [[0]]) in
           expr_let _ := Ident ident.Z.div @ y5 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y5 @ 67108864 in
           expr_let y8 := x [[0]] * x0 [[1]] + x [[1]] * x0 [[0]] in
           expr_let _ := Ident ident.Z.div @ y8 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y8 @ 67108864 in
           expr_let y11 := x [[0]] * x0 [[0]] in
           expr_let y12 := Ident ident.Z.div @ y11 @ 67108864 in
           expr_let y13 := Ident ident.Z.modulo @ y11 @ 67108864 in
           expr_let y14 := x [[0]] * x0 [[4]] +
                           (2 * (x [[1]] * x0 [[3]]) +
                            (67108864 * (x [[1]] * x0 [[4]]) +
                             (x [[2]] * x0 [[2]] +
                              (67108864 * (x [[2]] * x0 [[3]]) +
                               (2251799813685248 * (x [[2]] * x0 [[4]]) +
                                (2 * (x [[3]] * x0 [[1]]) +
                                 (67108864 * (x [[3]] * x0 [[2]]) +
                                  (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                   (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                    (x [[4]] * x0 [[0]] +
                                     (67108864 * (x [[4]] * x0 [[1]]) +
                                      (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                       (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                        5070602400912917605986812821504 * (x [[4]] * x0 [[4]])))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y14 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y14 @ 33554432 in
           expr_let y17 := x [[0]] * x0 [[3]] +
                           (x [[1]] * x0 [[2]] + (x [[2]] * x0 [[1]] + x [[3]] * x0 [[0]])) in
           expr_let _ := Ident ident.Z.div @ y17 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y17 @ 33554432 in
           expr_let y20 := x [[0]] * x0 [[2]] + (2 * (x [[1]] * x0 [[1]]) + x [[2]] * x0 [[0]]) in
           expr_let _ := Ident ident.Z.div @ y20 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y20 @ 33554432 in
           expr_let y23 := y12 + (x [[0]] * x0 [[1]] + x [[1]] * x0 [[0]]) in
           expr_let y24 := Ident ident.Z.div @ y23 @ 33554432 in
           expr_let y25 := Ident ident.Z.modulo @ y23 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y13 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y13 @ 33554432 in
           expr_let y28 := x [[0]] * x0 [[4]] +
                           (2 * (x [[1]] * x0 [[3]]) +
                            (67108864 * (x [[1]] * x0 [[4]]) +
                             (x [[2]] * x0 [[2]] +
                              (67108864 * (x [[2]] * x0 [[3]]) +
                               (2251799813685248 * (x [[2]] * x0 [[4]]) +
                                (2 * (x [[3]] * x0 [[1]]) +
                                 (67108864 * (x [[3]] * x0 [[2]]) +
                                  (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                   (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                    (x [[4]] * x0 [[0]] +
                                     (67108864 * (x [[4]] * x0 [[1]]) +
                                      (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                       (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                        5070602400912917605986812821504 * (x [[4]] * x0 [[4]])))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y28 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y28 @ 67108864 in
           expr_let y31 := x [[0]] * x0 [[3]] +
                           (x [[1]] * x0 [[2]] + (x [[2]] * x0 [[1]] + x [[3]] * x0 [[0]])) in
           expr_let _ := Ident ident.Z.div @ y31 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y31 @ 67108864 in
           expr_let y34 := y24 +
                           (x [[0]] * x0 [[2]] + (2 * (x [[1]] * x0 [[1]]) + x [[2]] * x0 [[0]])) in
           expr_let y35 := Ident ident.Z.div @ y34 @ 67108864 in
           expr_let y36 := Ident ident.Z.modulo @ y34 @ 67108864 in
           expr_let _ := Ident ident.Z.div @ y25 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y25 @ 67108864 in
           expr_let _ := Ident ident.Z.div @ y13 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y13 @ 67108864 in
           expr_let y41 := x [[0]] * x0 [[4]] +
                           (2 * (x [[1]] * x0 [[3]]) +
                            (67108864 * (x [[1]] * x0 [[4]]) +
                             (x [[2]] * x0 [[2]] +
                              (67108864 * (x [[2]] * x0 [[3]]) +
                               (2251799813685248 * (x [[2]] * x0 [[4]]) +
                                (2 * (x [[3]] * x0 [[1]]) +
                                 (67108864 * (x [[3]] * x0 [[2]]) +
                                  (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                   (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                    (x [[4]] * x0 [[0]] +
                                     (67108864 * (x [[4]] * x0 [[1]]) +
                                      (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                       (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                        5070602400912917605986812821504 * (x [[4]] * x0 [[4]])))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y41 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y41 @ 33554432 in
           expr_let y44 := y35 +
                           (x [[0]] * x0 [[3]] +
                            (x [[1]] * x0 [[2]] + (x [[2]] * x0 [[1]] + x [[3]] * x0 [[0]]))) in
           expr_let y45 := Ident ident.Z.div @ y44 @ 33554432 in
           expr_let y46 := Ident ident.Z.modulo @ y44 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y36 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y36 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y25 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y25 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y13 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y13 @ 33554432 in
           expr_let y53 := y45 +
                           (x [[0]] * x0 [[4]] +
                            (2 * (x [[1]] * x0 [[3]]) +
                             (67108864 * (x [[1]] * x0 [[4]]) +
                              (x [[2]] * x0 [[2]] +
                               (67108864 * (x [[2]] * x0 [[3]]) +
                                (2251799813685248 * (x [[2]] * x0 [[4]]) +
                                 (2 * (x [[3]] * x0 [[1]]) +
                                  (67108864 * (x [[3]] * x0 [[2]]) +
                                   (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                    (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                     (x [[4]] * x0 [[0]] +
                                      (67108864 * (x [[4]] * x0 [[1]]) +
                                       (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                        (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                         5070602400912917605986812821504 * (x [[4]] * x0 [[4]]))))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y53 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y53 @ 67108864 in
           expr_let _ := Ident ident.Z.div @ y46 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y46 @ 67108864 in
           expr_let _ := Ident ident.Z.div @ y36 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y36 @ 67108864 in
           expr_let _ := Ident ident.Z.div @ y25 @ 67108864 in
           expr_let _ := Ident ident.Z.modulo @ y25 @ 67108864 in
           expr_let y62 := Ident ident.Z.div @ y13 @ 67108864 in
           expr_let y63 := Ident ident.Z.modulo @ y13 @ 67108864 in
           expr_let y64 := y45 +
                           (x [[0]] * x0 [[4]] +
                            (2 * (x [[1]] * x0 [[3]]) +
                             (67108864 * (x [[1]] * x0 [[4]]) +
                              (x [[2]] * x0 [[2]] +
                               (67108864 * (x [[2]] * x0 [[3]]) +
                                (2251799813685248 * (x [[2]] * x0 [[4]]) +
                                 (2 * (x [[3]] * x0 [[1]]) +
                                  (67108864 * (x [[3]] * x0 [[2]]) +
                                   (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                    (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                     (x [[4]] * x0 [[0]] +
                                      (67108864 * (x [[4]] * x0 [[1]]) +
                                       (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                        (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                         5070602400912917605986812821504 * (x [[4]] * x0 [[4]]))))))))))))))) in
           expr_let _ := Ident ident.Z.div @ y64 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y64 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y46 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y46 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y36 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y36 @ 33554432 in
           expr_let y71 := y62 + y25 in
           expr_let y72 := Ident ident.Z.div @ y71 @ 33554432 in
           expr_let y73 := Ident ident.Z.modulo @ y71 @ 33554432 in
           expr_let _ := Ident ident.Z.div @ y63 @ 33554432 in
           expr_let _ := Ident ident.Z.modulo @ y63 @ 33554432 in
           y63
           :: y73
              :: y72 + y36
                 :: y46
                    :: y45 +
                       (x [[0]] * x0 [[4]] +
                        (2 * (x [[1]] * x0 [[3]]) +
                         (67108864 * (x [[1]] * x0 [[4]]) +
                          (x [[2]] * x0 [[2]] +
                           (67108864 * (x [[2]] * x0 [[3]]) +
                            (2251799813685248 * (x [[2]] * x0 [[4]]) +
                             (2 * (x [[3]] * x0 [[1]]) +
                              (67108864 * (x [[3]] * x0 [[2]]) +
                               (4503599627370496 * (x [[3]] * x0 [[3]]) +
                                (151115727451828646838272 * (x [[3]] * x0 [[4]]) +
                                 (x [[4]] * x0 [[0]] +
                                  (67108864 * (x [[4]] * x0 [[1]]) +
                                   (2251799813685248 * (x [[4]] * x0 [[2]]) +
                                    (151115727451828646838272 * (x [[4]] * x0 [[3]]) +
                                     5070602400912917605986812821504 * (x [[4]] * x0 [[4]])))))))))))))))
                       :: [])%expr) f g
     : forall f g : list Z, length f = 5%nat -> length g = 5%nat -> list Z
*)
