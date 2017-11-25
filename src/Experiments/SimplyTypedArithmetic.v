(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Crypto.Util.Tactics.UniquePose Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil Coq.Lists.List Crypto.Util.NatUtil.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
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
End Positional. End Positional.

Module Compilers.
  Module type.
    Inductive type := unit | prod (A B : type) | arrow (s d : type) | list (A : type) | nat | Z | bool.

    Fixpoint interp (t : type)
      := match t with
         | unit => Datatypes.unit
         | prod A B => interp A * interp B
         | arrow A B => interp A -> interp B
         | list A => Datatypes.list (interp A)
         | nat => Datatypes.nat
         | Z => BinInt.Z
         | bool => Datatypes.bool
         end%type.

    Ltac reify ty :=
      lazymatch eval cbv beta in ty with
      | Datatypes.unit => unit
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
      | Datatypes.nat => nat
      | Datatypes.bool => bool
      | BinInt.Z => Z
      end.

    Module Export Notations.
      Delimit Scope ctype_scope with ctype.
      Bind Scope ctype_scope with type.
      Notation "()" := unit : ctype_scope.
      Notation "A * B" := (prod A B) : ctype_scope.
      Notation "A -> B" := (arrow A B) : ctype_scope.
      Notation type := type.
    End Notations.
  End type.
  Export type.Notations.

  Module op.
    Import type.
    Inductive op : type -> type -> Set :=
    | Const {t} (v : interp t) : op unit t
    | Let_In {tx tC} : op (tx * (tx -> tC)) tC
    | App {s d} : op ((s -> d) * s) d
    | S : op nat nat
    | nil {t} : op unit (list t)
    | cons {t} : op (t * list t) (list t)
    | fst {A B} : op (A * B) A
    | snd {A B} : op (A * B) B
    | bool_rect {T} : op (T * T * bool) T
    | nat_rect {P} : op (P * (nat -> P -> P) * nat) P
    | pred : op nat nat
    | List_seq : op (nat * nat) (list nat)
    | List_repeat {A} : op (A * nat) (list A)
    | List_combine {A B} : op (list A * list B) (list (A * B))
    | List_map {A B} : op ((A -> B) * list A) (list B)
    | List_flat_map {A B} : op ((A -> list B) * list A) (list B)
    | List_partition {A} : op ((A -> bool) * list A) (list A * list A)
    | List_app {A} : op (list A * list A) (list A)
    | List_fold_right {A B} : op ((B -> A -> A) * A * list B) A
    | List_update_nth {T} : op (nat * (T -> T) * list T) (list T)
    | Z_runtime_mul : op (Z * Z) Z
    | Z_runtime_add : op (Z * Z) Z
    | Z_add : op (Z * Z) Z
    | Z_mul : op (Z * Z) Z
    | Z_pow : op (Z * Z) Z
    | Z_opp : op Z Z
    | Z_div : op (Z * Z) Z
    | Z_modulo : op (Z * Z) Z
    | Z_eqb : op (Z * Z) bool
    | Z_of_nat : op nat Z.

    Notation curry2 f
      := (fun '(a, b) => f a b).
    Notation curry3 f
      := (fun '(a, b, c) => f a b c).

    Definition interp {s d} (opc : op s d) : type.interp s -> type.interp d
      := match opc in op s d return type.interp s -> type.interp d with
         | Const t v => fun _ => v
         | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
         | App s d
           => fun '((f, x) : (type.interp s -> type.interp d) * type.interp s)
              => f x
         | S => Datatypes.S
         | nil t => fun _ => @Datatypes.nil (type.interp t)
         | cons t => curry2 (@Datatypes.cons (type.interp t))
         | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
         | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
         | bool_rect T => curry3 (@Datatypes.bool_rect (fun _ => type.interp T))
         | nat_rect P => curry3 (@Datatypes.nat_rect (fun _ => type.interp P))
         | pred => Nat.pred
         | List_seq => curry2 List.seq
         | List_combine A B => curry2 (@List.combine (type.interp A) (type.interp B))
         | List_map A B => curry2 (@List.map (type.interp A) (type.interp B))
         | List_repeat A => curry2 (@List.repeat (type.interp A))
         | List_flat_map A B => curry2 (@List.flat_map (type.interp A) (type.interp B))
         | List_partition A => curry2 (@List.partition (type.interp A))
         | List_app A => curry2 (@List.app (type.interp A))
         | List_fold_right A B => curry3 (@List.fold_right (type.interp A) (type.interp B))
         | List_update_nth T => curry3 (@update_nth (type.interp T))
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

    Module List.
      Notation seq := List_seq.
      Notation repeat := List_repeat.
      Notation combine := List_combine.
      Notation map := List_map.
      Notation flat_map := List_flat_map.
      Notation partition := List_partition.
      Notation app := List_app.
      Notation fold_right := List_fold_right.
      Notation update_nth := List_update_nth.
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

    Module Export Notations.
      Notation op := op.
    End Notations.
  End op.
  Export op.Notations.

  Inductive expr {var : type -> Type} : type -> Type :=
  | TT : expr ()
  | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
  | Var {t} (v : var t) : expr t
  | Op {s d} (opc : op s d) (args : expr s) : expr d
  | Abs {s d} (f : var s -> expr d) : expr (s -> d).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
  Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
  Notation "( )" := TT : expr_scope.
  Notation "()" := TT : expr_scope.
  Notation "'expr_let' x := A 'in' b" := (Op op.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.
  Notation "f ‘’ x" := (Op op.App (f, x)%expr) (at level 200) : expr_scope.

  Definition Expr t := forall var, @expr var t.

  Fixpoint interp {t} (e : @expr type.interp t) : type.interp t
    := match e with
       | TT => tt
       | Pair A B a b => (interp a, interp b)
       | Var t v => v
       | Op s d opc args => op.interp opc (interp args)
       | Abs s d f => fun v => interp (f v)
       end.

  Definition Interp {t} (e : Expr t) := interp (e _).

  Ltac is_known_const_cps2 term on_success on_failure :=
    let recurse term := is_known_const_cps2 term on_success on_failure in
    lazymatch term with
    | S ?term => recurse term
    | O => on_success ()
    | Z0 => on_success ()
    | Zpos ?p => recurse p
    | Zneg ?p => recurse p
    | xI ?p => recurse p
    | xO ?p => recurse p
    | xH => on_success ()
    | ?term => on_failure term
    end.
  Ltac require_known_const term :=
    is_known_const_cps2 term ltac:(fun _ => idtac) ltac:(fun term => fail 0 "Not a known const:" term).
  Ltac is_known_const term :=
    is_known_const_cps2 term ltac:(fun _ => true) ltac:(fun _ => false).

  Definition Uncurry0 {A var} (opc : op type.unit A) : @expr var A
    := Op opc TT.
  Definition Uncurry1 {A B var} (opc : op A B) : @expr var (A -> B)
    := λ a, Op opc (Var a).
  Definition Uncurry2 {A B C var} (opc : op (A * B) C) : @expr var (A -> B -> C)
    := λ a b, Op opc (Var a, Var b).
  Definition Uncurry3 {A B C D var} (opc : op (A * B * C) D) : @expr var (A -> B -> C -> D)
    := λ a b c, Op opc (Var a, Var b, Var c).

  Ltac reify_op var term :=
    (*let dummy := match goal with _ => idtac "attempting to reify_op" term end in*)
    let Uncurry0 x := constr:(Uncurry0 (var:=var) x) in
    let Uncurry1 x := constr:(Uncurry1 (var:=var) x) in
    let Uncurry2 x := constr:(Uncurry2 (var:=var) x) in
    let Uncurry3 x := constr:(Uncurry3 (var:=var) x) in
    lazymatch term with
    | S => Uncurry1 op.S
    | @nil ?T
      => let rT := type.reify T in
         Uncurry0 (@op.nil rT)
    | @cons ?T
      => let rT := type.reify T in
         Uncurry2 (@op.cons rT)
    | seq => Uncurry2 op.List.seq
    | @List.repeat ?A
      => let rA := type.reify A in
         Uncurry2 (@op.List.repeat rA)
    | @Let_In ?A (fun _ => ?B)
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry2 (@op.Let_In rA rB)
    | @combine ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry2 (@op.List.combine rA rB)
    | @List.map ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry2 (@op.List.map rA rB)
    | @List.flat_map ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry2 (@op.List.flat_map rA rB)
    | @fst ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry1 (@op.fst rA rB)
    | @snd ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry1 (@op.snd rA rB)
    | @List.partition ?A
      => let rA := type.reify A in
         Uncurry2 (@op.List.partition rA)
    | @List.app ?A
      => let rA := type.reify A in
         Uncurry2 (@op.List.app rA)
    | @List.fold_right ?A ?B
      => let rA := type.reify A in
         let rB := type.reify B in
         Uncurry3 (@op.List.fold_right rA rB)
    | pred => Uncurry1 op.pred
    | @update_nth ?T
      => let rT := type.reify T in
         Uncurry3 (@op.List.update_nth rT)
    | runtime_mul => Uncurry2 op.Z.runtime_mul
    | runtime_add => Uncurry2 op.Z.runtime_add
    | Z.add => Uncurry2 op.Z.add
    | Z.mul => Uncurry2 op.Z.mul
    | Z.pow => Uncurry2 op.Z.pow
    | Z.opp => Uncurry1 op.Z.opp
    | Z.div => Uncurry2 op.Z.div
    | Z.modulo => Uncurry2 op.Z.modulo
    | Z.eqb => Uncurry2 op.Z.eqb
    | Z.of_nat => Uncurry1 op.Z.of_nat
    | @nat_rect (fun _ => ?T)
      => let rT := type.reify T in
         Uncurry3 (@op.nat_rect rT)
    | @bool_rect (fun _ => ?T)
      => let rT := type.reify T in
         Uncurry3 (@op.bool_rect rT)
    | _
      => let assert_const := match goal with
                             | _ => require_known_const term
                             end in
         let T := type of term in
         let rT := type.reify T in
         Uncurry0 (@op.Const rT term)
    end.

  Module var_context.
    Inductive list {var : type -> Type} :=
    | nil
    | cons {t} (gallina_v : type.interp t) (v : var t) (ctx : list).
  End var_context.

  (* cf COQBUG(https://github.com/coq/coq/issues/5448) *)
  Ltac refresh n :=
    let n' := fresh n in
    let n' := fresh n' in
    let n' := fresh n' in
    n'.

  Ltac is_type_arg arg_ty :=
    lazymatch eval cbv beta in arg_ty with
    | Prop => true
    | Set => true
    | Type => true
    | _ -> ?A => is_type_arg A
    | _ => false
    end.

  Ltac build_dummy_delayed_arguments_for ty :=
    lazymatch ty with
    | forall x : ?T, ?P
      => let not_x := refresh x in
         let rest := constr:(
                       fun x : T
                       => match P with (* c.f. COQBUG(https://github.com/coq/coq/issues/6243) *)
                          | not_x
                            => ltac:(
                                 let P := (eval cbv delta [not_x] in not_x) in
                                 let v := build_dummy_delayed_arguments_for P in
                                 exact v
                               )
                          end) in
         lazymatch rest with
         | (fun _ => ?rest)
           => constr:((tt, rest))
         end
    | _ => tt
    end.
  Ltac check_delayed_arguments_dummy delayed_arguments if_dummy if_not_dummy :=
    lazymatch delayed_arguments with
    | tt => if_dummy ()
    | (tt, ?delayed_arguments) => check_delayed_arguments_dummy delayed_arguments if_dummy if_not_dummy
    | (_, _) => if_not_dummy ()
    end.
  Ltac plug_delayed_arguments f delayed_arguments :=
    check_delayed_arguments_dummy
      delayed_arguments
      ltac:(fun _ => f)
             ltac:(fun _ =>
                     lazymatch delayed_arguments with
                     | (tt, ?delayed_arguments)
                       =>
                       lazymatch type of f with
                       | forall x : ?T, _
                         => let x := refresh x in
                            constr:(fun x : T
                                    => ltac:(let v := plug_delayed_arguments (f x) delayed_arguments in
                                             exact v))
                       end
                     | (?arg, ?delayed_arguments)
                       => plug_delayed_arguments (f arg) delayed_arguments
                     end).

  Ltac reify_helper var term ctx delayed_arguments :=
    let reify_rec term := reify_helper var term ctx delayed_arguments in
    (*let dummy := match goal with _ => idtac "reify_helper: attempting to reify:" term end in*)
    match constr:(Set) with _ => let ret :=
                                       lazymatch ctx with
    | context[@var_context.cons _ ?rT term ?v _]
      => constr:(@Var var rT v)
    | _
      =>
      let term_is_known_const := is_known_const term in
      lazymatch term_is_known_const with
      | true => reify_op var term
      | false
        =>
        lazymatch term with
        | tt => TT
        | @pair ?A ?B ?a ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             constr:(Pair (var:=var) ra rb)
        | match ?b with true => ?t | false => ?f end
          => let T := type of t in
             reify_rec (@bool_rect (fun _ => T) t f b)
        | let x := ?a in @?b x
          => let A := type of a in
             let B := lazymatch type of b with forall x, @?B x => B end in
             reify_rec (@Let_In A B a b)
        | ?f ?x
          =>
          let x_ty := type of x in
          let x_type_arg := is_type_arg x_ty in
          lazymatch x_type_arg with
          | true
            => (* we can't reify things of type [Type], so we save it for later to plug in *)
            reify_helper var f ctx (x, delayed_arguments)
          | false
            =>
            let dummy_args := build_dummy_delayed_arguments_for x_ty in
            let rx := reify_helper var x ctx dummy_args in
            (* in rf's delayed_arguments, tt stands for "dummy" *)
            let rf := reify_helper var f ctx (tt, delayed_arguments) in
            constr:(Op (var:=var) op.App (Pair (var:=var) rf rx))
          end
        | (fun x : ?T => ?f)
          =>
          (*let dummy := match goal with _ => idtac "funcase delaying" delayed_arguments end in*)
          lazymatch delayed_arguments with
          | (tt, ?delayed_arguments)
            => (* dummy, don't plug in *)
            let rT := type.reify T in
            let not_x := refresh x in
            let not_x2 := refresh not_x in
            let rf0 :=
                constr:(
                  fun (x : T) (not_x : var rT)
                  => match f with
                     | not_x2
                       => ltac:(
                            let f := (eval cbv delta [not_x2] in not_x2) in
                            (*idtac "rec call" f "was" term;*)
                            let rf := reify_helper var f (@var_context.cons var rT x not_x ctx) delayed_arguments in
                            exact rf)
                     end) in
            lazymatch rf0 with
            | (fun _ => ?rf)
              => constr:(@Abs var rT _ rf)
            | _ => let dummy := match goal with
                                | _ => fail 1 "Failure to eliminate functional dependencies of" rf0
                                end in
                   constr:(I : I)
            end
          | (?arg, ?delayed_arguments)
            => (* we pull a trick with [match] to plug in [arg] without running cbv β *)
            (*let fx := constr:(match arg with x => f end) in
            let dummy := match goal with _ => idtac "testing beta1" fx end in*)
            reify_helper var (match arg with x => f end) ctx delayed_arguments
          end
        | _
          => let term := plug_delayed_arguments term delayed_arguments in
             reify_op var term
        end
      end
    end
    in
                                 (*let dummy := match goal with _ => idtac "success reifying" term "as" ret end in*)
    ret
  | _ => let dummy := match goal with _ => fail 1000000 "failure to reify" term end in
         constr:(I : I)
  end.
  Ltac reify var term :=
    let ty := type of term in
    let dummy_args := build_dummy_delayed_arguments_for ty in
    reify_helper var term (@var_context.nil var) dummy_args.
  Ltac Reify term :=
    constr:(fun var : type -> Type
            => ltac:(let r := reify var term in
                     exact r)).
  Ltac Reify_rhs _ :=
    let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
    let R := Reify RHS in
    transitivity (Interp R);
    [ | cbv beta iota delta [Interp interp op.interp Uncurry0 Uncurry1 Uncurry2 Uncurry3 Let_In type.interp bool_rect];
        reflexivity ].
End Compilers.
Import Associational Positional Compilers.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Definition w (i:nat) : Z := 2^Qceiling((25+1/2)*i).
Example base_25_5_mul (*(f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : Z)
        (f:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)
        (g:=(f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: nil)%list)*) (f g : list Z)
        (n:=10%nat)
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
  eapply f_equal2; [|trivial]. eapply f_equal.
(*   ?fg = *)
(*   mulmod w (2 ^ 255) [(1, 19)] (f9, f8, f7, f6, f5, f4, f3, f2, f1, f0) *)
(*     (g9, g8, g7, g6, g5, g4, g3, g2, g1, g0) *)
  (*cbv [f g].*)
  cbv [w Qceiling Qfloor Qopp Qnum Qdiv Qplus inject_Z Qmult Qinv Qden Pos.mul].
  apply (f_equal (fun F => F f g)).
  cbv [n].
  cbv delta [mulmod w to_associational mul to_associational reduce from_associational add_to_nth zeros place split].
  Reify_rhs ().
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
  (*trivial.
Defined.*)
Abort.

(* Eval cbv on this one would produce an ugly term due to the use of [destruct] *)
