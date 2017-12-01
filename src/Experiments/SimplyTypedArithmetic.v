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
  Notation "f x" := (Op op.App (f, x)%expr) (only printing) : expr_scope.

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

  Definition const {var t} (v : type.interp t) : @expr var t
    := Op (op.Const v) TT.

  Section option_partition.
    Context {A : Type} (f : A -> option Datatypes.bool).
    Fixpoint option_partition (l : list A) : option (list A * list A)
      := match l with
         | nil => Some (nil, nil)
         | cons x tl
           => match option_partition tl, f x with
              | Some (g, d), Some fx
                => Some (if fx then (x :: g, d) else (g, x :: d))
              | _, _ => None
              end
         end.
  End option_partition.
  Section option_flat_map.
    Context {A B : Type} (f : A -> option (list B)).
    Fixpoint option_flat_map (l : list A) : option (list B)
      := match l with
         | nil => Some nil
         | cons x t => match f x, option_flat_map t with
                       | Some fx, Some ft
                         => Some (fx ++ ft)
                       | _, _ => None
                       end
         end.
  End option_flat_map.

  Definition lift_option_list {A} (ls : list (option A)) : option (list A)
    := list_rect
         (fun _ => _)
         (Some nil)
         (fun x _ xs
          => match x, xs with
             | Some x, Some xs => Some (cons x xs)
             | _, _ => None
             end)
         ls.

  Section invert.
    Context {var : type -> Type}.

    Definition invert_Var {t} (e : @expr var t) : option (var t)
      := match e with
         | Var t v => Some v
         | _ => None
         end.

    Definition invert_Abs {s d} (e : @expr var (type.arrow s d)) : option (var s -> @expr var d)
      := match e in expr t return option match t with
                                         | type.arrow _ _ => _
                                         | _ => True
                                         end with
         | Abs s d f => Some f
         | _ => None
         end.

    Definition invert_Pair {A B} (e : @expr var (type.prod A B)) : option (@expr var A * @expr var B)
      := match e in expr t return option match t with
                                         | type.prod _ _ => _
                                         | _ => True
                                         end with
         | Pair _ _ a b => Some (a, b)
         | _ => None
         end.

    Definition invert_Op {t} (e : @expr var t) : option { s : _ & op s t * @expr var s }%type
      := match e with
         | Op s d opc args => Some (existT _ s (opc, args))
         | _ => None
         end.

    Definition invert_OpConst {t} (e : @expr var t) : option (type.interp t)
      := match invert_Op e with
         | Some (existT s (opc, args))
           => match opc with
              | op.Const t v => Some v
              | _ => None
              end
         | None => None
         end.

    Definition invert_op_S (e : @expr var type.nat) : option (@expr var type.nat)
      := match invert_Op e with
         | Some (existT s (opc, args))
           => match opc in op s d return expr s -> option (expr type.nat) with
              | op.S => fun args => Some args
              | _ => fun _ => None
              end args
         | None => None
         end.

    Definition invert_Z (e : @expr var type.Z) : option Z := invert_OpConst e.
    Definition invert_bool (e : @expr var type.bool) : option bool := invert_OpConst e.
    Fixpoint invert_nat_full (e : @expr var type.nat) : option nat
      := match e with
         | Op _ _ op.S args
           => option_map S (invert_nat_full args)
         | Op _ _ (op.Const type.nat v) _
           => Some v
         | _ => None
         end.
    (* oh, the horrors of not being able to use non-linear deep pattern matches *)
    Fixpoint invert_list_full {t} (e : @expr var (type.list t))
      : option (list (@expr var t))
      := match e in expr t return option match t with
                                         | type.list t => list (expr t)
                                         | _ => True
                                         end
         with
         | Op s d opc args
           => match opc in op s d
                    return option match s with
                                  | type.prod A (type.list B) => expr A * list (expr B)
                                  | _ => True
                                  end
                           -> option match d with
                                     | type.list t => list (expr t)
                                     | _ => True
                                     end
              with
              | op.Const (type.list _) v => fun _ => Some (List.map const v)
              | op.cons _ => option_map (fun '(x, xs) => cons x xs)
              | op.nil _ => fun _ => Some nil
              | _ => fun _ => None
              end
                (match args in expr t
                       return option match t with
                                     | type.prod A (type.list B) => expr A * list (expr B)
                                     | _ => True
                                     end
                 with
                 | Pair _ (type.list _) x xs
                   => match @invert_list_full _ xs with
                      | Some xs => Some (x, xs)
                      | None => None
                      end
                 | _ => None
                 end)
         | _ => None
         end.
    (*Section with_map.
      (* oh, the horrors of not being able to use non-linear deep
         pattern matches.  Luckily Coq's guard checker unfolds things,
         so as long as the thing we need to evaluate at the bottom is
         generic in what type it's looking at, we're good.  We can
         even give it data of the right type, which we need, but it
         costs us a lot *)
      Context (extra_dataT : type -> Type) {U} (f : forall t (d : extra_dataT t), @expr var t -> U t d).
      Local Notation list_to_extra_dataT t
        := (match t%ctype return Type with
            | type.list t' => extra_dataT t'
            | _ => True
            end).
      Local Notation list_to_forall_data_option_list t
        := (forall (d : list_to_extra_dataT t),
               option (match t%ctype as t'
                             return list_to_extra_dataT t' -> Type
                       with
                       | type.list t' => fun d => list (U t' d)
                       | _ => fun _ => True
                       end d)).
      Local Notation prod_list_to_extra_dataT t
        := (match t%ctype return Type with
            | type.prod _ (type.list t') => extra_dataT t'
            | _ => True
            end).
      Local Notation prod_list_to_forall_data_option_list t
        := (forall (d : prod_list_to_extra_dataT t),
               option (match t%ctype as t'
                             return prod_list_to_extra_dataT t' -> Type
                       with
                       | type.prod A (type.list t') => fun d => (expr A * list (U t' d))%type
                       | _ => fun _ => True
                       end d)).



      Fixpoint invert_map_list_full {t} (e : @expr var (type.list t))
        : forall d : extra_dataT t, option (list (U t d))
      := match e in expr t return list_to_forall_data_option_list t
           with
           | Op s d opc args
             => match opc in op s d
                      return (prod_list_to_forall_data_option_list s
                              -> list_to_forall_data_option_list d)
                with
                | op.Const (type.list _) v
                  => fun _ data => Some (List.map (f _ data) (List.map const v))
                | op.cons _
                  => fun xs data
                     => option_map (fun '(x, xs) => cons (f _ data x) xs) (xs data)
                | op.nil _
                  => fun _ _ => Some nil
                | _ => fun _ _ => None
                end
                  (match args in expr t
                         return prod_list_to_forall_data_option_list t
                   with
                   | Pair _ (type.list _) x xs
                     => fun data
                        => match @invert_map_list_full _ xs data with
                           | Some xs => Some (x, xs)
                           | None => None
                           end
                   | _ => fun _ => None
                   end)
           | _ => fun _ => None
           end.
    End with_map.*)
  End invert.

  Section gallina_reify.
    Context {var : type -> Type}.
    Definition reify_list {t} (ls : list (@expr var t)) : @expr var (type.list t)
      := list_rect
           (fun _ => _)
           (Op op.nil TT)
           (fun x _ xs => Op op.cons (x, xs))
           ls.
  End gallina_reify.


  Module arguments.
    Inductive arguments : type -> Set :=
    | generic {T} : arguments T
    (*| cps {T} (aT : arguments T) : arguments T*)
    | arrow {A B} (aB : arguments B) : arguments (A -> B)
    | unit : arguments type.unit
    | prod {A B} (aA : arguments A) (aB : arguments B) : arguments (A * B)
    | list {T} (aT : arguments T) : arguments (type.list T)
    | nat : arguments type.nat
    | Z : arguments type.Z
    | bool : arguments type.bool.

    Definition preinvertT (t : type) :=
      match t with
      | type.unit => Datatypes.unit
      | type.prod A B => arguments A * arguments B
      | type.arrow s d => arguments d
      | type.list A => arguments A
      | type.nat => Datatypes.unit
      | type.Z => Datatypes.unit
      | type.bool => Datatypes.unit
      end%type.
    Definition invertT (t : type) :=
      option (* [None] means "generic" *) (preinvertT t).

    Definition invert {t : type} (P : arguments t -> Type)
               (generic_case : P generic)
               (non_generic_cases
                : forall v : preinvertT t,
                   match t return forall v : preinvertT t, (arguments t -> Type) -> Type with
                   | type.unit
                     => fun v P => P unit
                   | type.prod A B
                     => fun '((a, b) : arguments A * arguments B) P
                        => P (prod a b)
                   | type.arrow s d => fun v P => P (arrow v)
                   | type.list A => fun v P => P (list v)
                   | type.nat => fun v P => P nat
                   | type.Z => fun v P => P Z
                   | type.bool => fun v P => P bool
                   end v P)
               (a : arguments t)
      : P a.
    Proof.
      destruct a;
        try specialize (fun a b => non_generic_cases (a, b));
        cbn in *;
        [ exact generic_case | apply non_generic_cases; apply tt .. ].
    Defined.

    Definition invert_arrow {s d} (a : arguments (type.arrow s d)) : arguments d
      := @invert (type.arrow s d) (fun _ => arguments d) generic (fun ad => ad) a.

    Definition invert_prod {A B} (a : arguments (type.prod A B)) : arguments A * arguments B
      := @invert (type.prod A B) (fun _ => arguments A * arguments B)%type (generic, generic) (fun '(a, b) => (a, b)) a.


    Fixpoint ground {t : type} : arguments t
      := match t with
         | type.unit => unit
         | type.prod A B => prod (@ground A) (@ground B)
         | type.arrow s d => arrow (@ground d)
         | type.list A => list (@ground A)
         | type.nat => nat
         | type.Z => Z
         | type.bool => bool
         end.

    Module type.
      Local Notation interp_type := type.interp.
      Section interp.
        Context (var_dom var_cod : type -> Type).
        Fixpoint interp {t} (a : arguments t) : Type
          := match a with
             | generic T => var_cod T
             (*| cps T aT => forall U, (@interp T aT -> var U) -> var U*)
             | arrow A B aB => var_dom A -> @interp B aB
             | unit => Datatypes.unit
             | prod A B aA aB => @interp A aA * @interp B aB
             | list T aT => Datatypes.list (@interp T aT)
             | nat => Datatypes.nat
             | Z => BinInt.Z
             | bool => Datatypes.bool
             end%type.
      End interp.

      Section ground.
        Context {var_dom var_cod : type -> Type}.
        Fixpoint const_of_ground {t}
          : interp_type t -> option (interp var_dom (@expr var_cod) (@ground t))
          := match t return interp_type t -> option (interp var_dom expr (@ground t)) with
             | type.prod A B
               => fun '((a, b) : interp_type A * interp_type B)
                  => match @const_of_ground A a, @const_of_ground B b with
                     | Some a', Some b' => Some (a', b')
                     | _, _ => None
                     end
             | type.arrow s d => fun _ => None
             | type.list A
               => fun ls : Datatypes.list (interp_type A)
                  => lift_option_list
                       (List.map (@const_of_ground A) ls)
             | type.unit
             | type.nat
             | type.Z
             | type.bool
               => fun v => Some v
             end.
      End ground.

      Module option.
        Section interp.
          Context (var_dom var_cod : type -> Type).
          Fixpoint interp {t} (a : arguments t) : Type
            := match a with
               | generic T => var_cod T
               (*| cps T aT => forall U, (@interp T aT -> var U) -> var U*)
               | arrow A B aB => var_dom A -> @interp B aB
               | unit => Datatypes.unit
               | prod A B aA aB => option (@interp A aA * @interp B aB)
               | list T aT => option (Datatypes.list (@interp T aT))
               | nat => option Datatypes.nat
               | Z => option BinInt.Z
               | bool => option Datatypes.bool
               end%type.
        End interp.

        Section flat_interp.
          Context (var_generic var_dom : type -> Type) (var_cod : forall t, arguments t -> Type).
          Fixpoint flat_interp {t} (a : arguments t) : Type
            := match a with
               | generic T => var_generic T
               (*| cps T aT => forall U, (@interp T aT -> var U) -> var U*)
               | arrow A B aB => var_dom A -> var_cod B aB
               | unit => Datatypes.unit
               | prod A B aA aB => @flat_interp A aA * @flat_interp B aB
               | list T aT => Datatypes.list (@flat_interp T aT)
               | nat => Datatypes.nat
               | Z => BinInt.Z
               | bool => Datatypes.bool
               end%type.
        End flat_interp.

        Definition interp_to_arrow_or_generic var_dom var_cod {t} a
          := @flat_interp var_cod var_dom (@interp var_dom var_cod) t a.

        Section lift_option.
          Context {var_dom var_cod : type -> Type}.
          Fixpoint lift_interp {t} {a : arguments t}
            : interp var_dom var_cod a -> option (interp_to_arrow_or_generic var_dom var_cod a)
            := match a in arguments t
                     return interp var_dom var_cod a -> option (interp_to_arrow_or_generic var_dom var_cod a)
               with
               | prod A B aA aB
                 => fun ab : option (interp _ _ aA * interp _ _ aB)
                    => match ab with
                       | Some (a, b)
                         => match @lift_interp A aA a, @lift_interp B aB b with
                            | Some a, Some b => Some (a, b)
                            | _, _ => None
                            end
                       | None => None
                       end
               | list T aT
                 => fun ls : option (Datatypes.list (interp _ _ aT))
                    => match ls with
                       | Some ls
                         => lift_option_list
                              (List.map (@lift_interp T aT) ls)
                       | None => None
                       end
               | arrow _ _ _
               | generic _
               | unit
                 => fun v => Some v
               | nat
               | Z
               | bool
                 => fun x => x
               end.
        End lift_option.
      End option.
    End type.

    Module expr.
      Section interp.
        Context (var : type -> Type).
        Fixpoint interp {t} (a : arguments t)
          : @expr var t -> type.option.interp (@expr var) (@expr var) a
          := match a in arguments t return expr t -> type.option.interp expr expr a with
             | generic T => fun e => e
             (*| cps T aT => fun e*)
             | arrow A B aB
               => fun e arg
                  => @interp
                       B aB
                       match invert_Abs e, invert_Var arg with
                       | Some f, Some arg => f arg
                       | _, _ => Op op.App (e, arg)
                       end
             | unit => fun _ => tt
             | prod A B aA aB
               => fun e
                  => option_map (fun '(a, b)
                                 => (@interp A aA a, @interp B aB b))
                                (invert_Pair e)
             | list T aT
               => fun e
                  => option_map
                       (List.map (@interp T aT))
                       (invert_list_full e)
             | nat => invert_nat_full
             | Z => invert_Z
             | bool => invert_bool
             end.
      End interp.

      Section reify.
        Context (var : type -> Type).
        Fixpoint reify {t} (a : arguments t)
          : type.interp var (@expr var) a -> @expr var t
          := match a in arguments t return type.interp var expr a -> expr t with
             | generic T => fun e => e
             | arrow A B aB => fun f => Abs (fun x => @reify B aB (f x))
             | unit => fun _ => TT
             | prod A B aA aB
               => fun '((a, b) : type.interp _ _ aA * type.interp _ _ aB)
                  => (@reify A aA a, @reify B aB b)%expr
             | list T aT
               => fun ls
                  => reify_list (List.map (@reify T aT) ls)
             | nat => @const var type.nat
             | Z => @const var type.Z
             | bool => @const var type.bool
             end.
      End reify.
    End expr.

    Module Export Notations.
      Delimit Scope arguments_scope with arguments.
      Bind Scope arguments_scope with arguments.
      Notation "()" := unit : arguments_scope.
      Notation "A * B" := (prod A B) : arguments_scope.
      Notation "A -> B" := (@arrow A _ B) (only printing) : arguments_scope.
      Notation "A -> B" := (arrow B) (only parsing) : arguments_scope.
      Global Coercion generic : type.type >-> arguments.
      Notation arguments := arguments.
    End Notations.

    Module op.
      Local Open Scope arguments_scope.
      Definition lookup {s d} (opc : op s d) : arguments s * arguments d
        := match opc in op s d return arguments s * arguments d with
           | op.Const t v => (generic, ground)
           | op.Let_In tx tC => (tx * (tx -> tC), generic)
           | op.App s d => ((s -> d) * s, generic)
           | op.S => (ground, ground)
           | op.nil t => (generic, ground)
           | op.cons t => (t * list t, list t)
           | op.fst A B => (A * B, generic)
           | op.snd A B => (A * B, generic)
           | op.bool_rect T => (T * T * bool, generic)
           | op.nat_rect P => (P * (nat -> P -> P) * nat, generic)
           | op.pred => (nat, ground)
           | op.List_seq => (nat * nat, ground)
           | op.List_repeat A => (A * nat, list A)
           | op.List_combine A B => (list A * list B, list (A * B))
           | op.List_map A B => ((A -> B) * list A, list B)
           | op.List_flat_map A B => ((A -> list B) * list A, list B)
           | op.List_partition A => ((A -> bool) * list A, list A * list A)
           | op.List_app A => (list A * list A, list A)
           | op.List_fold_right A B => ((B -> A -> A) * A * list B, generic)
           | op.List_update_nth T => (nat * (T -> T) * list T, list T)
           | op.Z_runtime_mul => (Z * Z, Z)
           | op.Z_runtime_add => (Z * Z, Z)
           | op.Z_add => (Z * Z, Z)
           | op.Z_mul => (Z * Z, Z)
           | op.Z_pow => (Z * Z, Z)
           | op.Z_opp => (Z, Z)
           | op.Z_div => (Z * Z, Z)
           | op.Z_modulo => (Z * Z, Z)
           | op.Z_eqb => (Z * Z, bool)
           | op.Z_of_nat => (nat, Z)
           end.

      Definition lookup_src {s d} opc := fst (@lookup s d opc).
      Definition lookup_dst {s d} opc := snd (@lookup s d opc).

      Definition option_map_prod {A B C} (f : A -> B -> C) (v : option (option A * option B))
        : option C
        := match v with
           | Some (Some a, Some b) => Some (f a b)
           | _ => None
           end.



      Definition rewrite
                 {var : type -> Type}
                 {s d} (opc : op s d)
                 (exploded_arguments : type.option.interp (@expr var) (@expr var) (lookup_src opc))
        : option (type.interp var (@expr var) (lookup_dst opc))
        := match opc in op s d
                 return
                 (forall (exploded_arguments' : option (type.option.interp_to_arrow_or_generic expr expr (lookup_src opc))),
                     option (type.interp var expr (lookup_dst opc)))
           with
           | op.Const t v => fun _ => arguments.type.const_of_ground v
           | op.Let_In tx tC
             => option_map
                  (fun '(ex, eC)
                   => match invert_Var ex, invert_OpConst ex with
                      | Some v, _ => eC ex
                      | None, Some v => eC ex
                      | None, None => Op op.Let_In (ex, Abs (fun v => eC (Var v)))
                      end)
           | op.App s d => option_map (fun '(f, x) => f x)
           | op.S as opc
           | op.pred as opc
           | op.Z_runtime_mul as opc
           | op.Z_runtime_add as opc
           | op.Z_add as opc
           | op.Z_mul as opc
           | op.Z_pow as opc
           | op.Z_opp as opc
           | op.Z_div as opc
           | op.Z_modulo as opc
           | op.Z_eqb as opc
           | op.Z_of_nat as opc
             => option_map (op.interp opc)
           | op.nil t => fun _ => Some (@nil (type.interp _ _ ground))
           | op.cons t => option_map (op.curry2 cons)
           | op.fst A B => option_map (@fst (expr A) (expr B))
           | op.snd A B => option_map (@snd (expr A) (expr B))
           | op.bool_rect T => option_map (op.curry3 (bool_rect (fun _ => _)))
           | op.nat_rect P
             => option_map
                  (fun '(O_case, S_case, v)
                   => nat_rect (fun _ => expr P) O_case (fun n (v : expr P) => S_case (@const _ type.nat n) v) v)
           | op.List_seq => option_map (op.curry2 List.seq)
           | op.List_repeat A => option_map (op.curry2 (@List.repeat (expr A)))
           | op.List_combine A B => option_map (op.curry2 (@List.combine (expr A) (expr B)))
           | op.List_map A B => option_map (op.curry2 (@List.map (expr A) (expr B)))
           | op.List_flat_map A B
             => fun args : option ((expr A -> option (Datatypes.list (expr B))) * Datatypes.list (expr A))
                => match args with
                   | Some (f, ls) => option_flat_map f ls
                   | None => None
                   end
           | op.List_partition A
             => fun args : option ((expr A -> option Datatypes.bool) * Datatypes.list (expr A))
                => match args with
                   | Some (f, ls) => option_partition f ls
                   | None => None
                   end
           | op.List_app A => option_map (op.curry2 (@List.app (expr A)))
           | op.List_fold_right A B => option_map (op.curry3 (@List.fold_right (expr A) (expr B)))
           | op.List_update_nth T => option_map (op.curry3 (@update_nth (expr T)))
           end
             (type.option.lift_interp exploded_arguments).
    End op.
  End arguments.
  Export arguments.Notations.

  Section partial_reduce.
    Context {var : type -> Type}.

    Local Notation partial_reduceT t a
      := ((@expr var t * arguments.type.option.interp (@expr var) (@expr var) a)%type)
           (only parsing).

    Fixpoint partial_reduce' {t} (e : @expr (@expr var) t)
      : forall a : arguments t, partial_reduceT t a
      := match e in expr t return (forall a : arguments t, partial_reduceT t a) with
         | TT
           => arguments.invert
                (fun a : arguments type.unit => partial_reduceT type.unit a)
                (TT, TT)
                (fun u => (TT, u))
         | Pair A B a b
           => arguments.invert
                (fun a => partial_reduceT (type.prod A B) a)
                (let ab := (fst (@partial_reduce' A a arguments.generic),
                            fst (@partial_reduce' B b arguments.generic))%expr in
                 (ab, ab))
                (fun '(aA, aB)
                 => let '(a0, a1) := @partial_reduce' A a aA in
                    let '(b0, b1) := @partial_reduce' B b aB in
                    ((a0, b0)%expr, Some (a1, b1)))
         | Var t v
           => fun a => (v, arguments.expr.interp _ _ v)
         | Op s d opc args
           => let '(args0, args1) := @partial_reduce' s args (arguments.op.lookup_src opc) in
              let e :=
                  match arguments.op.rewrite opc args1 with
                  | Some e => arguments.expr.reify _ _ e
                  | None => Op opc args0
                  end in
              fun a => (e, arguments.expr.interp _ _ e)
         | Abs s d f
           => fun a
              => let e' := Abs (fun x => fst (@partial_reduce' d (f (Var x)) (arguments.invert_arrow a))) in
                 arguments.invert
                   (fun a => partial_reduceT (type.arrow s d) a)
                   (e', e')
                   (fun ad
                    => (e',
                        (fun x =>
                           snd (@partial_reduce' d (f x) ad))))
                   a
         end.


    Definition partial_reduce {t} (e : @expr (@expr var) t) : @expr var t
      := snd (@partial_reduce' t e arguments.generic).
  End partial_reduce.

  Definition PartialReduce {t} (e : Expr t) : Expr t
    := fun var => @partial_reduce var t (e _).

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

  Ltac reify_helper var term value_ctx template_ctx :=
    let reify_rec term := reify_helper var term value_ctx template_ctx in
    (*let dummy := match goal with _ => idtac "reify_helper: attempting to reify:" term end in*)
    lazymatch value_ctx with
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
          let ty := type_of_first_argument_of f in
          let x_is_template_parameter := is_template_parameter ty in
          lazymatch x_is_template_parameter with
          | true
            => (* we can't reify things of type [Type], so we save it for later to plug in *)
            reify_helper var f value_ctx (x, template_ctx)
          | false
            =>
            let rx := reify_helper var x value_ctx tt in
            let rf := reify_helper var f value_ctx template_ctx in
            constr:(Op (var:=var) op.App (Pair (var:=var) rf rx))
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
              reify_helper var (match arg with x => f end) value_ctx template_ctx
            end
          | false
            =>
            let rT := type.reify T in
            let not_x := refresh x in
            let not_x2 := refresh not_x in
            let rf0 :=
                constr:(
                  fun (x : T) (not_x : var rT)
                  => match f return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
                     | not_x2
                       => ltac:(
                            let f := (eval cbv delta [not_x2] in not_x2) in
                            (*idtac "rec call" f "was" term;*)
                            let rf := reify_helper var f (@var_context.cons var rT x not_x value_ctx) template_ctx in
                            exact rf)
                     end) in
            lazymatch rf0 with
            | (fun _ => ?rf)
              => constr:(@Abs var rT _ rf)
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
             reify_op var term
        end
      end
    end.
  Ltac reify var term :=
    reify_helper var term (@var_context.nil var) tt.
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
  assert True.
  { let v := Reify ((fun x => 2^x) 255)%Z in
    pose v as E.
    vm_compute in E.
    pose (PartialReduce E) as E'.
    vm_compute in E'.
    constructor. }
  Reify_rhs ().
  let e := match goal with |- _ = Interp ?e => e end in
  pose e as E.
  exfalso.
  Timeout 2 vm_compute in E.
  pose (PartialReduce E) as E'.
  Timeout 2 vm_compute in E'.
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
