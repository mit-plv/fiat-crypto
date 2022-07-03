(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.


Reserved Notation "'dlet_list_pair_only_snd' x := v 'in' f"
         (at level 200, f at level 200, format "'dlet_list_pair_only_snd'  x  :=  v  'in' '//' f").
Reserved Notation "'dlet_list_pair' x := v 'in' f"
         (at level 200, f at level 200, format "'dlet_list_pair'  x  :=  v  'in' '//' f").
Reserved Notation "'dlet_list' x := v 'in' f"
         (at level 200, f at level 200, format "'dlet_list'  x  :=  v  'in' '//' f").
Declare Scope runtime_scope.
Delimit Scope runtime_scope with RT.
Import CPSBindNotations.
Local Open Scope cps_scope.

Module Type Runtime.
  Parameter Let_In : forall {A P} (x : A) (f : forall a : A, P a), P x.
  Parameter runtime_nth_default : forall {A}, A -> list A -> nat -> A.
  Parameter runtime_add : Z -> Z -> Z.
  Parameter runtime_sub : Z -> Z -> Z.
  Parameter runtime_mul : Z -> Z -> Z.
  Parameter runtime_div : Z -> Z -> Z.
  Parameter runtime_modulo : Z -> Z -> Z.
  Parameter runtime_opp : Z -> Z.
  Arguments runtime_add (_ _)%RT.
  Arguments runtime_sub (_ _)%RT.
  Arguments runtime_mul (_ _)%RT.
  Arguments runtime_div _%RT _%Z.
  Arguments runtime_modulo _%RT _%Z.
  Arguments runtime_opp _%RT.
  Infix "*" := runtime_mul : runtime_scope.
  Infix "+" := runtime_add : runtime_scope.
  Infix "-" := runtime_sub : runtime_scope.
  Infix "/" := runtime_div : runtime_scope.
  Notation "x 'mod' y" := (runtime_modulo x y) : runtime_scope.
  Notation "- x" := (runtime_opp x) : runtime_scope.
  Notation "'dlet_nd' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )) (only parsing).
  Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).

  Module RT_Z.
    Parameter zselect : Z -> Z -> Z -> Z.
    Parameter add_get_carry_full : Z -> Z -> Z -> Z * Z.
    Parameter add_with_get_carry_full : Z -> Z -> Z -> Z -> Z * Z.
    Parameter mul_split : Z -> Z -> Z -> Z * Z.
    Parameter land : Z -> Z -> Z.
  End RT_Z.
End Runtime.

Module RuntimeDefinitions <: Runtime.
  Definition Let_In := @LetIn.Let_In.
  Definition runtime_nth_default := List.nth_default.
  Definition runtime_add := Z.add.
  Definition runtime_sub := Z.sub.
  Definition runtime_mul := Z.mul.
  Definition runtime_opp := Z.opp.
  Definition runtime_div := Z.div.
  Definition runtime_modulo := Z.modulo.
  Module RT_Z.
    Definition zselect := Z.zselect.
    Definition add_get_carry_full := Z.add_get_carry_full.
    Definition add_with_get_carry_full := Z.add_with_get_carry_full.
    Definition mul_split := Z.mul_split.
    Definition land := Z.land.
  End RT_Z.
End RuntimeDefinitions.

Module RuntimeAxioms : Runtime.
  Include RuntimeDefinitions.
End RuntimeAxioms.

Module Export RuntimeDefinitionsCbv.
  Import RuntimeDefinitions.
  Declare Reduction cbv_no_rt
    := cbv -[Let_In
               runtime_nth_default
               runtime_add
               runtime_sub
               runtime_mul
               runtime_opp
               runtime_div
               runtime_modulo
               RT_Z.add_get_carry_full
               RT_Z.add_with_get_carry_full
               RT_Z.mul_split].
  Declare Reduction lazy_no_rt
    := lazy -[Let_In
                runtime_nth_default
                runtime_add
                runtime_sub
                runtime_mul
                runtime_opp
                runtime_div
                runtime_modulo
                RT_Z.add_get_carry_full
                RT_Z.add_with_get_carry_full
                RT_Z.mul_split].
  Declare Reduction pattern_rt
    := pattern Let_In,
       runtime_nth_default,
       runtime_add,
       runtime_sub,
       runtime_mul,
       runtime_opp,
       runtime_div,
       runtime_modulo,
       RT_Z.add_get_carry_full,
       RT_Z.add_with_get_carry_full,
       RT_Z.mul_split.

  Import RuntimeAxioms.
  Declare Reduction pattern_ax_rt
    := pattern (@Let_In),
       (@runtime_nth_default),
       runtime_add,
       runtime_sub,
       runtime_mul,
       runtime_opp,
       runtime_div,
       runtime_modulo,
       RT_Z.add_get_carry_full,
       RT_Z.add_with_get_carry_full,
       RT_Z.mul_split.
End RuntimeDefinitionsCbv.

Module RT_Extra (Import RT : Runtime).
  Fixpoint dlet_nd_list_pair {A B} (ls : list (A * B)) {T} (f : list (A * B) -> T) : T
    := match ls with
       | nil => f nil
       | cons x xs
         => dlet_nd x1 := fst x in dlet_nd x2 := snd x in @dlet_nd_list_pair A B xs T (fun xs => f ((x1, x2) :: xs))
       end.

  Fixpoint dlet_nd_list {A} (ls : list A) {T} (f : list A -> T) : T
    := match ls with
       | nil => f nil
       | cons x xs
         => dlet_nd x := x in @dlet_nd_list A xs T (fun xs => f (x :: xs))
       end.

  Fixpoint dlet_nd_list_pair_only_snd {A B} (ls : list (A * B)) {T} (f : list (A * B) -> T) : T
    := match ls with
       | nil => f nil
       | cons x xs
         => dlet_nd x2 := snd x in @dlet_nd_list_pair_only_snd A B xs T (fun xs => f ((fst x, x2) :: xs))
       end.

  Notation "'dlet_list_pair_only_snd' x := v 'in' f" := (dlet_nd_list_pair_only_snd v (fun x => f)).
  Notation "'dlet_list_pair' x := v 'in' f" := (dlet_nd_list_pair v (fun x => f)).
  Notation "'dlet_list' x := v 'in' f" := (dlet_nd_list v (fun x => f)).


  Definition expand_list_helper {A} (default : A) (ls : list A) (n : nat) (idx : nat) : list A
  := nat_rect
       (fun _ => nat -> list A)
       (fun _ => nil)
       (fun n' rec_call idx
        => cons (runtime_nth_default default ls idx) (rec_call (S idx)))
       n
       idx.
  Definition expand_list {A} (default : A) (ls : list A) (n : nat) : list A
    := expand_list_helper default ls n 0.
End RT_Extra.

Module Associational (Import RT : Runtime).
  Module Import Deps.
    Module Export RT_Extra := RT_Extra RT.
  End Deps.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', (snd t * snd t')%RT))
    q) p.

  Definition square_cps (p:list (Z*Z)) : ~> list (Z*Z) :=
    list_rect
      _
      (return nil)
      (fun t ts acc T k
       => (dlet two_t2 := (2 * snd t)%RT in
               acc
                 _
                 (fun acc
                  => k (((fst t * fst t, (snd t * snd t)%RT)
                           :: (map (fun t'
                                    => (fst t * fst t', (two_t2 * snd t')%RT))
                                   ts))
                          ++ acc))))
      p.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, (-snd cx)%RT)) p.

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  (* reduce at most [n] times, stopping early if the high list is nil at any point *)
  Definition repeat_reduce (n : nat) (s:Z) (c:list _) (p:list _) : list (Z * Z)
    := nat_rect
         _
         (fun p => p)
         (fun n' repeat_reduce_n' p
          => let lo_hi := split s p in
             if (length (snd lo_hi) =? 0)%nat
             then p
             else let p := fst lo_hi ++ mul c (snd lo_hi) in
                  repeat_reduce_n' p)
         n
         p.

  (* rough template (we actually have to do things a bit differently to account for duplicate weights):
[ dlet fi_c := c * fi in
   let (fj_high, fj_low) := split fj at s/fi.weight in
   dlet fi_2 := 2 * fi in
    dlet fi_2_c := 2 * fi_c in
    (if fi.weight^2 >= s then fi_c * fi else fi * fi)
       ++ fi_2_c * fj_high
       ++ fi_2 * fj_low
 | fi <- f , fj := (f weight less than i) ]
   *)
  (** N.B. We take advantage of dead code elimination to allow us to
      let-bind partial products that we don't end up using *)
  (** [v] -> [(v, v*c, v*c*2, v*2)] *)
  Definition let_bind_for_reduce_square_cps (c:list (Z*Z)) (p:list (Z*Z)) : ~> list ((Z*Z) * list(Z*Z) * list(Z*Z) * list(Z*Z)) :=
    fun T
    => let two := [(1,2)] (* (weight, value) *) in
       map_cps2 (fun t T k => dlet_list_pair_only_snd c_t := mul [t] c in dlet_list_pair_only_snd two_c_t := mul c_t two in dlet_list_pair_only_snd two_t := mul [t] two in k (t, c_t, two_c_t, two_t)) p.
  Definition reduce_square_cps (s:Z) (c:list (Z*Z)) (p:list (Z*Z)) : ~>list (Z*Z) :=
    (p <- let_bind_for_reduce_square_cps c p;
    let div_s := map (fun t => (fst t / s, snd t)) in
    return (list_rect
      _
      nil
      (fun t ts acc
       => (let '(t, c_t, two_c_t, two_t) := t in
           (if ((fst t * fst t) mod s =? 0)
            then div_s (mul [t] c_t)
            else mul [t] [t])
             ++ (flat_map
                   (fun '(t', c_t', two_c_t', two_t')
                    => if ((fst t * fst t') mod s =? 0)
                       then div_s
                              (if fst t' <=? fst t
                               then mul [t'] two_c_t
                               else mul [t] two_c_t')
                       else (if fst t' <=? fst t
                             then mul [t'] two_t
                             else mul [t] two_t'))
                   ts))
            ++ acc)
      p)).

  Definition bind_snd_cps (p : list (Z*Z)) : ~>list (Z * Z) :=
    @dlet_nd_list_pair_only_snd _ _ p.

  Section Carries.
    Definition carryterm_cps (w fw:Z) (t:Z * Z) : ~> list (Z * Z) :=
      fun T k
      => if (Z.eqb (fst t) w)
         then dlet_nd t2 := snd t in
              dlet_nd d2 := (t2 / fw)%RT in
              dlet_nd m2 := (t2 mod fw)%RT in
              k [(w * fw, d2);(w,m2)]
         else k [t].

    Definition carry_cps (w fw:Z) (p:list (Z * Z)) : ~> list (Z * Z):=
      fun T => flat_map_cps (carryterm_cps w fw) p.
  End Carries.
End Associational.

Module Positional (Import RT : Runtime).
  Module Import Deps.
    Module Associational := Associational RT.
  End Deps.
  Section Positional.
  Context (weight : nat -> Z).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition eval n x := Associational.eval (@to_associational n x).
  Definition zeros n : list Z := repeat 0 n.
  Definition add_to_nth i x (ls : list Z) : list Z
    := ListUtil.update_nth i (fun y => (x + y)%RT) ls.

  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => unit -> (nat * Z)%type)
      (fun _ => (O, if fst t =? 1 then snd t else (fst t * snd t)%RT))
      (fun i' place_i' _
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in if c =? 1 then snd t else (c * snd t)%RT)
          else place_i' tt)
      i
      tt.

  Definition from_associational_cps n (p:list (Z*Z)) : ~> list Z :=
    fun T => fold_right_cps2 (fun t ls T k =>
      let '(p1, p2) := place t (pred n) in
      dlet_nd p2 := p2 in
      k (add_to_nth p1 p2 ls)) (zeros n) p.

  Definition extend_to_length (n_in n_out : nat) (p:list Z) : list Z :=
    p ++ zeros (n_out - n_in).

  Definition drop_high_to_length (n : nat) (p:list Z) : list Z :=
    firstn n p.

  Section mulmod.
    Context (s:Z)
            (c:list (Z*Z)).
    Definition mulmod_cps (n:nat) (a b:list Z) : ~> list Z
      := let a_a := to_associational n a in
         let b_a := to_associational n b in
         let ab_a := Associational.mul a_a b_a in
         let abm_a := Associational.repeat_reduce n s c ab_a in
         from_associational_cps n abm_a.

    Definition squaremod_cps (n:nat) (a:list Z) : ~> list Z
      := (let a_a := to_associational n a in
         aa_a <- Associational.reduce_square_cps s c a_a;
         let aam_a := Associational.repeat_reduce (pred n) s c aa_a in
         from_associational_cps n aam_a).
  End mulmod.

  Definition add_cps (n:nat) (a b:list Z) : ~> list Z
    := let a_a := to_associational n a in
       let b_a := to_associational n b in
       from_associational_cps n (a_a ++ b_a).

  Section Carries.
    Definition carry_cps n m (index:nat) (p:list Z) : ~> list Z :=
      (p <- @Associational.carry_cps (weight index)
         (weight (S index) / weight index)
         (to_associational n p);
       from_associational_cps
           m p).

    Definition carry_reduce_cps n (s:Z) (c:list (Z * Z))
               (index:nat) (p : list Z) : ~> list Z :=
      (p <- @carry_cps n (S n) index p;
         p <- from_associational_cps
           n (Associational.reduce
                s c (to_associational (S n) p));
       return p).

    (* N.B. It is important to reverse [idxs] here, because fold_right is
      written such that the first terms in the list are actually used
      last in the computation. For example, running:

      `Eval cbv - [Z.add] in (fun a b c d => fold_right Z.add d [a;b;c]).`

      will produce [fun a b c d => (a + (b + (c + d)))].*)
    Definition chained_carries_cps n s c p (idxs : list nat) : ~> _ :=
      fun T => fold_right_cps2 (fun a b => carry_reduce_cps n s c a b) p (rev idxs).

    (* carries without modular reduction; useful for converting between bases *)
    Definition chained_carries_no_reduce_cps n p (idxs : list nat) : ~> _ :=
      fun T => fold_right_cps2 (fun a b => carry_cps n n a b) p (rev idxs).

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying. *)
    Definition encode_cps n s c (x : Z) : ~> list Z :=
      (p <- from_associational_cps n [(1,x)]; chained_carries_cps n s c p (seq 0 n)).

    (* Reverse of [eval]; translate from Z to basesystem by putting
    everything in first digit and then carrying, but without reduction. *)
    Definition encode_no_reduce_cps n (x : Z) : ~> list Z :=
      (p <- from_associational_cps n [(1,x)]; chained_carries_no_reduce_cps n p (seq 0 n)).
  End Carries.

  Section sub.
    Context (n:nat)
            (s:Z)
            (c:list (Z * Z))
            (coef:Z).

    Definition negate_snd_cps (a:list Z) : ~> list Z
      := let A := to_associational n a in
         let negA := Associational.negate_snd A in
         from_associational_cps n negA.

    Definition scmul_cps (x:Z) (a:list Z) : ~> list Z
      := let A := to_associational n a in
         let R := Associational.mul A [(1, x)] in
         from_associational_cps n R.

    Definition balance_cps : ~> list Z
      := (sc <- encode_cps n s c (s - Associational.eval c); v <- scmul_cps coef sc; return v).

    Definition sub_cps (a b:list Z) : ~> list Z
      := (balance <- balance_cps;
            ca <- add_cps n balance a;
            _b <- negate_snd_cps b;
            camb <- add_cps n ca _b;
            return camb).

    Definition opp_cps (a:list Z) : ~> list Z
      := sub_cps (zeros n) a.
  End sub.

  Section select.
    Definition zselect_cps (mask cond:Z) (p:list Z) : ~> _ :=
      fun T k => dlet t := RT_Z.zselect cond 0 mask in k (List.map (RT_Z.land t) p).

    Definition select (cond:Z) (if_zero if_nonzero:list Z) :=
      List.map (fun '(p, q) => RT_Z.zselect cond p q) (List.combine if_zero if_nonzero).
  End select.
End Positional.
End Positional.
