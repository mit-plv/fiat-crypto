Require Import Coq.omega.Omega.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapCast.

(** * Preliminaries: bounded and unbounded number types *)

Definition bound8 := 256.

Definition word8 := {n | n < bound8}.

Definition bound9 := 512.

Definition word9 := {n | n < bound9}.


(** * Expressions over unbounded words *)

Inductive base_type := Nat | Word8 | Word9.
Scheme Equality for base_type.
Definition interp_base_type (t : base_type)
  := match t with
     | Nat => nat
     | Word8 => word8
     | Word9 => word9
     end.
Definition base_type_max (x y : base_type) :=
  match x, y with
  | Nat, _ => Nat
  | _, Nat => Nat
  | Word9, _ => Word9
  | _, Word9 => Word9
  | Word8, Word8 => Word8
  end.
Definition base_type_min (x y : base_type) :=
  match x, y with
  | Word8, _ => Word8
  | _, Word8 => Word8
  | Word9, _ => Word9
  | _, Word9 => Word9
  | Nat, Nat => Nat
  end.
Definition interp_base_type_bounds (t : base_type)
  := nat.
Local Notation TNat := (Tbase Nat).
Local Notation TWord8 := (Tbase Word8).
Local Notation TWord9 := (Tbase Word9).
Inductive op : flat_type base_type -> flat_type base_type -> Set :=
| Const {t} (v : interp_base_type t) : op Unit (Tbase t)
| Plus (t : base_type) : op (Tbase t * Tbase t) (Tbase t)
| Cast (t1 t2 : base_type) : op (Tbase t1) (Tbase t2).

Definition Constf {var} {t} (v : interp_base_type t) : exprf base_type op (var:=var) (Tbase t)
  := Op (Const v) TT.

Theorem O_lt_S : forall n, O < S n.
Proof.
  intros; omega.
Qed.

Definition plus8 (a b : word8) : word8 :=
  let n := proj1_sig a + proj1_sig b in
  match le_lt_dec bound8 n with
  | left _ => exist _ O (O_lt_S _)
  | right pf => exist _ n pf
  end.

Definition plus9 (a b : word9) : word9 :=
  let n := proj1_sig a + proj1_sig b in
  match le_lt_dec bound9 n with
  | left _ => exist _ O (O_lt_S _)
  | right pf => exist _ n pf
  end.

Infix "+8" := plus8 (at level 50).
Infix "+9" := plus9 (at level 50).

Definition unbound {t} : interp_base_type t -> nat :=
  match t with
  | Nat => fun x => x
  | Word8 => fun x => proj1_sig x
  | Word9 => fun x => proj1_sig x
  end.

Definition bound {t} : nat -> interp_base_type t :=
  match t return nat -> interp_base_type t with
  | Nat => fun x => x
  | Word8 => fun x =>
               match le_lt_dec bound8 x with
               | left _ => exist _ O (O_lt_S _)
               | right pf => exist _ x pf
               end
  | Word9 => fun x =>
               match le_lt_dec bound9 x with
               | left _ => exist _ O (O_lt_S _)
               | right pf => exist _ x pf
               end
  end.

Definition interp_op {src dst} (opc : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := match opc in op src dst return interp_flat_type _ src -> interp_flat_type _ dst with
     | Const _ v => fun _ => v
     | Plus Nat => fun xy => fst xy + snd xy
     | Plus Word8 => fun xy => fst xy +8 snd xy
     | Plus Word9 => fun xy => fst xy +9 snd xy
     | Cast t1 t2 => fun x => bound (unbound x)
     end.

Definition interp_op_bounds {src dst} (opc : op src dst) : interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst
  := match opc in op src dst return interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst with
     | Const _ v => fun _ => unbound v
     | Plus _ => fun xy => fst xy + snd xy
     | Cast t1 t2 => fun x => x
     end.

Definition bound_type t (v : interp_base_type_bounds t) : base_type
  := if lt_dec v bound8
     then Word8
     else if lt_dec v bound9
          then Word9
          else Nat.

Definition failv t : interp_base_type t
  := match t with
     | Nat => 0
     | Word8 => exist _ 0 (O_lt_S _)
     | Word9 => exist _ 0 (O_lt_S _)
     end.
Definition failf var t : @exprf base_type op var (Tbase t)
  := Op (Const (failv t)) TT.

Definition bound_base_const t1 t2 (x1 : interp_base_type t1) (x2 : interp_base_type_bounds t2) : interp_base_type (bound_type _ x2)
  := bound (unbound x1).
Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
  := (@SmartFlatTypeMap2 _ _ interp_base_type_bounds (fun t v => Tbase (bound_type t v))).
Fixpoint new_type {t} : forall (e_bounds : interp_type interp_base_type_bounds t)
                               (input_bounds : interp_all_binders_for' t interp_base_type_bounds),
    type base_type
  := match t return interp_type _ t -> interp_all_binders_for' t _ -> type _ with
     | Tflat T => fun e_bounds _ => @new_flat_type T e_bounds
     | Arrow A B
       => fun e_bounds input_bounds
          => Arrow (@bound_type A (fst input_bounds))
                   (@new_type B (e_bounds (fst input_bounds)) (snd input_bounds))
     end.
Definition bound_op
           ovar src1 dst1 src2 dst2 (opc1 : op src1 dst1) (opc2 : op src2 dst2)
  : exprf base_type op (var:=ovar) src1
    -> interp_flat_type interp_base_type_bounds src2
    -> exprf base_type op (var:=ovar) dst1
  := match opc1 in op src1 dst1, opc2 in op src2 dst2
           return (exprf base_type op (var:=ovar) src1
                   -> interp_flat_type interp_base_type_bounds src2
                   -> exprf base_type op (var:=ovar) dst1)
     with
     | Plus T1, Plus T2
       => fun args args2
          => LetIn args
                   (fun args
                    => Op (Cast _ _) (Op (Plus (base_type_max
                                                  (bound_type T2 (interp_op_bounds (Plus _) args2))
                                                  (base_type_max
                                                     (bound_type T2 (fst args2))
                                                     (bound_type T2 (snd args2)))))
                                         (Pair (Op (Cast _ _) (Var (fst args)))
                                               (Op (Cast _ _) (Var (snd args))))))
     | Const _ _ as e, _
       => fun args args2 => Op e TT
     | Cast _ _ as e, Plus _
     | Cast _ _ as e, Const _ _
     | Cast _ _ as e, Cast _ _
       => fun args args2 => Op e args
     | Plus _, _
       => fun args args2 => @failf _ _
     end.

Definition interpf_smart_bound {var t}
           (e : interp_flat_type var t) (bounds : interp_flat_type interp_base_type_bounds t)
  : interp_flat_type (fun t => exprf _ op (var:=var) (Tbase t)) (new_flat_type bounds)
  := SmartFlatTypeMap2Interp2
       (f:=fun t v => Tbase _)
       (fun t bs v => Op (Cast t (bound_type t bs)) (Var v)) bounds e.
Definition interpf_smart_unbound {var t}
           (bounds : interp_flat_type interp_base_type_bounds t)
           (e : interp_flat_type (fun t => exprf _ op (var:=var) (Tbase t)) (new_flat_type bounds))
  : interp_flat_type (fun t => @exprf base_type op var (Tbase t)) t
  := SmartFlatTypeMapUnInterp2
       (f:=fun t v => Tbase (bound_type t _))
       (fun t bs v => Op (Cast (bound_type t bs) t) v)
       e.

Definition smart_boundf {var t1} (e1 : exprf base_type op (var:=var) t1) (bounds : interp_flat_type interp_base_type_bounds t1)
  : exprf base_type op (var:=var) (new_flat_type bounds)
  := LetIn e1 (fun e1' => SmartPairf (var:=var) (interpf_smart_bound e1' bounds)).
Fixpoint UnSmartArrow {P t}
  : forall (e_bounds : interp_type interp_base_type_bounds t)
           (input_bounds : interp_all_binders_for' t interp_base_type_bounds)
           (e : P (SmartArrow (new_flat_type input_bounds)
                              (new_flat_type (ApplyInterpedAll' e_bounds input_bounds)))),
    P (new_type e_bounds input_bounds)
  := match t
           return (forall (e_bounds : interp_type interp_base_type_bounds t)
                          (input_bounds : interp_all_binders_for' t interp_base_type_bounds)
                          (e : P (SmartArrow (new_flat_type input_bounds)
                                             (new_flat_type (ApplyInterpedAll' e_bounds input_bounds)))),
                      P (new_type e_bounds input_bounds))
     with
     | Tflat T => fun _ _ x => x
     | Arrow A B => fun e_bounds input_bounds
                    => @UnSmartArrow
                         (fun t => P (Arrow (bound_type A (fst input_bounds)) t))
                         B
                         (e_bounds (fst input_bounds))
                         (snd input_bounds)
     end.
Definition smart_bound {var t1} (e1 : expr base_type op (var:=var) t1)
           (e_bounds : interp_type interp_base_type_bounds t1)
           (input_bounds : interp_all_binders_for' t1 interp_base_type_bounds)
  : expr base_type op (var:=var) (new_type e_bounds input_bounds)
  := UnSmartArrow
       e_bounds
       input_bounds
       (SmartAbs
          (fun args
           => LetIn
                args
                (fun args
                 => LetIn
                      (SmartPairf (interpf_smart_unbound input_bounds (SmartVarfMap (fun _ => Var) args)))
                      (fun v => smart_boundf
                                  (ApplyAll e1 (interp_all_binders_for_of' v))
                                  (ApplyInterpedAll' e_bounds input_bounds))))).
Definition SmartBound {t1} (e : Expr base_type op t1)
           (input_bounds : interp_all_binders_for' t1 interp_base_type_bounds)
  : Expr base_type op (new_type _ input_bounds)
  := fun var => smart_bound (e var) (interp (@interp_op_bounds) (e _)) input_bounds.


Definition SmartCast_base {var A A'} (x : exprf base_type op (var:=var) (Tbase A))
  : exprf base_type op (var:=var) (Tbase A')
  := match base_type_eq_dec A A' with
     | left pf => match pf with
                  | eq_refl => x
                  end
     | right _ => Op (Cast _ A') x
     end.
(** We can squash [a -> b -> c] into [a -> c] if [min a b c = min a
    c], i.e., if the narrowest type we pass through in the original
    case is the same as the narrowest type we pass through in the new
    case. *)
Definition squash_cast {var} (a b c : base_type) : @exprf base_type op var (Tbase a) -> @exprf base_type op var (Tbase c)
  := if base_type_beq (base_type_min b (base_type_min a c)) (base_type_min a c)
     then SmartCast_base
     else fun x => Op (Cast b c) (Op (Cast a b) x).
Fixpoint maybe_push_cast {var t} (v : @exprf base_type op var t) : option (@exprf base_type op var t)
  := match v in exprf _ _ t return option (exprf _ _ t) with
     | Var _ _ as v'
       => Some v'
     | Op t1 tR opc args
       => match opc in op src dst return exprf _ _ src -> option (exprf _ _ dst) with
          | Cast b c
            => fun args
               => match @maybe_push_cast _ _ args with
                  | Some (Op _ _ opc' args')
                    => match opc' in op src' dst' return exprf _ _ src' -> option (exprf _ _ (Tbase c)) with
                       | Cast a b
                         => fun args''
                            => Some (squash_cast a b c args'')
                       | Const _ v
                         => fun args''
                            => Some (SmartCast_base (Op (Const v) TT))
                       | _ => fun _ => None
                       end args'
                  | Some (Var _ v as v') => Some (SmartCast_base v')
                  | Some _ => None
                  | None => None
                  end
          | Const _ v
            => fun _ => Some (Op (Const v) TT)
          | _ => fun _ => None
          end args
     | Pair _ _ _ _
     | LetIn _ _ _ _
     | TT
       => None
     end.
Definition push_cast {var t} : @exprf base_type op var t -> inline_directive (op:=op) (var:=var) t
  := match t with
     | Tbase _ => fun v => match maybe_push_cast v with
                           | Some e => inline e
                           | None => default_inline v
                           end
     | _ => default_inline
     end.

Definition Boundify {t1} (e1 : Expr base_type op t1) args2
  : Expr _ _ _
  := InlineConstGen
       (@push_cast)
       (Linearize
          (SmartBound
             (@MapInterpCast
                base_type interp_base_type_bounds
                op (@interp_op_bounds)
                (@failf)
                (@bound_op)
                t1 e1 (interp_all_binders_for_to' args2))
             (interp_all_binders_for_to' args2))).

(** * Examples *)

Example ex1 : Expr base_type op TNat := fun var =>
  LetIn (Constf (t:=Nat) 127) (fun a : var Nat =>
  LetIn (Constf (t:=Nat) 63) (fun b : var Nat =>
  LetIn (Op (tR:=TNat) (Plus Nat) (Pair (Var a) (Var b))) (fun c : var Nat =>
  Op (Plus Nat) (Pair (Var c) (Var c))))).

Example ex1f : Expr base_type op (Arrow Nat (Arrow Nat TNat)) := fun var =>
  Abs (fun a0 =>
  Abs (fun b0 =>
  LetIn (Var a0) (fun a : var Nat =>
  LetIn (Var b0) (fun b : var Nat =>
  LetIn (Op (tR:=TNat) (Plus Nat) (Pair (Var a) (Var b))) (fun c : var Nat =>
  Op (Plus Nat) (Pair (Var c) (Var c))))))).

Eval compute in (Interp (@interp_op) ex1).
Eval cbv -[plus] in (Interp (@interp_op) ex1f).

Notation e x := (exist _ x _).

Definition ex1b := Boundify ex1 tt.
Eval compute in ex1b.

Definition ex1fb := Boundify ex1f (63, 63)%core.
Eval compute in ex1fb.
