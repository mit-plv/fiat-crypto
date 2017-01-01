Require Import Coq.omega.Omega.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.MapInterp.

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
Definition interp_base_type_bounds (t : base_type)
  := nat.
Local Notation TNat := (Tbase Nat).
Local Notation TWord8 := (Tbase Word8).
Local Notation TWord9 := (Tbase Word9).
Inductive op : flat_type base_type -> flat_type base_type -> Set :=
| Plus (t : base_type) : op (Tbase t * Tbase t) (Tbase t)
| Cast (t1 t2 : base_type) : op (Tbase t1) (Tbase t2).

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
     | Plus Nat => fun xy => fst xy + snd xy
     | Plus Word8 => fun xy => fst xy +8 snd xy
     | Plus Word9 => fun xy => fst xy +9 snd xy
     | Cast t1 t2 => fun x => bound (unbound x)
     end.

Definition interp_op_bounds {src dst} (opc : op src dst) : interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst
  := match opc in op src dst return interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst with
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

Fixpoint VarBound {var} T1 T2 : interp_flat_type var T1 -> exprf base_type interp_base_type op (var:=var) T2
  := match T1, T2 return interp_flat_type var T1 -> exprf base_type interp_base_type op (var:=var) T2 with
     | Tbase T1', Tbase T2' => fun v : var T1' => Op (Cast _ _) (Var v)
     | Prod A1 B1, Prod A2 B2
       => fun xy
          => Pair (@VarBound _ _ _ (fst xy)) (@VarBound _ _ _ (snd xy))
     | Tbase _, _
     | Prod _ _, _
       => fun _ => Const (SmartValf _ (@failv) _)
     end.

Fixpoint SmartBound {var t1 t2} (v : @exprf base_type interp_base_type op var t1) : @exprf base_type interp_base_type op var t2.
Proof.
  refine (match flat_type_eq_dec _ base_type_beq internal_base_type_dec_bl internal_base_type_dec_lb t1 t2 with
          | left pf => match pf in (_ = y) return exprf _ _ _ y with
                       | eq_refl => v
                       end
          | right pf => _
          end).
  refine (match v in exprf _ _ _ t1, t2 return (exprf _ _ _ _ -> exprf _ _ _ t2) -> exprf _ _ _ t2 with
          | Op t1 tR (Cast _ _) args, _ => fun _ => @SmartBound _ _ _ args
          | Pair _ ex _ ey, Prod _ _ => fun _ => Pair (@SmartBound _ _ _ ex) (@SmartBound _ _ _ ey)
          | v', _ => fun default => default v'
          end _).
  refine (match t1, t2 return exprf base_type interp_base_type op t1 -> exprf base_type interp_base_type op t2 with
          | Tbase t1', Tbase t2' => Op (Cast _ _)
          | Prod A1 B1, Prod A2 B2 => fun x => LetIn x (VarBound _ _)
          | Tbase _, _
          | Prod _ _, _
            => fun _ => Const (SmartValf _ (@failv) _)
          end).
Defined.
Definition bound_base_const t1 t2 (x1 : interp_base_type t1) (x2 : interp_base_type_bounds t2) : interp_base_type (bound_type _ x2)
  := bound (unbound x1).
Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
  := (@SmartFlatTypeMap2 _ _ interp_base_type_bounds (fun t v => Tbase (bound_type t v))).
Definition bound_op ovar
           {src1 dst1 src2 dst2}
           (opc1 : op src1 dst1)
           (opc2 : op src2 dst2)
  : forall args2
           (args' : @exprf base_type interp_base_type op ovar (@new_flat_type _ (interpf (@interp_op_bounds) args2))),
    @exprf base_type interp_base_type op ovar (@new_flat_type _ (interpf (@interp_op_bounds) (Op opc2 args2)))
  := match opc1 in op src1 dst1, opc2 in op src2 dst2
           return (forall (args2 : exprf _ _ _ src2)
                          (args' : @exprf base_type interp_base_type op ovar (@new_flat_type _ (interpf (@interp_op_bounds) args2))),
                      @exprf base_type interp_base_type op ovar (@new_flat_type _ (interpf (@interp_op_bounds) (Op opc2 args2))))
     with
     | Plus T1, Plus T2 => fun args2 args' => Op (Plus _) (SmartBound args')
     | Cast t1 t2, Plus _
     | Cast t1 t2, Cast _ _
       => fun _ x => SmartBound x
     | Plus _, _
       => fun _ _ => Const (SmartValf _ (@failv) _)
     end.
Section with_ovar.
  Context (ovar : base_type -> Type).
  Local Notation ivar t := (@exprf base_type interp_base_type op ovar (Tbase t)) (only parsing).
  Local Notation ivarf := (fun t => ivar t).

  Fixpoint bound_var (tx1 tx2 tC1 : flat_type base_type)
           {struct tx2}
    : forall (f : interp_flat_type ivarf tx1 -> exprf base_type interp_base_type op (var:=ovar) tC1)
             (v : interp_flat_type ivarf tx2),
      exprf base_type interp_base_type op (var:=ovar) tC1
    := match tx1, tx2 return (interp_flat_type _ tx1 -> _) -> interp_flat_type _ tx2 -> _ with
       | Tbase T1, Tbase T2 => fun f v => f (SmartBound v)
       | Prod A1 B1, Prod A2 B2
         => fun f v
            => @bound_var
                 _ _ _
                 (fun v1 => @bound_var _ _ _ (fun v2 => f (v1, v2)) (snd v))
                 (fst v)
       | Tbase _, _
       | Prod _ _, _
         => fun f _ => f (SmartValf _ (fun t => Const (t:=Tbase _) (@failv t)) _)
       end.
End with_ovar.

Definition mapf_to_bounds_interp {var t1} (e1 : @exprf base_type interp_base_type op var t1)
  : @exprf base_type interp_base_type_bounds op var t1
  := mapf_interp (@unbound) e1.
Definition map_to_bounds_interp {var t1} (e1 : @expr base_type interp_base_type op var t1)
  : @expr base_type interp_base_type_bounds op var t1
  := map_interp (@unbound) e1.
Definition MapToBoundsInterp {t1} (e1 : @Expr base_type interp_base_type op t1)
  : @Expr base_type interp_base_type_bounds op t1
  := fun var => map_to_bounds_interp (e1 _).

Print map_interp_cast.

Definition Boundify {t1} (e1 : Expr base_type interp_base_type op t1) args2
  : Expr _ _ _ _
  := fun ovar
     => @map_interp_cast
          base_type base_type interp_base_type interp_base_type_bounds
          op op (@interp_op_bounds) (@failv)
          (@bound_type) bound_base_const bound_op
          ovar
          (@bound_var ovar)
          t1 (e1 _) t1 (MapToBoundsInterp e1 _) args2.

(** * Examples *)

Example ex1 : Expr base_type interp_base_type op TNat := fun var =>
  LetIn (Const (t:=TNat) 127) (fun a : var Nat =>
  LetIn (Const (t:=TNat) 63) (fun b : var Nat =>
  LetIn (Op (tR:=TNat) (Plus Nat) (Pair (Var a) (Var b))) (fun c : var Nat =>
  Op (Plus Nat) (Pair (Var c) (Var c))))).

Example ex1f : Expr base_type interp_base_type op (Nat -> Nat -> TNat) := fun var =>
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

Definition ex1fb := Boundify ex1f (63, (63, tt))%core.
Eval compute in ex1fb.
