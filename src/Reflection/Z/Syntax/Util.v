Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Definition make_const t : interp_base_type t -> op Unit (Tbase t)
  := fun v => OpConst (cast_const (t2:=TZ) v).
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ _ => true | _ => false end.
Arguments is_const [s d] v.

Definition cast_back_flat_const {var t f V}
           (v : interp_flat_type interp_base_type (@SmartFlatTypeMap base_type var f t V))
  : interp_flat_type interp_base_type t
  := @SmartFlatTypeMapUnInterp
       _ var interp_base_type interp_base_type
       f (fun _ _ => cast_const)
       t V v.

Definition cast_flat_const {var t f V}
           (v : interp_flat_type interp_base_type t)
  : interp_flat_type interp_base_type (@SmartFlatTypeMap base_type var f t V)
  := @SmartFlatTypeMapInterp2
       _ var interp_base_type interp_base_type
       f (fun _ _ => cast_const)
       t V v.

Definition base_type_leb (v1 v2 : base_type) : bool
  := match v1, v2 with
     | _, TZ => true
     | TZ, _ => false
     | TWord logsz1, TWord logsz2 => Compare_dec.leb logsz1 logsz2
     end.

Definition base_type_min := base_type_min base_type_leb.
Definition base_type_max := base_type_max base_type_leb.
Global Arguments base_type_min !_ !_ / .
Global Arguments base_type_max !_ !_ / .
Global Arguments TypeUtil.base_type_min _ _ _ /  _.
Global Arguments TypeUtil.base_type_max _ _ _ /  _.

Definition genericize_op {var' src dst} (opc : op src dst) {f}
  : forall {vs vd}, op (@SmartFlatTypeMap _ var' f src vs) (@SmartFlatTypeMap _ var' f dst vd)
  := match opc with
     | OpConst _ z => fun _ _ => OpConst z
     | Add _ _ _ => fun _ _ => Add _ _ _
     | Sub _ _ _ => fun _ _ => Sub _ _ _
     | Mul _ _ _ => fun _ _ => Mul _ _ _
     | Shl _ _ _ => fun _ _ => Shl _ _ _
     | Shr _ _ _ => fun _ _ => Shr _ _ _
     | Land _ _ _ => fun _ _ => Land _ _ _
     | Lor _ _ _ => fun _ _ => Lor _ _ _
     | Neg _ _ int_width => fun _ _ => Neg _ _ int_width
     | Cmovne _ _ _ _ _ => fun _ _ => Cmovne _ _ _ _ _
     | Cmovle _ _ _ _ _ => fun _ _ => Cmovle _ _ _ _ _
     end.

Lemma cast_const_id {t} v
  : @cast_const t t v = v.
Proof.
  destruct t; simpl; trivial.
  rewrite ZToWord_wordToZ; reflexivity.
Qed.

Lemma cast_const_idempotent {a b c} v
  : base_type_min b (base_type_min a c) = base_type_min a c
    -> @cast_const b c (@cast_const a b v) = @cast_const a c v.
Proof.
  repeat first [ reflexivity
               | congruence
               | progress destruct_head' base_type
               | progress simpl
               | progress break_match
               | progress subst
               | intro
               | match goal with
                 | [ H : ?leb _ _ = true |- _ ] => apply Compare_dec.leb_complete in H
                 | [ H : ?leb _ _ = false |- _ ] => apply Compare_dec.leb_iff_conv in H
                 | [ H : TWord _ = TWord _ |- _ ] => inversion H; clear H
                 end
               | rewrite ZToWord_wordToZ_ZToWord by omega *
               | rewrite wordToZ_ZToWord_wordToZ by omega * ].
Qed.

Lemma make_const_correct : forall T v, interp_op Unit (Tbase T) (make_const T v) tt = v.
Proof.
  destruct T; cbv -[FixedWordSizes.ZToWord FixedWordSizes.wordToZ FixedWordSizes.wordT];
    intro; rewrite ?ZToWord_wordToZ; reflexivity.
Qed.

Local Notation iffT A B := ((A -> B) * (B -> A))%type (only parsing).

Section unzify.
  Context {var'} {f : forall t : base_type, var' t -> base_type}.
  Let asZ := fun t => SmartFlatTypeMap
                        (fun _ _ => TZ)
                        (SmartValf (fun _ => base_type) (fun t => t) t).
  Definition unzify_op_helper_step
             (unzify_op_helper
              : forall {t : flat_type base_type}
                       {vs : interp_flat_type var' t},
                 iffT (interp_flat_type
                         interp_base_type
                         (asZ t))
                      (interp_flat_type
                         interp_base_type
                         (asZ (SmartFlatTypeMap f vs))))
             {t : flat_type base_type}
    : forall {vs : interp_flat_type var' t},
      iffT (interp_flat_type
              interp_base_type
              (asZ t))
           (interp_flat_type
              interp_base_type
              (asZ (SmartFlatTypeMap f vs)))
    := match t with
       | Tbase T => fun _ => (fun x => x, fun x => x)
       | Unit => fun _ => (fun x => x, fun x => x)
       | Prod A B
         => fun (vs : interp_flat_type _ A * interp_flat_type _ B)
            => let f1 := @unzify_op_helper A (fst vs) in
               let f2 := @unzify_op_helper B (snd vs) in
               ((fun x : interp_flat_type _ (asZ A) * interp_flat_type _ (asZ B)
                 => (fst f1 (fst x), fst f2 (snd x))),
                (fun x : interp_flat_type _ (asZ (SmartFlatTypeMap f (fst vs)))
                         * interp_flat_type _ (asZ (SmartFlatTypeMap f (snd vs)))
                 => (snd f1 (fst x), snd f2 (snd x))))
       end.
  Fixpoint unzify_op_helper {t vs}
    := @unzify_op_helper_step (@unzify_op_helper) t vs.

  Definition unzify_op
             {src dst : flat_type base_type}
             {vs : interp_flat_type var' src} {vd : interp_flat_type var' dst}
             (F : interp_flat_type interp_base_type (asZ src) -> interp_flat_type interp_base_type (asZ dst))
             (x : interp_flat_type interp_base_type (asZ (SmartFlatTypeMap f vs)))
    : interp_flat_type interp_base_type (asZ (SmartFlatTypeMap f vd))
    := fst unzify_op_helper (F (snd unzify_op_helper x)).
End unzify.

Arguments unzify_op_helper_step _ _ _ !_ _ / .
Arguments unzify_op_helper _ _ !_ _ / .

Lemma Zinterp_op_genericize_op {var' src dst opc f vs vd}
  : Zinterp_op _ _ (@genericize_op var' src dst opc f vs vd)
    = unzify_op (Zinterp_op _ _ opc).
Proof.
  destruct opc; unfold unzify_op; reflexivity.
Qed.

Lemma lift_op_prod_dst {src dstA dstB}
      {f : _ -> interp_flat_type _ (SmartFlatTypeMap _ (SmartValf _ _ _)) * interp_flat_type _ (SmartFlatTypeMap _ (SmartValf _ _ _))}
      {x}
  : @lift_op src (Prod dstA dstB) f x
    = (@lift_op src dstA (fun y => fst (f y)) x, @lift_op src dstB (fun y => snd (f y)) x).
Proof. reflexivity. Qed.

Lemma cast_back_flat_const_prod {var A B f} {V : _ * _}
      (v : interp_flat_type interp_base_type (@SmartFlatTypeMap base_type var f A (fst V))
           * interp_flat_type interp_base_type (@SmartFlatTypeMap base_type var f B (snd V)))
  : @cast_back_flat_const var (Prod A B) f V v
    = (@cast_back_flat_const var A f (fst V) (fst v),
       @cast_back_flat_const var B f (snd V) (snd v)).
Proof. reflexivity. Qed.
