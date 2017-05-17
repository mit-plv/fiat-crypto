Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.TypeUtil.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.ZUtil.
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
     | Opp _ _ => fun _ _ => Opp _ _
     | Zselect _ _ _ _ => fun _ _ => Zselect _ _ _ _
     | AddWithCarry _ _ _ _ => fun _ _ => AddWithCarry _ _ _ _
     | AddWithGetCarry bitwidth _ _ _ _ _ => fun _ _ => AddWithGetCarry bitwidth _ _ _ _ _
     end.

Lemma cast_const_id {t} v
  : @cast_const t t v = v.
Proof.
  destruct t; simpl; trivial.
  rewrite ZToWord_wordToZ; reflexivity.
Qed.

Lemma cast_const_idempotent_small {a b c} v
  : match b with
    | TZ => True
    | TWord bsz => 0 <= interpToZ (@cast_const a c v) < 2^Z.of_nat (2^bsz)
    end%Z
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
               | rewrite wordToZ_ZToWord_wordToZ by omega *
               | rewrite wordToZ_ZToWord by assumption
               | rewrite ZToWord_wordToZ_ZToWord_small by omega ].
Qed.

Lemma cast_const_split_mod {a b} v
  : @cast_const a b v = ZToInterp (match a, b with
                                   | TZ, _ => interpToZ v
                                   | _, TWord lgsz => (interpToZ v) mod (2^Z.of_nat (2^lgsz))
                                   | _, TZ => interpToZ v
                                   end).
Proof.
  destruct_head base_type; simpl; try reflexivity.
  rewrite <- wordToZ_ZToWord_mod, ZToWord_wordToZ by apply wordToZ_range.
  reflexivity.
Qed.

Lemma interpToZ_cast_const_mod {a b} v
  : interpToZ (@cast_const a b v)
    = match b with
      | TZ => interpToZ v
      | TWord lgsz => Z.max 0 (interpToZ v) mod (2^Z.of_nat (2^lgsz))
      end%Z.
Proof.
  repeat first [ progress destruct_head base_type
               | reflexivity
               | rewrite wordToZ_ZToWord_mod_full ].
Qed.

Lemma cast_const_ZToInterp_mod {a b} v
  : @cast_const a b (ZToInterp v)
    = ZToInterp match a with
                | TZ => v
                | TWord lgsz => Z.max 0 v mod 2^Z.of_nat (2^lgsz)
                end%Z.
Proof.
  repeat first [ progress destruct_head base_type
               | reflexivity
               | rewrite wordToZ_ZToWord_mod_full ].
Qed.

Lemma interpToZ_ZToInterp_mod {a} v
  : @interpToZ a (ZToInterp v)
    = match a with
      | TZ => v
      | TWord lgsz => Z.max 0 v mod 2^Z.of_nat (2^lgsz)
      end%Z.
Proof.
  etransitivity; [ apply (@interpToZ_cast_const_mod TZ) | ].
  reflexivity.
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

Lemma ZToInterp_eq_inj {a} x y
  : @ZToInterp a x = @ZToInterp a y
    <-> match a with
        | TZ => x
        | TWord lgsz => Z.max 0 x mod 2^Z.of_nat (2^lgsz)
        end%Z
        = match a with
          | TZ => y
          | TWord lgsz => Z.max 0 y mod 2^Z.of_nat (2^lgsz)
          end%Z.
Proof.
  rewrite <- !interpToZ_ZToInterp_mod.
  destruct a; try reflexivity; simpl.
  split; intro H; try congruence.
  rewrite <- (ZToWord_wordToZ (FixedWordSizes.ZToWord x)), <- (ZToWord_wordToZ (FixedWordSizes.ZToWord y)).
  congruence.
Qed.

Lemma interpToZ_range {a} (v : interp_base_type a)
  : match a with
    | TZ => True
    | TWord lgsz => 0 <= interpToZ v < 2^Z.of_nat (2^lgsz)
    end%Z.
Proof.
  destruct a; trivial; simpl.
  apply wordToZ_range.
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

Lemma base_type_leb_total
  : forall x y : base_type, base_type_leb x y = true \/ base_type_leb y x = true.
Proof.
  induction x, y; simpl; auto.
  rewrite !Nat.leb_le; omega.
Qed.
