Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Definition make_const t : interp_base_type t -> op Unit (Tbase t)
  := OpConst.
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ _ => true | _ => false end.
Arguments is_const [s d] v.
Definition is_cast s d (v : op s d) : bool
  := match v with Cast _ _ => true | _ => false end.
Arguments is_cast [s d] v.

Definition base_type_leb (v1 v2 : base_type) : bool
  := match v1, v2 with
     | _, TZ => true
     end.

Definition base_type_min := base_type_min base_type_leb.
Global Arguments base_type_min !_ !_ / .
Global Arguments TypeUtil.base_type_min _ _ _ /  _.

Definition Castb {var} A A' (v : exprf base_type op (var:=var) (Tbase A))
  : exprf base_type op (var:=var) (Tbase A')
  := Op (Cast A A') v.

Local Notation Se opv := (Some (existT _ (_, _) opv)) (only parsing).

Definition genericize_op src dst (opc : op src dst) (t_in t_out : base_type)
  : option { src'dst' : _ & op (fst src'dst') (snd src'dst') }
  := match opc with
     | OpConst T z => Se (OpConst z)
     | Add T => Se (Add t_out)
     | Sub T => Se (Sub t_in)
     | Mul T => Se (Mul t_out)
     | Shl T => Se (Shl t_out)
     | Shr T => Se (Shr t_in)
     | Land T => Se (Land t_out)
     | Lor T => Se (Lor t_out)
     | Neg T int_width => Se (Neg t_out int_width)
     | Cmovne T => Se (Cmovne t_out)
     | Cmovle T => Se (Cmovle t_out)
     | Cast T1 T2 => None
     end.

Lemma cast_const_id {t} v
  : @cast_const t t v = v.
Proof.
  destruct t; simpl; trivial.
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
                 end
               | rewrite ZToWord_wordToZ_ZToWord by omega *
               | rewrite wordToZ_ZToWord_wordToZ by omega * ].
Qed.

Lemma is_cast_correct s d opc
  : forall e,
    @is_cast (Tbase s) (Tbase d) opc = true
    -> Syntax.interp_op _ _ opc (interpf Syntax.interp_op e)
       = interpf Syntax.interp_op (Castb s d e).
Proof.
  preinvert_one_type opc; intros ? opc.
  pose (fun x y => op y x) as op'.
  change op with (fun x y => op' y x) in opc; cbv beta in opc.
  preinvert_one_type opc; intros ? opc; subst op'; cbv beta in *.
  destruct opc; try exact I; simpl; try congruence.
Qed.

Lemma wff_Castb {var1 var2 G A A'} {e1 e2 : exprf base_type op (Tbase A)}
      (Hwf : wff (var1:=var1) (var2:=var2) G e1 e2)
  : wff G (Castb A A' e1) (Castb A A' e2).
Proof. constructor; assumption. Qed.
