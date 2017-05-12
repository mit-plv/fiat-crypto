(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Import Crypto.Compilers.CommonSubexpressionEliminationProperties.

Local Set Decidable Equality Schemes.
Local Set Boolean Equality Schemes.
Inductive symbolic_op :=
| SOpConst (z : Z)
| SAdd
| SSub
| SMul
| SShl
| SShr
| SLand
| SLor
| SOpp
| SZselect
| SAddWithCarry
| SAddWithGetCarry (bitwidth : Z)
.

Definition symbolic_op_leb (x y : symbolic_op) : bool
  := match x, y with
     | SOpConst z1, SOpConst z2 => Z.leb z1 z2
     | SAddWithGetCarry bw1, SAddWithGetCarry bw2 => Z.leb bw1 bw2
     | SOpConst _, _ => true
     | _, SOpConst _ => false
     | SAdd, _ => true
     | _, SAdd => false
     | SSub, _ => true
     | _, SSub => false
     | SMul, _ => true
     | _, SMul => false
     | SShl, _ => true
     | _, SShl => false
     | SShr, _ => true
     | _, SShr => false
     | SLand, _ => true
     | _, SLand => false
     | SLor, _ => true
     | _, SLor => false
     | SOpp, _ => true
     | _, SOpp => false
     | SZselect, _ => true
     | _, SZselect => false
     | SAddWithCarry, _ => true
     | _, SAddWithCarry => false
     (*| SAddWithGetCarry _, _ => true
     | _, SAddWithGetCarry _ => false*)
     end.

Local Notation symbolic_expr := (@symbolic_expr base_type symbolic_op).
Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type symbolic_op base_type_beq symbolic_op_beq).
Local Notation symbolic_expr_leb := (@symbolic_expr_leb base_type symbolic_op base_type_beq symbolic_op_beq symbolic_op_leb base_type_leb).

Definition symbolize_op s d (opc : op s d) : symbolic_op
  := match opc with
     | OpConst T z => SOpConst z
     | Add T1 T2 Tout => SAdd
     | Sub T1 T2 Tout => SSub
     | Mul T1 T2 Tout => SMul
     | Shl T1 T2 Tout => SShl
     | Shr T1 T2 Tout => SShr
     | Land T1 T2 Tout => SLand
     | Lor T1 T2 Tout => SLor
     | Opp T Tout => SOpp
     | Zselect T1 T2 T3 Tout => SZselect
     | AddWithCarry T1 T2 T3 Tout => SAddWithCarry
     | AddWithGetCarry bitwidth T1 T2 T3 Tout1 Tout2 => SAddWithGetCarry bitwidth
     end.

Definition denote_symbolic_op s d (opc : symbolic_op) : option (op s d)
  := match opc, s, d with
     | SOpConst z, Unit, Tbase T => Some (OpConst z)
     | SAdd, Prod (Tbase _) (Tbase _), Tbase _ => Some (Add _ _ _)
     | SSub, Prod (Tbase _) (Tbase _), Tbase _ => Some (Sub _ _ _)
     | SMul, Prod (Tbase _) (Tbase _), Tbase _ => Some (Mul _ _ _)
     | SShl, Prod (Tbase _) (Tbase _), Tbase _ => Some (Shl _ _ _)
     | SShr, Prod (Tbase _) (Tbase _), Tbase _ => Some (Shr _ _ _)
     | SLand, Prod (Tbase _) (Tbase _), Tbase _ => Some (Land _ _ _)
     | SLor, Prod (Tbase _) (Tbase _), Tbase _ => Some (Lor _ _ _)
     | SOpp, Tbase _, Tbase _ => Some (Opp _ _)
     | SZselect, Prod (Prod (Tbase _) (Tbase _)) (Tbase _), Tbase _ => Some (Zselect _ _ _ _)
     | SAddWithCarry, Prod (Prod (Tbase _) (Tbase _)) (Tbase _), Tbase _ => Some (AddWithCarry _ _ _ _)
     | SAddWithGetCarry bitwidth, Prod (Prod (Tbase _) (Tbase _)) (Tbase _), Prod (Tbase _) (Tbase _)
       => Some (AddWithGetCarry bitwidth _ _ _ _ _)
     | SAdd, _, _
     | SSub, _, _
     | SMul, _, _
     | SShl, _, _
     | SShr, _, _
     | SLand, _, _
     | SLor, _, _
     | SOpp, _, _
     | SOpConst _, _, _
     | SZselect, _, _
     | SAddWithCarry, _, _
     | SAddWithGetCarry _, _, _
       => None
     end.

Lemma symbolic_op_leb_total
  : forall a1 a2, symbolic_op_leb a1 a2 = true \/ symbolic_op_leb a2 a1 = true.
Proof.
  induction a1, a2; simpl; auto;
    rewrite !Z.leb_le; omega.
Qed.

Module SymbolicExprOrder <: TotalLeBool.
  Definition t := (flat_type base_type * symbolic_expr)%type.
  Definition leb (x y : t) : bool := symbolic_expr_leb (snd x) (snd y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros; apply symbolic_expr_leb_total;
      auto using internal_base_type_dec_bl, internal_base_type_dec_lb, internal_symbolic_op_dec_bl, internal_symbolic_op_dec_lb, base_type_leb_total, symbolic_op_leb_total.
  Qed.
End SymbolicExprOrder.

Module Import SymbolicExprSort := Sort SymbolicExprOrder.

Fixpoint symbolic_op_args_to_list (t : flat_type base_type)
         (opc : symbolic_op) (args : symbolic_expr)
  : list (flat_type base_type * symbolic_expr)
  := match args, t with
     | SOp argT opc' args', _
       => if symbolic_op_beq opc opc'
          then symbolic_op_args_to_list argT opc args'
          else (t, args)::nil
     | SPair x y, Prod A B
       => symbolic_op_args_to_list A opc x ++ symbolic_op_args_to_list B opc y
     | SPair x y, Unit
       => symbolic_op_args_to_list Unit opc x ++ symbolic_op_args_to_list Unit opc y
     | STT, _
     | SVar _, _
     | SPair _ _, _
     | SFst _ _ _, _
     | SSnd _ _ _, _
     | SInvalid, _
       => (t, args)::nil
     end%list.

Fixpoint symbolic_op_list_to_args (args : list (flat_type base_type * symbolic_expr)) : symbolic_expr
  := match args with
     | nil => SInvalid
     | (t, arg)::nil => arg
     | (t1, arg1)::(t2, arg2)::nil
       => SPair arg1 arg2
     | (t1, arg1)::(((t2, arg2)::args'') as args')
       => SPair arg1 (SOp t2 SAdd (symbolic_op_list_to_args args'))
     end%list.

Definition normalize_symbolic_expr_mod_c (opc : symbolic_op) (args : symbolic_expr) : symbolic_expr
  := match opc with
     | SAdd
     | SMul
     | SLand
     | SLor
       => let ls := symbolic_op_args_to_list Unit opc args in
          let ls := sort ls in
          symbolic_op_list_to_args ls
     | SOpConst _
     | SSub
     | SShl
     | SShr
     | SOpp
     | SZselect
     | SAddWithCarry
     | SAddWithGetCarry _
       => args
     end.

Definition csef inline_symbolic_expr_in_lookup {var t} (v : exprf _ _ t) xs
  := @csef base_type symbolic_op base_type_beq symbolic_op_beq
           internal_base_type_dec_bl op symbolize_op
           normalize_symbolic_expr_mod_c
           var inline_symbolic_expr_in_lookup t v xs.

Definition cse inline_symbolic_expr_in_lookup {var} (prefix : list _) {t} (v : expr _ _ t) xs
  := @cse base_type symbolic_op base_type_beq symbolic_op_beq
          internal_base_type_dec_bl op symbolize_op
          normalize_symbolic_expr_mod_c
          inline_symbolic_expr_in_lookup var prefix t v xs.

Definition CSE_gen inline_symbolic_expr_in_lookup {t} (e : Expr _ _ t) (prefix : forall var, list { t : flat_type base_type & exprf _ _ t })
  : Expr _ _ t
  := @CSE base_type symbolic_op base_type_beq symbolic_op_beq
          internal_base_type_dec_bl op symbolize_op
          normalize_symbolic_expr_mod_c
          inline_symbolic_expr_in_lookup t e prefix.

Definition CSE inline_symbolic_expr_in_lookup {t} (e : Expr _ _ t)
  : Expr _ _ t
  := @CSE_gen inline_symbolic_expr_in_lookup t e (fun _ => nil).
