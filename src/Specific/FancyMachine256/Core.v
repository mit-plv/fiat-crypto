(** * A Fancy Machine with 256-bit registers *)
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Export Coq.ZArith.ZArith.
Require Export Crypto.BoundedArithmetic.Interface.
Require Export Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Export Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Export Crypto.Util.Tuple.
Require Import Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod.
Require Export Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.CommonSubexpressionElimination.
Require Export Crypto.Reflection.Reify.
Require Export Crypto.Util.ZUtil.
Require Export Crypto.Util.Notations.

Open Scope Z_scope.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta3' x := (fst x, eta (snd x)).

(** ** Reflective Assembly Syntax *)
Section reflection.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive base_type := TZ | Tbool | TW.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | TZ => Z
    | Tbool => bool
    | TW => fancy_machine.W
    end.
  Local Notation tZ := (Tbase TZ).
  Local Notation tbool := (Tbase Tbool).
  Local Notation tW := (Tbase TW).
  Local Open Scope ctype_scope.
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | OPldi     : op tZ tW
  | OPshrd    : op (tW * tW * tZ) tW
  | OPshl     : op (tW * tZ) tW
  | OPshr     : op (tW * tZ) tW
  | OPmkl     : op (tW * tZ) tW
  | OPadc     : op (tW * tW * tbool) (tbool * tW)
  | OPsubc    : op (tW * tW * tbool) (tbool * tW)
  | OPmulhwll : op (tW * tW) tW
  | OPmulhwhl : op (tW * tW) tW
  | OPmulhwhh : op (tW * tW) tW
  | OPselc    : op (tbool * tW * tW) tW
  | OPaddm    : op (tW * tW * tW) tW.

  Definition interp_op src dst (f : op src dst)
    : interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst
    := match f in op s d return interp_flat_type_gen _ s -> interp_flat_type_gen _ d with
       | OPldi     => ldi
       | OPshrd    => fun xyz => let '(x, y, z) := eta3 xyz in shrd x y z
       | OPshl     => fun xy => let '(x, y) := eta xy in shl x y
       | OPshr     => fun xy => let '(x, y) := eta xy in shr x y
       | OPmkl     => fun xy => let '(x, y) := eta xy in mkl x y
       | OPadc     => fun xyz => let '(x, y, z) := eta3 xyz in adc x y z
       | OPsubc    => fun xyz => let '(x, y, z) := eta3 xyz in subc x y z
       | OPmulhwll => fun xy => let '(x, y) := eta xy in mulhwll x y
       | OPmulhwhl => fun xy => let '(x, y) := eta xy in mulhwhl x y
       | OPmulhwhh => fun xy => let '(x, y) := eta xy in mulhwhh x y
       | OPselc    => fun xyz => let '(x, y, z) := eta3 xyz in selc x y z
       | OPaddm    => fun xyz => let '(x, y, z) := eta3 xyz in addm x y z
       end.

  Inductive SConstT := ZConst (_ : Z) | BoolConst (_ : bool) | INVALID_CONST.
  Inductive op_code : Set :=
  | SOPldi | SOPshrd | SOPshl | SOPshr | SOPmkl | SOPadc | SOPsubc
  | SOPmulhwll | SOPmulhwhl | SOPmulhwhh | SOPselc | SOPaddm.

  Definition symbolicify_const (t : base_type) : interp_base_type t -> SConstT
    := match t with
       | TZ => fun x => ZConst x
       | Tbool => fun x => BoolConst x
       | TW => fun x => INVALID_CONST
       end.
  Definition symbolicify_op s d (v : op s d) : op_code
    := match v with
       | OPldi => SOPldi
       | OPshrd => SOPshrd
       | OPshl => SOPshl
       | OPshr => SOPshr
       | OPmkl => SOPmkl
       | OPadc => SOPadc
       | OPsubc => SOPsubc
       | OPmulhwll => SOPmulhwll
       | OPmulhwhl => SOPmulhwhl
       | OPmulhwhh => SOPmulhwhh
       | OPselc => SOPselc
       | OPaddm => SOPaddm
       end.

  Definition CSE {t} e := @CSE base_type SConstT op_code base_type_beq SConstT_beq op_code_beq internal_base_type_dec_bl interp_base_type op symbolicify_const symbolicify_op t e (fun _ => nil).
End reflection.

Ltac base_reify_op op op_head ::=
     lazymatch op_head with
     | @Interface.ldi => constr:(reify_op op op_head 1 OPldi)
     | @Interface.shrd => constr:(reify_op op op_head 3 OPshrd)
     | @Interface.shl => constr:(reify_op op op_head 2 OPshl)
     | @Interface.shr => constr:(reify_op op op_head 2 OPshr)
     | @Interface.mkl => constr:(reify_op op op_head 2 OPmkl)
     | @Interface.adc => constr:(reify_op op op_head 3 OPadc)
     | @Interface.subc => constr:(reify_op op op_head 3 OPsubc)
     | @Interface.mulhwll => constr:(reify_op op op_head 2 OPmulhwll)
     | @Interface.mulhwhl => constr:(reify_op op op_head 2 OPmulhwhl)
     | @Interface.mulhwhh => constr:(reify_op op op_head 2 OPmulhwhh)
     | @Interface.selc => constr:(reify_op op op_head 3 OPselc)
     | @Interface.addm => constr:(reify_op op op_head 3 OPaddm)
     end.
Ltac base_reify_type T ::=
     match T with
     | Z => TZ
     | bool => Tbool
     | fancy_machine.W => TW
     end.

Ltac Reify' e := Reify.Reify' base_type (interp_base_type _) op e.
Ltac Reify e :=
  let v := Reify.Reify base_type (interp_base_type _) op e in
  constr:(CSE _ (InlineConst (Linearize v))).
(*Ltac Reify_rhs := Reify.Reify_rhs base_type (interp_base_type _) op (interp_op _).*)

(** ** Raw Syntax Trees *)
(** These are used solely for pretty-printing the expression tree in a
    form that can be basically copy-pasted into other languages which
    can be compiled for the Fancy Machine.  Hypothetically, we could
    add support for custom named identifiers, by carrying around
    [string] identifiers and using them for pretty-printing...  It
    might also be possible to verify this layer, too, by adding a
    partial interpretation function... *)
Section syn.
  Context {var : base_type -> Type}.
  Inductive syntax :=
  | RegPInv
  | RegMod
  | RegMuLow
  | RegZero
  | cConstZ : Z -> syntax
  | cConstBool : bool -> syntax
  | cLowerHalf : syntax -> syntax
  | cUpperHalf : syntax -> syntax
  | cLeftShifted : syntax -> Z -> syntax
  | cRightShifted : syntax -> Z -> syntax
  | cVar : var TW -> syntax
  | cVarC : var Tbool -> syntax
  | cBind : syntax -> (var TW -> syntax) -> syntax
  | cBindCarry : syntax -> (var Tbool -> var TW -> syntax) -> syntax
  | cMul128 : syntax -> syntax -> syntax
  | cRshi : syntax -> syntax -> Z -> syntax
  | cSelc : var Tbool -> syntax -> syntax -> syntax
  | cAddc : var Tbool -> syntax -> syntax -> syntax
  | cAddm : syntax -> syntax -> syntax
  | cAdd : syntax -> syntax -> syntax
  | cSub : syntax -> syntax -> syntax
  | cPair : syntax -> syntax -> syntax
  | cAbs {t} : (var t -> syntax) -> syntax
  | cINVALID {T} (_ : T).
End syn.

Notation "'Return' x" := (cVar x) (at level 200).
Notation "'c.Mul128' ( x , A , B ) , b" :=
  (cBind (cMul128 A B) (fun x => b))
    (at level 200, b at level 200, format "'c.Mul128' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) (cVar B)) (fun c x => cBindCarry (cAddc c (cVar A1) (cVar B1)) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").

Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub A (cVar B)) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub (cVar A) (cVar B)) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").

Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm A B) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm A (cVar B)) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm (cVar A) B) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm (cVar A) (cVar B)) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").

Notation "'c.Rshi' ( x , A , B , C ) , b" :=
  (cBind (cRshi (cVar A) (cVar B) C) (fun x => b))
    (at level 200, b at level 200, format "'c.Rshi' ( x ,  A ,  B ,  C ) , '//' b").

Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf x)
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf (cVar x))
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf x)
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf (cVar x))
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted x v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted (cVar x) v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted x v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted (cVar x) v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Notation "'λ'  x .. y , t" := (cAbs (fun x => .. (cAbs (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Syntax := forall var, @syntax var.

(** Assemble a well-typed easily interpretable expression into a
    syntax tree we can use for pretty-printing. *)
Section assemble.
  Context (ops : fancy_machine.instructions (2 * 128)).

  Section with_var.
    Context {var : base_type -> Type}.

    Fixpoint assemble_syntax_const
             {t}
      : interp_flat_type_gen (interp_base_type _) t -> @syntax var
      := match t return interp_flat_type_gen (interp_base_type _) t -> @syntax var with
         | Tbase TZ => cConstZ
         | Tbase Tbool => cConstBool
         | Tbase t => fun _ => cINVALID t
         | Prod A B => fun xy => cPair (@assemble_syntax_const A (fst xy))
                                       (@assemble_syntax_const B (snd xy))
         end.

    Definition assemble_syntaxf_step
               (assemble_syntaxf : forall {t} (v : @Syntax.exprf base_type (interp_base_type _) op (fun _ => @syntax var) t), @syntax var)
               {t} (v : @Syntax.exprf base_type (interp_base_type _) op (fun _ => @syntax var) t) : @syntax var.
    Proof.
      refine match v return @syntax var with
             | Syntax.Const t x => assemble_syntax_const x
             | Syntax.Var _ x => x
             | Syntax.Op t1 tR op args
               => let v := @assemble_syntaxf t1 args in
                 (* handle both associativities of pairs in 3-ary
                    operators, in case we ever change the
                    associativity *)
                  match op, v with
                  | OPldi    , cConstZ 0 => RegZero
                  | OPldi    , cConstZ v => cINVALID v
                  | OPldi    , RegZero => RegZero
                  | OPldi    , RegMod => RegMod
                  | OPldi    , RegMuLow => RegMuLow
                  | OPldi    , RegPInv => RegPInv
                  | OPshrd   , cPair x (cPair y (cConstZ n)) => cRshi x y n
                  | OPshrd   , cPair (cPair x y) (cConstZ n) => cRshi x y n
                  | OPshl    , cPair w (cConstZ n) => cLeftShifted w n
                  | OPshr    , cPair w (cConstZ n) => cRightShifted w n
                  | OPmkl    , _ => cINVALID op
                  | OPadc    , cPair (cPair x y) (cVarC c) => cAddc c x y
                  | OPadc    , cPair x (cPair y (cVarC c)) => cAddc c x y
                  | OPadc    , cPair (cPair x y) (cConstBool false) => cAdd x y
                  | OPadc    , cPair x (cPair y (cConstBool false)) => cAdd x y
                  | OPsubc   , cPair (cPair x y) (cConstBool false) => cSub x y
                  | OPsubc   , cPair x (cPair y (cConstBool false)) => cSub x y
                  | OPmulhwll, cPair x y => cMul128 (cLowerHalf x) (cLowerHalf y)
                  | OPmulhwhl, cPair x y => cMul128 (cUpperHalf x) (cLowerHalf y)
                  | OPmulhwhh, cPair x y => cMul128 (cUpperHalf x) (cUpperHalf y)
                  | OPselc   , cPair (cVarC c) (cPair x y) => cSelc c x y
                  | OPselc   , cPair (cPair (cVarC c) x) y => cSelc c x y
                  | OPaddm   , cPair x (cPair y RegMod) => cAddm x y
                  | OPaddm   , cPair (cPair x y) RegMod => cAddm x y
                  | _, _ => cINVALID op
                  end
             | Syntax.Let tx ex _ eC
               => let ex' := @assemble_syntaxf _ ex in
                 let eC' := fun x => @assemble_syntaxf _ (eC x) in
                 let special := match ex' with
                                | RegZero as ex'' | RegMuLow as ex'' | RegMod as ex'' | RegPInv as ex''
                                | cUpperHalf _ as ex'' | cLowerHalf _ as ex''
                                | cLeftShifted _ _ as ex''
                                | cRightShifted _ _ as ex''
                                  => Some ex''
                                | _ => None
                                end in
                 match special, tx return (interp_flat_type_gen _ tx -> _) -> _ with
                 | Some x, Tbase _ => fun eC' => eC' x
                 | _, Tbase TW
                   => fun eC' => cBind ex' (fun x => eC' (cVar x))
                 | _, Prod (Tbase Tbool) (Tbase TW)
                   => fun eC' => cBindCarry ex' (fun c x => eC' (cVarC c, cVar x))
                 | _, _
                   => fun _ => cINVALID (fun x : Prop => x)
                 end eC'
             | Syntax.Pair _ ex _ ey
               => cPair (@assemble_syntaxf _ ex) (@assemble_syntaxf _ ey)
             end.
    Defined.

    Fixpoint assemble_syntaxf {t} v {struct v} : @syntax var
      := @assemble_syntaxf_step (@assemble_syntaxf) t v.
    Fixpoint assemble_syntax {t} (v : @Syntax.expr base_type (interp_base_type _) op (fun _ => @syntax var) t) (args : list (@syntax var)) {struct v}
      : @syntax var
      := match v, args return @syntax var with
         | Syntax.Return _ x, _ => assemble_syntaxf x
         | Syntax.Abs _ _ f, nil => cAbs (fun x => @assemble_syntax _ (f (cVar x)) args)
         | Syntax.Abs _ _ f, cons v vs => @assemble_syntax _ (f v) vs
         end.
  End with_var.

  Definition AssembleSyntax {t} (v : Syntax.Expr _ _ _ t) (args : list Syntax) : Syntax
    := fun var => @assemble_syntax var t (v _) (List.map (fun f => f var) args).
End assemble.
