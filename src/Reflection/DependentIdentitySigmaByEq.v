Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.LetIn.

Section demo_by_eq.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {var : base_type_code -> Type}
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall a b, base_type_code_beq a b = true -> a = b)
          (faileb : forall var t, @exprf base_type_code op var (Tbase t)).

  Local Notation ivar := (fun t => @exprf base_type_code op var (Tbase t)).

  Fixpoint faile {t} : @exprf base_type_code op var t
    := match t with
       | Tbase T => faileb _ _
       | Unit => TT
       | Prod A B => Pair (@faile A) (@faile B)
       end.
  Fixpoint failf {t} : interp_flat_type ivar t
    := match t with
       | Tbase T => faileb _ _
       | Unit => tt
       | Prod A B => (@failf A, @failf B)%core
       end.

  Definition cast_or (P : flat_type base_type_code -> Type) {A B : flat_type base_type_code}
             (x : P A) (default : P B)
    : P B
    := match sumbool_of_bool (@flat_type_beq _ base_type_code_beq A B) with
       | left pf => match @flat_type_dec_bl _ _ base_type_code_bl_transparent _ _ pf with
                    | eq_refl => x
                    end
       | right _ => default
       end.
  Definition cast_exprf {A B} (x : @exprf base_type_code op var A)
    : @exprf base_type_code op var B
    := cast_or (@exprf base_type_code op var) x (@faile _).
  Definition cast_ivarf {A B} (x : interp_flat_type ivar A)
    : interp_flat_type ivar B
    := cast_or (interp_flat_type _) x (@failf _).

  Section parametrized.
    Context (let_in : forall T t'
                             (A:=interp_flat_type ivar T -> @exprf base_type_code op var t')
                             (B:=@exprf base_type_code op var t'),
                A -> (A -> B) -> B).
    Fixpoint pexist_id {t} (e : @exprf base_type_code op ivar t)
      : { t' : _ & @exprf base_type_code op var t' }
      := match e with
         | TT => existT _ _ TT
         | Var t v => existT _ (Tbase t) v
         | Op t1 tR opc args
           => let (argsT, argsv) := @pexist_id _ args in
              existT _ _ (Op opc (cast_exprf argsv))
         | Pair tx ex ty ey
           => let (xT, xv) := @pexist_id _ ex in
              let (yT, yv) := @pexist_id _ ey in
              existT _ _ (Pair xv yv)
         | LetIn tx ex tC eC
           => dlet Cv := (fun v => @pexist_id _ (eC v)) in
              let (CfailT, Cfailv) := Cv failf in
              existT
                _
                CfailT
                (let_in
                   _ CfailT
                   (fun v => cast_exprf (projT2 (Cv v)))
                   (fun Cv'
                    => let (xT, xv) := @pexist_id _ ex in
                       LetIn xv
                             (fun v => cast_exprf (Cv' (cast_ivarf (SmartVarVarf v))))))
         end.
  End parametrized.
  Definition exist_id
             {t} (e : @exprf base_type_code op ivar t)
    : { t' : _ & @exprf base_type_code op var t' }
    := Eval cbv beta iota delta [pexist_id Let_In] in
        @pexist_id (fun _ _ x f => let y := x in f y) t e.
  Definition dexist_id
             {t} (e : @exprf base_type_code op ivar t)
    : { t' : _ & @exprf base_type_code op var t' }
    := Eval cbv [pexist_id] in
        @pexist_id (fun _ _ x f => dlet y := x in f y) t e.
End demo_by_eq.
