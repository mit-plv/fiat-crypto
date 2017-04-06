Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall a b, base_type_code_beq a b = true -> a = b)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t)).

  Local Notation pick_type
    := (@SmartFlatTypeMap _ _ pick_typeb).

  Context (cast_op : forall ovar t1 tR opc args_bs
                            (argsv : exprf base_type_code op (var:=ovar) (pick_type args_bs)),
              exprf base_type_code op (var:=ovar) (pick_type (interp_op_bounds t1 tR opc args_bs))).

  Section with_var.
    Context {ovar : base_type_code -> Type}.
    Local Notation ivarP t
      := (fun bs : interp_flat_type interp_base_type_bounds t
          => @exprf base_type_code op ovar (pick_type bs))%type.
    Local Notation ivar t := (sigT (ivarP t)) (only parsing).
    Local Notation ivarf := (fun t => ivar (Tbase t)).
    Context (let_in : forall T t'
                             (A:=(interp_flat_type ivarf T -> @exprf base_type_code op ovar t')%type)
                             (B:=@exprf base_type_code op ovar t'),
                A -> (A -> B) -> B).
    Local Notation SmartFail
      := (SmartValf _ (@failv _)).
    Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
      := (SmartPairf (SmartFail t)).
    Definition fail t : @expr base_type_code op ovar t
      := match t with
         | Arrow A B => Abs (fun _ => @failf B)
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
    Definition cast_orT (P : type base_type_code -> Type) {A B : type base_type_code}
               (x : P A) (default : P B)
      : P B
      := match sumbool_of_bool (@type_beq _ base_type_code_beq A B) with
         | left pf => match @type_dec_bl _ _ base_type_code_bl_transparent _ _ pf with
                      | eq_refl => x
                      end
         | right _ => default
         end.
    Definition cast_exprf {A B} (x : @exprf base_type_code op ovar A)
      : @exprf base_type_code op ovar B
      := cast_or (@exprf base_type_code op ovar) x (@failf _).
    Definition cast_expr {A B} (x : @expr base_type_code op ovar A)
      : @expr base_type_code op ovar B
      := cast_orT (@expr base_type_code op ovar) x (@fail _).
    (*Definition cast_ivarf {A B} (x : interp_flat_type ivarf A)
      : interp_flat_type ivarf B
      := cast_or (interp_flat_type _) x (SmartFail _).*)

    Fixpoint existT_ivar {t} : forall bs,
        interp_flat_type ovar (@pick_type t bs)
        -> interp_flat_type ivarf t
      := match t return forall bs, interp_flat_type _ (@pick_type t bs) -> interp_flat_type _ t with
         | Tbase T
           => fun bound var
              => existT (ivarP (Tbase T)) bound (Var (t:=@pick_typeb T bound) var)
         | Unit => fun _ _ => tt
         | Prod A B
           => fun (bs : interp_flat_type _ _ * interp_flat_type _ _)
                  (vs : interp_flat_type _ (pick_type (fst bs)) * interp_flat_type _ (pick_type (snd bs)))
              => let '(vx, vy) := vs in
                 (@existT_ivar _ _ vx, @existT_ivar _ _ vy)
         end%core.

    Definition fail_with_bounds {t} : interp_flat_type interp_base_type_bounds t -> interp_flat_type ivarf t
      := SmartVarfMap (fun _ v => existT _ v (failf _)).

    Fixpoint mapf_cast
             {t} (e : @exprf base_type_code op ivarf t)
             {struct e}
      : ivar t
      := match e in exprf _ _ t return ivar t with
         | TT => existT _ tt TT
         | Var t v => v
         | Pair tx ex ty ey
           => let 'existT x_bs xv := @mapf_cast _ ex in
              let 'existT y_bs yv := @mapf_cast _ ey in
              existT _ (x_bs, y_bs) (Pair xv yv)
         | LetIn tx ex tC eC
           => dlet Cv := (fun v => @mapf_cast _ (eC v)) in
               let 'existT x_bs xv := @mapf_cast _ ex in
               let 'existT Cfail_bs _ := Cv (fail_with_bounds x_bs) in
               existT
                 _
                 Cfail_bs
                 (let_in
                    _ (pick_type Cfail_bs)
                    (fun v => cast_exprf (projT2 (Cv v)))
                    (fun Cv'
                     => LetIn xv
                              (fun v => cast_exprf (Cv' (existT_ivar x_bs v)))))
                       | Op t1 tR opc args
                         => let 'existT args_bs argsv := @mapf_cast _ args in
                            existT
                              _
                              (interp_op_bounds _ _ opc args_bs)
                              (cast_op _ _ _ opc args_bs argsv)
         end%core.
    Definition map_cast
             {t} (e : @expr base_type_code op ivarf t)
             (in_bounds : interp_flat_type interp_base_type_bounds (domain t))
      : { out_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                       & @expr base_type_code op ovar (Arrow (pick_type in_bounds) (pick_type out_bounds)) }
      := dlet f := (fun v => mapf_cast (invert_Abs e v)) in
         let 'existT f_fail_bs _ := f (fail_with_bounds in_bounds) in
         existT
           _
           f_fail_bs
           (Abs
              (fun x
               => let_in
                    _ (pick_type f_fail_bs)
                    (fun v => cast_exprf (projT2 (f v)))
                    (fun f' => f' (existT_ivar _ x)))).
  End with_var.

  Definition MapCast
             (let_in : forall A B, A -> (A -> B) -> B)
             {t} (e : @Expr base_type_code op t)
             (in_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : { out_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                     & forall var, @expr base_type_code op var (Arrow (pick_type in_bounds) (pick_type out_bounds)) }
    := dlet f := (fun ovar => @map_cast ovar (fun _ _ => let_in _ _) t (e _) in_bounds) in
       let 'existT bs _ := f interp_base_type_bounds in
       existT
         _
         bs
         (fun ovar
          => let_in
               _ _ (fun ovar => cast_expr (projT2 (f ovar)))
               (fun f' => f' ovar)).
End language.

Global Arguments mapf_cast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op {ovar} let_in {t} e.
Global Arguments map_cast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op {ovar} let_in {t} e.
Global Arguments MapCast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op let_in {t} e.
