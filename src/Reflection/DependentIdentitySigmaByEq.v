Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.LetInMonad.

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
    Context (M : Type -> Type)
            (ret : forall A, A -> M A)
            (denote : forall A, M A -> A)
            (bind : forall A B, M A -> (A -> M B) -> M B).
    Section with_let_in.
      Context (let_in : forall T
                               (A:=interp_flat_type ivar T -> { t' : _ & @exprf base_type_code op var t' })
                               (B:={ t' : _ & @exprf base_type_code op var t' }),
                  A -> (A -> M B) -> M B).
      Fixpoint mpexist_id {t} (e : @exprf base_type_code op ivar t)
        : M { t' : _ & @exprf base_type_code op var t' }
        := match e with
           | TT => ret _ (existT _ _ TT)
           | Var t v => ret _ (existT _ (Tbase t) v)
           | Op t1 tR opc args
             => bind _ _ (@mpexist_id _ args)
                     (fun argsv
                      => ret _ (let (argsvT, argsv) := argsv in
                                existT _ _ (Op opc (cast_exprf argsv))))
           | Pair tx ex ty ey
             => bind _ _ (@mpexist_id _ ex)
                     (fun xv
                      => bind _ _ (@mpexist_id _ ey)
                              (fun yv
                               => ret _ (let (xvT, xv) := xv in
                                         let (yvT, yv) := yv in
                                         existT _ _ (Pair xv yv))))
           | LetIn tx ex tC eC
             => let_in _ (fun v => denote _ (@mpexist_id _ (eC v)))
                       (fun Cv
                        => bind _ _ (@mpexist_id _ ex)
                                (fun xv
                                 => ret _ (let (xvT, xv) := xv in
                                           existT
                                             _
                                             (projT1 (Cv failf))
                                             (LetIn xv
                                                    (fun v => cast_exprf (projT2 (Cv (cast_ivarf (SmartVarVarf v)))))))))
           end.
    (*Let type_of {var' t} (e : @exprf base_type_code op var' t) : flat_type base_type_code :=
      match e with
      | TT => t
      | _ => t
      end.
    Fixpoint mpexist_id_nd {t} (e : @exprf base_type_code op ivar t)
      : M (@exprf base_type_code op var t)
      := match e with
         | TT => ret _ TT
         | Var t v => ret _ v
         | Op t1 tR opc args
           => bind _ _ (@mpexist_id_nd _ args)
                   (fun argsv
                    => ret _ (Op opc (cast_exprf argsv)))
         | Pair tx ex ty ey
           => bind _ _ (@mpexist_id_nd _ ex)
                   (fun xv
                    => bind _ _ (@mpexist_id_nd _ ey)
                            (fun yv
                             => ret _ (Pair xv yv)))
         | LetIn tx ex tC eC
           => let_in _ _ (fun v => denote _ (@mpexist_id_nd _ (eC v)))
                     (fun Cv
                      => bind _ (@exprf base_type_code op var tC) (@mpexist_id_nd _ ex)
                              (fun xv
                               => ret _ (LetIn xv
                                               (fun v => cast_exprf (B:=tC) (cast_exprf (B:=type_of (Cv failf)) (Cv (cast_ivarf (SmartVarVarf v))))))))
         end.*)
    End with_let_in.

    Section push_let_in_types_only.
      Context (let_in : forall T t'
                               (A:=interp_flat_type ivar T -> @exprf base_type_code op var t')
                               (B:=@exprf base_type_code op var t'),
                  A -> (A -> M B) -> M B).
      Definition push_let_in_on_types
                 T
                 (A:=interp_flat_type ivar T -> { t' : _ & @exprf base_type_code op var t' })
                 (B:={ t' : _ & @exprf base_type_code op var t' })
                 (x : A)
                 (f : A -> M B)
        : M B
        := let (xfailfT, xfailf) := x failf in
           bind _ _ (let_in T xfailfT
                            (fun v => cast_exprf (projT2 (x v)))
                            (fun x' => bind _ _ (f (fun v => existT _ _ (x' v)))
                                            (fun v => ret _ (cast_exprf (projT2 v)))))
                (fun pr => ret _ (existT _ _ pr)).
    End push_let_in_types_only.
  End parametrized.
  Fixpoint exist_id {t} (e : @exprf base_type_code op ivar t)
    : { t' : _ & @exprf base_type_code op var t' }
    := match e with
       | TT => existT _ _ TT
       | Var t v => existT _ (Tbase t) v
       | Op t1 tR opc args
         => let (argsvT, argsv) := @exist_id _ args in
            existT _ _ (Op opc (cast_exprf argsv))
       | Pair tx ex ty ey
         => let (xvT, xv) := @exist_id _ ex in
            let (yvT, yv) := @exist_id _ ey in
            existT _ _ (Pair xv yv)
       | LetIn tx ex tC eC
         => let (xvT, xv) := @exist_id _ ex in
            let Cv := (fun v => @exist_id _ (eC v)) in
            existT
              _
              (projT1 (Cv failf))
              (LetIn xv
                     (fun v => cast_exprf (projT2 (Cv (cast_ivarf (SmartVarVarf v))))))
       end.
  Definition mexist_id {t} (e : @exprf base_type_code op ivar t)
    : LetInM { t' : _ & @exprf base_type_code op var t' }
    := Eval cbv [mpexist_id] in
        @mpexist_id (fun T => LetInM T) (@LetInMonad.ret) (@LetInMonad.denote) (@LetInMonad.bind) (fun T => @LetInMonad.let_in _ _) t e.
  Definition mpush_let_in_on_types
    := Eval cbv [push_let_in_on_types] in
        @push_let_in_on_types (fun T => LetInM T) (@LetInMonad.ret) (@LetInMonad.bind) (fun T t' => @LetInMonad.let_in _ _).
  Definition pexist_id (let_in : forall T, _ -> (_ -> _) -> _)
             {t} (e : @exprf base_type_code op ivar t)
    : { t' : _ & @exprf base_type_code op var t' }
    := Eval cbv [mpexist_id] in
        @mpexist_id (fun T => T) (fun _ v => v) (fun _ v => v) (fun _ _ x f => f x) let_in t e.
  Definition ppush_let_in_on_types (let_in : forall T t', _ -> _ -> _)
    := Eval cbv [push_let_in_on_types] in
        @push_let_in_on_types (fun T => T) (fun _ v => v) (fun _ _ x f => f x) let_in.
  Definition dexist_id
             {t} (e : @exprf base_type_code op ivar t)
    : { t' : _ & @exprf base_type_code op var t' }
    := Eval cbv [mpexist_id] in
        @mpexist_id (fun T => T) (fun _ v => v) (fun _ v => v) (fun _ _ x f => f x) (fun _ x f => dlet y := x in f y) t e.
  Definition dpush_let_in_on_types
    := Eval cbv [push_let_in_on_types] in
        @push_let_in_on_types (fun T => T) (fun _ v => v) (fun _ _ x f => f x) (fun _ _ x f => dlet y := x in f y).
  (*Definition pexist_id_nd (let_in : forall A B, A -> (A -> B) -> B)
             {t} (e : @exprf base_type_code op ivar t)
    : @exprf base_type_code op var t
    := Eval cbv [mpexist_id_nd] in
        @mpexist_id_nd (fun T => T) (let_in) (fun _ v => v) (fun _ v => v) (fun _ _ x f => f x) t e.
  Definition dexist_id_nd
             {t} (e : @exprf base_type_code op ivar t)
    : @exprf base_type_code op var t
    := Eval cbv [mpexist_id_nd] in
        @mpexist_id_nd (fun T => T) (fun _ _ x f => dlet y := x in f y) (fun _ v => v) (fun _ v => v) (fun _ _ x f => f x) t e.*)
End demo_by_eq.
