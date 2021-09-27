Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.LetIn.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.UnderLets.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Rewriter.All.
Require Import Crypto.MiscCompilerPasses.
Require Import Crypto.Stringification.C.
Import ListNotations. Local Open Scope Z_scope.

Import Language.Compilers.
Import UnderLets.Compilers.
Import AbstractInterpretation.Compilers.
Import Rewriter.All.Compilers.
Import MiscCompilerPasses.Compilers.
Import Stringification.C.Compilers.
Import Language.API.Compilers.
Local Coercion Z.of_nat : nat >-> Z.
Import Compilers.API.

Local Existing Instance AbstractInterpretation.default_Options.

Local Notation "x + y"
  := ((#ident.Z_add @ x @ y)%expr)
     : expr_scope.
Local Notation "x * y"
  := ((#ident.Z_mul @ x @ y)%expr)
     : expr_scope.
Local Notation "x" := (expr.Var x) (only printing, at level 9) : expr_scope.
Local Notation cstZ r := (#ident.Z_cast @ #(@ident.Literal base.type.zrange r%zrange))%expr.
Local Notation cstZZ r1 r2 := (#ident.Z_cast2 @ (#(@ident.Literal base.type.zrange r1%zrange), #(@ident.Literal base.type.zrange r2%zrange)))%expr.

Example test1 : True.
Proof.
  let v := Reify ((fun x => 2^x) 255)%Z in
  pose v as E.
  vm_compute in E.
  pose (PartialEvaluate RewriteRules.default_opts E) as E'.
  vm_compute in E'.
  lazymatch (eval cbv delta [E'] in E') with
  | (fun var => expr.Ident (ident.Literal ?v)) => idtac
  end.
  constructor.
Qed.
Module testrewrite.
  Import expr.
  Import ident.

  Redirect "log" Eval compute in RewriteRules.RewriteNBE RewriteRules.default_opts (fun var =>
                          (#ident.fst @ (expr_let x := ##10 in ($x, $x)))%expr).

  Notation "x + y" := (@expr.Ident base.type ident _ _ ident.Z_add @ x @ y)%expr : expr_scope.

  Redirect "log" Eval compute in RewriteRules.RewriteNBE RewriteRules.default_opts (fun var =>
                          ((\ x , expr_let y := ##5 in #ident.fst @ $x + (#ident.fst @ $x + ($y + $y)))
                             @ (##1, ##1))%expr).

  Redirect "log" Eval compute in RewriteRules.RewriteNBE RewriteRules.default_opts (fun var =>
                          ((\ x , expr_let y := ##5 in $y + ($y + (#ident.fst @ $x + #ident.snd @ $x)))
                             @ (##1, ##7))%expr).

  Redirect "log" Eval cbv in partial.eval_with_bound partial.default_relax_zrange false (@ident.is_comment) false
                                      (RewriteRules.RewriteNBE RewriteRules.default_opts (fun var =>
                (\z , ((\ x , expr_let y := ##5 in $y + ($z + (#ident.fst @ $x + #ident.snd @ $x)))
                         @ (##1, ##7)))%expr) _)
                (Datatypes.Some r[0~>100]%zrange, Datatypes.tt).
End testrewrite.
Module testpartial.
  Import expr.
  Import ident.

  Redirect "log" Eval compute in partial.eval
                          (#ident.fst @ (expr_let x := ##10 in ($x, $x)))%expr.

  Notation "x + y" := (@expr.Ident base.type ident _ _ (ident.Z_add) @ x @ y)%expr : expr_scope.

  Redirect "log" Eval compute in partial.eval
                          ((\ x , expr_let y := ##5 in #ident.fst @ $x + (#ident.fst @ $x + ($y + $y)))
                             @ (##1, ##1))%expr.

  Redirect "log" Eval compute in partial.eval
                          ((\ x , expr_let y := ##5 in $y + ($y + (#ident.fst @ $x + #ident.snd @ $x)))
                             @ (##1, ##7))%expr.


  Redirect "log" Eval cbv in partial.eval_with_bound
                partial.default_relax_zrange
                false (@ident.is_comment) false
                (\z , ((\ x , expr_let y := ##5 in $y + ($z + (#ident.fst @ $x + #ident.snd @ $x)))
                         @ (##1, ##7)))%expr
                (Datatypes.Some r[0~>100]%zrange, Datatypes.tt).
End testpartial.

Module test2.
  Example test2 : True.
  Proof.
    let v := Reify (fun y : Z
                    => (fun k : Z * Z -> Z * Z
                        => dlet_nd x := (y * y) in
                            dlet_nd z := (x * x) in
                            k (z, z))
                         (fun v => v)) in
    pose v as E.
    vm_compute in E.
    pose (partial.Eval E) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var _,
                expr_let x0 := ($x * $x) in
              expr_let x1 := ($x0 * $x0) in
              ($x1, $x1))%expr) => idtac
    end.
    pose (partial.EvalWithBound partial.default_relax_zrange false (@ident.is_comment) false E' (Some r[0~>10]%zrange, tt)) as E''.
    lazy in E''.
     lazymatch (eval cbv delta [E''] in E'') with
     | (fun var : type -> Type =>
          (λ x : var _,
                 expr_let y := (cstZ r[0 ~> 100]) @ (((cstZ r[0 ~> 10]) @ $x) * ((cstZ r[0 ~> 10]) @ $x)) in
               expr_let y0 := (cstZ r[0 ~> 10000]) @ (((cstZ r[0 ~> 100]) @ $y) * ((cstZ r[0 ~> 100]) @ $y)) in
               ((cstZ r[0 ~> 10000]) @ $y0, (cstZ r[0 ~> 10000]) @ $y0))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test2.
Module test3.
  Example test3 : True.
  Proof.
    let v := Reify (fun y : Z
                    => dlet_nd x := dlet_nd x := (y * y) in
                        (x * x) in
                        dlet_nd z := dlet_nd z := (x * x) in
                        (z * z) in
                        (z * z)) in
    pose v as E.
    vm_compute in E.
    pose (partial.Eval E) as E'.
    vm_compute in E'.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var _,
                expr_let x0 := $x * $x in
              expr_let x1 := $x0 * $x0 in
              expr_let x2 := $x1 * $x1 in
              expr_let x3 := $x2 * $x2 in
              $x3 * $x3)%expr)
      => idtac
    end.
    pose (partial.EvalWithBound partial.default_relax_zrange false (@ident.is_comment) false E' (Some r[0~>10]%zrange, tt)) as E'''.
    lazy in E'''.
    lazymatch (eval cbv delta [E'''] in E''') with
    | (fun var : type -> Type =>
          (λ x : var _,
           expr_let y := (cstZ r[0 ~> 100]) @ (((cstZ r[0 ~> 10]) @ $x) * ((cstZ r[0 ~> 10]) @ $x)) in
           expr_let y0 := (cstZ r[0 ~> 10000]) @ (((cstZ r[0 ~> 100]) @ $y) * ((cstZ r[0 ~> 100]) @ $y)) in
           expr_let y1 := (cstZ r[0 ~> 100000000]) @ (((cstZ r[0 ~> 10000]) @ $y0) * ((cstZ r[0 ~> 10000]) @ $y0)) in
           expr_let y2 := (cstZ r[0 ~> 10000000000000000]) @ (((cstZ r[0 ~> 100000000]) @ $y1) * ((cstZ r[0 ~> 100000000]) @ $y1)) in
           (cstZ r[0 ~> 100000000000000000000000000000000]) @ (((cstZ r[0 ~> 10000000000000000]) @ $y2) * ((cstZ r[0 ~> 10000000000000000]) @ $y2)))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test3.
Module test3point5.
  Example test3point5 : True.
  Proof.
    let v := Reify (fun y : (list Z) => List.nth_default (-1) y 0) in
    pose v as E.
    vm_compute in E.
    pose (partial.EvalWithBound partial.default_relax_zrange false (@ident.is_comment) false E (Some [Some r[0~>10]%zrange], tt)) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var : type -> Type =>
         (λ x : var _,
          (cstZ r[0 ~> 10]) @ (#ident.List_nth_default @ #(ident.Literal (0)%Z) @ $x @ #(ident.Literal 0%nat)))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test3point5.
Module test4.
  Example test4 : True.
  Proof.
    let v := Reify (fun y : (list Z * list Z)
                    => dlet_nd x := List.nth_default (-1) (fst y) 0 in
                        dlet_nd z := List.nth_default (-1) (snd y) 0 in
                        dlet_nd xz := (x * z) in
                        (xz :: xz :: nil)) in
    pose v as E.
    vm_compute in E.
    pose (partial.Eval E) as E'.
    lazy in E'.
    clear E.
    pose (Some [Some r[0~>10]%zrange],Some [Some r[0~>10]%zrange], Datatypes.tt) as bound.
    pose (partial.EtaExpandWithListInfoFromBound E' bound) as E''.
    lazy in E''.
    clear E'.
    pose (PartialEvaluate RewriteRules.default_opts E'') as E'''.
    lazy in E'''.
    pose (partial.EvalWithBound partial.default_relax_zrange false (@ident.is_comment) false E''' bound) as E''''.
    lazy in E''''.
    clear E'' E'''.
    lazymatch (eval cbv delta [E''''] in E'''') with
    | (fun var : type -> Type =>
         (λ x : var _,
          expr_let y := (cstZ r[0 ~> 10]) @
                        (#ident.List_nth_default @ #(ident.Literal (0)%Z) @ (#ident.fst @ $x) @ #(ident.Literal 0%nat)) in
          expr_let y0 := (cstZ r[0 ~> 10]) @
                          (#ident.List_nth_default @ #(ident.Literal (0)%Z) @ (#ident.snd @ $x) @ #(ident.Literal 0%nat)) in
          expr_let y1 := (cstZ r[0 ~> 100]) @ (((cstZ r[0 ~> 10]) @ $y) * ((cstZ r[0 ~> 10]) @ $y0)) in
          (cstZ r[0 ~> 100]) @ $y1 :: (cstZ r[0 ~> 100]) @ $y1 :: [])%expr)
      => idtac
    end.
    constructor.
  Qed.
End test4.
Module test5.
  Example test5 : True.
  Proof.
    let v := Reify (fun y : (Z * Z)
                    => dlet_nd x := (13 * (fst y * snd y)) in
                        x) in
    pose v as E.
    vm_compute in E.
    pose (RewriteRules.RewriteArith (2^8) RewriteRules.default_opts (partial.Eval E)) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         expr.Abs (fun v
              => (expr_let v0 := (#ident.Z_mul @ (#ident.fst @ $v) @ (#ident.Z_mul @ (#ident.snd @ $v) @ #(ident.Literal 13))) in
                      $v0)%expr))
      => idtac
    end.
    constructor.
  Qed.

  Example test5_2 : True.
  Proof.
    let v := Reify (fun y : (Z * Z)
                    => dlet_nd x := (2 * (19 * (fst y * snd y))) in
                        x) in
    pose v as E.
    vm_compute in E.
    pose (RewriteRules.RewriteArith (2^8) RewriteRules.default_opts (partial.Eval E)) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         expr.Abs (fun v
              => (expr_let v0 := (#ident.Z_mul @ (#ident.fst @ $v) @ (#ident.Z_mul @ (#ident.snd @ $v) @ (#ident.Z_mul @ #(ident.Literal 2) @ #(ident.Literal 19)))) in
                      $v0)%expr))
      => idtac
    end.
    constructor.
  Qed.
End test5.
Module test6.
  (* check for no dead code with if *)
  Example test6 : True.
  Proof.
    let v := Reify (fun y : Z
                    => if 0 =? 1
                       then dlet_nd x := (y * y) in
                                x
                       else y) in
    pose v as E.
    vm_compute in E.
    pose (PartialEvaluate RewriteRules.default_opts E) as E''.
    lazy in E''.
    lazymatch eval cbv delta [E''] in E'' with
    | fun var : type -> Type => (λ x : var _, $x)%expr
      => idtac
    end.
    exact I.
  Qed.
End test6.
Module test7.
  Example test7 : True.
  Proof.
    let v := Reify (fun y : Z
                    => dlet_nd x := y + y in
                        dlet_nd z := x in
                        dlet_nd z' := z in
                        dlet_nd z'' := z in
                        z'' + z'') in
    pose v as E.
    vm_compute in E.
    pose (Subst01.Subst01 ident.is_comment (DeadCodeElimination.EliminateDead ident.is_comment E)) as E''.
    lazy in E''.
    lazymatch eval cbv delta [E''] in E'' with
    | fun var : type -> Type => (λ x : var _, expr_let v0 := $x + $x in $v0 + $v0)%expr
      => idtac
    end.
    exact I.
  Qed.
End test7.
Module test8.
  Example test8 : True.
  Proof.
    let v := Reify (fun y : Z
                    => dlet_nd x := y + y in
                        dlet_nd z := x in
                        dlet_nd z' := z in
                        dlet_nd z'' := z in
                        z'' + z'') in
    pose v as E.
    vm_compute in E.
    pose (GeneralizeVar.GeneralizeVar (E _)) as E''.
    lazy in E''.
    unify E E''.
    exact I.
  Qed.
End test8.
Module test9.
  Example test9 : True.
  Proof.
    let v := Reify (fun y : list Z => (hd 0%Z y, tl y)) in
    pose v as E.
    vm_compute in E.
    pose (PartialEvaluate RewriteRules.default_opts E) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var
       => (λ x,
           (#ident.list_case
              @ (λ _, #(ident.Literal 0%Z))
              @ (λ x0 _, $x0)
              @ $x,
            #ident.list_case
              @ (λ _, #ident.nil)
              @ (λ _ x1, $x1)
              @ $x))%expr)
      => idtac
    end.
    exact I.
  Qed.
End test9.
(*
Module test10.
  Example test10 : True.
  Proof.
    let v := Reify (fun (f : Z -> Z -> Z) x y => f (x + y) (x * y))%Z in
    pose v as E.
    vm_compute in E.
    pose (Uncurry.expr.Uncurry (partial.Eval true (canonicalize_list_recursion E))) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         (λ v,
          ident.fst @@@ $v @
                    (ident.fst @@@ (ident.snd @@@ $v) + ident.snd @@@ (ident.snd @@@ $v)) @
                    (ident.fst @@@ (ident.snd @@@ $v) * ident.snd @@@ (ident.snd @@@ $v)))%expr)
      => idtac
    end.
    constructor.
  Qed.
End test10.
 *)
(*
Module test11.
  Example test11 : True.
  Proof.
    let v := Reify (fun x y => (fun f a b => f a b) (fun a b => a + b) (x + y) (x * y))%Z in
    pose v as E.
    vm_compute in E.
    pose (Uncurry.expr.Uncurry (partial.Eval true (canonicalize_list_recursion E))) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var =>
         (λ x,
          ident.fst @@@ $x + ident.snd @@@ $x + ident.fst @@@ $x * ident.snd @@@ $x)%expr)
      => idtac
    end.
    constructor.
  Qed.
End test11.
 *)
Module test12.
  Example test12 : True.
  Proof.
    let v := Reify (fun y : list Z => repeat y 2) in
    pose v as E.
    vm_compute in E.
    pose (Some (repeat (@None zrange) 3), Datatypes.tt) as bound.
    pose (PartialEvaluate RewriteRules.default_opts (partial.EtaExpandWithListInfoFromBound E bound)) as E'.
    lazy in E'.
    clear E.
    lazymatch (eval cbv delta [E'] in E') with
    | (fun var
       => (λ x, [ [ $x[[0]] ; $x[[1]]; $x[[2]] ] ; [ $x[[0]] ; $x[[1]]; $x[[2]] ] ])%expr)
      => idtac
    end.
    exact I.
  Qed.
End test12.
Module test13.
  Example test13 : True.
  Proof.
    let v0 := constr:(nat_rect (fun _ => nat -> nat) (fun v => v) (fun n' rec v => (n' + rec (S v))%nat) 3 0%nat) in
    let v := Reify v0 in
    pose v as E;
      pose v0 as exp.
    vm_compute in E.
    vm_compute in exp.
    pose (PartialEvaluate RewriteRules.default_opts E) as E'.
    vm_compute in E'.
    clear E.
    let r := Reify exp in
    unify r E'.
    exact I.
  Qed.
End test13.
Module test14.
  Import PreExtra.
  Local Open Scope string_scope.
  Example test14 : True.
  Proof.
    let v := Reify (fun y : Z
                    => dlet_nd x := y + y in
                        dlet_nd z := y + y in
                        dlet_nd w := y + y in
                        dlet_nd v := y + y in
                        dlet_nd __ := ident.comment ("note", (x, x, z, z)) in
                        dlet_nd __ := ident.comment_no_keep ("note", (w, w, v, v)) in
                        y) in
    pose v as E.
    vm_compute in E.
    pose (Subst01.Subst01 ident.is_comment (DeadCodeElimination.EliminateDead ident.is_comment E)) as E''.
    lazy in E''.
    pose (PartialEvaluate RewriteRules.default_opts E'') as E'''.
    vm_compute in E'''.
    pose (partial.EvalWithBound partial.default_relax_zrange false (@ident.is_comment) true E''' (Some r[0~>1]%zrange, tt)) as E''''.
    lazy in E''''.
    unify E E''.
    unify E'' E'''.
    lazymatch (eval cbv [E''''] in E'''') with
    | fun var : type -> Type =>
        (λ x : var (type.base (base.type.type_base Compilers.Z)),
               expr_let v := cstZ r[0 ~> 2] @
                                  (cstZ r[0 ~> 1] @ $x + cstZ r[0 ~> 1] @ $x) in
             expr_let v0 := cstZ r[0 ~> 2] @
                                 (cstZ r[0 ~> 1] @ $x + cstZ r[0 ~> 1] @ $x) in
             expr_let v1 := cstZ r[0 ~> 2] @
                                 (cstZ r[0 ~> 1] @ $x + cstZ r[0 ~> 1] @ $x) in
             expr_let v2 := cstZ r[0 ~> 2] @
                                 (cstZ r[0 ~> 1] @ $x + cstZ r[0 ~> 1] @ $x) in
             expr_let _ := #Compilers.ident_comment @ (###_, ($v, $v, $v0, $v0)) in
             expr_let _ := #Compilers.ident_comment_no_keep @
                            (###_, ($v1, $v1, $v2, $v2)) in
             cstZ r[0 ~> 1] @ $x)%expr
      => idtac
    end.
    exact I.
  Qed.
End test14.
