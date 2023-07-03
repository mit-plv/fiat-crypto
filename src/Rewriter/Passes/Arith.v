Require Import Coq.ZArith.ZArith.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.RulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.API.Compilers.
  Import Language.Wf.Compilers.
  Import Language.WfExtra.Compilers.
  Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.GoalType.
  Import Rewriter.AllTactics.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Context (max_const_val : Z).

      Definition VerifiedRewriterArith : VerifiedRewriter_with_args false false true (arith_rewrite_rules_proofs max_const_val).
      Proof using All. make_rewriter. Defined.

      (*
        Trying to add the rule
          (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z) =
          (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))
        causes make_rewriter to fail with the message:

Error:
In environment
max_const_val : Z
H : forall i n : nat,
    Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (n - 1))) =
    Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (n - 1)))
v1 : RewriteRules.Compile.value' false
       (type.base (base.type.type_base Compilers.nat))
v2 : Compilers.base_interp Compilers.nat
H0 : expr.interp_related (@Compilers.ident_interp) v1 v2
v0 : RewriteRules.Compile.value' false
       (type.base (base.type.type_base Compilers.nat))
v3 : Compilers.base_interp Compilers.nat
H1 : expr.interp_related (@Compilers.ident_interp) v0 v3
v4 : RewriteRules.Compile.value' false
       (type.base (base.type.type_base Compilers.nat))
v5 : Compilers.base_interp Compilers.nat
H2 : expr.interp_related (@Compilers.ident_interp) v4 v5
Heqb2 : (1 =? 1) = true
Heqb1_2 : (1 =? 1)%Z = true
Heqb1_1_2 : (2 =? 2)%Z = true
Heqb1_1_1_1, Heqb1_1_1_2 : (1 =? 1)%Z = true
Unable to unify "v3" with "v2".
       *)


      

      (* Trying to add the rule
           (forall n x y, ident_adk_mul n x y = adk_mul n x y)
         causes make_rewriter to fail with the message:

============================
WARNING: UNSOLVED GOAL:
max_const_val : Z
v1 : (API.expr (type.base (base.type.type_base Compilers.nat)))
v2 : nat
H0 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v1 v2)
v0 :
(API.expr (type.base (base.type.list (base.type.type_base Compilers.Z))))
v3 : (list Z)
H1 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v0 v3)
v4 :
(API.expr (type.base (base.type.list (base.type.type_base Compilers.Z))))
v5 : (list Z)
H2 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v4 v5)
x1 :
(RewriteRules.Compile.value' false
   (type.base (base.type.type_base Compilers.nat)))
x2 : (API.interp_type (type.base (base.type.type_base Compilers.nat)))
H :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x1 x2)
x0 :
(RewriteRules.Compile.value' false
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
x3 :
(API.interp_type
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
H3 :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x0 x3)
x4 :
(RewriteRules.Compile.value' false
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
x5 :
(API.interp_type
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
H4 :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x4 x5)
============================
(expr.interp_related_gen (@Compilers.ident_interp)
   (fun t : API.type =>
    ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
      (@Compilers.ident_interp))
   (expr_let v := (λ (v : API.expr
                            (type.base (base.type.type_base Compilers.nat)))
                   (v0 : API.expr
                           (type.base
                              (base.type.list
                                 (base.type.type_base Compilers.Z))))
                   (v1 : API.expr
                           (type.base (base.type.type_base Compilers.Z))),
                   #Compilers.ident_List_nth_default @ $$v1 @ $$v0 @ $$v) @
                  (#Compilers.ident_Nat_sub @ $$x1 @ ###1) @ $$x0 @ ###0%Z *
                  (λ (v : API.expr
                            (type.base (base.type.type_base Compilers.nat)))
                   (v0 : API.expr
                           (type.base
                              (base.type.list
                                 (base.type.type_base Compilers.Z))))
                   (v1 : API.expr
                           (type.base (base.type.type_base Compilers.Z))),
                   #Compilers.ident_List_nth_default @ $$v1 @ $$v0 @ $$v) @
                  (#Compilers.ident_Nat_sub @ $$x1 @ ###1) @ $$x4 @ ###0%Z in
    (λ v0 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z))),
     #Compilers.ident_list_rect_arrow @
     (λ v1 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))),
      (λ (v2 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v3 v4 v5
        v6 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z)))),
       #Compilers.ident_List_map @
       ((λ (v7 : API.expr (type.base (base.type.type_base Compilers.nat)))
         (v8 v9 v10
          v11 : API.expr
                  (type.base
                     (base.type.list (base.type.type_base Compilers.Z))))
         (v12 : API.expr (type.base (base.type.type_base Compilers.nat))),
         #Compilers.ident_List_fold_right @ #Compilers.ident_Z_add @ ###0%Z @
         (#Compilers.ident_List_map @
          (λ v13 : API.expr (type.base (base.type.type_base Compilers.nat)),
           ((λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            $$v13 @ $$v8 @ ###0%Z -
            (λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            (#Compilers.ident_Nat_sub @ $$v12 @ $$v13) @ $$v8 @ ###0%Z) *
           ((λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            (#Compilers.ident_Nat_sub @ $$v12 @ $$v13) @ $$v9 @ ###0%Z -
            (λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            $$v13 @ $$v9 @ ###0%Z)) @
          (#Compilers.ident_List_seq @
           (#Compilers.ident_Nat_sub @ $$v12 @
            (#Compilers.ident_Nat_sub @ $$v7 @ ###1)) @
           (#Compilers.ident_Z_to_nat @
            (###1%Z +
             ((#Compilers.ident_Z_of_nat @ $$v12 + ###1%Z) / ###2%Z - ###1%Z) -
             #Compilers.ident_Z_of_nat @
             (#Compilers.ident_Nat_sub @ $$v12 @
              (#Compilers.ident_Nat_sub @ $$v7 @ ###1)))))) +
         #Compilers.ident_bool_rect @
         (λ _ : API.expr (type.base ()),
          (λ (v14 : API.expr (type.base (base.type.type_base Compilers.nat)))
           (v15 : API.expr
                    (type.base
                       (base.type.list (base.type.type_base Compilers.Z))))
           (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
           #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
          (#Compilers.ident_Nat_sub @ $$v7 @ ###1) @ $$v10 @ ###0%Z) @
         (λ _ : API.expr (type.base ()),
          (λ (v14 : API.expr (type.base (base.type.type_base Compilers.nat)))
           (v15 : API.expr
                    (type.base
                       (base.type.list (base.type.type_base Compilers.Z))))
           (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
           #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @ $$v12 @
          $$v11 @ ###0%Z -
          #Compilers.ident_bool_rect @ (λ _ : API.expr (type.base ()),
                                        ###0%Z) @
          (λ _ : API.expr (type.base ()),
           (λ (v15 : API.expr (type.base (base.type.type_base Compilers.nat)))
            (v16 : API.expr
                     (type.base
                        (base.type.list (base.type.type_base Compilers.Z))))
            (v17 : API.expr (type.base (base.type.type_base Compilers.Z))),
            #Compilers.ident_List_nth_default @ $$v17 @ $$v16 @ $$v15) @
           (#Compilers.ident_Nat_sub @ $$v12 @ $$v7) @ $$v11 @ ###0%Z) @
          (#Compilers.ident_Nat_ltb @ $$v12 @ $$v7)) @
         (#Compilers.ident_Nat_eqb @ $$v12 @
          (#Compilers.ident_Nat_sub @
           (#Compilers.ident_Nat_mul @ ###2 @ $$v7) @ ###2))) @ $$v2 @ $$v3 @
        $$v4 @ $$v5 @ $$v6) @
       (#Compilers.ident_List_seq @ ###0 @
        (#Compilers.ident_Nat_sub @ (#Compilers.ident_Nat_mul @ ###2 @ $$v2) @
         ###1))) @ $$x1 @ $$x0 @ $$x4 @ $$v0 @
      (#Compilers.ident_List_rev @ $$v1)) @
     (λ (v1 : API.expr (type.base (base.type.type_base Compilers.Z)))
      (_ : API.expr
             (type.base (base.type.list (base.type.type_base Compilers.Z))))
      (v3 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z))) ->
            UnderLets.UnderLets (Language.Compilers.base.type Compilers.base)
              IdentifiersBasicGENERATED.Compilers.ident API.interp_type
              (API.expr
                 (type.base
                    (base.type.list (base.type.type_base Compilers.Z)))))
      (v4 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z)))),
      expr_let v5 := (λ (v5 : API.expr
                                (type.base
                                   (base.type.type_base Compilers.nat)))
                      (v6 : API.expr
                              (type.base
                                 (base.type.list
                                    (base.type.type_base Compilers.Z))))
                      (v7 : API.expr
                              (type.base (base.type.type_base Compilers.Z))),
                      #Compilers.ident_List_nth_default @ $$v7 @ $$v6 @ $$v5) @
                     ###0 @ $$v4 @ ###0%Z + $$v1 in
      $$v3 @ ($$v5 :: $$v4)) @ $$v0 @ []) @
    (#Compilers.ident_List_map @
     (λ v0 : API.expr (type.base (base.type.type_base Compilers.nat)),
      (λ (v1 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v2 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))))
       (v3 : API.expr (type.base (base.type.type_base Compilers.Z))),
       #Compilers.ident_List_nth_default @ $$v3 @ $$v2 @ $$v1) @ $$v0 @ $$x0 @
      ###0%Z *
      (λ (v1 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v2 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))))
       (v3 : API.expr (type.base (base.type.type_base Compilers.Z))),
       #Compilers.ident_List_nth_default @ $$v3 @ $$v2 @ $$v1) @ $$v0 @ $$x4 @
      ###0%Z) @
     (#Compilers.ident_List_seq @ ###0 @
      (#Compilers.ident_Nat_sub @ $$x1 @ ###1)) ++
     [$$v] ++
     #Compilers.ident_List_repeat @ ###0%Z @
     (#Compilers.ident_Nat_sub @ $$x1 @ ###1))) (ADK.adk_mul x2 x3 x5))
============================
Tactic call ran for 0.64 secs (0.639u,0.s) (success)
WARNING: Remaining goal:
max_const_val : Z
v1 : (API.expr (type.base (base.type.type_base Compilers.nat)))
v2 : nat
H0 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v1 v2)
v0 :
(API.expr (type.base (base.type.list (base.type.type_base Compilers.Z))))
v3 : (list Z)
H1 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v0 v3)
v4 :
(API.expr (type.base (base.type.list (base.type.type_base Compilers.Z))))
v5 : (list Z)
H2 :
(expr.interp_related_gen (@Compilers.ident_interp)
   (@type.related (Language.Compilers.base.type Compilers.base)
      (Language.Compilers.base.interp Compilers.base_interp)
      (fun t : Language.Compilers.base.type Compilers.base => eq)) v4 v5)
x1 :
(RewriteRules.Compile.value' false
   (type.base (base.type.type_base Compilers.nat)))
x2 : (API.interp_type (type.base (base.type.type_base Compilers.nat)))
H :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x1 x2)
x0 :
(RewriteRules.Compile.value' false
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
x3 :
(API.interp_type
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
H3 :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x0 x3)
x4 :
(RewriteRules.Compile.value' false
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
x5 :
(API.interp_type
   (type.base (base.type.list (base.type.type_base Compilers.Z))))
H4 :
(ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
   (@Compilers.ident_interp) x4 x5)
============================
(expr.interp_related_gen (@Compilers.ident_interp)
   (fun t : API.type =>
    ProofsCommon.Compilers.RewriteRules.Compile.value_interp_related
      (@Compilers.ident_interp))
   (expr_let v := (λ (v : API.expr
                            (type.base (base.type.type_base Compilers.nat)))
                   (v0 : API.expr
                           (type.base
                              (base.type.list
                                 (base.type.type_base Compilers.Z))))
                   (v1 : API.expr
                           (type.base (base.type.type_base Compilers.Z))),
                   #Compilers.ident_List_nth_default @ $$v1 @ $$v0 @ $$v) @
                  (#Compilers.ident_Nat_sub @ $$x1 @ ###1) @ $$x0 @ ###0%Z *
                  (λ (v : API.expr
                            (type.base (base.type.type_base Compilers.nat)))
                   (v0 : API.expr
                           (type.base
                              (base.type.list
                                 (base.type.type_base Compilers.Z))))
                   (v1 : API.expr
                           (type.base (base.type.type_base Compilers.Z))),
                   #Compilers.ident_List_nth_default @ $$v1 @ $$v0 @ $$v) @
                  (#Compilers.ident_Nat_sub @ $$x1 @ ###1) @ $$x4 @ ###0%Z in
    (λ v0 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z))),
     #Compilers.ident_list_rect_arrow @
     (λ v1 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))),
      (λ (v2 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v3 v4 v5
        v6 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z)))),
       #Compilers.ident_List_map @
       ((λ (v7 : API.expr (type.base (base.type.type_base Compilers.nat)))
         (v8 v9 v10
          v11 : API.expr
                  (type.base
                     (base.type.list (base.type.type_base Compilers.Z))))
         (v12 : API.expr (type.base (base.type.type_base Compilers.nat))),
         #Compilers.ident_List_fold_right @ #Compilers.ident_Z_add @ ###0%Z @
         (#Compilers.ident_List_map @
          (λ v13 : API.expr (type.base (base.type.type_base Compilers.nat)),
           ((λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            $$v13 @ $$v8 @ ###0%Z -
            (λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            (#Compilers.ident_Nat_sub @ $$v12 @ $$v13) @ $$v8 @ ###0%Z) *
           ((λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            (#Compilers.ident_Nat_sub @ $$v12 @ $$v13) @ $$v9 @ ###0%Z -
            (λ (v14 : API.expr
                        (type.base (base.type.type_base Compilers.nat)))
             (v15 : API.expr
                      (type.base
                         (base.type.list (base.type.type_base Compilers.Z))))
             (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
             #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
            $$v13 @ $$v9 @ ###0%Z)) @
          (#Compilers.ident_List_seq @
           (#Compilers.ident_Nat_sub @ $$v12 @
            (#Compilers.ident_Nat_sub @ $$v7 @ ###1)) @
           (#Compilers.ident_Z_to_nat @
            (###1%Z +
             ((#Compilers.ident_Z_of_nat @ $$v12 + ###1%Z) / ###2%Z - ###1%Z) -
             #Compilers.ident_Z_of_nat @
             (#Compilers.ident_Nat_sub @ $$v12 @
              (#Compilers.ident_Nat_sub @ $$v7 @ ###1)))))) +
         #Compilers.ident_bool_rect @
         (λ _ : API.expr (type.base ()),
          (λ (v14 : API.expr (type.base (base.type.type_base Compilers.nat)))
           (v15 : API.expr
                    (type.base
                       (base.type.list (base.type.type_base Compilers.Z))))
           (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
           #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @
          (#Compilers.ident_Nat_sub @ $$v7 @ ###1) @ $$v10 @ ###0%Z) @
         (λ _ : API.expr (type.base ()),
          (λ (v14 : API.expr (type.base (base.type.type_base Compilers.nat)))
           (v15 : API.expr
                    (type.base
                       (base.type.list (base.type.type_base Compilers.Z))))
           (v16 : API.expr (type.base (base.type.type_base Compilers.Z))),
           #Compilers.ident_List_nth_default @ $$v16 @ $$v15 @ $$v14) @ $$v12 @
          $$v11 @ ###0%Z -
          #Compilers.ident_bool_rect @ (λ _ : API.expr (type.base ()),
                                        ###0%Z) @
          (λ _ : API.expr (type.base ()),
           (λ (v15 : API.expr (type.base (base.type.type_base Compilers.nat)))
            (v16 : API.expr
                     (type.base
                        (base.type.list (base.type.type_base Compilers.Z))))
            (v17 : API.expr (type.base (base.type.type_base Compilers.Z))),
            #Compilers.ident_List_nth_default @ $$v17 @ $$v16 @ $$v15) @
           (#Compilers.ident_Nat_sub @ $$v12 @ $$v7) @ $$v11 @ ###0%Z) @
          (#Compilers.ident_Nat_ltb @ $$v12 @ $$v7)) @
         (#Compilers.ident_Nat_eqb @ $$v12 @
          (#Compilers.ident_Nat_sub @
           (#Compilers.ident_Nat_mul @ ###2 @ $$v7) @ ###2))) @ $$v2 @ $$v3 @
        $$v4 @ $$v5 @ $$v6) @
       (#Compilers.ident_List_seq @ ###0 @
        (#Compilers.ident_Nat_sub @ (#Compilers.ident_Nat_mul @ ###2 @ $$v2) @
         ###1))) @ $$x1 @ $$x0 @ $$x4 @ $$v0 @
      (#Compilers.ident_List_rev @ $$v1)) @
     (λ (v1 : API.expr (type.base (base.type.type_base Compilers.Z)))
      (_ : API.expr
             (type.base (base.type.list (base.type.type_base Compilers.Z))))
      (v3 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z))) ->
            UnderLets.UnderLets (Language.Compilers.base.type Compilers.base)
              IdentifiersBasicGENERATED.Compilers.ident API.interp_type
              (API.expr
                 (type.base
                    (base.type.list (base.type.type_base Compilers.Z)))))
      (v4 : API.expr
              (type.base (base.type.list (base.type.type_base Compilers.Z)))),
      expr_let v5 := (λ (v5 : API.expr
                                (type.base
                                   (base.type.type_base Compilers.nat)))
                      (v6 : API.expr
                              (type.base
                                 (base.type.list
                                    (base.type.type_base Compilers.Z))))
                      (v7 : API.expr
                              (type.base (base.type.type_base Compilers.Z))),
                      #Compilers.ident_List_nth_default @ $$v7 @ $$v6 @ $$v5) @
                     ###0 @ $$v4 @ ###0%Z + $$v1 in
      $$v3 @ ($$v5 :: $$v4)) @ $$v0 @ []) @
    (#Compilers.ident_List_map @
     (λ v0 : API.expr (type.base (base.type.type_base Compilers.nat)),
      (λ (v1 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v2 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))))
       (v3 : API.expr (type.base (base.type.type_base Compilers.Z))),
       #Compilers.ident_List_nth_default @ $$v3 @ $$v2 @ $$v1) @ $$v0 @ $$x0 @
      ###0%Z *
      (λ (v1 : API.expr (type.base (base.type.type_base Compilers.nat)))
       (v2 : API.expr
               (type.base (base.type.list (base.type.type_base Compilers.Z))))
       (v3 : API.expr (type.base (base.type.type_base Compilers.Z))),
       #Compilers.ident_List_nth_default @ $$v3 @ $$v2 @ $$v1) @ $$v0 @ $$x4 @
      ###0%Z) @
     (#Compilers.ident_List_seq @ ###0 @
      (#Compilers.ident_Nat_sub @ $$x1 @ ###1)) ++
     [$$v] ++
     #Compilers.ident_List_repeat @ ###0%Z @
     (#Compilers.ident_Nat_sub @ $$x1 @ ###1))) (ADK.adk_mul x2 x3 x5))
File "./src/Rewriter/Passes/Arith.v", line 23, characters 23-36:
Error: Proof is not complete.
       *)

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterArith.
      Let optsT := Eval hnf in optsT VerifiedRewriterArith.

      Definition RewriteArith (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterArith opts t.

      Lemma Wf_RewriteArith opts {t} e (Hwf : Wf e) : Wf (@RewriteArith opts t e).
      Proof. now apply VerifiedRewriterArith. Qed.

      Lemma Interp_RewriteArith opts {t} e (Hwf : Wf e) : API.Interp (@RewriteArith opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterArith. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
#[global]
    Hint Resolve Wf_RewriteArith : wf wf_extra.
#[global]
    Hint Opaque RewriteArith : wf wf_extra interp interp_extra rewrite.
#[global]
    Hint Rewrite @Interp_RewriteArith : interp interp_extra.
  End Hints.
End Compilers.
