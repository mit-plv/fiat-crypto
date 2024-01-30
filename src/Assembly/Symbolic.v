Require Crypto.Assembly.Parse.
Require Import Coq.Program.Tactics.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.Orders.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Crypto.Util.ZRange.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Land.Fold.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Subscript.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Equalities.Prod.
Require Import Crypto.Util.Structures.Equalities.Option.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.Orders.Prod.
Require Import Crypto.Util.Structures.Orders.Option.
Require Import Crypto.Util.Structures.OrdersEx.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Concat.
Require Import Crypto.Util.ListUtil.GroupAllBy.
Require Import Crypto.Util.ListUtil.FoldMap. Import FoldMap.List.
Require Import Crypto.Util.ListUtil.IndexOf. Import IndexOf.List.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ListUtil.Partition.
Require Import Crypto.Util.ListUtil.Filter.
Require Import Crypto.Util.ListUtil.PermutationCompat. Import ListUtil.PermutationCompat.Coq.Sorting.Permutation.
Require Import Crypto.Util.NUtil.Sorting.
Require Import Crypto.Util.NUtil.Testbit.
Require Import Crypto.Util.FSets.FMapOption.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.FSets.FMapZ.
Require Import Crypto.Util.FSets.FMapProd.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.FSets.FMapSect.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapFacts.
Require Import Crypto.Util.FSets.FMapTrieEx.
Require Import Crypto.Util.MSets.MSetN.
Require Import Crypto.Util.ListUtil.PermutationCompat.
Require Import Crypto.Util.Bool.LeCompat.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.InHypUnderBindersDo.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Lxor.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Listable.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.Bool.Reflect.
Require Import coqutil.Z.bitblast.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.Show.Enum.
Require Import Crypto.Assembly.Syntax.
Import ListNotations.
Definition idx := N.
Local Set Decidable Equality Schemes.
Definition symbol := N.

Class OperationSize := operation_size : N.
Global Instance Show_OperationSize : Show OperationSize := show_N.

Section S.
Implicit Type s : OperationSize.
Variant op := old s (_:symbol) | const (_ : Z) | add s | addcarry s | subborrow s | addoverflow s | neg s | shl s | shr s | sar s | rcr s | and s | or s | xor s | slice (lo sz : N) | mul s | set_slice (lo sz : N) | selectznz | iszero (* | ... *)
  | addZ | mulZ | negZ | shlZ | shrZ | andZ | orZ | xorZ | addcarryZ s | subborrowZ s.
Definition op_beq a b := if op_eq_dec a b then true else false.
End S.

Global Instance Show_op : Show op := fun o =>
  match o with
  | old s n => "old " ++ show s ++ " " ++ show n
  | const n => "const " ++ show n
  | add s => "add " ++ show s
  | addcarry s => "addcarry " ++ show s
  | subborrow s => "subborrow " ++ show s
  | addoverflow s => "addoverflow " ++ show s
  | neg s => "neg " ++ show s
  | shl s => "shl " ++ show s
  | shr s => "shr " ++ show s
  | sar s => "sar " ++ show s
  | rcr s => "rcr " ++ show s
  | and s => "and " ++ show s
  | or s => "or " ++ show s
  | xor s => "xor " ++ show s
  | slice lo sz => "slice " ++ show lo ++ " " ++ show sz
  | mul s => "mul " ++ show s
  | set_slice lo sz => "set_slice " ++ show lo ++ " " ++ show sz
  | selectznz => "selectznz"
  | iszero => "iszero"
  | addZ => "addZ"
  | mulZ => "mulZ"
  | negZ => "negZ"
  | shlZ => "shlZ"
  | shrZ => "shrZ"
  | andZ => "andZ"
  | orZ => "orZ"
  | xorZ => "xorZ"
  | addcarryZ s => "addcarryZ " ++ show s
  | subborrowZ s => "subborrowZ " ++ show s
  end%string.

Definition show_op_subscript : Show op := fun o =>
  match o with
  | old s n => "old" ++ String.to_subscript (show s) ++ " " ++ show n
  | const n => "const " ++ show n
  | add s => "add" ++ String.to_subscript (show s)
  | addcarry s => "addcarry" ++ String.to_subscript (show s)
  | subborrow s => "subborrow" ++ String.to_subscript (show s)
  | addoverflow s => "addoverflow" ++ String.to_subscript (show s)
  | neg s => "neg" ++ String.to_subscript (show s)
  | shl s => "shl" ++ String.to_subscript (show s)
  | shr s => "shr" ++ String.to_subscript (show s)
  | sar s => "sar" ++ String.to_subscript (show s)
  | rcr s => "rcr" ++ String.to_subscript (show s)
  | and s => "and" ++ String.to_subscript (show s)
  | or s => "or" ++ String.to_subscript (show s)
  | xor s => "xor" ++ String.to_subscript (show s)
  | slice lo sz => "slice" ++ String.to_subscript (show lo) ++ "," ++ String.to_subscript (show sz)
  | mul s => "mul" ++ String.to_subscript (show s)
  | set_slice lo sz => "set_slice" ++ String.to_subscript (show lo) ++ "," ++ String.to_subscript (show sz)
  | selectznz => "selectznz"
  | iszero => "iszero"
  | addZ => "addℤ"
  | mulZ => "mulℤ"
  | negZ => "negℤ"
  | shlZ => "shlℤ"
  | shrZ => "shrℤ"
  | andZ => "andℤ"
  | orZ => "orℤ"
  | xorZ => "xorℤ"
  | addcarryZ s => "addcarryℤ" ++ String.to_subscript (show s)
  | subborrowZ s => "subborrowℤ" ++ String.to_subscript (show s)
  end%string.

Module FMapOp.
  Definition op_args : Set := (option OperationSize * (option symbol * (option Z * (option N * option N)))).
  Definition op' : Set := N * op_args.
  Definition eta_op_cps {T} (k : op -> T) (o : op) : T.
  Proof.
    pose o as o'.
    destruct o.
    all: let v := (eval cbv [o'] in o') in
         exact (k v).
  Defined.

  Definition nat_of_op (o : op) : nat.
  Proof.
    evar (base : nat).
    destruct o.
    all: let rec peel_S val :=
           lazymatch val with
           | S ?val => apply S; peel_S val
           | ?ev => is_evar ev;
                    let __ := open_constr:(eq_refl : ev = S _) in
                    exact O
           end in
         let v := (eval cbv [base] in base) in
         peel_S v.
    Unshelve.
    exact O.
  Defined.

  Definition args_of_op (o : op) : op_args.
  Proof.
    destruct o; hnf.
    all: repeat lazymatch reverse goal with
                | [ H : ?T |- ?A * ?B ]
                  => lazymatch A with
                     | context[option T]
                       => split; [ | clear H ]
                     | _ => split; [ repeat apply pair; exact None | ]
                     end
                | [ H : ?T |- _ ]
                  => lazymatch goal with
                     | [ |- option T ] => exact (Some H)
                     | [ |- _ ] => idtac "bad"
                     end
                | [ |- _ * _ ] => split
                | [ |- option _ ] => exact None
                end.
  Defined.

  Definition op'_of_op : op -> op'
    := Eval compute in eta_op_cps (fun o => (N.of_nat (nat_of_op o), args_of_op o)).

  Derive op_of_op'_opt
         SuchThat ((forall (o : op), op_of_op'_opt (op'_of_op o) = Some o)
                   /\ (forall (n n' : op'), option_map op'_of_op (op_of_op'_opt n) = Some n' -> n = n'))
         As op_op'_correct.
  Proof.
    instantiate (1:=ltac:(intros [n v]; hnf in v; destruct_head'_prod; destruct n as [|n])) in (value of op_of_op'_opt).
    subst op_of_op'_opt.
    split.
    { intro o; destruct o; cbv [op'_of_op].
      all: [ > cbv beta iota;
             lazymatch goal with
             | [ |- ?ev = Some _ ]
               => is_evar ev;
                  let H := fresh in
                  pose ev as H;
                  instantiate (1:=ltac:(lazymatch goal with
                                        | [ n : positive |- _ ]
                                          => destruct n
                                        | _ => idtac
                                        end)) in (value of H);
                  subst H; cbv beta iota
             end .. ].
      all: lazymatch goal with
           | [ |- ?ev = Some ?v ]
             => is_evar ev;
                let h := head v in
                let H := fresh in
                pose ev as H;
                instantiate (1:=ltac:(reverse)) in (value of H);
                subst H;
                repeat match goal with
                       | [ |- context[?ev ?x] ]
                         => is_evar ev;
                            let H := fresh in
                            pose ev as H;
                            lazymatch x with
                            | Some _
                              => instantiate (1:=ltac:(let x := fresh "x" in intro x; intros; destruct x; [ reverse | exact None ])) in (value of H)
                            | None
                              => instantiate (1:=ltac:(let x := fresh "x" in intro x; intros; destruct x; [ exact None | reverse ])) in (value of H)
                            | ?x
                              => tryif is_var x
                                then instantiate (1:=ltac:(intro)) in (value of H)
                                else idtac "unknown" x
                            end;
                            subst H; cbv beta iota
                       end;
                reflexivity
           end. }
    { intros [n nargs] [n' nargs'].
      set (f := option_map _).
      break_innermost_match.
      all: let G := lazymatch goal with |- ?G => G end in
           tryif has_evar G then instantiate (1:=None) else idtac.
      all: vm_compute.
      all: lazymatch goal with
           | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; inversion_pair; subst; try reflexivity
           | [ |- None = Some _ -> _ ] => let H := fresh in intro H; exfalso; clear -H; inversion_option
           end. }
  Qed.

  Module OptionNMap <: S := OptionUsualMap NMap.
  Module OptionZMap <: S := OptionUsualMap ZMap.
  Module OptionSymbolMap <: S := OptionNMap.
  Module OptionOperationSizeMap <: S := OptionNMap.
  Module OpArgsMap0 <: S := OptionNMap.
  Module OpArgsMap1 <: S := ProdUsualMap OptionNMap OpArgsMap0.
  Module OpArgsMap2 <: S := ProdUsualMap OptionZMap OpArgsMap1.
  Module OpArgsMap3 <: S := ProdUsualMap OptionSymbolMap OpArgsMap2.
  Module OpArgsMap4 <: S := ProdUsualMap OptionOperationSizeMap OpArgsMap3.
  Module OpArgsMap <: S := OpArgsMap4.
  Module OpMap' <: S := ProdUsualMap NMap OpArgsMap.
  Module OpSectOp' <: SectMiniOrderedType OpMap'.E.
    Definition t := op.
    Include HasUsualEq.
    Include UsualIsEq.
    Include UsualIsEqOrig.
    Definition to_ : t -> OpMap'.E.t := Eval vm_compute in op'_of_op.
    Definition of_ (v : OpMap'.E.t) : t
      := Eval vm_compute in match op_of_op'_opt v with
                            | Some v => v
                            | None => old 0%N 0%N
                            end.
    Global Instance Proper_to_ : Proper (Logic.eq ==> Logic.eq) to_ | 5.
    Proof. repeat intro; subst; reflexivity. Qed.
    Global Instance Proper_of_ : Proper (Logic.eq ==> Logic.eq) of_ | 5.
    Proof. repeat intro; subst; reflexivity. Qed.
    Lemma of_to : forall x, eq (of_ (to_ x)) x.
    Proof.
      intro x.
      refine (_ : match op_of_op'_opt (op'_of_op x) with
                  | Some v => v
                  | None => _
                  end = x).
      rewrite (proj1 op_op'_correct).
      reflexivity.
    Qed.
    Include LiftIsoHasLt OpMap'.E.
    Include LiftSectHasMiniOrderedType OpMap'.E.
    Include LiftSectIsLt OpMap'.E.
  End OpSectOp'.
  Module OpMap <: UsualS := SectS OpMap' OpSectOp'.
End FMapOp.

Module OpMap := FMapOp.OpMap.

Module Export RewritePass.
  Variant rewrite_pass :=
    | addbyte_small
    | addcarry_bit
    | addcarry_small
    | addoverflow_bit
    | addoverflow_small
    | combine_consts
    | constprop
    | consts_commutative
    | drop_identity
    | flatten_associative
    | flatten_bounded_associative
    | fold_consts_to_and
    | set_slice0_small
    | set_slice_set_slice
    | shift_to_mul
    | slice0
    | slice01_addcarryZ
    | slice01_subborrowZ
    | slice_set_slice
    | truncate_small
    | unary_truncate
    | xor_same
  .
  Definition rewrite_pass_beq (x y : rewrite_pass) : bool := if rewrite_pass_eq_dec x y then true else false.

  Derive rewrite_pass_Listable SuchThat (@FinitelyListable rewrite_pass rewrite_pass_Listable) As rewrite_pass_FinitelyListable.
  Proof. prove_ListableDerive. Qed.
  Global Existing Instances rewrite_pass_Listable rewrite_pass_FinitelyListable.

  Global Instance show_rewrite_pass : Show rewrite_pass.
  Proof. prove_Show_enum (). Defined.
  Global Instance show_lvl_rewrite_pass : ShowLevel rewrite_pass := show_rewrite_pass.

  Definition parse_rewrite_pass_list : list (string * rewrite_pass)
    := Eval vm_compute in
      List.map
        (fun r => (show r, r))
        (list_all rewrite_pass).

  Definition parse_rewrite_pass : ParserAction rewrite_pass
    := parse_strs parse_rewrite_pass_list.

  Definition default_rewrite_pass_order : list rewrite_pass
    := [constprop
        ;slice0
        ;slice01_addcarryZ
        ;slice01_subborrowZ
        ;set_slice_set_slice
        ;slice_set_slice
        ;set_slice0_small
        ;shift_to_mul
        ;flatten_associative
        ;consts_commutative
        ;fold_consts_to_and
        ;drop_identity
        ;flatten_bounded_associative
        ;unary_truncate
        ;truncate_small
        ;combine_consts
        ;addoverflow_bit
        ;addcarry_bit
        ;addcarry_small
        ;addoverflow_small
        ;addbyte_small
        ;xor_same
    ].
End RewritePass.

Module Export Options.
  (* Holds the order and multiplicity of passes *)
  Class rewriting_pipeline_opt := rewriting_pipeline : list rewrite_pass.
  (* Holds the passes that are enabled *)
  Class rewriting_pass_filter_opt := rewriting_pass_filter : rewrite_pass -> bool.
  (* Holds the actual list of passes that are used; we make this a
     separate option so that it is computed once and for all rather
     than every time, because it is (currently) quadratic to compute
     in the number of passes *)
  Class rewriting_passes_opt := rewriting_passes : list rewrite_pass.
  Definition default_rewriting_passes
             {rewriting_pipeline : rewriting_pipeline_opt}
             {rewriting_pass_filter : rewriting_pass_filter_opt}
    : rewriting_passes_opt
    := List.filter rewriting_pass_filter rewriting_pipeline.

  Class symbolic_options_opt :=
    { asm_rewriting_pipeline : rewriting_pipeline_opt
    ; asm_rewriting_pass_filter : rewriting_pass_filter_opt
    }.

  (* This holds the list of computed options, which are passed around between methods *)
  Class symbolic_options_computed_opt :=
    { asm_rewriting_passes : rewriting_passes_opt
    }.

  (* N.B. The default rewriting pass filter should not be changed here, but instead changed in CLI.v where it is derived from a default string *)
  Definition default_symbolic_options : symbolic_options_opt
    := {| asm_rewriting_pipeline := default_rewrite_pass_order
       ; asm_rewriting_pass_filter := fun _ => true
       |}.
End Options.
Module Export Hints.
  Global Existing Instance default_rewriting_passes.
  Global Existing Instances
         Build_symbolic_options_opt
         Build_symbolic_options_computed_opt
         asm_rewriting_pipeline
         asm_rewriting_pass_filter
         asm_rewriting_passes
  .
  #[global]
   Hint Cut [
      ( _ * )
        (asm_rewriting_pipeline
        | asm_rewriting_pass_filter
        | asm_rewriting_passes
        ) ( _ * )
        (Build_symbolic_options_opt
        | Build_symbolic_options_computed_opt
        )
    ] : typeclass_instances.
End Hints.

Definition associative o := match o with add _|addZ|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ=> true | _ => false end.
Definition commutative o := match o with add _|addZ|addcarry _|addoverflow _|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ => true | _ => false end.
Definition identity o := match o with mul s => Some match s with N0 => 0%Z | _ => 1%Z end| mulZ=>Some 1%Z |add _|addZ|or _|orZ|xor _|xorZ|addcarry _|addcarryZ _|addoverflow _ => Some 0%Z | and s => Some (Z.ones (Z.of_N s))|andZ => Some (-1)%Z |_=> None end.
(* identity, but not in the first slot *)
Definition identity_after_0 o := match o with subborrow _|subborrowZ _ => Some 0%Z | _=> None end.
Definition unary_truncate_size o := match o with add s|and s|or s|xor s|mul s => Some (Z.of_N s) | addZ|mulZ|andZ|orZ|xorZ => Some (-1)%Z | _ => None end.
Definition op_always_interps o := match o with add _|addcarry _|addoverflow _|and _|or _|xor _|mul _|addZ|mulZ|andZ|orZ|xorZ|addcarryZ _ => true | _ => false end.
Definition combines_to o := match o with add s => Some (mul s) | addZ => Some mulZ | _ => None end.
(* the inner operation can be dropped when replacing it with another operation results in a bounded output *)
Variant drop_kind := drop_always | drop_if_bounded (bound : ZRange.zrange) (rep_op : op).
Definition bounds_for_drop_inner_associative o_outer o_inner :=
  match o_outer with addcarryZ s|addcarry s(*|addoverflow s*) =>
  match o_inner with
  | addZ => Some drop_always
  | add _ => (s' <- unary_truncate_size o_inner; Some (drop_if_bounded (ZRange.Build_zrange 0 (Z.ones s')) addZ))
  | _ => None end | _ => None end%option.

Definition node (A : Set) : Set := op * list A.
Global Instance Show_node {A : Set} {show_A : Show A} : Show (node A) := show_prod.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).
Local Set Elimination Schemes.
Section expr_ind.
  Context (P : expr -> Prop)
    (HRef : forall i, P (ExprRef i))
    (HApp : forall n, Forall P (snd n) -> P (ExprApp n)).
  Fixpoint expr_ind e {struct e} : P e :=
    match e with
    | ExprRef i => HRef i
    | ExprApp n => HApp _ (list_rect _ (Forall_nil _) (fun e _ H => Forall_cons e (expr_ind e) H) (snd n))
    end.
End expr_ind.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.
Definition Show_expr_body (Show_expr : Show expr) : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fun e => match e with
               | ExprRef i => "ExprRef " ++ show i
               | ExprApp (o, e) => "ExprApp " ++ show (o, e)
               end%string.
Definition Show_expr : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fix Show_expr e := Show_expr_body Show_expr e.
Global Existing Instance Show_expr.

Local Notation max_powers_of_two := 5%nat (only parsing).
Local Notation max_decimal := 256%Z (only parsing).

Definition show_infix_op (o : op) : option string
  := match o with
     | add s => Some ("+" ++ String.to_subscript (show s))
     | shl s => Some (">>" ++ String.to_subscript (show s))
     | shr s => Some (">>" ++ String.to_subscript (show s))
     | and s => Some ("&"  ++ String.to_subscript (show s))
     | or s  => Some ("|"  ++ String.to_subscript (show s))
     | xor s => Some ("^"  ++ String.to_subscript (show s))
     | mul s => Some ("*"  ++ String.to_subscript (show s))
     | sar s => Some (">>>" ++ String.to_subscript (show s))
     | addZ  => Some "+ℤ"
     | mulZ  => Some "*ℤ"
     | shlZ  => Some "<<ℤ"
     | shrZ  => Some ">>ℤ"
     | andZ  => Some "&ℤ"
     | orZ   => Some "|ℤ"
     | xorZ  => Some "^ℤ"
     | _ => None
     end%string.

Definition show_prefix_op (o : op) : option (string * Level)
  := match o with
     | neg s => Some ("-" ++ String.to_subscript (show s), opp_lvl)
     | negZ => Some ("-ℤ", opp_lvl)
     | _ => None
     end%string.

Definition show_lvl_expr_pretty : ShowLevel expr
  := fix show_lvl_pretty_expr (e : expr) : Level -> string
    := let __ : ShowLevel expr := show_lvl_pretty_expr in
       let __ : Show expr := @Show_of_ShowLevel _ show_lvl_pretty_expr in
       let show_comment_args args
         := match args with
            | nil => ""
            | _ => " (* " ++ show args ++ " *)"
            end%string in
       match e with
       | ExprRef i => fun _ => "#" ++ show i
       | ExprApp (old s x, args) => lvl_wrap_parens app_lvl ("old" ++ String.to_subscript (show s) ++ " " ++ show x ++ show_comment_args args)
       | ExprApp (const x, args) => fun lvl => PowersOfTwo.show_lvl_Z_up_to max_powers_of_two max_decimal x lvl ++ show_comment_args args
       | ExprApp ((add _|shl _|shr _|and _|or _|xor _|mul _|sar _|addZ|mulZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args)
         => let o : string := invert_Some (show_infix_op o) in
            match args with
            | nil => fun _ => o ++ "[]"
            | x :: nil => fun _ => o ++ "[" ++ show x ++ "]"
            | _ => fun _ => "(" ++ String.concat (" " ++ o ++ " ") (List.map show args) ++ ")"
            end
       | ExprApp ((neg _|negZ) as o, args)
         => let '(o, lvl) := invert_Some (show_prefix_op o) in
            match args with
            | nil => fun _ => o ++ "[]"
            | x :: nil => fun _ => o ++ show_lvl x lvl
            | _ => fun _ => o ++ show args
            end
       | ExprApp (o, args)
         => fun _ => "(" ++ show_op_subscript o ++ ", " ++ show args ++ ")"
       end%string%list.

Definition show_expr_pretty : Show expr
  := @Show_of_ShowLevel _ show_lvl_expr_pretty.

Lemma op_beq_spec a b : BoolSpec (a=b) (a<>b) (op_beq a b).
Proof using Type. cbv [op_beq]; destruct (op_eq_dec a b); constructor; congruence. Qed.
Global Instance reflect_eq_op : reflect_rel eq op_beq | 10 := reflect_rel_of_BoolSpec op_beq_spec.
Fixpoint expr_beq (X Y : expr) {struct X} : bool :=
  match X, Y with
  | ExprRef x, ExprRef x0 => N.eqb x x0
  | ExprApp x, ExprApp x0 =>
      Prod.prod_beq _ _ op_beq (ListUtil.list_beq expr expr_beq) x x0
  | _, _ => false
  end.
Lemma expr_beq_spec a b : BoolSpec (a=b) (a<>b) (expr_beq a b).
Proof using Type.
  revert b; induction a, b; cbn.
  1: destruct (N.eqb_spec i i0); constructor; congruence.
  1,2: constructor; congruence.
  destruct n, n0; cbn.
  destruct (op_beq_spec o o0); cbn in *; [subst|constructor; congruence].
  revert l0; induction H, l0; cbn; try (constructor; congruence); [].
  destruct (H e); cbn; try (constructor; congruence); []; subst.
  destruct (IHForall l0); [left|right]; congruence.
Qed.
Global Instance reflect_eq_expr : reflect_rel eq expr_beq | 10 := reflect_rel_of_BoolSpec expr_beq_spec.
Lemma expr_beq_true a b : expr_beq a b = true -> a = b.
Proof using Type. destruct (expr_beq_spec a b); congruence. Qed.

Require Import Crypto.Util.Option Crypto.Util.Notations Coq.Lists.List.
Import ListNotations.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Definition signed s n : Z := (Z.land (Z.shiftl 1 (Z.of_N s-1) + n) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1))%Z.
  Definition op_to_Z_binop (o : op) : option _
      := match o with
         | add _ => Some Z.add
         | shl _ => Some Z.shiftl
         | shr _ => Some Z.shiftr
         | and _ => Some Z.land
         | or _ => Some Z.lor
         | xor _ => Some Z.lxor
         | mul _ => Some Z.mul
         | addZ => Some Z.add
         | mulZ => Some Z.mul
         | shlZ => Some Z.shiftl
         | shrZ => Some Z.shiftr
         | andZ => Some Z.land
         | orZ => Some Z.lor
         | xorZ => Some Z.lxor
         | _ => None
         end.

  Definition interp_op o (args : list Z) : option Z :=
    Eval cbv [invert_Some identity op_to_Z_binop] in
    let keep n x := Z.land x (Z.ones (Z.of_N n)) in
    match o, args with
    | old s x, nil => match ctx x with Some v => Some (keep s v) | None => None end
    | const z, nil => Some z
    | addcarry s, args =>
        Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s) mod 2)
    | subborrow s, cons a args' =>
        Some ((- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s)) mod 2)
    | addoverflow s, args => Some (Z.b2z (negb (Z.eqb
      (signed s (keep s (List.fold_right Z.add 0 args)))
                         (List.fold_right Z.add 0%Z (List.map (signed s) args)))))
    | neg s, [a] => Some (keep s (- a))
    | shl s, [a; b] => Some (keep s (Z.shiftl a b))
    | shr s, [a; b] => Some (keep s (Z.shiftr a b))
    | sar s, [a; b] => Some (keep s (Z.shiftr (signed s a) b))
    | rcr s, [v1; cf; cnt] => Some (
        let v1c := Z.lor v1 (Z.shiftl cf (Z.of_N s)) in
        let l := Z.lor v1c (Z.shiftl v1 (1+Z.of_N s)) in
        keep s (Z.shiftr l cnt))
    | (add s|and s|or s|xor s|mul s) as o, args
      => let id := invert_Some (identity o) in
         let o := invert_Some (op_to_Z_binop o) in
         Some (keep s (List.fold_right o id args))
    | (addZ|mulZ|andZ|orZ|xorZ) as o, args
      => let id := invert_Some (identity o) in
         let o := invert_Some (op_to_Z_binop o) in
         Some (List.fold_right o id args)
    | slice lo sz, [a] => Some (keep sz (Z.shiftr a (Z.of_N lo)))
    | set_slice lo sz, [a; b] =>
        Some (Z.lor (Z.shiftl (keep sz b) (Z.of_N lo))
                    (Z.ldiff a (Z.shiftl (Z.ones (Z.of_N sz)) (Z.of_N lo))))
    | selectznz, [c; a; b] => Some (if Z.eqb c 0 then a else b)
    | iszero, [a] => Some (Z.b2z (Z.eqb a 0))
    | negZ, [a] => Some (Z.opp a)
    | shlZ, [a; b] => Some (Z.shiftl a b)
    | shrZ, [a; b] => Some (Z.shiftr a b)
    | addcarryZ s, args => Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s))
    | subborrowZ s, cons a args' => Some (- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s))
    | _, _ => None
    end%Z.
End WithContext.
Definition interp0_op := interp_op (fun _ => None).

Lemma interp_op_weaken_symbols G1 G2 o args
  (H : forall (s:symbol) v, G1 s = Some v -> G2 s = Some v)
  : forall v, interp_op G1 o args = Some v -> interp_op G2 o args = Some v.
Proof using Type.
  cbv [interp_op option_map]; intros;
    repeat (BreakMatch.break_match || BreakMatch.break_match_hyps);
    inversion_option; subst;
    try congruence.
  all : eapply H in Heqo0; congruence.
Qed.

Lemma interp_op_interp0_op o a v (H : interp0_op o a = Some v)
  : forall G, interp_op G o a = Some v.
Proof using Type. intros; eapply interp_op_weaken_symbols in H; try eassumption; discriminate. Qed.

Definition node_beq {A : Set} (arg_eqb : A -> A -> bool) : node A -> node A -> bool :=
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).
Global Instance reflect_node_beq {A : Set} {arg_eqb} {H : reflect_rel (@eq A) arg_eqb}
  : reflect_rel eq (@node_beq A arg_eqb) | 10 := _.

Local Open Scope Z_scope.
Require Crypto.Language.API.
Require Crypto.AbstractInterpretation.ZRange.
Require Crypto.AbstractInterpretation.ZRangeProofs.
Require Import Crypto.CastLemmas.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Util.ZRange.LandLorBounds.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.LandLorBounds.

Section bound_node_via_PHOAS.
  Import Crypto.Util.ZRange.
  Import API.Compilers.
  Import AbstractInterpretation.ZRange.Compilers.
  Import AbstractInterpretation.ZRangeProofs.Compilers.

  Local Instance : shiftr_avoid_uint1_opt := false.
  Local Notation interp_PHOAS_op := (ZRange.ident.option.interp true).

  Definition op_to_PHOAS_binop (o : op) : option _
    := match o with
       | add _ => Some ident.Z_add
       | shl _ => Some ident.Z_shiftl
       | shr _ => Some ident.Z_shiftr
       | and _ => Some ident.Z_land
       | or _ => Some ident.Z_lor
       | xor _ => Some ident.Z_lxor
       | mul _ => Some ident.Z_mul
       | addZ => Some ident.Z_add
       | mulZ => Some ident.Z_mul
       | shlZ => Some ident.Z_shiftl
       | shrZ => Some ident.Z_shiftr
       | andZ => Some ident.Z_land
       | orZ => Some ident.Z_lor
       | xorZ => Some ident.Z_lxor
       | _ => None
       end.
  Definition op_to_PHOAS_unop (o : op) : option _
    := match o with
       | neg _ => Some ident.Z_opp
       | negZ => Some ident.Z_opp
       | _ => None
       end.
  Definition op_to_PHOAS_tritop (o : op) : option _
    := match o with
       | selectznz => Some ident.Z_zselect
       | _ => None
       end.
  Definition op_to_bounds (o : op) : option _
    := match o with
       | add s
       | shl s
       | shr s
       | and s
       | or s
       | xor s
       | mul s
       | neg s
         => Some r[0~>Z.ones (Z.of_N s)]
       | _ => None
       end%zrange.

  Definition op_to_PHOAS_bounds (o : op) : option (list (unit -> option zrange) -> option zrange)
    := let unthunk := List.map (fun x => x tt) in
       match o with
       | old s _ => Some (fun _ => Some r[0~>Z.ones (Z.of_N s)])
       | const x
         => Some (fun _ => interp_PHOAS_op (ident.Literal (t:=base.type.Z) x))
       | (add _|and _|or _|xor _|mul _) as o
         => let b : zrange := invert_Some (op_to_bounds o) in
            let id : Z := invert_Some (identity o) in
            let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_binop o)) in
            Some (fun args => interp_PHOAS_op ident.Z_cast (Some b) (fold_right o (Some r[id~>id]) (unthunk args)))
       | (addcarry _ | subborrow _ | addoverflow _ | iszero)
         => Some (fun _ => Some r[0~>1])
       | (addZ|mulZ|andZ|orZ|xorZ) as o
         => let id : Z := invert_Some (identity o) in
            let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_binop o)) in
            Some (fun args => fold_right o (Some r[id~>id]) (unthunk args))
       | (shl _|shr _) as o
         => let b : zrange := invert_Some (op_to_bounds o) in
            let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_binop o)) in
            Some (fun args
                  => match args with
                     | [x; y] => interp_PHOAS_op ident.Z_cast (Some b) (o (x tt) (y tt))
                     | _ => None
                     end)
       | (shlZ|shrZ) as o
         => let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_binop o)) in
            Some (fun args
                  => match args with
                     | [x; y] => o (x tt) (y tt)
                     | _ => None
                     end)
       | (neg _) as o
         => let b : zrange := invert_Some (op_to_bounds o) in
            let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_unop o)) in
            Some (fun args
                  => match args with
                     | [x] => interp_PHOAS_op ident.Z_cast (Some b) (o (x tt))
                     | _ => None
                     end)
       | (negZ) as o
         => let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_unop o)) in
            Some (fun args
                  => match args with
                     | [x] => o (x tt)
                     | _ => None
                     end)
       | (selectznz) as o
         => let o := interp_PHOAS_op (invert_Some (op_to_PHOAS_tritop o)) in
            Some (fun args
                  => match args with
                     | [x; y; z] => o (x tt) (y tt) (z tt)
                     | _ => None
                     end)
       | (slice _ s | sar s | rcr s) as o
         => Some (fun _ => Some r[0~>Z.ones (Z.of_N s)])
       | set_slice 0 w
         => Some (fun args
                  => match unthunk args with
                     | [Some a; Some b]
                       => if ((lower a <? 0) || (lower b <? 0))%Z%bool
                          then None
                          else let a := upper a in
                               let b := upper b in
                               Some r[0~>(Z.lor
                                            (Z.land (Z.ones (Z.succ (Z.log2 b))) (Z.ones (Z.of_N w)))
                                            (Z.ldiff (Z.ones (Z.succ (Z.log2 a))) (Z.ones (Z.of_N w))))]
                     | _ => None
                     end)
       | addcarryZ _
       | subborrowZ _
       | set_slice _ _
         => None
       end%zrange.

  Local Coercion is_true : bool >-> Sortclass.

  Lemma interp_op_op_to_PHOAS_bounds_set_slice_0 G o bf arg_bounds args v b
        (H : op_to_PHOAS_bounds o = Some bf)
        (Hargs : Forall2 (fun v b => match b with
                                     | Some b => is_bounded_by_bool v b = true
                                     | None => True
                                     end)
                         args arg_bounds)
        (Hop : interp_op G o args = Some v)
        arg_bounds' (Hb : bf arg_bounds' = Some b)
        (Ha : arg_bounds = List.map (fun x => x tt) arg_bounds')
        w (Ho : set_slice 0 w = o)
    : is_bounded_by_bool v b.
  Proof.
    subst o; cbv [op_to_PHOAS_bounds interp_op] in *; inversion_option; subst.
    break_innermost_match_hyps; inversion_option; subst.
    repeat (destruct_one_head list; inversion_list).
    invlist Forall2.
    break_innermost_match_hyps; inversion_option; subst.
    apply unreflect_bool; reflect_hyps; cbn [upper lower].
    autorewrite with zsimplify_const.
    rewrite Z.land_ones_ones.
    rewrite Z.lor_nonneg, Z.ldiff_nonneg, !Z.land_ones by lia.
    repeat apply conj; auto with zarith.
    match goal with
    | [ H : ~(?x < 0 \/ ?y < 0) |- _ ] => assert (0 <= x /\ 0 <= y) by lia; clear H
    end.
    clear G; destruct_head zrange; destruct_head'_and.
    pose proof Z.log2_le_mono; pose proof Z.log2_nonneg; specialize_all_ways.
    repeat match goal with H : _ -> _ |- _ => clear H end.
    break_innermost_match; reflect_hyps; destruct_head'_or; try lia.
    apply Z.le_bitwise; rewrite ?Z.lor_nonneg, ?Z.ldiff_nonneg; auto with zarith.
    intros; rewrite <- Z.land_ones by lia.
    Z.bitblast_core; cbn.
    all: repeat rewrite ?andb_true_r, ?andb_false_r, ?andb_false_l, ?andb_true_l, ?orb_false_r, ?orb_false_l, ?orb_true_l, ?orb_true_r.
    all: cbv [Bool.le]; break_innermost_match; auto.
    all: rewrite ?Z.min_le_iff in *.
    all: destruct_head'_or.
    all: rewrite Z.bits_above_log2 in * by lia.
    all: congruence.
  Qed.

  Lemma interp_op_op_to_PHOAS_bounds_fold_right_helper G o arg_bounds args v
        (Hargs : Forall2 (fun v b => match b with
                                     | Some b => is_bounded_by_bool v b = true
                                     | None => True
                                     end)
                         args arg_bounds)
        (Hop : interp_op G o args = Some v)
        id (Hid : identity o = Some id)
        bo (Hbo : op_to_PHOAS_binop o = Some bo)
        (o' := interp_PHOAS_op bo)
        (bf := fold_right o' (Some r[id~>id]%zrange))
        b (Hb : bf arg_bounds = Some b)
    : is_bounded_by_bool (fold_right (ident.interp bo) id args) b.
  Proof.
    subst o' bf; subst.
    pose proof (@ZRange.ident.option.interp_related _ _ _ bo
                 : type.related_hetero _ (interp_PHOAS_op bo) (ident.interp bo)) as Hbounds.
    cbn -[interp_PHOAS_op] in *.
    cbv [Morphisms.respectful_hetero] in *.
    revert dependent b.
    clear Hop v.
    induction Hargs; cbn [fold_right]; intros; inversion_option; subst.
    { apply ZRange.is_bounded_by_bool_constant. }
    let H := match goal with H : interp_PHOAS_op bo _ _ = Some _ |- _ => H end in
    in_hyp_under_binders_do (fun H' => rewrite H in H').
    apply Hbounds; clear Hbounds.
    all: break_innermost_match; try reflexivity; specialize_under_binders_by reflexivity.
    all: auto.
  Qed.

  Lemma interp_op_op_to_PHOAS_bounds G o bf arg_bounds args v b
        (H : op_to_PHOAS_bounds o = Some bf)
        (Hargs : Forall2 (fun v b => match b with
                                     | Some b => is_bounded_by_bool v b = true
                                     | None => True
                                     end)
                         args arg_bounds)
        (Hop : interp_op G o args = Some v)
        arg_bounds' (Hb : bf arg_bounds' = Some b)
        (Ha : arg_bounds = List.map (fun x => x tt) arg_bounds')
    : is_bounded_by_bool v b.
  Proof.
    (* pose proof the lemmas that we needed extra insight to prove separately *)
    pose proof (@interp_op_op_to_PHOAS_bounds_set_slice_0 G o bf arg_bounds args v b H Hargs Hop arg_bounds' Hb Ha) as Hslice.
    pose proof (@interp_op_op_to_PHOAS_bounds_fold_right_helper G o arg_bounds args v Hargs Hop) as Hfold_right.
    (* destruct the operation, do general cleanup *)
    cbv [op_to_PHOAS_bounds] in *.
    all: repeat first [ progress subst
                      | progress inversion_option
                      | progress cbn [interp_op] in *
                      | break_innermost_match_hyps_step ].
    (* make use of the special-insight lemmas *)
    all: first [ specialize (Hslice _ eq_refl) | clear Hslice ].
    all: first [ specialize (Hfold_right _ eq_refl _ eq_refl) | clear Hfold_right ].
    all: try assumption.
    (* forward reasoning of destructing bounds interp things, so we can expose the PHOAS bounds lemmas *)
    all: let rec do_on T :=
           lazymatch T with
           | ?F ?x
             => let h := head x in
                try (constr_eq h (@ZRange.ident.option.interp); destruct x eqn:?);
                do_on F
           | _ => idtac
           end in
         repeat match goal with
                | [ H : ?T = Some _ |- _ ] => do_on T
                end.
    (* pose proof the bounds be get from PHOAS reasoning *)
    all: repeat match goal with
                | [ H : context[@ZRange.ident.option.interp ?a ?b ?t ?op] |- _ ]
                  => unique pose proof (@ZRange.ident.option.interp_related a b t op)
                end.
    (* various simplification and cleanup *)
    all: cbn -[interp_PHOAS_op] in *.
    all: cbv [Morphisms.respectful_hetero] in *.
    all: invlist Forall2.
    all: repeat first [ progress subst
                      | assumption
                      | progress cbn [List.map] in *
                      | inversion_list_step
                      | match goal with
                        | [ H : Forall2 _ nil _ |- _ ] => inversion H; clear H
                        | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                        | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                        | [ H : nil = List.map _ ?ls |- _ ] => is_var ls; destruct ls
                        | [ H : _ :: _ = List.map _ ?ls |- _ ] => is_var ls; destruct ls
                        end ].
    all: break_innermost_match_hyps.
    (* handle goals with relatively simple bounds that follow just from masking/casting/modulo *)
    all: try change (Z.land ?x 0) with (Z.land x (Z.ones 0)).
    all: repeat match goal with
                | [ |- context[is_bounded_by_bool (Z.land ?x (Z.ones ?n)) _] ]
                  => rewrite (@Z.land_ones x n), ?(Z.ones_equiv n), <- ?Z.sub_1_r by lia
                | [ |- is_true (is_bounded_by_bool (?y mod ?x) r[0~>?x-1]) ]
                  => apply unreflect_bool; cbn [lower upper]; generalize (Z.mod_pos_bound y x); try lia
                | [ |- is_true (is_bounded_by_bool (?y mod ?x) r[0~>_]) ]
                  => try now apply unreflect_bool; cbn [lower upper]; generalize (Z.mod_pos_bound y x); lia
                | [ |- is_true (is_bounded_by_bool (Z.b2z ?b) r[0~>1]) ]
                  => case b; vm_compute; reflexivity
                end.
    (* transform asm masking (Z.land _ (Z.ones _)) into PHOAS casting (ident.cast), so the bounds things line up *)
    all: repeat first [ assumption
                      | solve [ auto ]
                      | match goal with
                        | [ |- context[is_bounded_by_bool (?x mod ?y) ?b] ]
                          => rewrite <- (Z.sub_add 1 y), (Z.sub_1_r y);
                             rewrite <- (@ident.cast_out_of_bounds_simple_0_mod (Z.pred y)) by auto with zarith;
                             rewrite <- ?Z.ones_equiv
                        end ].
    all: rewrite ?Z.add_simpl_r. (* idk why we need this *)
    (* start applying and specializing PHOAS bounds hypotheses *)
    all: repeat first [ reflexivity
                      | assumption
                      | solve [ auto ]
                      | exactly_once (idtac; multimatch goal with
                                             | [ H : _ |- _ ] => apply H; clear H
                                             end)
                      | break_innermost_match_step
                      | progress specialize_under_binders_by reflexivity
                      | progress specialize_under_binders_by eapply zrange_lb ].
    (* some PHOAS bounds hypotheses have a match in their conclusion; we rewrite away the match by autospecializing it with hypotheses in the context *)
    all: repeat first [ match goal with
                        | [ H : ?x = _ |- _ ]
                          => let h := head x in
                             constr_eq h (@ZRange.ident.option.interp);
                             progress in_hyp_under_binders_do (fun H' => rewrite H in H')
                        end ].
    (* finish specializing PHOAS bounds hypotheses *)
    all: repeat first [ reflexivity
                      | assumption
                      | congruence
                      | progress inversion_option
                      | progress subst
                      | solve [ auto ]
                      | exactly_once (idtac; multimatch goal with
                                             | [ H : _ |- _ ] => apply H; clear H
                                             end)
                      | break_innermost_match_step
                      | apply zrange_lb
                      | progress specialize_under_binders_by reflexivity
                      | progress specialize_under_binders_by apply zrange_lb
                      | break_innermost_match_hyps_step ].
    (* Somehow, Z.zselect gets unfolded in the goal and broken up by break_innermost_match above; so we must unfold it in the hyps *)
    all: cbv [Z.zselect] in *.
    all: repeat match goal with
                | [ H : (?x =? 0) = _ |- _ ] => in_hyp_under_binders_do (fun H' => rewrite H in H')
                end.
    all: try now cbv [is_true]; eauto with nocore.
  Qed.

  Definition bound_node_idx_via_PHOAS (lookup_bounds : idx -> option zrange) (n : node idx) : option zrange
    := (let '(o, args) := n in
        b <- op_to_PHOAS_bounds o;
        b (List.map (fun idx 'tt => lookup_bounds idx) args))%option.

  Lemma bound_node_idx_via_PHOAS_Forall2_ext lookup_bounds1 lookup_bounds2 n1 n2
    : fst n1 = fst n2 -> Forall2 (fun i1 i2 => lookup_bounds1 i1 = lookup_bounds2 i2) (snd n1) (snd n2) -> bound_node_idx_via_PHOAS lookup_bounds1 n1 = bound_node_idx_via_PHOAS lookup_bounds2 n2.
  Proof.
    destruct n1 as [o1 a1], n2 as [o2 a2]; cbn [fst snd]; intro; subst.
    cbv [bound_node_idx_via_PHOAS Crypto.Util.Option.bind]; break_innermost_match; try reflexivity.
    intro H; apply f_equal.
    induction H; cbn; f_equal; eauto.
    match goal with H : _ |- _ => now rewrite H end.
  Qed.

  Lemma bound_node_idx_via_PHOAS_Forall_ext lookup_bounds1 lookup_bounds2 n
    : Forall (fun i => lookup_bounds1 i = lookup_bounds2 i) (snd n) -> bound_node_idx_via_PHOAS lookup_bounds1 n = bound_node_idx_via_PHOAS lookup_bounds2 n.
  Proof.
    intro H; apply bound_node_idx_via_PHOAS_Forall2_ext; cbn; try reflexivity.
    induction H; constructor; eauto.
  Qed.

  Lemma interp_op_bound_node_idx_via_PHOAS lookup_bounds (evalGd : Symbolic.expr -> _ -> Prop) G o args argsZ bs v
        (H : bound_node_idx_via_PHOAS lookup_bounds (o, args) = Some bs)
        (Hargs : Forall (fun i => forall v b,
                             evalGd (ExprRef i) v
                             -> lookup_bounds i = Some b
                             -> is_bounded_by_bool v b = true)
                        args)
        (HargsZ : Forall2 evalGd (List.map ExprRef args) argsZ)
        (Hop : interp_op G o argsZ = Some v)
    : is_bounded_by_bool v bs.
  Proof.
    cbv [bound_node_idx_via_PHOAS Crypto.Util.Option.bind] in *; break_innermost_match_hyps; inversion_option; subst.
    eapply interp_op_op_to_PHOAS_bounds; try eassumption; try reflexivity.
    rewrite !Forall2_map_r_iff.
    rewrite Forall2_map_l_iff in HargsZ.
    clear dependent o.
    clear dependent bs.
    induction HargsZ; invlist Forall; constructor; break_innermost_match_hyps; break_innermost_match; inversion_option; subst; eauto.
  Qed.
End bound_node_via_PHOAS.

Class description := descr : option ((unit -> string) * bool (* always show *)).
#[global]
Typeclasses Opaque description.
Definition eager_description := option (string * bool).
Notation Build_description descr always_show := (Some (fun 'tt => descr, always_show)) (only parsing).
Notation no_description := None (only parsing).

(* all indices in the node must be already present in the dag *)
Definition node_arg_ok (i : idx) (n : idx) := (n < i)%N.
Definition node_args_ok (i : idx) (n : list idx) := Forall (node_arg_ok i) n.
(* fresh symbols must have value <= their index, so that fresh symbols are truly fresh *)
Definition node_ok (i : idx) (n : node idx) := (forall w s args, n = (old w s, args) -> (s <= i)%N) /\ node_args_ok i (snd n).
Lemma new_node_ok n (pf : match n with (old _ _, _) => False | _ => True end) i (Hi : node_args_ok i (snd n)) : node_ok i n.
Proof. split; repeat intro; subst; assumption. Qed.
Existing Class node_ok.
Existing Class node_arg_ok.
Existing Class node_args_ok.
#[global]
Hint Extern 1 (node_ok ?i ?n) => exact (@new_node_ok n I i) : typeclass_instances.
#[global] Instance node_args_ok_nil i : node_args_ok i nil.
Proof. constructor. Qed.
Lemma node_args_ok_cons i x xs : node_arg_ok i x -> node_args_ok i xs -> node_args_ok i (x :: xs).
Proof. constructor; assumption. Qed.
(* For @cons N and @cons idx *)
#[global] Hint Extern 2 (node_args_ok ?i (@cons _ ?x ?xs)) => simple notypeclasses refine (@node_args_ok_cons i x xs) : typeclass_instances.
Lemma relax_node_arg_ok i1 i2 n : (i1 < i2)%N -> node_arg_ok i1 n -> node_arg_ok i2 n.
Proof. cbv [node_arg_ok idx] in *; lia. Qed.
Lemma relax_node_args_ok i1 i2 n : (i1 < i2)%N -> node_args_ok i1 n -> node_args_ok i2 n.
Proof. cbv [node_args_ok]; intro; apply Forall_impl; intro; apply relax_node_arg_ok; assumption. Qed.
Lemma relax_node_ok i1 i2 n : (i1 < i2)%N -> node_ok i1 n -> node_ok i2 n.
Proof.
  cbv [node_ok]; intro H; pose proof (@relax_node_args_ok i1 i2 (snd n) H).
  intuition (auto; subst).
  specialize_under_binders_by reflexivity.
  lia.
Qed.
Module Type DagDefinitions.
  Parameter t : Type.
  Parameter empty : t.
  Parameter size : t -> N.
  Parameter lookup : t -> idx -> option (node idx).
  Parameter lookup_bounds : t -> idx -> option ZRange.zrange.
  Parameter reverse_lookup : t -> node idx -> option idx.
  Axiom size_ok : t -> Prop.
  Axiom merge_node : forall {descr : description} (n : node idx) (d : t), idx * t.
End DagDefinitions.
Module DagExtraDefinitions (Import dag : DagDefinitions).
  Definition all_nodes_ok (d : t) : Prop
    := forall i r, lookup d i = Some r -> node_ok i r.
  Definition bounds_ok (d : t) : Prop
    := (forall i r, lookup d i = Some r -> lookup_bounds d i = bound_node_idx_via_PHOAS (lookup_bounds d) r)
       /\ (forall i, lookup d i = None -> lookup_bounds d i = None).
  (* We require that all ok nodes reference only other nodes in the dag; we can overapproximate this by requiring all indices <= size be present, which is tautological for assoc-list dags *)
  Definition ok (d : t) : Prop
  := size_ok d
     /\ bounds_ok d
     /\ (forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n)
     /\ (forall i n, lookup d i = Some n -> (i < size d)%N)
     /\ (forall i, lookup d i = None -> (size d <= i)%N).

  Definition gensym (s:OperationSize) (d : t) : node idx
    := (old s (size d), []).
  Existing Class ok.
  Existing Class all_nodes_ok.

  Definition get_eager_description_description (d : eager_description) : option string
    := option_map fst d.
  Definition get_eager_description_always_show (d : eager_description) : bool
    := match d with Some (_, always_show) => always_show | None => false end.
  Definition force_description : description -> eager_description
    := option_map (fun '(descr, always_show) => (descr tt, always_show)).

  Definition M T := t -> T * t.
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun d => let '(v, d) := v d in f v d.
  Definition ret {A} (v : A) : M A
    := fun d => (v, d).

  Module Type EagerDagDefinitions.
    Parameter t : Type.
    Parameter force : dag.t -> t.
    Parameter description_lookup : forall (d : t) (descr : string), list idx.
    Parameter elements : t -> list (idx * node idx * eager_description).
  End EagerDagDefinitions.
End DagExtraDefinitions.
Module Type DagExtraDefinitionsSig (dag : DagDefinitions).
  Include DagExtraDefinitions dag.
End DagExtraDefinitionsSig.
Module Type DagProperties (Import dag : DagDefinitions) (Import dag' : DagExtraDefinitionsSig dag).
  Axiom lookup_merge_node
    : forall {descr : description} (n : node idx) (d : t) i
             {ok : ok d},
      dag.lookup (snd (dag.merge_node n d)) i = match dag.lookup d i with
                                                | Some v => Some v
                                                | None
                                                  => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                     then Some n
                                                     else None
                                                end.

  Axiom reverse_lookup_merge_node
    : forall {d : t}
             {ok : ok d} {descr : description} (n n' : node idx),
      dag.reverse_lookup (snd (dag.merge_node n d)) n'
      = if node_beq N.eqb n' n
        then Some (fst (dag.merge_node n d))
        else dag.reverse_lookup d n'.

  Axiom fst_merge_node
    : forall {descr : description} (n : node idx) (d : t),
      fst (dag.merge_node n d) = match reverse_lookup d n with
                                 | Some i => i
                                 | None => size d
                                 end.

  Axiom lookup_bounds_merge_node
    : forall {descr : description} (n : node idx) (d : t) i
             {ok : ok d},
      dag.lookup_bounds (snd (dag.merge_node n d)) i = match dag.lookup_bounds d i with
                                                       | Some v => Some v
                                                       | None
                                                         => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                            then bound_node_idx_via_PHOAS (lookup_bounds d) n
                                                            else None
                                                       end.

  Axiom lookup_empty : forall i, lookup empty i = None.
  Axiom reverse_lookup_empty : forall n, reverse_lookup empty n = None.
  Axiom lookup_bounds_empty : forall i, lookup_bounds empty i = None.
  Axiom size_empty : size empty = 0%N.
  Axiom size_ok_empty : size_ok empty.

  Axiom size_merge_node
    : forall {descr:description} n (d:t),
      size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Axiom size_ok_merge_node
    : forall {descr:description} n (d:t),
      ok d -> size_ok (snd (merge_node n d)).
End DagProperties.
Module DagExtraProperties (Import dag : DagDefinitions) (Import dag' : DagExtraDefinitionsSig dag) (Import dag'' : DagProperties dag dag').
  Lemma iff_reverse_lookup_lookup d {ok : ok d}
    : forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n.
  Proof. apply ok. Qed.

  Lemma lookup_value_size d {ok : ok d}
    : forall i n, lookup d i = Some n -> (i < size d)%N.
  Proof. apply ok. Qed.

  Lemma lookup_size_error d {ok : ok d}
    : forall i, (size d <= i)%N -> lookup d i = None.
  Proof.
    intro i; generalize (lookup_value_size d i); destruct lookup; intuition.
    specialize_under_binders_by reflexivity.
    lia.
  Qed.

  Lemma lookup_error_size d {ok : ok d}
    : forall i, lookup d i = None -> (size d <= i)%N.
  Proof. apply ok. Qed.

  Lemma lookup_bounds_ok (d : t) {ok : ok d}
    : forall i r, dag.lookup d i = Some r -> dag.lookup_bounds d i = bound_node_idx_via_PHOAS (dag.lookup_bounds d) r.
  Proof. apply ok. Qed.

  Lemma lookup_bounds_lookup (d : t) {ok : ok d}
    : forall i, dag.lookup_bounds d i = match dag.lookup d i with
                                        | None => None
                                        | Some r => bound_node_idx_via_PHOAS (dag.lookup_bounds d) r
                                        end.
  Proof.
    intro i.
    pose proof (lookup_bounds_ok d i).
    pose proof (lookup_error_size d i).
    pose proof (lookup_value_size d i).
    destruct ok; cbv [bounds_ok] in *; destruct_head'_and.
    destruct lookup_bounds eqn:?, lookup eqn:?.
    all: specialize_under_binders_by reflexivity.
    all: specialize_under_binders_by eassumption.
    all: auto.
    all: congruence.
  Qed.

  Lemma all_nodes_idx_present (d : t)
        {ok : ok d}
        {all_ok : all_nodes_ok d}
    : forall i r, dag.lookup d i = Some r -> Forall (fun a => dag.lookup d a <> None) (snd r).
  Proof.
    cbv [all_nodes_ok] in *; destruct_head'_and.
    intros; specialize_under_binders_by eassumption.
    cbv [node_ok node_args_ok node_arg_ok] in *; destruct_head'_and.
    let H := match goal with H : Forall _ ?l |- Forall _ ?l => H end in
    induction H; constructor; try assumption.
    repeat match goal with
           | [ H : lookup _ _ = Some _ |- _ ] => apply lookup_value_size in H; [ | assumption .. ]
           | [ H : lookup _ _ = None |- _ ] => apply lookup_error_size in H; [ | assumption .. ]
           | [ |- None <> None ] => exfalso
           | [ |- Some _ <> None ] => congruence
           | [ |- ?x <> None ] => destruct x eqn:?
           | [ |- False ] => lia
           end.
  Qed.

  Lemma reverse_lookup_gensym s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.reverse_lookup d (gensym s d) = None.
  Proof.
    cbv [dag'.all_nodes_ok] in *.
    destruct (reverse_lookup d (gensym s d)) as [i|] eqn:H; [ | reflexivity ].
    rewrite iff_reverse_lookup_lookup in H by assumption.
    cbv [node_ok gensym] in *.
    repeat first [ progress destruct_head'_and
                 | progress specialize_under_binders_by eassumption
                 | progress specialize_under_binders_by reflexivity ].
    apply lookup_value_size in H; trivial.
    lia.
  Qed.

  Lemma lookup_merge_node_gensym {descr : description} s (d : t) i
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.lookup (snd (dag.merge_node (gensym s d) d)) i
      = if (i =? size d)%N
        then Some (gensym s d)
        else dag.lookup d i.
  Proof.
    rewrite lookup_merge_node, reverse_lookup_gensym by assumption.
    cbv [andb is_None].
    break_innermost_match; try reflexivity; reflect_hyps; subst; try tauto.
    rewrite lookup_size_error in * by first [ assumption | lia ].
    congruence.
  Qed.

  Lemma fst_merge_node_gensym {descr : description} s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : fst (dag.merge_node (gensym s d) d) = size d.
  Proof.
    rewrite fst_merge_node, reverse_lookup_gensym by assumption; reflexivity.
  Qed.

  Lemma bound_node_gensym s (d : t) {lookup_bounds}
    : bound_node_idx_via_PHOAS lookup_bounds (gensym s d) = Some {| ZRange.lower := 0; ZRange.upper := Z.ones (Z.of_N s) |}.
  Proof. reflexivity. Qed.

  Lemma size_merge_node_le {descr:description} n (d:t)
    : (size d <= size (snd (merge_node n d)))%N.
  Proof.
    rewrite size_merge_node; break_innermost_match; lia.
  Qed.

  Lemma size_merge_node_gensym {descr:description} s (d:t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : size (snd (merge_node (gensym s d) d)) = N.succ (size d).
  Proof. rewrite size_merge_node, reverse_lookup_gensym by assumption; reflexivity. Qed.

  Global Instance empty_ok : ok empty | 10.
  Proof.
    repeat apply conj; intros *;
      cbv [bounds_ok]; intros *;
      rewrite ?lookup_empty, ?reverse_lookup_empty, ?size_empty, ?lookup_bounds_empty; try apply size_ok_empty;
      intuition first [ congruence | lia ].
  Qed.
  Global Instance empty_all_nodes_ok : all_nodes_ok empty | 10.
  Proof.
    repeat intro; subst; rewrite lookup_empty in *; congruence.
  Qed.
  Global Instance merge_node_ok {descr:description} {n:node idx} {d : t} {dok : ok d} {dnok : all_nodes_ok d} {nok : node_args_ok (size d) (snd n)} : ok (snd (merge_node n d)) | 10.
  Proof.
    destruct (dok).
    repeat apply conj; cbv [bounds_ok node_args_ok node_arg_ok all_nodes_ok node_ok] in *; intros *;
      rewrite Forall_forall_iff_nth_error in nok;
      setoid_rewrite Forall_forall_iff_nth_error in dnok.
    all: split_and.
    all: rewrite ?lookup_merge_node, ?reverse_lookup_merge_node, ?fst_merge_node, ?size_merge_node, ?lookup_bounds_merge_node by assumption.
    all: erewrite ?(@bound_node_idx_via_PHOAS_Forall_ext (lookup_bounds (snd (merge_node _ _))))
      by (rewrite Forall_forall_iff_nth_error; intros *; rewrite lookup_bounds_merge_node by assumption; reflexivity).
    all: let tac :=
           repeat first [ progress subst
                        | progress intros
                        | progress destruct_head'_and
                        | progress reflect_hyps
                        | break_innermost_match_step
                        | break_innermost_match_hyps_step
                        | apply size_ok_merge_node
                        | lia
                        | progress inversion_option
                        | progress specialize_under_binders_by reflexivity
                        | congruence
                        | tauto
                        | apply bound_node_idx_via_PHOAS_Forall_ext
                        | rewrite Forall_forall_iff_nth_error
                        | match goal with
                          | [ H : lookup ?d (size ?d) = Some _ |- _ ] => apply lookup_value_size in H; [ | assumption .. ]
                          | [ H : ?x = bound_node_idx_via_PHOAS _ _ |- ?y = bound_node_idx_via_PHOAS _ _ ]
                            => replace y with x by congruence; rewrite H;
                               apply bound_node_idx_via_PHOAS_Forall_ext
                          end
                        | split
                        | progress split_iff ] in
         do 2 (tac;
               repeat match goal with
                      | [ H : _ = Some _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                      | [ H : _ = None |- _ ] => progress specialize_all_ways_under_binders_by exact H
                      end;
               tac).
  Qed.
  Global Instance merge_node_all_nodes_ok {descr:description} {n:node idx} {d : t} {dok : ok d} {dnok : all_nodes_ok d} {nok : node_ok (size d) n}
    : all_nodes_ok (snd (merge_node n d)) | 10.
  Proof.
    cbv [all_nodes_ok] in *; intros i r; specialize (dnok i r).
    rewrite lookup_merge_node in * by assumption.
    cbv [andb is_None]; break_innermost_match; intros; inversion_option; reflect_hyps; subst; auto.
  Qed.
  Global Instance gensym_node_ok s d : node_ok (size d) (gensym s d) | 10.
  Proof.
    cbv [node_ok gensym]; split; cbn [snd]; try exact _.
    inversion 1; subst; reflexivity.
  Qed.
  Global Hint Extern 1 (node_ok (size _) (gensym _ _)) => exact (@gensym_node_ok _ _) : typeclass_instances.

  Lemma eq_fst_merge_node_change_descr {descr1 descr2 : description} (n : node idx) (d : t)
    : fst (@merge_node descr1 n d) = fst (@merge_node descr2 n d).
  Proof.
    rewrite !fst_merge_node; reflexivity.
  Qed.

  Lemma lookup_merge_node' {descr1 descr2 : description} (n : node idx) (d : t)
        {ok : ok d}
    : dag.lookup (snd (@dag.merge_node descr1 n d)) (fst (@dag.merge_node descr2 n d)) = Some n.
  Proof.
    rewrite lookup_merge_node, fst_merge_node by assumption.
    cbv [andb is_None].
    repeat first [ rewrite iff_reverse_lookup_lookup in * by assumption
                 | rewrite lookup_size_error in * by first [ assumption | lia ]
                 | progress inversion_option
                 | progress subst
                 | reflexivity
                 | progress reflect_hyps
                 | lia
                 | break_innermost_match_step ].
  Qed.

  Lemma lookup_None d {ok : ok d}
    : forall i, lookup d i = None <-> (size d <= i)%N.
  Proof.
    intro i.
    pose proof (lookup_value_size d i).
    pose proof (lookup_size_error d i).
    pose proof (lookup_error_size d i).
    split; intro; destruct (lookup d i);
      specialize_under_binders_by first [ reflexivity | lia | eassumption ];
      inversion_option; first [ lia | congruence | auto ].
  Qed.

  Lemma lookup_Some d {ok : ok d}
    : forall i, lookup d i <> None <-> (i < size d)%N.
  Proof.
    intro i.
    pose proof (lookup_value_size d i).
    pose proof (lookup_size_error d i).
    pose proof (lookup_error_size d i).
    split; intro; destruct (lookup d i);
      specialize_under_binders_by first [ reflexivity | lia | eassumption ];
      inversion_option; first [ lia | congruence | auto ].
  Qed.

  Lemma lookup_ind d {ok : ok d} {dnok : all_nodes_ok d}
             (P : option (node idx) -> Prop)
             (PNone : P None)
             (PSome : forall o args,
                 (exists i, dag.lookup d i = Some (o, args) /\ node_ok i (o, args))
                 -> Forall (fun a => P (dag.lookup d a)) args
                 -> P (Some (o, args)))
    : forall i, P (dag.lookup d i).
  Proof.
    induction i using (well_founded_induction N.lt_wf_0).
    destruct (lookup d i) as [ [o args] |] eqn:H'; [ | assumption ].
    apply PSome.
    { eexists; split; try eapply dnok; eassumption. }
    { apply dnok in H'.
      cbv [node_ok node_args_ok node_arg_ok] in *; destruct_head'_and.
      cbn [snd] in *.
      let H := match goal with H : Forall _ _ |- _ => H end in
      revert H.
      apply Forall_impl; eauto. }
  Qed.
End DagExtraProperties.
Module Type DagExtraPropertiesSig (dag : DagDefinitions) (dag' : DagExtraDefinitionsSig dag) (dag'' : DagProperties dag dag').
  Include DagExtraProperties dag dag' dag''.
End DagExtraPropertiesSig.
Module Type Dag.
  Include DagDefinitions.
  Include DagExtraDefinitions.
  Declare Module eager : EagerDagDefinitions.
  Include DagProperties.
  Include DagExtraProperties.
End Dag.
Module Old.
Module dag <: Dag.
  Definition t : Type := list (node idx * description * option ZRange.zrange).
  Definition empty : t := nil.
  Definition size (d : t) : N := N.of_nat (List.length d).
  Definition lookup (d : t) (i : idx) : option (node idx)
    := option_map (fun '(n, _d, _b) => n) (List.nth_error d (N.to_nat i)).
  Definition lookup_bounds (d : t) (i : idx) : option ZRange.zrange
    := (n <- List.nth_error d (N.to_nat i); let '(_n, _d, b) := n in b)%option.
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := option_map N.of_nat (List.indexof (fun '(n', _, _) => node_beq N.eqb i n') d).
  Definition size_ok (d : t) : Prop
    := True.
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => (size d, d ++ [(n, descr, bound_node_idx_via_PHOAS (lookup_bounds d) n)])
       end.

  Include DagExtraDefinitions.

  Module eager <: EagerDagDefinitions.
    Definition t := list (idx * node idx * eager_description).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr, _)) => (N.of_nat idx, n, force_description descr))
                  (List.enumerate d).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _) => idx) (List.filter (fun '(_, _, descr') => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
    Definition elements (d : t) : list (idx * node idx * eager_description) := d.
  End eager.

  Lemma lookup_merge_node {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup (snd (dag.merge_node n d)) i = match dag.lookup d i with
                                                | Some v => Some v
                                                | None
                                                  => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                     then Some n
                                                     else None
                                                end.
  Proof.
    cbv [dag.merge_node andb is_None lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | progress cbn [fst snd option_map List.nth_error] in *
                   | progress cbv [option_map] in *
                   | rewrite Nat2N.id in *
                   | rewrite nth_error_app in *
                   | rewrite Nat.sub_diag in *
                   | rewrite nth_error_length_error in * by lia
                   | rewrite @nth_error_nil_error in *
                   | congruence
                   | break_innermost_match_step
                   | match goal with
                     | [ H : nth_error (_ :: _) ?x = _ |- _ ] => destruct x eqn:?; cbn [nth_error] in H
                     end ].
  Qed.

  Lemma reverse_lookup_merge_node {d : t}
        {ok : ok d} {descr : description} (n n' : node idx)
    : dag.reverse_lookup (snd (dag.merge_node n d)) n'
      = if node_beq N.eqb n' n
        then Some (fst (dag.merge_node n d))
        else dag.reverse_lookup d n'.
  Proof.
    cbv [dag.merge_node andb is_None reverse_lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | congruence
                   | progress inversion_option
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | rewrite @indexof_app in *
                   | progress cbv [option_map Crypto.Util.Option.value Crypto.Util.Option.sequence idx] in *
                   | progress cbn [fst snd option_map indexof] in *
                   | rewrite Nat.add_0_r
                   | congruence
                   | break_innermost_match_step
                   | progress break_match
                   | progress break_match_hyps ].
  Qed.

  Lemma fst_merge_node {descr : description} (n : node idx) (d : t)
    : fst (dag.merge_node n d) = match reverse_lookup d n with
                                 | Some i => i
                                 | None => size d
                                 end.
  Proof. cbv [merge_node]; break_innermost_match; reflexivity. Qed.

  Lemma lookup_bounds_merge_node
        {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup_bounds (snd (dag.merge_node n d)) i = match dag.lookup_bounds d i with
                                                       | Some v => Some v
                                                       | None
                                                         => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                            then bound_node_idx_via_PHOAS (lookup_bounds d) n
                                                            else None
                                                       end.
  Proof.
    cbv [merge_node]; break_innermost_match; cbn [snd]; reflect_hyps.
    all: repeat first [ progress destruct_head'_and
                      | progress subst
                      | progress inversion_option
                      | progress inversion_pair
                      | reflexivity
                      | assumption
                      | lia
                      | exfalso; assumption
                      | rewrite Nat2N.id in *
                      | rewrite ListUtil.nth_error_app
                      | rewrite Nat.sub_diag in *
                      | rewrite nth_error_length_error in * by lia
                      | rewrite @nth_error_nil_error in *
                      | break_innermost_match_step
                      | break_innermost_match_hyps_step
                      | progress cbv [lookup_bounds Crypto.Util.Option.bind size] in *
                      | match goal with
                        | [ H : nth_error (_ :: _) ?x = _ |- _ ] => destruct x eqn:?; cbn [nth_error] in H
                        end
                      | progress break_match ].
  Qed.

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite nth_error_nil_error. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. reflexivity. Qed.
  Lemma lookup_bounds_empty i : lookup_bounds empty i = None.
  Proof. cbv [empty lookup_bounds]; now rewrite nth_error_nil_error. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.
  Lemma size_ok_empty : size_ok empty.
  Proof. exact I. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; rewrite ?app_length; cbn [List.length]; lia.
  Qed.

  Lemma size_ok_merge_node {descr:description} n (d:t)
    : ok d -> size_ok (snd (merge_node n d)).
  Proof. constructor. Qed.

  Include DagExtraProperties.
End dag.
End Old.
Module New.
Module dag <: Dag.
  Module IdxMap <: UsualS := NMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module ListIdxMap <: UsualS := ListNMap.
  Module NodeIdxMap <: UsualS := ProdUsualMap OpMap ListIdxMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module IdxMapProperties := FMapFacts.OrdProperties IdxMap <+ OrdProperties_RemoveHints IdxMap.
  Module NodeIdxMapProperties := FMapFacts.OrdProperties NodeIdxMap <+ OrdProperties_RemoveHints NodeIdxMap.

  Definition t : Type := NodeIdxMap.t idx * IdxMap.t (node idx * description * option ZRange.zrange) * N (* size *).
  Definition empty : t := (@NodeIdxMap.empty _, @IdxMap.empty _, 0%N).
  Definition size (d : t) : N := let '(_, _, sz) := d in sz.
  Definition lookup (d : t) (i : idx) : option (node idx)
    := let '(_, d, _) := d in option_map (fun '(n, _, _) => n) (IdxMap.find i d).
  Definition lookup_bounds (d : t) (i : idx) : option ZRange.zrange
    := (let '(_, d, _) := d in n <- IdxMap.find i d; let '(_n, _d, b) := n in b)%option.
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := let '(d, _, _) := d in NodeIdxMap.find i d.
  Definition size_ok (d : t) : Prop
    := let '(im, nm, n) := d in
       NodeIdxMap.cardinal im = N.to_nat (size d)
       /\ IdxMap.cardinal nm = N.to_nat (size d).
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => let lookup_bounds := lookup_bounds d in
            let '(d, d', sz) := d in
            (sz, (NodeIdxMap.add n sz d, IdxMap.add sz (n, descr, bound_node_idx_via_PHOAS lookup_bounds n) d', N.succ sz))
       end.

  Include DagExtraDefinitions.

  Module eager <: EagerDagDefinitions.
    Definition t := list (idx * node idx * eager_description).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr, _b)) => (idx, n, force_description descr))
                  (IdxMap.elements (let '(_, d, _) := d in d)).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _) => idx) (List.filter (fun '(_, _, descr') => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
    Definition elements (d : t) : list (idx * node idx * eager_description) := d.
  End eager.

  Lemma lookup_merge_node {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup (snd (dag.merge_node n d)) i = match dag.lookup d i with
                                                | Some v => Some v
                                                | None
                                                  => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                     then Some n
                                                     else None
                                                end.
  Proof.
    cbv [dag.merge_node andb is_None lookup dag.ok size option_map] in *;
      let tac :=
        repeat first [ assumption
                     | reflexivity
                     | lia
                     | congruence
                     | progress specialize_under_binders_by eassumption
                     | progress subst
                     | progress destruct_head'_and
                     | progress destruct_head' iff
                     | progress split_iff
                     | progress break_innermost_match_hyps
                     | progress specialize_by reflexivity
                     | progress inversion_option
                     | progress inversion_pair
                     | progress reflect_hyps
                     | progress cbn [fst snd option_map] in *
                     | rewrite IdxMap.add_o
                     | break_innermost_match_step ] in
      tac; specialize_all_ways; tac.
  Qed.

  Lemma lookup_bounds_merge_node {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup_bounds (snd (dag.merge_node n d)) i = match dag.lookup_bounds d i with
                                                       | Some v => Some v
                                                       | None
                                                         => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                            then bound_node_idx_via_PHOAS (lookup_bounds d) n
                                                            else None
                                                       end.
  Proof.
    destruct (ok).
    cbv [merge_node]; cbv [size_ok] in *; break_innermost_match; cbn [snd]; reflect_hyps.
    all: let tac :=
           repeat first [ progress destruct_head'_and
                        | progress subst
                        | progress inversion_option
                        | progress inversion_pair
                        | reflexivity
                        | assumption
                        | lia
                        | exfalso; assumption
                        | rewrite IdxMap.add_o
                        | progress specialize_under_binders_by reflexivity
                        | break_innermost_match_step
                        | break_innermost_match_hyps_step
                        | progress cbv [lookup_bounds Crypto.Util.Option.bind size bounds_ok option_map lookup] in * ] in
         tac;
         repeat match goal with
                | [ H : _ = Some _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                end;
         tac.
  Qed.

  Lemma reverse_lookup_merge_node {d : t}
        {ok : ok d} {descr : description} (n n' : node idx)
    : dag.reverse_lookup (snd (dag.merge_node n d)) n'
      = if node_beq N.eqb n' n
        then Some (fst (dag.merge_node n d))
        else dag.reverse_lookup d n'.
  Proof.
    cbv [dag.merge_node andb is_None reverse_lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | congruence
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | progress cbn [fst snd option_map] in *
                   | rewrite NodeIdxMap.add_o
                   | break_innermost_match_step ].
  Qed.

  Lemma fst_merge_node {descr : description} (n : node idx) (d : t)
    : fst (dag.merge_node n d) = match reverse_lookup d n with
                                 | Some i => i
                                 | None => size d
                                 end.
  Proof. cbv [merge_node]; break_innermost_match; reflexivity. Qed.

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite IdxMap.find_empty. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. cbv [empty reverse_lookup]; now rewrite NodeIdxMap.find_empty. Qed.
  Lemma lookup_bounds_empty i : lookup_bounds empty i = None.
  Proof. cbv [empty lookup_bounds]; now rewrite IdxMap.find_empty. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.
  Lemma size_ok_empty : size_ok empty.
  Proof. cbv [size_ok empty size]; now rewrite NodeIdxMapProperties.P.cardinal_1, IdxMapProperties.P.cardinal_1 by first [ apply NodeIdxMap.empty_1 | apply IdxMap.empty_1 ]. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; try reflexivity.
  Qed.

  Lemma size_ok_merge_node {descr:description} n (d:t)
    : ok d -> size_ok (snd (merge_node n d)).
  Proof.
    cbv [merge_node size_ok size ok]; break_innermost_match; cbn [snd] in *; inversion_pair; subst;
      rewrite ?NodeIdxMap.cardinal_add, ?IdxMap.cardinal_add, ?NodeIdxMap.mem_find_b, ?IdxMap.mem_find_b; try solve [ intuition auto ]; [].
    cbv [reverse_lookup lookup option_map idx] in *.
    repeat first [ progress intros
                 | progress destruct_head'_and
                 | progress split_iff
                 | congruence
                 | lia
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress specialize_under_binders_by reflexivity
                 | match goal with
                   | [ H : _ = Some _ |- _ ] => progress specialize_under_binders_by rewrite H
                   end ].
  Qed.

  Include DagExtraProperties.
End dag.
End New.
Require coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Module WithDag (dag : Dag).
Global Arguments dag.t : simpl never.
Global Arguments dag.empty : simpl never.
Global Arguments dag.size : simpl never.
Global Arguments dag.lookup : simpl never.
Global Arguments dag.lookup_bounds : simpl never.
Global Arguments dag.reverse_lookup : simpl never.
Global Arguments dag.ok : simpl never.
Global Arguments dag.all_nodes_ok : simpl never.
Global Arguments dag.merge_node : simpl never.
Global Arguments dag.gensym : simpl never.
Global Strategy 1000 [
      dag.t
        dag.empty
        dag.size
        dag.lookup
        dag.lookup_bounds
        dag.reverse_lookup
        dag.ok
        dag.all_nodes_ok
        dag.merge_node
        dag.gensym
    ].
Notation dag := dag.t.
Declare Scope dagM_scope.
Delimit Scope dagM_scope with dagM.
Bind Scope dagM_scope with dag.M.
Notation "x <- y ; f" := (dag.bind y (fun x => f%dagM)) : dagM_scope.

Section WithDag.
  Context (ctx : symbol -> option Z) (dag : dag.t).
  Definition reveal_step reveal (i : idx) : expr :=
    match dag.lookup dag i with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Definition reveal_node n '(op, args) :=
    ExprApp (op, List.map (reveal n) args).

  (** given a set of indices, get the set of indices of their arguments *)
  Definition reveal_gather_deps_args (ls : NSet.t) : NSet.t
    := fold_right
         (fun i so_far => match dag.lookup dag i with
                          | None => so_far
                          | Some (_op, args) => fold_right NSet.add so_far args
                          end)
         NSet.empty
         (NSet.elements ls).

  (** given a set of seen indices and a set of newly-revealed indices,
  we want to merge the new indices into what's been seen and recurse
  on the new indices *)
  Definition reveal_gather_deps_step reveal_gather_deps (so_far : NSet.t) (new_idxs : NSet.t) : NSet.t
    := let new_idxs := NSet.diff new_idxs so_far in
       if NSet.is_empty new_idxs
       then so_far
       else reveal_gather_deps (NSet.union so_far new_idxs) (reveal_gather_deps_args new_idxs).

  Fixpoint reveal_gather_deps_list (n : nat) (so_far : NSet.t) (new_idxs : NSet.t) : NSet.t
    := match n with
       | O => NSet.union so_far new_idxs
       | S n => reveal_gather_deps_step (reveal_gather_deps_list n) so_far new_idxs
       end.

  Definition reveal_gather_deps (n : nat) (i : idx) : NSet.t
    := reveal_gather_deps_list n NSet.empty (NSet.singleton i).

  Definition reveal_step_from_deps reveal (deps : NSet.t) (i : idx) : expr
    := if NSet.mem i deps
       then match dag.lookup dag i with
            | None => (* undefined *) ExprRef i
            | Some (op, args) => ExprApp (op, List.map reveal args)
            end
       else ExprRef i.
  Fixpoint reveal_from_deps_fueled (fuel : nat) (deps : NSet.t) (i : idx) :=
    match fuel with
    | O => ExprRef i
    | S fuel => reveal_step_from_deps (reveal_from_deps_fueled fuel deps) deps i
    end.
  (** depth determines which indices get expanded, but all references
  to the same index get expanded if they appear in the output *)
  Definition reveal_at_least n (i : idx) : expr
    := reveal_from_deps_fueled (S (N.to_nat (dag.size dag))) (reveal_gather_deps n i) i.

  Definition reveal_node_at_least n '(op, args) :=
    ExprApp (op, List.map (reveal_at_least n) args).

  Local Unset Elimination Schemes.
  Inductive eval : expr -> Z -> Prop :=
  | ERef i op args args' n
    (_:dag.lookup dag i = Some (op, args))
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprRef i) n
  | EApp op args args' n
    (_:List.Forall2 eval args args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprApp (op, args)) n.

  Variant eval_node : node idx -> Z -> Prop :=
  | ENod op args args' n
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval_node (op, args) n.


  Section eval_ind.
    Context (P : expr -> Z -> Prop)
      (HRef : forall i op args args' n, dag.lookup dag i = Some (op, args) ->
        Forall2 (fun e n => eval e n /\ P e n) (map ExprRef args) args' ->
        interp_op ctx op args' = Some n ->
        P (ExprRef i) n)
      (HApp : forall op args args' n,
        Forall2 (fun i e => eval i e /\ P i e) args args' ->
        interp_op ctx op args' = Some n ->
        P (ExprApp (op, args)) n).
    Fixpoint eval_ind i n (pf : eval i n) {struct pf} : P i n :=
      match pf with
      | ERef _ _ _ _ _ A B C => HRef _ _ _ _ _ A (Forall2_weaken (fun _ _ D => conj D (eval_ind _ _ D)) _ _ B) C
      | EApp _ _ _ _ A B => HApp _ _ _ _ (Forall2_weaken (fun _ _ C => conj C (eval_ind _ _ C)) _ _ A) B
      end.
  End eval_ind.

  Lemma eval_eval : forall e v1, eval e v1 -> forall v2, eval e v2 -> v1=v2.
  Proof using Type.
    induction 1; inversion 1; subst;
    enough (args' = args'0) by congruence;
    try replace args0 with args in * by congruence.
    { eapply Forall2_map_l in H0.
      eapply Forall2_flip in H0.
      eapply (proj1 (Forall2_map_l _ _ _)) in H5.
      epose proof Forall2_trans H0 H5 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
    { eapply Forall2_flip in H.
      epose proof Forall2_trans H H4 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
  Qed.

  Lemma eval_eval_Forall2 xs vxs (_ : Forall2 eval xs vxs)
    vys (_ : Forall2 eval xs vys) : vxs = vys.
  Proof using Type.
    revert dependent vys; induction H; inversion 1; subst;
      eauto; eauto using f_equal2, IHForall2, eval_eval.
  Qed.

  Lemma eval_reveal : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal n i = e -> eval e v.
  Proof using Type.
    induction n; cbn [reveal]; cbv [reveal_step]; intros; subst; eauto; [].
    inversion H; subst; clear H.
    rewrite H1; econstructor; try eassumption; [].
    eapply (proj1 (Forall2_map_l _ _ _)) in H2.
    clear dependent i; clear dependent v.
    induction H2; cbn; eauto.
  Qed.

  Lemma eval_node_reveal_node : forall n v, eval_node n v ->
    forall f e, reveal_node f n = e -> eval e v.
  Proof using Type.
    cbv [reveal_node]; inversion 1; intros; subst.
    econstructor; eauto.
    eapply (proj1 (Forall2_map_l _ _ _)) in H0; eapply Forall2_map_l.
    eapply Forall2_weaken; try eassumption; []; cbv beta; intros.
    eapply eval_reveal; eauto.
  Qed.

  Lemma eval_reveal_from_deps_fueled deps : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal_from_deps_fueled n deps i = e -> eval e v.
  Proof using Type.
    induction n; cbn [reveal_from_deps_fueled]; cbv [reveal_step_from_deps]; intros; subst; eauto; [].
    break_innermost_match_step; eauto; [].
    inversion H; subst; clear H.
    rewrite H1; econstructor; try eassumption; [].
    eapply (proj1 (Forall2_map_l _ _ _)) in H2.
    clear dependent i; clear dependent v.
    induction H2; cbn; eauto.
  Qed.

  Lemma eval_reveal_at_least : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal_at_least n i = e -> eval e v.
  Proof using Type.
    cbv [reveal_at_least].
    intros; eapply eval_reveal_from_deps_fueled; eassumption.
  Qed.

  Lemma eval_node_reveal_node_at_least : forall n v, eval_node n v ->
    forall f e, reveal_node_at_least f n = e -> eval e v.
  Proof using Type.
    cbv [reveal_node]; inversion 1; intros; subst.
    econstructor; eauto.
    eapply (proj1 (Forall2_map_l _ _ _)) in H0; eapply Forall2_map_l.
    eapply Forall2_weaken; try eassumption; []; cbv beta; intros.
    eapply eval_reveal_at_least; eauto.
  Qed.
End WithDag.

Definition merge_node {descr : description} (n : node idx) : dag.M idx
  := dag.merge_node n.

Fixpoint merge {descr : description} (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let idxs := if commutative op
                then N.sort (fst idxs_d)
                else (fst idxs_d) in
    merge_node (op, idxs) (snd idxs_d)
  end.

Lemma node_beq_sound e x : node_beq N.eqb e x = true -> e = x.
Proof using Type.
  eapply Prod.internal_prod_dec_bl.
  { intros X Y; destruct (op_beq_spec X Y); congruence. }
  { intros X Y. eapply ListUtil.internal_list_dec_bl, N.eqb_eq. }
Qed.

Lemma eval_weaken_merge_node G d {dok : dag.ok d} {descr:description} x e n : eval G d e n -> eval G (snd (dag.merge_node x d)) e n.
Proof using Type.
  induction 1; subst; econstructor; eauto.
  { erewrite dag.lookup_merge_node by assumption.
    match goal with H : _ |- _ => rewrite H end; reflexivity. }
  all : eapply Forall2_weaken; [|eassumption].
  { intuition eauto. eapply H2. }
  { intuition eauto. eapply H1. }
Qed.

Lemma eval_weaken_symbols G1 G2 d e n
  (H : forall s v, G1 s = Some v -> G2 s = Some v)
  : eval G1 d e n -> eval G2 d e n.
Proof using Type.
  induction 1; subst; econstructor;
    intuition eauto using interp_op_weaken_symbols.
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
Qed.

Lemma eval_eval0 d e n G : eval (fun _ => None) d e n -> eval G d e n.
Proof using Type. eapply eval_weaken_symbols; congruence. Qed.

Lemma permute_commutative G op args n : commutative op = true ->
  interp_op G op args = Some n ->
  forall args', Permutation.Permutation args args' ->
  interp_op G op args' = Some n.
Proof using Type.
  destruct op; inversion 1; cbn; intros ? ? Hp;
    try (erewrite <- Z.fold_right_Proper_Permutation_add; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_mul; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_land; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lor; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lxor; eauto).
  { erewrite <-(Z.fold_right_Proper_Permutation_add _ _ eq_refl _ (map _ args'));
      eauto using Permutation.Permutation_map. }
Qed.

(* the gensym state cannot map anything past the end of the dag *)
Definition gensym_ok (G : symbol -> option Z) (d : dag) := forall s _v, G s = Some _v -> (s < dag.size d)%N.
Definition dag_ok G (d : dag) := dag.ok d /\ dag.all_nodes_ok d /\ forall i r, dag.lookup d i = Some r -> exists v, eval G d (ExprRef i) v.
Definition gensym_dag_ok G d := gensym_ok G d /\ dag_ok G d.

Lemma gensym_ok_size_Proper G d1 d2
      (H : (dag.size d1 <= dag.size d2)%N)
  : gensym_ok G d1 -> gensym_ok G d2.
Proof using Type. cbv [gensym_ok]; intros; specialize_under_binders_by eassumption; lia. Qed.

Lemma gensym_ok_merge_node G d {descr:description} n
  : gensym_ok G d -> gensym_ok G (snd (dag.merge_node n d)).
Proof using Type. apply gensym_ok_size_Proper, dag.size_merge_node_le. Qed.

Lemma empty_gensym_dag_ok : gensym_dag_ok (fun _ => None) dag.empty.
Proof using Type.
  cbv [gensym_dag_ok dag_ok gensym_ok].
  repeat match goal with |- _ /\ _ => split end; try exact _; intros *;
    rewrite ?dag.lookup_empty; try congruence.
Qed.

Lemma eval_merge_node {descr descr' descr'' descr'''} :
  forall G d, gensym_dag_ok G d ->
  forall op args n, let e := (op, args) in
  eval G d (ExprApp (op, List.map ExprRef args)) n ->
  eval G (snd (@merge_node descr e d)) (ExprRef (fst (@merge_node descr' e d))) n /\
  gensym_dag_ok G (snd (@merge_node descr'' e d)) /\
  forall i e', eval G d i e' -> eval G (snd (@merge_node descr''' e d)) i e'.
Proof using Type.
  intros.
  cbv beta delta [merge_node].
  inversion H0; subst.
  cbv [gensym_dag_ok dag_ok] in *; destruct_head'_and.
  assert (Hnok : node_ok (dag.size d) e).
  { subst e; cbv [node_ok]; split; intros; inversion_pair; subst; cbn [interp_op snd] in *.
    all: break_innermost_match_hyps; inversion_option; subst.
    all: cbv [gensym_ok] in *.
    all: specialize_under_binders_by eassumption; try lia.
    cbv [node_args_ok node_arg_ok].
    match goal with
    | [ H : forall s v, ?G s = Some v -> (s < dag.size ?d)%N,
          H' : Forall2 (eval ?G ?d) (map ExprRef ?args) ?args',
          H'' : dag.ok ?d
          |- Forall _ ?args ]
      => clear -H H' H''; revert args' H'; induction args;
         inversion 1; subst; constructor; eauto
    end.
    inversion_one_head' @eval.
    eapply dag.lookup_value_size; eauto. }
  repeat match goal with |- _ /\ _ => split end; try exact _.
  1: econstructor; try eassumption.
  all: eauto using Forall2_weaken, eval_weaken_merge_node.
  all: try now apply gensym_ok_merge_node.
  { now rewrite dag.lookup_merge_node' by assumption. }
  { apply @dag.merge_node_ok; try assumption.
    apply Hnok. }
  { intros *; rewrite dag.lookup_merge_node by assumption.
    break_innermost_match; inversion 1; subst; specialize_under_binders_by eassumption; destruct_head'_ex.
    all: eauto using eval_weaken_merge_node.
    reflect_hyps; destruct_head'_and; subst.
    lazymatch goal with
    | [ |- context[snd (@dag.merge_node ?descr ?e ?d)] ]
      => replace (dag.size d) with (fst (@dag.merge_node descr e d))
        by (rewrite dag.fst_merge_node; break_innermost_match; congruence)
    end.
    eexists; econstructor;
      [ rewrite dag.lookup_merge_node' by assumption; reflexivity
      | eauto using Forall2_weaken, eval_weaken_merge_node .. ]. }
Qed.

Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Global Set Default Goal Selector "1".

Lemma eval_merge {descr:description} G :
  forall e n,
  forall d, gensym_dag_ok G d ->
  eval G d e n ->
  eval G (snd (merge e d)) (ExprRef (fst (merge e d))) n /\
  gensym_dag_ok G (snd (merge e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge e d)) i e'.
Proof using Type.
  induction e; intros; eauto; [].
  rename n0 into v.

  set (merge _ _) as m; cbv beta iota delta [merge] in m; fold @merge in m.
  destruct n as (op&args).
  repeat match goal with
    m := let x := ?A in @?B x |- _ =>
    let y := fresh x in
    set A as y;
    let m' := eval cbv beta in (B y) in
    change m' in (value of m)
  end.

  inversion H1; clear H1 ; subst.

  cbn [fst snd] in *.
  assert (gensym_dag_ok G (snd idxs_d) /\
    Forall2 (fun i v => eval G (snd idxs_d) (ExprRef i) v) (fst idxs_d) args' /\
    forall i e', eval G d i e' -> eval G (snd idxs_d) i e'
  ) as HH; [|destruct HH as(?&?&?)].
  { clear m idxs H6 v op; revert dependent d; revert dependent args'.
    induction H; cbn; intros; inversion H4; subst;
      split_and; pose proof @Forall2_weaken; typeclasses eauto 8 with core. }
  clearbody idxs_d.

  enough (eval G (snd idxs_d) (ExprApp (op, map ExprRef idxs)) v) by
    (unshelve (let lem := open_constr:(eval_merge_node _ _ ltac:(eassumption) op idxs v) in
               edestruct lem as (?&?&?)); eauto); clear m.

  pose proof length_Forall2 H4; pose proof length_Forall2 H2.

  cbn [fst snd] in *; destruct (commutative op) eqn:?; cycle 1; subst idxs.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [].
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try congruence; [].
    rewrite ListUtil.map_nth_default_always. eapply H8. }

  pose proof N.Sort.Permuted_sort (fst idxs_d) as Hperm.
  eapply (Permutation.Permutation_Forall2 Hperm) in H2.
  case H2 as (argExprs&Hperm'&H2).
  eapply permute_commutative in H6; try eassumption; [].
  epose proof Permutation.Permutation_length Hperm.
  epose proof Permutation.Permutation_length Hperm'.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try trivial; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    rewrite ListUtil.map_nth_default_always. eapply H10. }
  Unshelve. all : constructor.
Qed.

Definition zconst s (z:Z) := const (Z.land z (Z.ones (Z.of_N s)))%Z.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Fixpoint interp_expr (e : expr) : option Z :=
    match e with
    | ExprApp (o, arges) =>
        args <- Option.List.lift (List.map interp_expr arges);
        interp_op ctx o args
    | _ => None
    end%option.
End WithContext.
Definition interp0_expr := interp_expr (fun _ => None).

Lemma eval_interp_expr G e : forall d v, interp_expr G e = Some v -> eval G d e v.
Proof using Type.
  induction e; cbn; try discriminate; intros.
  case n in *; cbn [fst snd] in *.
  destruct (Option.List.lift _) eqn:? in *; try discriminate.
  econstructor; try eassumption; [].
  clear dependent v.
  revert dependent l0.
  induction H; cbn in *.
  { inversion 1; subst; eauto. }
  destruct (interp_expr _) eqn:? in *; cbn in *; try discriminate; [].
  destruct (fold_right _ _ _) eqn:? in *; cbn in *; try discriminate; [].
  specialize (fun d => H d _ eq_refl).
  inversion 1; subst.
  econstructor; trivial; [].
  eapply IHForall; eassumption.
Qed.

Lemma eval_interp0_expr e v (H : interp0_expr e = Some v) : forall G d, eval G d e v.
Proof using Type.
  cbv [interp0_expr]; intros.
  eapply eval_interp_expr, eval_weaken_symbols in H; [eassumption|congruence].
Qed.

Section bound_expr_via_PHOAS.
  Import Crypto.Util.ZRange.
  Import API.Compilers.
  Import AbstractInterpretation.ZRange.Compilers.
  Import AbstractInterpretation.ZRangeProofs.Compilers.

  Local Notation interp_PHOAS_op := (ZRange.ident.option.interp true).

  Fixpoint bound_expr_via_PHOAS (d : dag) (e : Symbolic.expr) : option zrange
    := match e with
       | ExprApp (o, args)
         => match op_to_PHOAS_bounds o with
            | Some o
              => o (List.map (fun e 'tt => bound_expr_via_PHOAS d e) args)
            | None => None
            end
       | ExprRef i => dag.lookup_bounds d i
       end.

  Local Coercion is_true : bool >-> Sortclass.

  Fixpoint eval_bound_expr_via_PHOAS' G d (Hok : gensym_dag_ok G d) e b
           (H_dag : forall i b, dag.lookup_bounds d i = Some b -> forall v, eval G d (ExprRef i) v -> is_bounded_by_bool v b = true)
           {struct e}
    : bound_expr_via_PHOAS d e = Some b ->
      forall v, eval G d e v -> is_bounded_by_bool v b = true.
  Proof using Type.
    intros H v.
    assert (dag.ok d) by apply Hok.
    specialize (fun e v b H H_dag => eval_bound_expr_via_PHOAS' G d Hok e b H_dag H v).
    destruct e as [?|[n args] ]; cbn [bound_expr_via_PHOAS] in *.
    { clear eval_bound_expr_via_PHOAS'; intros; inversion_option; eauto. }
    let P := lazymatch type of eval_bound_expr_via_PHOAS' with forall e v, @?P e v => P end in
    assert (eval_bound_expr_via_PHOAS'_Forall : forall args', List.length args = List.length args' -> Forall2 P args args').
    { clear -eval_bound_expr_via_PHOAS'.
      induction args as [|arg args IH], args'; cbn [List.length];
        first [ constructor; try apply IH | clear; intro; exfalso; congruence ].
      { apply eval_bound_expr_via_PHOAS'. }
      { clear eval_bound_expr_via_PHOAS'; congruence. } }
    clear eval_bound_expr_via_PHOAS'.
    break_innermost_match_hyps; inversion_option.
    inversion 1; subst.
    eapply (@interp_op_op_to_PHOAS_bounds G n); try (eassumption || reflexivity).
    rewrite !Forall2_map_r_iff.
    eassert (H' : List.length _ = List.length _) by (eapply eq_length_Forall2; eassumption).
    specialize (eval_bound_expr_via_PHOAS'_Forall _ H').
    rewrite !Forall2_forall_iff_nth_error.
    intro i;
      repeat match goal with
             | [ H : Forall2 _ _ _ |- _ ] => rewrite Forall2_forall_iff_nth_error in H; specialize (H i)
             | [ H : Forall _ _ |- _ ] => rewrite Forall_forall_iff_nth_error in H; specialize (H i)
             end.
    cbv [option_eq] in *.
    break_innermost_match; break_innermost_match_hyps; inversion_option; auto; tauto.
  Qed.

  Lemma eval_bound_expr_via_PHOAS_dag G d (Hok : gensym_dag_ok G d)
    : forall i b, dag.lookup_bounds d i = Some b -> forall v, eval G d (ExprRef i) v -> is_bounded_by_bool v b = true.
  Proof.
    assert (dag.ok d) by apply Hok.
    assert (dag.all_nodes_ok d) by apply Hok.
    intro i; rewrite dag.lookup_bounds_lookup by apply Hok.
    intros b H' v He.
    inversion_one_head' @eval.
    repeat lazymatch goal with H : _ |- _ => tryif constr_eq H i then fail else revert H end.
    set (k := dag.lookup _ _) in *.
    revert k.
    let P := match goal with |- let k := _ in @?P k => P end in
    apply (dag.lookup_ind d P); intros; inversion_option; inversion_pair; subst.
    eapply interp_op_bound_node_idx_via_PHOAS; try eassumption; [].
    eapply Forall_impl; [ | eassumption ]; cbv beta; intros *.
    rewrite dag.lookup_bounds_lookup by assumption.
    destruct_head'_ex; destruct_head'_and.
    break_innermost_match; intros; inversion_option.
    inversion_one_head' @eval.
    match goal with
    | [ H : ?x = Some _, H' : ?x = _ |- _ ] => rewrite H in H'
    end.
    inversion_option; subst.
    eauto.
  Qed.

  Lemma eval_bound_expr_via_PHOAS G d (Hok : gensym_dag_ok G d) e b
    : bound_expr_via_PHOAS d e = Some b ->
      forall v, eval G d e v -> is_bounded_by_bool v b = true.
  Proof using Type.
    eauto using eval_bound_expr_via_PHOAS', eval_bound_expr_via_PHOAS_dag.
  Qed.
End bound_expr_via_PHOAS.

Notation bound_expr := bound_expr_via_PHOAS.
Lemma eval_bound_expr G d e b : bound_expr d e = Some b ->
  forall v, gensym_dag_ok G d -> eval G d e v -> (ZRange.lower b <= v <= ZRange.upper b)%Z.
Proof using Type.
  intros H v Hok He.
  eapply eval_bound_expr_via_PHOAS in He; [ | eassumption .. ].
  reflect_hyps; lia.
Qed.

Import coqutil.Tactics.Tactics.
Ltac t:= match goal with
  | _ => progress intros
  | H : eval _ _ (ExprApp _) _ |- _ => inversion H; clear H; subst
  | H : Forall _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : _ = true |- _ => autoforward with typeclass_instances in H
  | H : forall b, _ |- _ => pose proof (H _ ltac:(eassumption) _ _ ltac:(eassumption)); clear H
  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | _ => progress cbv [interp_op] in *
  | _ => progress cbn [fst snd] in *
  | _ => progress destruct_one_match
  | _ => progress Option.inversion_option
  | _ => progress subst
  end.

Lemma bound_sum' G d
  es (He : Forall (fun e => forall b, bound_expr d e = Some b ->
       forall (v : Z), eval G d e v -> (ZRange.lower b <= v <= ZRange.upper b)%Z) es)
  : forall
  bs (Hb : Option.List.lift (map (bound_expr d) es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  , (fold_right Z.add 0 (List.map ZRange.lower bs) <= fold_right Z.add 0 vs <= fold_right Z.add 0 (List.map ZRange.upper bs))%Z.
Proof using Type.
  induction He; cbn in *; repeat t; cbn in *; [ lia | ].
  destruct (bound_expr _) eqn:? in *; cbn in *; repeat t.
  destruct (fold_right (B:=option _) _) eqn:? in *; cbn in *; repeat t; cbn in *.
  specialize (IHHe _ ltac:(eassumption) _ ltac:(eassumption)); cbn.
  specialize (H _ ltac:(exact eq_refl) _ ltac:(eassumption)).
  Lia.lia.
Qed.

Import Crypto.Util.ZRange.

Lemma bound_sum G d es
  (Hok : gensym_dag_ok G d)
  bs (Hb : Option.List.lift (map (bound_expr d) es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  : (fold_right Z.add 0 (List.map ZRange.lower bs) <= fold_right Z.add 0 vs <= fold_right Z.add 0 (List.map ZRange.upper bs))%Z.
Proof using Type.
  eapply bound_sum' in Hb; eauto.
  eapply Forall_forall; intros.
  eapply eval_bound_expr; eauto.
Qed.

Definition isCst (e : expr) :=
  match e with ExprApp ((const _), []) => true | _ => false end.

Module Rewrite.
Class Ok r := rwok : forall G d e v, gensym_dag_ok G d -> eval G d e v -> eval G d (r d e) v.
Class description_of (r : dag -> expr -> expr) := describe : string.
#[global] Bind Scope string_scope with description_of.
#[global] Typeclasses Opaque description_of.
Ltac resolve_match_using_hyp :=
  match goal with |- context[match ?x with _ => _ end] =>
  match goal with H : x = ?v |- _ =>
      let h := Head.head v in
      is_constructor h;
      rewrite H
  end end.

Create HintDb step_db discriminated.

Ltac step := match goal with
  | |- Ok ?r => cbv [Ok r]; intros
  | _ => solve [trivial | contradiction]
  |  _ => resolve_match_using_hyp
  | _ => inversion_option_step

  | H : _ = ?v |- _ => is_var v; progress subst v
  | H : ?v = _ |- _ => is_var v; progress subst v

  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | |- eval _ ?d ?e ?v =>
      match goal with
        H : eval _ d e ?v' |- _ =>
            let Heq := fresh in
            enough (Heq : v = v') by (rewrite Heq; exact H);
            try (clear H; clear e)
      end

  | H: interp_op _ (const _) nil = Some _ |- _ => inversion H; clear H; subst
  | H: interp0_op _ _ = Some _ |- _ => eapply interp_op_interp0_op in H
  | H: interp0_expr _ = Some _ |- _ => eapply eval_interp0_expr in H
  | H: bound_expr _ _ = Some _ |- _ => eapply eval_bound_expr in H; eauto; [ ]

  | H : (?x <=? ?y)%N = ?b |- _ => is_constructor b; destruct (N.leb_spec x y); (inversion H || clear H)
  | H : andb _ _ = true |- _ => eapply Bool.andb_prop in H; case H as (?&?)
  | H : N.eqb ?n _ = true |- _ => eapply N.eqb_eq in H; try subst n
  | H : Z.eqb ?n _ = true |- _ => eapply Z.eqb_eq in H; try subst n
  | H : expr_beq ?a ?b = true |- _ => replace a with b in * by (symmetry;exact (expr_beq_true a b H)); clear H
  | _ => progress destruct_one_match_hyp
  | _ => progress destruct_one_match

  | H : eval _ _ ?e _ |- _ => assert_fails (is_var e); inversion H; clear H; subst
  | H : Forall2 (eval _ _) (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 (eval _ _) _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst

  | _ => progress cbn [fst snd map option_map] in *
  | _ => progress cbn [ZRange.lower ZRange.upper invert_Some op_to_Z_binop identity] in *
  | _ => progress autorewrite with zsimplify_const step_db
  end.

Ltac Econstructor :=
  match goal with
  | |- Forall2 (eval _ _) _ _ =>  econstructor
  | |- eval _ _ ?e _ => econstructor
  end.

Ltac t := repeat (step || Econstructor || eauto || (progress cbn [interp0_op interp_op] in * ) ).

#[local] Hint Rewrite Z.fold_right_land_ones_id : step_db.

Definition slice0 (d : dag) :=
  fun e => match e with
    ExprApp (slice 0 s, [(ExprApp ((addZ|mulZ|negZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args))]) =>
        ExprApp ((match o with addZ=>add s|mulZ=>mul s|negZ=>neg s|shlZ=>shl s|shrZ => shr s|andZ => and s| orZ => or s|xorZ => xor s |_=>old 0%N 999999%N end), args)
      | _ => e end.
#[local] Instance describe_slice0 : description_of Rewrite.slice0
  := "Merges (slice 0 s) into addZ,mulZ,negZ,shlZ,shrZ,andZ,orZ,xorZ".
Global Instance slice0_ok : Ok slice0. Proof using Type. t. Qed.

Definition slice01_addcarryZ (d : dag) :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (addcarryZ s, args))]) =>
        ExprApp (addcarry s, args)
      | _ => e end.
#[local] Instance describe_slice01_addcarryZ : description_of Rewrite.slice01_addcarryZ
  := "Merges (slice 0 1) into addcarryZ".
Global Instance slice01_addcarryZ_ok : Ok slice01_addcarryZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice01_subborrowZ (d : dag) :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (subborrowZ s, args))]) =>
        ExprApp (subborrow s, args)
      | _ => e end.
#[local] Instance describe_slice01_subborrowZ : description_of Rewrite.slice01_subborrowZ
  := "Merges (slice 0 1) into subborrowZ".
Global Instance slice01_subborrowZ_ok : Ok slice01_subborrowZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice_set_slice (d : dag) :=
  fun e => match e with
    ExprApp (slice 0 s1, [ExprApp (set_slice 0 s2, [_; e'])]) =>
      if N.leb s1 s2 then ExprApp (slice 0 s1, [e']) else e | _ => e end.
#[local] Instance describe_slice_set_slice : description_of Rewrite.slice_set_slice
  := "Simplifies slice applied to set_slice".
Global Instance slice_set_slice_ok : Ok slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice_set_slice (d : dag) :=
  fun e => match e with
    ExprApp (set_slice lo1 s1, [ExprApp (set_slice lo2 s2, [x; e']); y]) =>
      if andb (N.eqb lo1 lo2) (N.leb s2 s1) then ExprApp (set_slice lo1 s1, [x; y]) else e | _ => e end.
#[local] Instance describe_set_slice_set_slice : description_of Rewrite.set_slice_set_slice
  := "Simplifies set_slice applied to set_slice".
Global Instance set_slice_set_slice_ok : Ok set_slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice0_small (d : dag) :=
  fun e => match e with
    ExprApp (set_slice 0 s, [x; y]) =>
      match bound_expr d x, bound_expr d y with Some a, Some b =>
      if Z.leb 0 (ZRange.lower a) && Z.leb 0 (ZRange.lower b) && Z.leb (ZRange.upper a) (Z.ones (Z.of_N s)) && Z.leb (ZRange.upper b) (Z.ones (Z.of_N s)) then y
      else e | _, _ => e end | _ => e end%bool.
#[local] Instance describe_set_slice0_small : description_of Rewrite.set_slice0_small
  := "Simplifies set_slice when the slice being set fully overwrites the original".
Global Instance set_slice0_small_ok : Ok set_slice0_small.
Proof using Type.
  t.
  destruct_head'_and.
  rewrite Z.ones_equiv, <- Z.lt_le_pred in * |- .
  assert ((0 <= y < 2^Z.of_N sz)%Z) by lia; clear dependent z.
  assert ((0 <= y0 < 2^Z.of_N sz)%Z) by lia; clear dependent z0.
  rewrite ?Z.shiftl_0_r, Z.land_ones, Z.mod_small by lia.
  destruct (Z.eq_dec y 0); subst.
  { rewrite Z.ldiff_0_l, Z.lor_0_r; trivial. }
  rewrite Z.ldiff_ones_r_low, Z.lor_0_r; try Lia.lia.
  eapply Z.log2_lt_pow2; Lia.lia.
Qed.

Definition truncate_small (d : dag) :=
  fun e => match e with
    ExprApp (slice 0%N s, [e']) =>
      match bound_expr d e' with Some b =>
      if Z.leb 0 (ZRange.lower b) && Z.leb (ZRange.upper b) (Z.ones (Z.of_N s))
      then e'
      else e | _ => e end | _ => e end.
#[local] Instance describe_truncate_small : description_of Rewrite.truncate_small
  := "Simplifies slice when it's a no-op".
Global Instance truncate_small_ok : Ok truncate_small. Proof using Type. t; []. cbn in *; eapply Z.land_ones_low_alt_ones; eauto. lia. Qed.

Definition addcarry_bit (d : dag) :=
  fun e => match e with
    ExprApp (addcarry s, ([ExprApp (const a, nil);b])) =>
      if option_beq zrange_beq (bound_expr d b) (Some r[0~>1]%zrange) then
      match interp0_op (addcarry s) [a; 0], interp0_op (addcarry s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
#[local] Instance describe_addcarry_bit : description_of Rewrite.addcarry_bit
  := "Simplifies (addcarry s, [const a; b]) when b is known to be a single bit".
Global Instance addcarry_bit_ok : Ok addcarry_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    reflect_hyps; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addoverflow_bit (d : dag) :=
  fun e => match e with
    ExprApp (addoverflow s, ([ExprApp (const a, nil);b])) =>
      if option_beq zrange_beq (bound_expr d b) (Some r[0~>1]%zrange) then
      match interp0_op (addoverflow s) [a; 0] , interp0_op (addoverflow s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
#[local] Instance describe_addoverflow_bit : description_of Rewrite.addoverflow_bit
  := "Simplifies (addoverflow s, [const a; b]) when b is known to be a single bit".
Global Instance addoverflow_bit_ok : Ok addoverflow_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    reflect_hyps; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addbyte_small (d : dag) :=
  fun e => match e with
    ExprApp (add (8%N as s), args) =>
      match Option.List.lift (List.map (bound_expr d) args) with
      | Some bounds =>
          if Z.leb 0 (List.fold_right Z.add 0%Z (List.map lower bounds)) && Z.leb (List.fold_right Z.add 0%Z (List.map upper bounds)) (Z.ones (Z.of_N s))
          then ExprApp (add 64%N, args)
          else e | _ => e end | _ =>  e end.
#[local] Instance describe_addbyte_small : description_of Rewrite.addbyte_small
  := "Replaces (add 8, args) with (add 64, args) when doing so doesn't change semantics".
Global Instance addbyte_small_ok : Ok addbyte_small.
Proof using Type.
  t; f_equal.
  let H := match goal with H : Forall2 (eval _ _) _ _ |- _ => H end in
  eapply bound_sum in H; eauto.
  rewrite Z.ones_equiv in * |- ; rewrite !Z.land_ones, !Z.mod_small; try lia;
    replace (Z.of_N 8) with 8 in * by (vm_compute; reflexivity);
    replace (Z.of_N 64) with 64 in * by (vm_compute; reflexivity); lia.
Qed.

Definition addcarry_small (d : dag) :=
  fun e => match e with
    ExprApp (addcarry s, args) =>
      match Option.List.lift (List.map (bound_expr d) args) with
      | Some bounds =>
          if Z.leb 0 (List.fold_right Z.add 0%Z (List.map lower bounds)) && Z.leb (List.fold_right Z.add 0%Z (List.map upper bounds)) (Z.ones (Z.of_N s))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
#[local] Instance describe_addcarry_small : description_of Rewrite.addcarry_small
  := "Replaces (addcarry _, args) with 0 when bounds analysis can prove there's no carry".
Global Instance addcarry_small_ok : Ok addcarry_small.
Proof using Type.
  t; f_equal.
  let H := match goal with H : Forall2 (eval _ _) _ _ |- _ => H end in
  eapply bound_sum in H; eauto.
  rewrite Z.ones_equiv in * |- ; rewrite Z.shiftr_div_pow2, Z.div_small; cbn; lia.
Qed.

Lemma signed_small s v (Hv : (0 <= v <= Z.ones (Z.of_N s-1))%Z) : signed s v = v.
Proof using Type.
  destruct (N.eq_dec s 0); subst; cbv [signed].
  { rewrite Z.land_0_r. cbn in *; Lia.lia. }
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.ones_equiv in Hv.
  rewrite Z.mod_small; try ring.
  enough (2 ^ Z.of_N s = 2 ^ (Z.of_N s - 1) + 2 ^ (Z.of_N s - 1))%Z; try Lia.lia.
  replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia.
  rewrite Z.pow_add_r; try Lia.lia.
Qed.

Definition addoverflow_small (d : dag) :=
  fun e => match e with
    ExprApp (addoverflow s, ([_]|[_;_]|[_;_;_]) as args) =>
      match Option.List.lift (List.map (bound_expr d) args) with
      | Some bounds =>
          if List.forallb (Z.leb 0) (List.map lower bounds) && Z.leb (List.fold_right Z.add 0%Z (List.map upper bounds)) (Z.ones (Z.of_N s-1))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
#[local] Instance describe_addoverflow_small : description_of Rewrite.addoverflow_small
  := "Replaces (addoverflow _, args) when there are at most 3 args and when bounds analysis can prove there's no overflow".
Global Instance addoverflow_small_ok : Ok addoverflow_small.
Proof using Type.
  t; cbv [Option.List.lift Crypto.Util.Option.bind fold_right map List.forallb] in *;
  BreakMatch.break_match_hyps; Option.inversion_option; t;
    epose proof Z.ones_equiv (Z.of_N s -1);
    destruct_head'_and; reflect_hyps; destruct_head'_and.
  all : rewrite Z.land_ones, !Z.mod_small, !signed_small, !Z.eqb_refl; trivial.
  all : try split; try Lia.lia.
  all : replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia;
  rewrite Z.pow_add_r; try Lia.lia.
  all : destruct s; cbn in * |- ; lia.
Qed.

Definition constprop (d : dag) :=
  fun e => match interp0_expr e with
           | Some v => ExprApp (const v, nil)
           | _ => e end.
#[local] Instance describe_constprop : description_of Rewrite.constprop
  := "Performs constant propagation, evaluating expressions that are known to be constant".
Global Instance constprop_ok : Ok constprop.
Proof using Type. t. f_equal; eauto using eval_eval. Qed.

(* convert unary operations to slice *)
Definition unary_truncate (d : dag) :=
  fun e => match e with
    ExprApp (o, [x]) =>
    match unary_truncate_size o with
    | Some (-1)%Z => x
    | Some 0%Z => ExprApp (const 0, nil)
    | Some (Zpos p)
      => ExprApp (slice 0%N (Npos p), [x])
    | _ => e end | _ => e end.
#[local] Instance describe_unary_truncate : description_of Rewrite.unary_truncate
  := "Some operations are equivalent to truncation when applied to only one argument; this pass canonicalizes such expressions".
Global Instance unary_truncate_ok : Ok unary_truncate.
Proof using Type.
  t.
  all: repeat first [ progress cbv [unary_truncate_size] in *
                    | progress cbn [fold_right Z.of_N] in *
                    | progress change (Z.of_N 0) with 0 in *
                    | progress change (Z.ones 0) with 0 in *
                    | apply (f_equal (@Some _))
                    | lia
                    | progress autorewrite with zsimplify_const
                    | progress break_innermost_match_hyps
                    | match goal with
                      | [ H : Z.of_N ?s = 0 |- _ ] => is_var s; destruct s; try lia
                      | [ H : Z.of_N ?s = Z.pos _ |- _ ] => is_var s; destruct s; try lia
                      | [ H : Z.pos _ = Z.pos _ |- _ ] => inversion H; clear H
                      end
                    | progress t ].
Qed.

Lemma fold_right_filter_identity_gen A B C f init F G xs
      (Hid : forall x y, F x = false -> G (f x y) = G y)
      (HProper : forall x y y', G y = G y' -> G (f x y) = G (f x y'))
  : G (@fold_right A B f init (filter F xs)) = G (@fold_right A B f init xs) :> C.
Proof.
  induction xs as [|x xs IH]; [ | specialize (Hid x) ]; cbn; break_innermost_match; cbn; rewrite ?Hid by auto; auto; congruence.
Qed.

Lemma fold_right_filter_identity A B f init F xs
      (Hid : forall x y, F x = false -> f x y = y)
  : @fold_right A B f init (filter F xs) = @fold_right A B f init xs.
Proof.
  apply fold_right_filter_identity_gen with (G:=id); cbv [id]; intuition (subst; eauto).
Qed.

Lemma signed_0 s : signed s 0 = 0%Z.
Proof using Type.
  destruct (N.eq_dec s 0); subst; trivial.
  cbv [signed].
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.mod_small; try ring.
  split; try (eapply Z.pow_lt_mono_r; Lia.lia).
  eapply Z.pow_nonneg; Lia.lia.
Qed.
#[global]
Hint Rewrite signed_0 : zsimplify_const zsimplify zsimplify_fast.
Global Hint Resolve signed_0 : zarith.

Lemma interp_op_drop_identity o id : identity o = Some id ->
  forall G xs, interp_op G o xs = interp_op G o (List.filter (fun v => negb (Z.eqb v id)) xs).
Proof using Type.
  destruct o; cbn [identity invert_Some op_to_Z_binop]; intro; inversion_option; subst; intros G xs; cbn [interp_op identity invert_Some op_to_Z_binop]; f_equal.
  all: break_innermost_match_hyps; break_innermost_match; inversion_option; subst.
  all: rewrite ?fold_right_map.
  all: rewrite ?fold_right_filter_identity by now intros; reflect_hyps; subst; auto with zarith; autorewrite with zsimplify_const; lia.
  all: repeat first [ reflexivity
                    | progress autorewrite with zsimplify_const ].
  { (idtac + symmetry); apply fold_right_filter_identity_gen with (G:=fun x => Z.land x _).
    all: intros; reflect_hyps; subst.
    all: rewrite <- ?Z.land_assoc, ?(Z.land_comm (Z.ones _)), ?Z.land_ones in * by lia.
    all: push_Zmod; pull_Zmod.
    all: congruence. }
Qed.

Lemma interp_op_drop_identity_after_0 o id : identity_after_0 o = Some id ->
  forall G x xs, interp_op G o (x :: xs) = interp_op G o (x :: List.filter (fun v => negb (Z.eqb v id)) xs).
Proof using Type.
  destruct o; cbn [identity_after_0]; intro; inversion_option; subst; intros G x xs; cbn [interp_op]; f_equal.
  all: rewrite ?fold_right_map.
  all: rewrite ?fold_right_filter_identity by now intros; reflect_hyps; subst; auto with zarith; autorewrite with zsimplify_const; lia.
  all: repeat first [ reflexivity
                    | progress autorewrite with zsimplify_const ].
Qed.

Lemma interp_op_nil_is_identity o i (Hi : identity o = Some i)
  G : interp_op G o [] = Some i.
Proof using Type.
  destruct o; cbn [identity invert_Some op_to_Z_binop] in *; break_innermost_match_hyps; inversion_option; subst; cbn [interp_op fold_right identity invert_Some op_to_Z_binop]; f_equal.
  all: cbn [interp_op fold_right]; autorewrite with zsimplify_const; try reflexivity.
  { cbn [identity]; break_innermost_match; try reflexivity.
    rewrite Z.land_ones by lia; Z.rewrite_mod_small; try reflexivity;
      (* compat with older versions of Coq (needed for 8.11, not for 8.13) *)
      rewrite Z.mod_small; rewrite ?Z.log2_lt_pow2; cbn [Z.log2]; try lia. }
  { change 1 with (Z.ones 1).
    Z.bitblast. }
Qed.

Lemma interp_op_always_interps G o args
  : op_always_interps o = true -> interp_op G o args <> None.
Proof. destruct o; cbn; congruence. Qed.

Lemma interp0_op_always_interps o args
  : op_always_interps o = true -> interp0_op o args <> None.
Proof. apply interp_op_always_interps. Qed.

(* completeness check, just update the definition if this doesn't go through *)
Lemma interp_op_always_interps_complete o
  : op_always_interps o = false -> exists G args, interp_op G o args = None.
Proof.
  destruct o; cbn; try solve [ inversion 1 ]; intros _; do 2 try eapply ex_intro.
  all: repeat match goal with
              | [ |- match ?ev with [] => None | _ => _ end = None ] => let __ := open_constr:(eq_refl : ev = []) in cbv beta iota
              | [ |- match ?ev with _ :: _ => None | _ => _ end = None ] => let __ := open_constr:(eq_refl : ev = _ :: _) in cbv beta iota
              | [ |- None = None ] => reflexivity
              end.
  Unshelve. all: shelve_unifiable.
  all: lazymatch goal with
       | [ |- Z ] => exact 0%Z
       | [ |- _ -> option _ ] => intro; exact None
       | [ |- list _ ] => exact nil
       | _ => idtac
       end.
  all: fail_if_goals_remain ().
Qed.

Lemma invert_interp_op_associative o : associative o = true ->
  forall G x xs v, interp_op G o (x :: xs) = Some v ->
  exists v', interp_op G o xs = Some v' /\
  interp_op G o [x; v'] = Some v.
Proof using Type.
  destruct o; inversion 1; intros * HH; inversion HH; clear HH; subst; cbn;
    eexists; split; eauto; f_equal; break_innermost_match; try ring; try solve [Z.bitblast].
  { rewrite !Z.add_0_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
  { rewrite !Z.mul_1_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
Qed.

(** TODO: plausibly we want to define all associative operations in terms of some [make_associative_op] definition, so that we can separate out the binary operation reasoning from the fold and option reasoning *)
(* is it okay for associative to imply identity? *)
Lemma interp_op_associative_spec_fold o : associative o = true ->
  forall G xs, interp_op G o xs = fold_right (fun v acc => acc <- acc; interp_op G o [v; acc])%option (interp_op G o []) xs.
Proof using Type.
  intros H G; induction xs as [|x xs IHxs]; cbn [fold_right]; [ reflexivity | ].
  rewrite <- IHxs; clear IHxs.
  destruct o; inversion H; cbn [interp_op Crypto.Util.Option.bind fold_right identity invert_Some op_to_Z_binop]; break_innermost_match; f_equal.
  all: autorewrite with zsimplify_const.
  all: try solve [ Z.bitblast ].
  all: try solve [ rewrite ?Z.land_ones in *; push_Zmod; pull_Zmod; Lia.lia ].
Qed.

Lemma interp_op_associative_spec_id o : associative o = true ->
  forall G, interp_op G o [] = identity o.
Proof using Type.
  intros H G.
  pose proof (fun id H => interp_op_nil_is_identity o id H G) as H1.
  destruct o; inversion H; cbn [identity] in *; break_innermost_match_hyps; erewrite H1; try reflexivity.
Qed.

Lemma interp_op_associative_identity_Some o : associative o = true ->
  forall G xs vxs, interp_op G o xs = Some vxs -> Option.is_Some (identity o) = true.
Proof using Type.
  intros H G xs vxs H1; rewrite <- interp_op_associative_spec_id with (G:=G) by assumption.
  rewrite interp_op_associative_spec_fold in H1 by assumption.
  cbv [Option.is_Some]; break_innermost_match; try reflexivity.
  exfalso.
  clear -H1.
  revert dependent vxs; induction xs as [|?? IH]; cbn in *; intros; inversion_option.
  unfold Crypto.Util.Option.bind at 1 in H1; break_innermost_match_hyps; eauto.
Qed.

Lemma interp_op_associative_spec_assoc o : associative o = true ->
  forall G ys vys, interp_op G o ys = Some vys ->
  forall   zs vzs, interp_op G o zs = Some vzs ->
  forall x, ((xy <- interp_op G o [x; vys]; interp_op G o [xy; vzs]) = (yz <- interp_op G o [vys; vzs]; interp_op G o [x; yz]))%option.
Proof.
  destruct o; inversion 1; intros * H1 * H2; cbn [interp_op fold_right Crypto.Util.Option.bind identity invert_Some op_to_Z_binop] in *.
  all: intros; autorewrite with zsimplify_const; f_equal; inversion_option.
  all: rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod; rewrite <- ?Z.land_ones by lia.
  all: try solve [ f_equal; lia ].
  all: try reflexivity.
  all: try solve [ Z.bitblast ].
  all: try lia.
Qed.

Lemma interp_op_associative_spec_concat o : associative o = true ->
  forall G xs, interp_op G o (List.concat xs) = (vxs <-- List.map (interp_op G o) xs; interp_op G o vxs)%option.
Proof using Type.
  intros H G; induction xs as [|x xs IHxs]; cbn [fold_right]; [ reflexivity | ].
  cbn [List.concat List.map Option.List.bind_list].
  rewrite interp_op_associative_spec_fold, fold_right_app, <- interp_op_associative_spec_fold by assumption.
  rewrite IHxs; clear IHxs.
  setoid_rewrite Option.List.bind_list_cps_id; rewrite <- Option.List.eq_bind_list_lift.
  destruct (Option.List.lift (map (interp_op G o) xs)) as [vxs|]; cbn [Crypto.Util.Option.bind].
  { revert vxs; clear xs.
    induction x as [|x xs IHxs]; intro vxs.
    { cbn [fold_right].
      destruct (interp_op G o []) as [id|] eqn:H'; cbn [Crypto.Util.Option.bind].
      { etransitivity; erewrite interp_op_drop_identity by (erewrite <- interp_op_associative_spec_id; eassumption); [ | reflexivity ].
        cbn [List.filter]; unfold negb at 2; break_innermost_match_step; reflect_hyps; try congruence. }
      { pose proof (interp_op_associative_identity_Some o H G vxs) as H1.
        rewrite interp_op_associative_spec_id in * by assumption.
        rewrite H' in *.
        cbn [Option.is_Some] in *.
        destruct interp_op; try reflexivity; specialize (H1 _ eq_refl); congruence. } }
    { cbn [fold_right].
      rewrite IHxs; clear IHxs.
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      unfold Crypto.Util.Option.bind at 2; break_innermost_match_step; cbn [Crypto.Util.Option.bind]; [ | reflexivity ].
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      symmetry.
      setoid_rewrite interp_op_associative_spec_fold at 2; [ | assumption ].
      cbn [fold_right].
      setoid_rewrite <- interp_op_associative_spec_fold; [ | assumption ].
      destruct (interp_op G o vxs) eqn:?; cbn [Crypto.Util.Option.bind]; [ | cbv [Crypto.Util.Option.bind]; break_match; reflexivity ].
      eapply interp_op_associative_spec_assoc; eassumption. } }
  { etransitivity; [ | cbv [Crypto.Util.Option.bind]; break_innermost_match; reflexivity ].
    induction x as [|? ? IHx]; cbn; rewrite ?IHx; reflexivity. }
Qed.

Lemma interp_op_associative_app_bind G o : associative o = true ->
  forall xs ys,
  interp_op G o (xs ++ ys) = (vxs <- interp_op G o xs; vys <- interp_op G o ys; interp_op G o [vxs; vys])%option.
Proof using Type.
  intros.
  etransitivity; [ etransitivity; [ | refine (interp_op_associative_spec_concat o H G [xs; ys]) ] | ].
  { cbn [concat]; rewrite List.app_nil_r; reflexivity. }
  { cbn [map Option.List.bind_list].
    cbv [Crypto.Util.Option.bind]; break_innermost_match; reflexivity. }
Qed.

Lemma interp_op_associative_app G o : associative o = true ->
  forall xs vxs, interp_op G o xs = Some vxs ->
  forall ys vys, interp_op G o ys = Some vys ->
  interp_op G o (xs ++ ys) = interp_op G o [vxs; vys].
Proof using Type.
  intros H * H1 * H2.
  rewrite interp_op_associative_app_bind, H1, H2 by assumption.
  reflexivity.
Qed.

Lemma interp_op_associative_idempotent G o : associative o = true ->
  forall xs vxs, interp_op G o xs = Some vxs ->
  interp_op G o [vxs] = Some vxs.
Proof using Type.
  intros H xs vxs H1.
  pose proof (interp_op_associative_spec_concat o H G [ xs ]) as H2.
  cbn in H2.
  rewrite List.app_nil_r, H1 in H2; cbn [Crypto.Util.Option.bind] in *; congruence.
Qed.

Lemma interp_op_associative_cons o : associative o = true ->
  forall G x xs ys v,
  interp_op G o xs = Some v -> interp_op G o ys = Some v ->
  interp_op G o (x :: xs) = interp_op G o (x :: ys).
Proof using Type.
  intros H * H1 H2.
  etransitivity; [ etransitivity | ]; [ | refine (interp_op_associative_spec_concat o H _ [ [x]; xs]) | ].
  all: cbn [concat List.app map Option.List.bind_list]; rewrite ?List.app_nil_r.
  1: reflexivity.
  symmetry; etransitivity; [ etransitivity | ]; [ | refine (interp_op_associative_spec_concat o H _ [ [x]; ys]) | ].
  all: cbn [concat List.app map Option.List.bind_list]; rewrite ?List.app_nil_r.
  1: reflexivity.
  rewrite !H1, H2; cbn [Crypto.Util.Option.bind].
  reflexivity.
Qed.

Definition flatten_associative (d : dag) :=
  fun e => match e with
    ExprApp (o, args) =>
    if associative o then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end.
#[local] Instance describe_flatten_associative : description_of Rewrite.flatten_associative
  := "Flattens nested associative operations, such as turning (add [x; add [y; z]]) into (add [x; y; z])".
Global Instance flatten_associative_ok : Ok flatten_associative.
Proof using Type.
  repeat step.
  let v := match goal with v : Z |- _ => v end in
  let H := match goal with H : Forall2 (eval _ _) _ _ |- _ => H end in
  revert dependent v; induction H; cbn.
  { econstructor; eauto. }
  intros ? H4.
  pose proof H4.
  eapply invert_interp_op_associative in H4; eauto. destruct H4 as (?&?&?).
  specialize (IHForall2 _ ltac:(eassumption)).
  inversion IHForall2; subst.
  let x := match goal with |- context[match x with ExprRef _ => _ | _ => _ end] => x end in
  destruct x as [i|[o' args''] ].
  { econstructor. { econstructor. eauto. eauto. }
    erewrite interp_op_associative_cons; eauto. }
  { destruct (op_beq_spec o o'); subst; cycle 1.
    { econstructor. { econstructor. eauto. eauto. }
      erewrite interp_op_associative_cons; eauto. }
    let H := match goal with H : eval _ _ (ExprApp (_, ?args)) _ |- eval _ _ (ExprApp (_, ?args ++ _)) _ => H end in
    inversion H; clear H; subst.
    econstructor; eauto using Forall2_app.
    erewrite interp_op_associative_app; eauto. }
Qed.

Definition flatten_bounded_associative (d : dag) :=
  fun e => match e with
    ExprApp (o, args) =>
    ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => match bounds_for_drop_inner_associative o o' with
        | Some drop_always => args'
        | Some (drop_if_bounded bound o'') => match bound_expr d (ExprApp (o'', args')) with
        | Some ubound => if is_tighter_than_bool ubound bound then args' else [e']
                                              | _ => [e'] end | _ => [e'] end | _ => [e'] end) args) | _ => e end.
#[local] Instance describe_flatten_bounded_associative : description_of Rewrite.flatten_bounded_associative
  := "Flattens some nested operations such as add inside addcarry".

Lemma fold_right_add_cps_id init ls
  : fold_right Z.add init ls = fold_right Z.add 0 ls + init.
Proof. induction ls; cbn; lia. Qed.

Global Instance flatten_bounded_associative_ok : Ok flatten_bounded_associative.
Proof using Type.
  cbv [Ok flatten_bounded_associative].
  intros G d e v Hok He.
  destruct He; try solve [ t ]; [].
  lazymatch goal with
  | [ H0 : Forall2 ?P ?args ?args', H1 : interp_op _ _ ?args' = _
      |- eval _ _ (ExprApp (_, flat_map ?f args)) _ ]
    => epose [] as preargs; epose [] as preargs';
       assert (Hpre : Forall2 P preargs preargs') by constructor;
       change (flat_map f args) with (preargs ++ flat_map f args); change args' with (preargs' ++ args') in H1;
       clearbody preargs preargs';
       revert preargs preargs' Hpre H1;
       induction H0; cbn [flat_map]; intros *
  end.
  { rewrite !List.app_nil_r; intros; t. }
  { rewrite app_cons_app_app, !app_assoc.
    break_innermost_match; reflect_hyps.
    all: try solve [ intro; apply IHForall2, Forall2_app; auto ].
    all: [ > | ].
    all: let H := match goal with H : bounds_for_drop_inner_associative _ _ = _ |- _ => H end in
         cbv [bounds_for_drop_inner_associative Crypto.Util.Option.bind unary_truncate_size] in H.
    all: repeat first [ progress inversion_option | break_innermost_match_hyps_step ].
    all: match goal with
         | [ H : _ = _ :> drop_kind |- _ ] => inversion H; clear H
         end.
    all: subst.
    all: match goal with
         | [ H : eval _ _ (ExprApp _) _ |- _ ] => inversion H; clear H
         end; subst.
    all: lazymatch goal with
         | [ H : bound_expr _ _ = _ |- _ ]
           => let H' := fresh in
              pose proof H as H';
              cbn [bound_expr] in H; break_innermost_match_hyps; inversion_option; subst;
              (eapply eval_bound_expr in H';
               [ | try eassumption; (econstructor; [ eassumption | cbn [interp_op]; reflexivity ]) .. ])
         | _ => idtac
         end.
    all: reflect_hyps.
    all: repeat step.
    all: intros; eapply IHForall2; try apply Forall2_app; clear IHForall2.
    all: lazymatch goal with
         | [ |- Forall2 _ _ _ ] => eassumption
         | _ => idtac
         end.
    all: cbn [interp_op Option.invert_Some op_to_Z_binop identity] in *; inversion_option; subst.
    all: rewrite !fold_right_app.
    all: cbn [fold_right].
    all: repeat first [ match goal with
                        | [ |- context[fold_right Z.add ?init ?ls] ]
                          => lazymatch init with
                             | 0 => fail
                             | _ => rewrite (fold_right_add_cps_id init ls)
                             end
                        end
                      | reflexivity ].
    all: rewrite !Z.land_ones, ?Z.ones_equiv in * by lia.
    all: Z.rewrite_mod_small.
    all: try reflexivity. }
Qed.

Definition consts_commutative (d : dag) :=
  fun e => match e with
    ExprApp (o, args) =>
    if commutative o then
    let csts_exprs := List.partition isCst args in
    if associative o
    then match interp0_expr (ExprApp (o, fst csts_exprs)) with
         | Some v => ExprApp (o, ExprApp (const v, nil):: snd csts_exprs)
         | _ => ExprApp (o, fst csts_exprs ++ snd csts_exprs)
         end
    else ExprApp (o, fst csts_exprs ++ snd csts_exprs)
    else e | _ => e end.
#[local] Instance describe_consts_commutative : description_of Rewrite.consts_commutative
  := "Moves all constants to the beginning of commutative n-ary operation lists, additionally combining the constants into a single node when the operation is associative".

Global Instance consts_commutative_ok : Ok consts_commutative.
Proof using Type.
  step.
  destruct_one_head' @expr; trivial.
  destruct_one_head' node.
  destruct commutative eqn:?; trivial.
  inversion_one_head' @eval.
  let l := match goal with l : list expr |- _ => l end in
  epose proof Permutation_partition l isCst.
  let H := match goal with H : Forall2 (eval _ _) _ _ |- _ => H end in
  eapply Permutation.Permutation_Forall2 in H; [|eassumption].
  destruct_head'_ex; destruct_head'_and.
  epose proof permute_commutative  _ _ _ _ ltac:(eassumption) ltac:(eassumption) _ ltac:(eassumption).
  break_match; [|solve[repeat Econstructor; eauto] .. ].

  set (fst (partition isCst l)) as csts in *; clearbody csts.
  set (snd (partition isCst l)) as exps in *; clearbody exps.
  clear dependent l. clear dependent args'.
  move o at top; move Heqb0 at top; move Heqb at top.
  let H := match goal with H : interp0_expr _ = Some _ |- _ => H end in
  eapply eval_interp0_expr in H; instantiate (1:=d) in H; instantiate (1:=G) in H.

  let H := match goal with H : Forall2 (eval _ _) (_ ++ _) _ |- _ => H end in
  eapply Forall2_app_inv_l in H; destruct H as (?&?&?&?&?); subst.
  econstructor. { econstructor. econstructor. econstructor. exact eq_refl. eassumption. }

  inversion_one_head' @eval.
  let H := multimatch goal with H : Forall2 (eval _ _) _ _ |- _ => H end in
  eapply eval_eval_Forall2 in H; eauto; progress subst.
  clear dependent exps. clear dependent csts.

  change (?x :: ?xs) with ([x] ++ xs).
  rewrite interp_op_associative_app_bind in * by assumption.
  erewrite interp_op_associative_idempotent by eassumption; cbn [Crypto.Util.Option.bind].
  unfold Crypto.Util.Option.bind in * |- .
  break_innermost_match_hyps; inversion_option; subst; cbn [Crypto.Util.Option.bind].
  assumption.
Qed.

Definition neqconst i := fun a : expr => negb (option_beq Z.eqb (interp0_expr a) (Some i)).
Definition drop_identity (d : dag) :=
  fun e => match e with ExprApp (o, args) =>
    match identity o with
    | Some i =>
        let args := List.filter (neqconst i) args in
        match args with
        | nil => ExprApp (const i, nil)
        | _ => ExprApp (o, args)
        end
    | _ => match identity_after_0 o, args with
    | Some i, arg :: args =>
        let args := List.filter (neqconst i) args in
        ExprApp (o, arg :: args)
    | _, _ => e end end | _ => e end.
#[local] Instance describe_drop_identity : description_of Rewrite.drop_identity
  := "Drops constant identity subexpressions, such as 0s in add and 1s in mul".

Lemma filter_neqconst_helper G d id
      l args
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ List.filter (fun v => negb (Z.eqb v id)) args' = List.filter (fun v => negb (Z.eqb v id)) args.
Proof.
  induction H; cbn; [ eexists; split; constructor | ].
  destruct_head'_ex; destruct_head'_and.
  unfold neqconst at 1.
  unfold negb at 1; break_innermost_match_step; reflect_hyps.
  all: unfold negb at 1; break_innermost_match_step; reflect_hyps.
  all: repeat first [ match goal with
                      | [ H : interp0_expr ?e = Some _, H' : eval ?Gv ?dv ?e _ |- _ ]
                        => apply eval_interp0_expr with (G:=Gv) (d:=dv) in H
                      end
                    | progress reflect_hyps
                    | congruence
                    | progress subst
                    | solve [ eauto ]
                    | step; eauto; [] ].
  all: econstructor; split; [ constructor; eassumption | cbn [filter] ].
  all: unfold negb in *; break_innermost_match; reflect_hyps; try congruence.
Qed.

Lemma filter_neqconst G d o id
      (Hid : identity o = Some id)
      l args
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ interp_op G o args' = interp_op G o args.
Proof.
  edestruct filter_neqconst_helper as [args' [H1 H2] ]; try eassumption.
  exists args'; split; try eassumption.
  erewrite interp_op_drop_identity, H2, <- interp_op_drop_identity by eassumption.
  reflexivity.
Qed.

Lemma filter_neqconst' G d o id
      (Hid : identity_after_0 o = Some id)
      e arg l args
      (H0 : eval G d e arg)
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ interp_op G o (arg :: args') = interp_op G o (arg :: args).
Proof.
  edestruct filter_neqconst_helper as [args' [H1 H2] ]; try eassumption.
  exists args'; split; try eassumption.
  erewrite interp_op_drop_identity_after_0, H2, <- interp_op_drop_identity_after_0 by eassumption.
  reflexivity.
Qed.

Global Instance drop_identity_Ok : Ok drop_identity.
Proof using Type.
  repeat (step; eauto; []).
  inversion H; subst; clear H.
  destruct identity eqn:?; [ | destruct identity_after_0 eqn:? ]; break_innermost_match.
  all: repeat (step; eauto; []).
  all: pose proof filter_neqconst.
  all: pose proof filter_neqconst'.
  all: specialize_under_binders_by eassumption.
  all: destruct_head'_ex.
  all: destruct_head'_and.
  all: repeat first [ progress subst
                    | progress inversion_option
                    | match goal with
                      | [ H : ?ls = nil, H' : context[?ls] |- _ ] => rewrite H in H'
                      | [ H : ?ls = cons _ _, H' : context[?ls] |- _ ] => rewrite H in H'
                      | [ H : Forall2 _ nil _ |- _ ] => inversion H; clear H
                      | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                      end
                    | erewrite interp_op_nil_is_identity in * by eassumption
                    | solve [ t ] ].
Qed.

Definition fold_consts_to_and (d : dag) :=
  fun e => match consts_commutative d e with
           | ExprApp ((and _ | andZ) as o, ExprApp (const v, nil) :: args)
             => let v' := match o with
                          | and sz => Z.land v (Z.ones (Z.of_N sz))
                          | _ => v
                          end in
                if (v' <? 0)%Z
                then if (v' =? -1)%Z
                     then ExprApp (andZ, args)
                     else ExprApp (andZ, ExprApp (const v', nil) :: args)
                else if (v' =? 0)
                     then ExprApp (const 0, nil)
                     else let v_sz := (1 + Z.log2 v') in
                          if (v' =? Z.ones v_sz)%Z
                          then ExprApp (and (Z.to_N v_sz), args)
                          else ExprApp (and (Z.to_N v_sz), ExprApp (const v', nil) :: args)
           | _ => e
           end.
#[local] Instance describe_fold_consts_to_and : description_of Rewrite.fold_consts_to_and
  := "Truncates constant arguments to bitwise and, dropping them if they provably do not change the result".

Global Instance fold_consts_to_and_Ok : Ok fold_consts_to_and.
Proof using Type.
  repeat (step; eauto; []).
  break_innermost_match; try assumption; reflect_hyps.
  all: match goal with
       | [ H : eval _ _ ?e _, H' : consts_commutative _ ?e = _ |- _ ]
         => eapply consts_commutative_ok in H; [ | eassumption .. ];
            rewrite H' in H; clear e H'
       end.
  all: repeat (step; eauto; []).
  all: cbn [interp_op fold_right identity invert_Some op_to_Z_binop] in *; inversion_option; subst.
  all: repeat first [ match goal with
                      | [ H : Z.land _ (Z.ones (Z.of_N ?sz)) < 0 |- _ ]
                        => exfalso; revert H; clear; rewrite Z.land_neg;
                           pose proof (Z.ones_nonneg (Z.of_N sz) ltac:(lia));
                           lia
                      | [ |- context[fold_right Z.land ?v ?ls] ]
                        => lazymatch v with -1 => fail | _ => idtac end;
                           rewrite (@Z.fold_right_land_m1_cps v ls)
                      | [ H : Z.land ?x ?y = _ |- context[Z.land (Z.land ?x _) ?y] ]
                        => rewrite !(Z.land_comm x), <- !Z.land_assoc, H
                      | [ |- context[Z.land ?x ?y] ]
                        => match goal with
                           | [ |- context[Z.land ?y ?x] ]
                             => rewrite (Z.land_comm x y)
                           end
                      | [ H : ?x = Z.ones _ |- _ ]
                        => is_var x; rewrite <- H
                      | [ |- Z.land (Z.land ?x ?y) (Z.ones (1 + Z.log2 ?x)) = Z.land ?x ?y ]
                        => rewrite !(Z.land_comm x), <- !Z.land_assoc; f_equal
                      | [ |- Z.land (Z.land (Z.land ?y ?s) ?v) (Z.ones (1 + Z.log2 (Z.land ?y ?s))) = Z.land (Z.land ?y ?v) ?s ]
                        => cut (Z.land (Z.land y s) (Z.ones (1 + Z.log2 (Z.land y s))) = Z.land y s);
                           [ rewrite <- !(Z.land_comm v), <- !Z.land_assoc;
                             let H := fresh in intro H; rewrite H; reflexivity
                           | generalize dependent (Z.land y s); intros ]
                      | [ H : context[Z.land ?y (Z.ones ?z)] |- context[Z.land (Z.ones ?z) ?y] ]
                        => rewrite (Z.land_comm (Z.ones z) y)
                      | [ H : ?lhs = ?rhs |- _ ]
                        => lazymatch rhs with context[lhs] => idtac end;
                           rewrite <- !H
                      end
                    | progress autorewrite with zsimplify_const
                    | apply (f_equal (@Some _))
                    | progress cbn [fold_right]
                    | rewrite Z2N.id by auto with zarith
                    | solve [ t ]
                    | solve [ Z.bitblast;
                              repeat first [ now rewrite Z.bits_above_log2 by lia
                                           | progress Z.bitblast_core
                                           | lazymatch goal with
                                             | [ H : ?i < ?v, H' : context[Z.land ?y (Z.ones ?v)] |- context[Z.testbit ?y ?i] ]
                                               => (replace (Z.testbit y i) with (Z.testbit (Z.land y (Z.ones v)) i) by Z.bitblast_core;
                                                   rewrite Z.bits_above_log2 by lia)
                                             end ] ]
                    | t ].
Qed.

Definition xor_same (d : dag) :=
  fun e => match e with ExprApp (xor _,[x;y]) =>
    if expr_beq x y then ExprApp (const 0, nil) else e | _ => e end.
#[local] Instance describe_xor_same : description_of Rewrite.xor_same
  := "Replaces xor x x with 0".
Global Instance xor_same_ok : Ok xor_same.
Proof using Type.
  t; cbn [fold_right]. rewrite Z.lxor_0_r, Z.lxor_nilpotent; trivial.
Qed.

Definition shift_to_mul (d : dag) :=
  fun e => match e with
    ExprApp ((shl _ | shlZ) as o, [e'; ExprApp (const v, [])]) =>
      let o' := match o with shl bitwidth => mul bitwidth | shlZ => mulZ | _ => o (* impossible *) end in
      let bw := match o with shl bitwidth => Some bitwidth | shlZ => None | _ => None (* impossible *) end in
      if Z.eqb v 0
      then match bw with
           | Some N0 => ExprApp (const 0, nil)
           | Some (Npos p) => ExprApp (slice 0%N (Npos p), [e'])
           | None => e'
           end
      else if Z.ltb 0 v
      then ExprApp (o', [e'; ExprApp (const (2^v)%Z, [])])
      else e | _ => e end.
#[local] Instance describe_shift_to_mul : description_of Rewrite.shift_to_mul
  := "Rewrites shl to an equivalent multiplication".
Global Instance shift_to_mul_ok : Ok shift_to_mul.
Proof. t; cbn in *; rewrite ?Z.shiftl_mul_pow2, ?Z.land_0_r by lia; repeat (lia + f_equal). Qed.

(* o is like mul *)
(* invariant: Forall2 (fun x '(y, z) => eval (o x i) matches eval (o y z)) input output *)
Definition split_consts (d : dag) (o : op) (i : Z) : list expr -> list (expr * Z)
  := List.map
       (fun e
        => match e with
           | ExprApp (o', args)
             => if op_beq o' o
                then
                  let '(csts, exprs) :=
                    if commutative o' && associative o'
                    then let '(csts, exprs) := List.partition isCst args in
                         (interp0_expr (ExprApp (o', csts)), exprs)
                    else
                      (* nest matches for fewer proof cases *)
                      match match args with
                            | [arg; ExprApp ((const c), _)]
                              => Some (c, arg)
                            | _ => None
                            end with
                      | Some (c, arg) => (Some c, [arg])
                      | None => (Some i, args)
                      end
                  in
                  match csts, exprs with
                  | None, _ => (e, i)
                  | Some c, [arg] => (arg, c)
                  | Some c, args => (ExprApp (o', args), c)
                  end
                else (e, i)
           | _ => (e, i)
           end%bool).

(* invariant: input is a permutation of concat (List.map (fun '(e, zs) => List.map (pair e) zs) output) *)
Definition group_consts (d : dag) (ls : list (expr * Z)) : list (expr * list Z)
  := Option.List.map
       (fun xs => match xs with
                  | [] => None
                  | (e, z) :: xs => Some (e, z :: List.map snd xs)
                  end)
       (List.groupAllBy (fun x y => expr_beq (fst x) (fst y)) ls).

(* o is like add *)
(* spec: if interp0_op o zs is always Some _, then Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) input output *)
Definition compress_consts (d : dag) (o : op) (ls : list (expr * list Z)) : list (expr * Z)
  := List.flat_map
       (fun '(e, zs) => match interp0_op o zs with
                        | None => List.map (pair e) zs
                        | Some z => [(e, z)]
                        end)
       ls.

(* o is like mul *)
(* spec is that Forall (fun '(e, z) e' => o (eval e) z matches eval e') inputs outputs *)
Definition app_consts (d : dag) (o : op) (ls : list (expr * Z)) : list expr
  := List.map (fun '(e, z) => let z := ExprApp (const z, []) in
                              let default := ExprApp (o, [e; z]) in
                              if associative o
                              then match e with
                                   | ExprApp (o', args)
                                     => if op_beq o' o
                                        then ExprApp (o, args ++ [z])
                                        else default
                                   | _ => default end else default)
              ls.

Definition combine_consts_pre (d : dag) : expr -> expr :=
  fun e => match e with ExprApp (o, args) =>
    if commutative o && associative o && op_always_interps o then match combines_to o with
    | Some o' => match identity o' with
    | Some idv =>
        ExprApp (o, app_consts d o' (compress_consts d o (group_consts d (split_consts d o' idv args))))
    | None => e end | None => e end else e | _ => e end%bool.

Definition cleanup_combine_consts (d : dag) : expr -> expr :=
  let simp_outside := List.fold_left (fun e f => f e) [flatten_associative d] in
  let simp_inside := List.fold_left (fun e f => f e) [constprop d;drop_identity d;unary_truncate d;truncate_small d] in
  fun e => simp_outside match e with ExprApp (o, args)  =>
    ExprApp (o, List.map simp_inside args)
                   | _ => e end.

Definition combine_consts (d : dag) : expr -> expr := fun e => cleanup_combine_consts d (combine_consts_pre d e).
#[local] Instance describe_combine_consts : description_of Rewrite.combine_consts
  := "Rewrites expressions like (x + x * 5) into (x * 6)".

Lemma split_consts_correct o i ls G d argsv
      (HGdok : gensym_dag_ok G d)
      (H : Forall2 (eval G d) ls argsv)
      (Hi : identity o = Some i)
  : Forall2 (fun '(e, z) v => exists v', eval G d e v' /\ (interp_op G o [v'; z] = Some v \/ (z = i /\ (v = v' \/ interp_op G o [v'] = Some v)))) (split_consts d o i ls) argsv.
Proof.
  assert (eval G d (ExprApp (o, [])) i) by now econstructor; [ constructor | apply interp_op_nil_is_identity; assumption ].
  cbv [split_consts].
  revert dependent argsv; intro argsv.
  revert argsv; induction ls as [|x xs IH], argsv as [|v argsv];
    try specialize (IH argsv); intros; cbn [List.map];
    invlist Forall2; specialize_by_assumption; constructor; try assumption; clear IH.
  repeat first [ progress inversion_pair
               | progress subst
               | progress inversion_option
               | progress inversion_list
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress reflect_hyps
               | rewrite app_nil_r in *
               | solve [ eauto 10 ]
               | eapply ex_intro; split; [ now unshelve (repeat first [ eassumption | econstructor ]) | ]
               | match goal with
                 | [ |- (let '(x, y) := match ?v with _ => _ end in _) _ ]
                   => tryif is_var v then destruct v else destruct v eqn:?
                 | [ H : (match ?v with _ => _ end) = _ |- _ ]
                   => tryif is_var v then destruct v else destruct v eqn:?
                 | [ H : Forall2 _ (_ :: _) _ |- _ ] => rewrite Forall2_cons_l_ex_iff in H
                 | [ H : Forall2 _ [] _ |- _ ] => rewrite Forall2_nil_l_iff in H
                 | [ H : Forall _ (_ :: _) |- _ ] => rewrite Forall_cons_iff in H
                 | [ H : Forall2 _ (_ ++ _) _ |- _ ] => apply Forall2_app_inv_l in H
                 | [ H : interp_op _ (const _) _ = _ |- _ ] => cbn [interp_op] in H
                 | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H
                 | [ H : ?x = Some _, H' : ?x = Some _ |- _ ] => rewrite H in H'
                 | [ H : context[interp_op _ _ (_ ++ _)] |- _ ] => rewrite interp_op_associative_app_bind in H by assumption; cbv [Crypto.Util.Option.bind] in H
                 | [ H : partition _ _ = _ |- _ ]
                   => let H' := fresh in
                      pose proof H as H'; apply List.Forall_partition in H';
                      let H' := fresh in
                      pose proof H as H'; apply List.partition_eq_filter in H';
                      apply List.partition_permutation in H
                 | [ H : Permutation _ ?l, H' : Forall2 _ ?l ?args, H'' : interp_op _ _ ?args = Some _ |- _ ]
                   => is_var args; eapply Permutation_Forall2 in H'; [ | symmetry; exact H ];
                      let H''' := fresh in
                      destruct H' as [? [H''' H'] ];
                      eapply permute_commutative in H''; try exact H'''; try assumption; [];
                      clear args H'''
                 | [ H : eval _ _ (ExprApp _) _ |- _ ] => inversion H; clear H
                 | [ H : interp0_expr (ExprApp _) = Some _ |- _ ]
                   => eapply eval_interp0_expr in H
                 | [ H : Forall2 (eval _ _) ?ls ?v1, H' : Forall2 (eval _ _) ?ls ?v2 |- _ ]
                   => assert (v1 = v2) by (eapply eval_eval_Forall2; eassumption);
                      clear H'
                 | [ H : Permutation (@filter ?A ?f ?ls) ?ls |- _ ]
                   => apply Permutation_length, List.filter_eq_length_eq in H;
                      generalize dependent (@filter A f ls); intros; subst
                 | [ H : interp_op _ ?o [?x] = Some _ |- context[interp_op _ ?o (?x :: ?ls)] ]
                   => change (x :: ls) with ([x] ++ ls);
                      rewrite interp_op_associative_app_bind, H by assumption;
                      try erewrite interp_op_associative_idempotent by eassumption;
                      cbn [Crypto.Util.Option.bind]
                 | [ H : commutative ?o = true, H' : interp_op _ ?o [?a; ?b] = Some ?v |- interp_op _ ?o [?b; ?a] = Some ?v \/ _ ]
                   => left; erewrite permute_commutative; [ reflexivity | .. ]; try eassumption; rewrite Permutation_rev; reflexivity
                 end
               | erewrite <- interp_op_associative_app by eassumption ].
Qed.

Lemma group_consts_Permutation (d : dag) ls
  : Permutation (List.concat (List.map (fun '(e, zs) => List.map (pair e) zs) (group_consts d ls))) ls.
Proof.
  cbv [group_consts].
  let fv := match goal with |- context[List.groupAllBy ?f ls] => f end in
  pose proof (@List.Forall_groupAllBy _ fv ls) as H;
  etransitivity; [ | apply List.concat_groupAllBy with (f:=fv) ];
  generalize dependent (List.groupAllBy fv ls); intro gfls; intros.
  match goal with |- ?R ?x ?y => cut (x = y); [ intros ->; reflexivity | ] end.
  apply f_equal.
  induction H; [ reflexivity | ]; cbn.
  break_innermost_match; cbn [List.map]; try solve [ exfalso; assumption ].
  repeat (f_equal; try assumption; []).
  cbn [fst snd] in *.
  lazymatch goal with
  | [ H : Forall _ ?ls |- map (pair _) (map snd ?ls) = ?ls ]
    => revert H; clear
  end.
  intro H; induction H; destruct_head'_prod; cbn [List.map fst snd]; reflect_hyps; subst; cbn [fst snd].
  all: f_equal; assumption.
Qed.

Lemma group_consts_nonempty d ls
  : Forall (fun '(e, zs) => zs <> nil) (group_consts d ls).
Proof.
  cbv [group_consts].
  let fv := match goal with |- context[List.groupAllBy ?f ls] => f end in
  pose proof (@List.Forall_groupAllBy_full _ fv ls) as H;
  generalize dependent (List.groupAllBy fv ls); intro gfls; intros.
  induction gfls as [|x xs IH]; cbn [list_rect Option.List.map fold_right] in *; break_innermost_match; destruct_head'_and; destruct_head'_False;
    constructor; try congruence; eauto.
Qed.

Lemma compress_consts_correct d o ls
      (Ho : op_always_interps o = true)
  : Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) ls (compress_consts d o ls).
Proof.
  cbv [compress_consts].
  induction ls as [|x xs IH]; cbn [List.flat_map]; break_innermost_match; cbn [List.app];
    try solve [ exfalso; eapply interp0_op_always_interps; eassumption ]; constructor; eauto.
Qed.

(* in a more specific, usable form *)
Lemma compress_consts_correct_alt G d o' o ls argsv
      (HGdok : gensym_dag_ok G d)
      (Ho : op_always_interps o = true)
      (H : Forall2 (fun '(e, zs) v => exists z, interp0_op o zs = Some z /\ exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) ls argsv)
  : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) (compress_consts d o ls) argsv.
Proof.
  eapply compress_consts_correct in Ho.
  apply Forall2_flip in H.
  eapply Forall2_trans in Ho; [ | exact H ].
  apply Forall2_flip.
  eapply Forall2_weaken; [ | eassumption ]; cbv beta.
  intros; repeat (destruct_head'_ex || destruct_head'_prod || destruct_head'_and || subst).
  repeat first [ progress inversion_option
               | progress subst
               | match goal with
                 | [ H : ?x = Some _, H' : ?x = Some _ |- _ ] => rewrite H in H'
                 end
               | solve [ eauto ] ].
Qed.

Lemma app_consts_correct G d o ls argsv
      (HGdok : gensym_dag_ok G d)
      (H : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o xs = Some z) /\ eval G d e v' /\ interp_op G o [v'; z] = Some v) ls argsv)
  : Forall2 (eval G d) (app_consts d o ls) argsv.
Proof.
  cbv [app_consts].
  induction H; cbn [List.map]; constructor.
  all: repeat first [ assumption
                    | progress destruct_head'_prod
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | progress reflect_hyps
                    | break_innermost_match_step
                    | match goal with
                      | [ |- eval _ _ (ExprApp (_, [_; _])) _ ]
                        => econstructor; [ | eassumption ]; unshelve (repeat (constructor; [ shelve | ])); [ .. | constructor ]
                      | [ |- eval _ _ (ExprApp (const ?z, [])) _ ]
                        => econstructor; [ constructor | reflexivity ]
                      end
                    | step; eauto; []
                    | match goal with
                      | [ |- eval _ _ (ExprApp (_, _ ++ _)) _ ]
                        => econstructor; [ repeat first [ eassumption | apply Forall2_app | apply Forall2_cons | apply Forall2_nil ] | ]
                      end
                    | erewrite interp_op_associative_app; try eassumption; []
                    | eapply interp_op_associative_idempotent; try eassumption ].
Qed.

Lemma combines_to_correct o o' v G xs vxs xsv
      (H : combines_to o = Some o')
      (H' : Forall2 (fun x vx => interp_op G o' [v; x] = Some vx) xs vxs)
      (H'' : interp_op G o xs = Some xsv)
  : interp_op G o' [v; xsv] = interp_op G o vxs.
Proof.
  cbv [combines_to] in H; destruct o; inversion_option; subst.
  all: cbn [interp_op fold_right op_to_Z_binop invert_Some identity] in *; break_innermost_match; inversion_option; subst; apply f_equal.
  all: autorewrite with zsimplify_const in *; try reflexivity.
  all: rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  all: eapply Forall2_weaken in H';
    [
    | intros *;
      let H := fresh in
      intro H;
      inversion_option;
      autorewrite with zsimplify_const in H;
      rewrite ?Z.land_ones in H by lia; exact H ].
  all: rewrite <- Forall2_map_l in H'.
  all: apply Forall2_eq in H'; subst.
  all: induction xs as [|x xs IH]; cbn [fold_right List.map]; autorewrite with zsimplify_const; try reflexivity.
  all: push_Zmod; pull_Zmod.
  all: revert IH; push_Zmod; intro IH; rewrite <- IH; clear IH; pull_Zmod.
  all: rewrite <- Z.mul_add_distr_l.
  all: reflexivity.
Qed.

(* should this be factored differently? *)
Lemma interp_op_combines_to_idempotent G o o' (H : combines_to o = Some o') xs vxs
  : interp_op G o xs = Some vxs -> interp_op G o' [vxs] = Some vxs.
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right op_to_Z_binop invert_Some identity]; break_innermost_match; intros; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: apply f_equal; try reflexivity.
  rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  reflexivity.
Qed.

Lemma interp_op_combines_to_idempotent_rev G o o' (H : combines_to o = Some o') xs vxs
  : interp_op G o' xs = Some vxs -> interp_op G o [vxs] = Some vxs.
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: apply f_equal; try reflexivity.
  rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  reflexivity.
Qed.

Lemma interp_op_combines_to_singleton_same_size G o o' (H : combines_to o = Some o') v
  : interp_op G o [v] = interp_op G o' [v].
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right op_to_Z_binop invert_Some identity]; intros; break_innermost_match; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: reflexivity.
Qed.

(* a more general version useful for us *)
Lemma combines_to_correct_or o o' v G xs vxs xsv
      (Ho : associative o = true)
      (Ho' : op_always_interps o = true)
      (H : combines_to o = Some o')
      (H' : Forall2 (fun x vx => interp_op G o' [v; x] = Some vx \/ interp_op G o' [v; x] = interp_op G o' [vx]) xs vxs)
      (H'' : interp_op G o xs = Some xsv)
  : interp_op G o' [v; xsv] = interp_op G o vxs.
Proof.
  rewrite <- (List.concat_map_singleton vxs).
  rewrite interp_op_associative_spec_concat, map_map by assumption.
  rewrite Option.List.bind_list_cps_id, <- Option.List.eq_bind_list_lift; cbv [Crypto.Util.Option.bind]; break_match; revgoals.
  { exfalso.
    let H := match goal with H : _ = None |- _ => H end in
    revert H; clear -Ho Ho'.
    cbv [Option.List.lift].
    induction vxs as [|?? IH]; cbn; cbv [Crypto.Util.Option.bind] in *; break_match; try congruence.
    intro; eapply interp_op_always_interps; eassumption. }
  eapply combines_to_correct; try eassumption.
  let l := match goal with |- Forall2 _ _ ?l => l end in
  revert dependent xsv; revert dependent l.
  cbv [Option.List.lift] in *.
  induction H'; cbn [List.map fold_right]; intros [|z xs]; intros; cbv [Crypto.Util.Option.bind] in *; break_match_hyps.
  all: inversion_option; inversion_list; subst; constructor.
  all: repeat first [ break_innermost_match_hyps_step
                    | progress inversion_option
                    | progress subst
                    | assumption
                    | match goal with
                      | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                      | [ H : context[?x :: ?l] |- _ ]
                        => is_var x; is_var l; change (x :: l) with ([x] ++ l) in *;
                           rewrite interp_op_associative_app_bind in H by assumption;
                           cbv [Crypto.Util.Option.bind] in H
                      | [ H : context[interp_op _ _ [_] ] |- _ ] => erewrite interp_op_combines_to_idempotent_rev in H by eassumption
                      end
                    | progress destruct_head'_or
                    | erewrite interp_op_combines_to_singleton_same_size in * by eassumption
                    | congruence ].
Qed.

Lemma combines_to_correct_alt G d o o' xs ys i z z1 e
      (Ho : combines_to o = Some o')
      (Hi : identity o' = Some i)
      (Ha : associative o = true)
      (Hai : op_always_interps o = true)
      (H : Forall2 (fun x y => exists v', eval G d e v' /\ (interp_op G o' [v'; x] = Some y \/ (x = i /\ (y = v' \/ interp_op G o' [v'] = Some y)))) xs ys)
      (H' : interp_op G o ys = Some z1)
      (Hz : interp_op G o xs = Some z)
      (Hnonempty : xs <> nil)
  : exists v' : Z, (exists xs0 : list Z, interp_op G o' xs0 = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some z1.
Proof.
  cut (exists v', eval G d e v');
    [ intros [ev ?]; exists ev
    | match goal with
      | [ H : Forall2 _ ?l _, H' : ?l <> [] |- _ ]
        => inversion H; subst; try congruence; destruct_head'_ex; destruct_head'_and; eauto
      end ].
  repeat apply conj.
  { eexists [_]; eapply interp_op_combines_to_idempotent; eassumption. }
  { assumption. }
  { rewrite <- H'.
    eapply combines_to_correct_or; try eassumption.
    clear z1 z H' Hz Hnonempty.
    induction H; constructor; eauto.
    repeat (destruct_head'_ex; destruct_head'_and; destruct_head'_or).
    all: repeat (step; eauto; []); subst; eauto.
    all: erewrite @interp_op_drop_identity in * by eassumption; cbn [filter] in *; cbv [negb] in *; break_innermost_match; break_innermost_match_hyps;
      reflect_hyps; subst.
    all: try congruence.
    all: try now (idtac + left); apply interp_op_nil_is_identity.
    all: eauto. }
Qed.

Lemma combine_consts_helper o o' G d ls args i
      (H : Forall2
             (fun '(e, zs) y =>
                Forall2
                  (fun '(e, z') (v : Z) =>
                     exists v' : Z, eval G d e v' /\ (interp_op G o' [v'; z'] = Some v \/ (z' = i /\ (v = v' \/ interp_op G o' [v'] = Some v))))
                  (map (pair e) zs) y)
             ls args)
      (Hi' : identity o' = Some i)
      (Halways : op_always_interps o = true)
      (Hassoc : associative o = true)
      (Hc : combines_to o = Some o')
      (Hnonempty : Forall (fun '(e, zs) => zs <> nil) ls)
  : exists args',
    interp_op G o (concat args) = interp_op G o args'
    /\ Forall2
         (fun '(e, zs) (v0 : Z) =>
            exists z' : Z,
              interp0_op o zs = Some z' /\
                (exists v' : Z, (exists xs : list Z, interp_op G o' xs = Some z') /\ eval G d e v' /\ interp_op G o' [v'; z'] = Some v0))
         ls args'.
Proof.
  revert ls args H Hnonempty.
  induction ls as [|x xs IH], args as [|arg args]; try specialize (IH args).
  all: rewrite ?Forall2_nil_l_iff, ?Forall2_nil_r_iff, ?Forall2_cons_cons_iff; try congruence.
  { exists nil; split; [ cbn; reflexivity | constructor ]. }
  repeat first [ progress destruct_head_prod
               | progress destruct_head_and
               | progress destruct_head_ex
               | progress intros
               | progress specialize_by_assumption
               | progress invlist Forall ].
  match goal with
  | [ |- ex ?P ] => cut (exists a b, P ([a] ++ b)); [ intros [a [b ?] ]; exists ([a] ++ b); assumption | ]
  end.
  cbv beta.
  rewrite !interp_op_associative_app_bind by assumption.
  setoid_rewrite interp_op_associative_app_bind; [ | assumption ].
  cbv [Crypto.Util.Option.bind]; break_innermost_match; inversion_option; subst; do 2 eexists; break_innermost_match; split; try reflexivity.
  all: repeat first [ progress inversion_option
                    | match goal with
                      | [ H : interp_op _ _ ?l = Some ?x, H' : interp_op _ _ [?v] = Some ?x' |- interp_op _ _ [?x; ?y] = interp_op _ _ [?x'; ?y'] ]
                        => erewrite interp_op_associative_idempotent in H' by first [ exact H | assumption ]
                      | [ H : Some _ = _ |- _ ] => symmetry in H
                      | [ H : interp_op _ _ [?x] = _ |- _ ]
                        => tryif is_evar x then fail else erewrite interp_op_associative_idempotent in H by eassumption
                      | [ H : interp_op _ _ _ = None |- _ ]
                        => apply interp_op_always_interps in H; [ exfalso | assumption ]
                      end
                    | progress subst
                    | progress cbn [List.app]
                    | apply Forall2_cons
                    | eassumption
                    | rewrite @Forall2_map_l_iff in *
                    | match goal with
                      | [ |- exists z, interp0_op ?o ?l = Some z /\ _ ]
                        => let H := fresh in
                           destruct (interp0_op o l) eqn:H;
                           [ eexists; split; [ reflexivity | ]
                           | apply interp_op_always_interps in H; [ exfalso | assumption ] ]
                      end ].
  all: try congruence.
  eapply combines_to_correct_alt; try ((idtac + eapply interp_op_interp0_op); eassumption).
  Unshelve.
  all: try solve [ constructor ].
Qed.

Global Instance cleanup_combine_consts_Ok : Ok cleanup_combine_consts.
Proof.
  repeat (step; eauto; []); cbn [fold_left].
  repeat match goal with
         | [ |- eval _ _ (?r ?d ?e) _ ]
           => apply (_:Ok r); try assumption
         end.
  econstructor; [ | eassumption ].
  rewrite Forall2_map_l.
  rewrite !@Forall2_forall_iff_nth_error in *; cbv [option_eq] in *.
  intros.
  repeat match goal with
         | [ H : context[nth_error ?l] |- context[nth_error ?l ?i] ] => specialize (H i)
         end.
  break_innermost_match; eauto.
  cbn [fold_left].
  repeat lazymatch goal with
  | H : eval ?c ?d ?e _ |- context[?r ?d ?e] =>
    let Hr := fresh in epose proof ((_:Ok r) _ _ _ _ ltac:(eassumption) H) as Hr; clear H
  end.
  assumption.
Qed.

Global Instance combine_consts_pre_Ok : Ok combine_consts_pre.
Proof using Type.
  repeat (step; eauto; []).
  match goal with
  | [ |- context[split_consts ?d ?o ?i ?l] ]
    => pose proof (@split_consts_correct o i l _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(assumption)) as Hs
  end.
  match goal with
  | [ |- context[group_consts ?d ?ls] ]
    => pose proof (@group_consts_Permutation d ls) as Hg;
       pose proof (@group_consts_nonempty d ls) as Hg'
  end.
  eapply Permutation_Forall2 in Hs; [ | symmetry; exact Hg ].
  destruct Hs as [? [? Hs] ].
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  let H := match goal with H : interp_op _ _ _ = Some _ |- _ => H end in
  eapply permute_commutative in H; [ | eassumption .. ].
  rewrite Forall2_concat_l_ex_iff in Hs.
  destruct Hs as [? [? Hs] ]; subst.
  rewrite Forall2_map_l_iff in Hs.
  eapply Forall2_weaken, combine_consts_helper in Hs; try assumption; try solve [ intros; destruct_head'_prod; eassumption ]; [ | try eassumption .. ].
  destruct Hs as [? [? Hs] ].
  econstructor; [ apply app_consts_correct, compress_consts_correct_alt; try assumption | ].
  { eassumption. }
  { congruence. }
Qed.

Global Instance combine_consts_Ok : Ok combine_consts.
Proof. repeat step; apply cleanup_combine_consts_Ok, combine_consts_pre_Ok; assumption. Qed.

(* M-x query-replace-regex RET \(| RewritePass\.\)\([^ ]*\) => _ RET \1\2 => \2 *)
Definition named_pass (name : RewritePass.rewrite_pass) : dag -> expr -> expr
  := match name with
     | RewritePass.addbyte_small => addbyte_small
     | RewritePass.addcarry_bit => addcarry_bit
     | RewritePass.addcarry_small => addcarry_small
     | RewritePass.addoverflow_bit => addoverflow_bit
     | RewritePass.addoverflow_small => addoverflow_small
     | RewritePass.combine_consts => combine_consts
     | RewritePass.constprop => constprop
     | RewritePass.consts_commutative => consts_commutative
     | RewritePass.drop_identity => drop_identity
     | RewritePass.flatten_associative => flatten_associative
     | RewritePass.flatten_bounded_associative => flatten_bounded_associative
     | RewritePass.fold_consts_to_and => fold_consts_to_and
     | RewritePass.set_slice0_small => set_slice0_small
     | RewritePass.set_slice_set_slice => set_slice_set_slice
     | RewritePass.shift_to_mul => shift_to_mul
     | RewritePass.slice0 => slice0
     | RewritePass.slice01_addcarryZ => slice01_addcarryZ
     | RewritePass.slice01_subborrowZ => slice01_subborrowZ
     | RewritePass.slice_set_slice => slice_set_slice
     | RewritePass.truncate_small => truncate_small
     | RewritePass.unary_truncate => unary_truncate
     | RewritePass.xor_same => xor_same
     end.

Global Instance named_pass_Ok {n} : Ok (named_pass n).
Proof. destruct n; cbv [named_pass]; exact _. Qed.

Global Instance describe_pass n : description_of (named_pass n).
Proof.
  destruct n; cbv [named_pass]; try exact _.
  all: fail_if_goals_remain ().
Defined.

Definition expr {rewriting_passes : rewriting_passes_opt} (d : dag) : expr -> expr :=
  List.fold_left (fun e f => f d e)
                 (List.map named_pass rewriting_passes).

Local Instance expr_Ok {rewriting_passes : rewriting_passes_opt} : Ok expr.
Proof.
  pose proof (@named_pass_Ok).
  cbv [expr]; induction rewriting_passes; cbn [map fold_left]; cbv [Ok] in *; eauto.
Qed.

Lemma eval_expr {rewriting_passes : rewriting_passes_opt} c d e v : gensym_dag_ok c d -> eval c d e v -> eval c d (expr d e) v.
Proof.
  apply expr_Ok.
Qed.
End Rewrite.

Definition simplify {opts : symbolic_options_computed_opt} (dag : dag) (e : node idx) :=
  Rewrite.expr dag (reveal_node_at_least dag 3 e).

Lemma eval_simplify {opts : symbolic_options_computed_opt} G d n v : gensym_dag_ok G d -> eval_node G d n v -> eval G d (simplify d n) v.
Proof using Type. eauto using Rewrite.eval_expr, eval_node_reveal_node_at_least. Qed.

Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (idx * idx).

Definition get_flag (st : flag_state) (f : FLAG) : option idx
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option idx) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : idx) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).
Definition reverse_lookup_flag (st : flag_state) (i : idx) : option FLAG
  := option_map
       (@snd _ _)
       (List.find (fun v => option_beq N.eqb (Some i) (fst v))
                  (Tuple.to_list _ (Tuple.map2 (@pair _ _) st (CF, PF, AF, ZF, SF, OF)))).

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).
Definition reverse_lookup_widest_reg (st : reg_state) (i : idx) : option REG
  := option_map
       (fun v => widest_register_of_index (fst v))
       (List.find (fun v => option_beq N.eqb (Some i) (snd v))
                  (List.enumerate (Tuple.to_list _ st))).

Definition load (a : idx) (s : mem_state) : option idx :=
  option_map snd (find (fun p => fst p =? a)%N s).
Definition remove (a : idx) (s : mem_state) : list idx * mem_state :=
  let '(vs, s) := List.partition (fun p => fst p =? a)%N s in
  (List.map snd vs, s).
Definition store (a v : idx) (s : mem_state) : option mem_state :=
  n <- indexof (fun p => fst p =? a)%N s;
  Some (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)) s).
Definition reverse_lookup_mem (st : mem_state) (i : idx) : option (N * idx)
  := option_map
       (fun '(n, (_, ptsto)) => (N.of_nat n, ptsto))
       (List.find (fun v => N.eqb i (fst (snd v)))
                  (List.enumerate st)).

Local Unset Boolean Equality Schemes.
Local Unset Decidable Equality Schemes.
Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Global Instance show_reg_state : Show reg_state := fun st =>
  show (List.map (fun '(n, v) => (widest_register_of_index n, v)) (ListUtil.List.enumerate (Option.List.map id (Tuple.to_list _ st)))).

Global Instance show_flag_state : Show flag_state :=
  fun '(cfv, pfv, afv, zfv, sfv, ofv) => (
  "(*flag_state*)(CF="++show cfv
  ++" PF="++show pfv
  ++" AF="++show afv
  ++" ZF="++show zfv
  ++" SF="++show sfv
  ++" ZF="++show zfv
  ++" OF="++show ofv++")")%string.
Global Instance show_lines_dag : ShowLines dag := (fun d:dag =>
  ["(*dag*)["]
    ++List.map (fun '(i, v, descr) =>"(*"++show i ++"*) " ++ show v++";"
                                         ++ (if dag.get_eager_description_always_show descr
                                             then match dag.get_eager_description_description descr with
                                                  | Some descr => " " ++ String.Tab ++ "(*" ++ descr ++ "*)"
                                                  | None => ""
                                                  end
                                             else ""))%string (dag.eager.elements (dag.eager.force d))
  ++["]"])%list%string.
Global Instance show_lines_mem_state : ShowLines mem_state :=
  @show_lines_list _ ShowLines_of_Show.

Global Instance ShowLines_symbolic_state : ShowLines symbolic_state :=
 fun X : symbolic_state =>
 match X with
 | {|
     dag_state := ds;
     symbolic_reg_state := rs;
     symbolic_flag_state := fs;
     symbolic_mem_state := ms
   |} =>
   ["(*symbolic_state*) {|";
   "  dag_state :="] ++ show_lines ds ++ [";";
   ("  symbolic_reg_state := " ++ show rs ++ ";")%string;
   ("  symbolic_flag_state := " ++ show fs ++";")%string;
   "  symbolic_mem_state :="] ++show_lines ms ++ [";";
   "|}"]
 end%list%string.


Module error.
  Local Unset Boolean Equality Schemes.
  Local Unset Decidable Equality Schemes.
  Variant error :=
  | get_flag (f : FLAG) (s : flag_state)
  | get_reg (r : nat + REG) (s : reg_state)
  | load (a : idx) (s : symbolic_state)
  | remove (a : idx) (s : symbolic_state)
  | remove_has_duplicates (a : idx) (vs : list idx) (s : symbolic_state)
  | store (a v : idx) (s : symbolic_state)
  | set_const (_ : CONST) (_ : idx)
  | expected_const (_ : idx) (_ : expr)

  | unsupported_memory_access_size (_:N)
  | unsupported_label_in_memory (_:string)
  | unsupported_label_argument (_:JUMP_LABEL)
  | unimplemented_prefix (_:NormalInstruction)
  | unimplemented_instruction (_ : NormalInstruction)
  | unsupported_line (_ : RawLine)
  | ambiguous_operation_size (_ : NormalInstruction)
  .

  Global Instance show_lines_error : ShowLines error
    := fun e
       => match e with
          | get_flag f s
            => ["In flag state " ++ show_flag_state s;
                "Flag " ++ show f ++ " was read without being set."]
          | get_reg (inl i) s
            => ["Invalid reg index " ++ show_nat i]
          | get_reg (inr r) s
            => ["In reg state " ++ show_reg_state s;
                "Register " ++ show (r : REG) ++ " read without being set."]
          | load a s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " loaded without being present."]%string)%list
          | remove a s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " removed without being present."]%string)%list
          | remove_has_duplicates a ls s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " occurs multiple times during removal (" ++ show ls ++ ")."]%string)%list
          | store a v s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " updated (with value " ++ show v ++ ") without being present."]%string)%list
          | set_const c i
            => ["SetOperand called with Syntax.const " ++ show c ++ " " ++ show i]%string
          | expected_const i x
            => ["RevealConst called at " ++ show i ++ " resulted in non-const value " ++ show x]
          | unsupported_memory_access_size n => ["error.unsupported_memory_access_size " ++ show n]
          | unsupported_label_in_memory l => ["error.unsupported_label_in_memory " ++ l]
          | unsupported_label_argument l => ["error.unsupported_label_argument " ++ show l]
          | unimplemented_instruction n => ["error.unimplemented_instruction " ++ show n]
          | unimplemented_prefix n => ["error.unimplemented_prefix " ++ show n]
          | unsupported_line n => ["error.unsupported_line " ++ show n]
          | ambiguous_operation_size n => ["error.ambiguous_operation_size " ++ show n]
          end%string.
  Global Instance Show_error : Show error := _.
End error.
Notation error := error.error.

Definition M T := symbolic_state -> ErrorT (error * symbolic_state) (T * symbolic_state).
Definition ret {A} (x : A) : M A :=
  fun s => Success (x, s).
Definition err {A} (e : error) : M A :=
  fun s => Error (e, s).
Definition some_or {A} (f : symbolic_state -> option A) (e : symbolic_state -> error) : M A :=
  fun st => match f st with Some x => Success (x, st) | None => Error (e st, st) end.
Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun s => (x_s <- x s; f (fst x_s) (snd x_s))%error.
Definition lift_dag {A} (v : dag.M A) : M A :=
  fun s => let '(v, d) := v s.(dag_state) in
           Success (v, update_dag_with s (fun _ => d)).

Declare Scope x86symex_scope.
Delimit Scope x86symex_scope with x86symex.
Bind Scope x86symex_scope with M.
Notation "x <- y ; f" := (bind y (fun x => f%x86symex)) : x86symex_scope.
Section MapM. (* map over a list in the state monad *)
  Context {A B} (f : A -> M B).
  Fixpoint mapM (l : list A) : M (list B) :=
    match l with
    | nil => ret nil
    | cons a l => b <- f a; bs <- mapM l; ret (cons b bs)
    end%x86symex.
End MapM.
Definition mapM_ {A B} (f: A -> M B) l : M unit := _ <- mapM f l; ret tt.

Definition error_get_reg_of_reg_index ri : symbolic_state -> error
  := error.get_reg (let r := widest_register_of_index ri in
                    if (reg_index r =? ri)%nat
                    then inr r
                    else inl ri).

Definition GetFlag f : M idx :=
  some_or (fun s => get_flag s f) (error.get_flag f).
Definition GetReg64 ri : M idx :=
  some_or (fun st => get_reg st ri) (error_get_reg_of_reg_index ri).
Definition Load64 (a : idx) : M idx := some_or (load a) (error.load a).
Definition Remove64 (a : idx) : M idx
  := fun s => let '(vs, m) := remove a s in
              match vs with
              | [] => Error (error.remove a s, s)
              | [v] => Success (v, update_mem_with s (fun _ => m))
              | vs => Error (error.remove_has_duplicates a vs s, s)
              end.
Definition SetFlag f i : M unit :=
  fun s => Success (tt, update_flag_with s (fun s => set_flag s f i)).
Definition HavocFlags : M unit :=
  fun s => Success (tt, update_flag_with s (fun _ => Tuple.repeat None 6)).
Definition PreserveFlag {T} (f : FLAG) (k : M T) : M T :=
  vf <- (fun s => Success (get_flag s f, s));
  x <- k;
  _ <- (fun s => Success (tt, update_flag_with s (fun s => set_flag_internal s f vf)));
  ret x.
Definition SetReg64 rn i : M unit :=
  fun s => Success (tt, update_reg_with s (fun s => set_reg s rn i)).
Definition Store64 (a v : idx) : M unit :=
  ms <- some_or (store a v) (error.store a v);
  fun s => Success (tt, update_mem_with s (fun _ => ms)).
Definition Merge {descr : description} (e : expr) : M idx := fun s =>
  let i_dag := merge e s in
  Success (fst i_dag, update_dag_with s (fun _ => snd i_dag)).
Definition App {opts : symbolic_options_computed_opt} {descr : description} (n : node idx) : M idx :=
  fun s => Merge (simplify s n) s.
Definition Reveal n (i : idx) : M expr :=
  fun s => Success (reveal s n i, s).
Definition RevealConst (i : idx) : M Z :=
  x <- Reveal 1 i;
  match x with
  | ExprApp (const n, nil) => ret n
  | _ => err (error.expected_const i x)
  end.

Definition GetReg {opts : symbolic_options_computed_opt} {descr:description} r : M idx :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  v <- GetReg64 rn;
  App ((slice lo sz), [v]).
Definition SetReg {opts : symbolic_options_computed_opt} {descr:description} r (v : idx) : M unit :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  if N.eqb sz 64
  then v <- App (slice 0 64, [v]);
       SetReg64 rn v (* works even if old value is unspecified *)
  else old <- GetReg64 rn;
       v <- App ((set_slice lo sz), [old; v]);
       SetReg64 rn v.

Class AddressSize := address_size : OperationSize.
Definition Address {opts : symbolic_options_computed_opt} {descr:description} {sa : AddressSize} (a : MEM) : M idx :=
  _ <- match a.(mem_base_label) with
       | None => ret tt
       | Some l => err (error.unsupported_label_in_memory l)
       end;
  base <- match a.(mem_base_reg) with
           | Some r => GetReg r
           | None => App ((const 0), nil)
           end;
  index <- match a.(mem_scale_reg) with
           | Some (z, r) => z <- App (zconst sa z, []); r <- GetReg r; App (mul sa, [r; z])
           | None => App ((const 0), nil)
           end;
  offset <- App (match a.(mem_offset) with
                             | Some s => (zconst sa s, nil)
                             | None => (const 0, nil) end);
  bi <- App (add sa, [base; index]);
  App (add sa, [bi; offset]).

Definition Load {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Load64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Remove {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Remove64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Store {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) v : M unit :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  old <- Load64 addr;
  v <- App (slice 0 (Syntax.operand_size a s), [v]);
  v <- App (set_slice 0 (Syntax.operand_size a s), [old; v])%N;
  Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App (zconst s a, [])
  | mem a => Load a
  | reg r => GetReg r
  | label l => err (error.unsupported_label_argument l)
  end.

Definition SetOperand {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (o : ARG) (v : idx) : M unit :=
  match o with
  | Syntax.const a => err (error.set_const a v)
  | mem a => Store a v
  | reg a => SetReg a v
  | label l => err (error.unsupported_label_argument l)
  end.

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreARG (_ : ARG)
| PreFLG (_ : FLAG)
| PreRef (_ : idx)
| PreApp (_ : op) (_ : list pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Local Coercion PreARG : ARG >-> pre_expr.
Local Coercion PreFLG : FLAG >-> pre_expr.
Local Coercion PreRef : idx >-> pre_expr.
Example __testPreARG_boring : ARG -> list pre_expr := fun x : ARG => @cons pre_expr x nil.
(*
Example __testPreARG : ARG -> list pre_expr := fun x : ARG => [x].
*)

Fixpoint Symeval {opts : symbolic_options_computed_opt} {descr:description} {s : OperationSize} {sa : AddressSize} (e : pre_expr) : M idx :=
  match e with
  | PreARG o => GetOperand o
  | PreFLG f => GetFlag f
  | PreRef i => ret i
  | PreApp op args =>
      idxs <- mapM Symeval args;
      App (op, idxs)
  end.

Definition rcrcnt s cnt : Z :=
  if N.eqb s 8 then Z.land cnt 31 mod 9 else
  if N.eqb s 16 then Z.land cnt 31 mod 17 else
  Z.land cnt (Z.of_N s-1).

Notation "f @ ( x , y , .. , z )" := (PreApp f (@cons pre_expr x (@cons pre_expr y .. (@cons pre_expr z nil) ..))) (at level 10) : x86symex_scope.
Definition SymexNormalInstruction {opts : symbolic_options_computed_opt} {descr:description} (instr : NormalInstruction) : M unit :=
  let stack_addr_size : AddressSize := 64%N in
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some s =>
  match Syntax.prefix instr with None =>
  let s : OperationSize := s in
  let resize_reg r := some_or (fun _ => reg_of_index_and_shift_and_bitcount_opt (reg_index r, 0%N (* offset *), s)) (fun _ => error.unimplemented_instruction instr) in
  match instr.(Syntax.op), instr.(args) with
  | (mov | movzx), [dst; src] => (* Note: unbundle when switching from N to Z *)
    v <- GetOperand src;
    SetOperand dst v
  | xchg, [a; b] => (* Note: unbundle when switching from N to Z *)
    va <- GetOperand a;
    vb <- GetOperand b;
    _ <- SetOperand b va;
    SetOperand a vb
  | cmovc, [dst; src]
  | cmovb, [dst; src]
  | cmovo, [dst; src]
    =>
    let flag := match instr.(Syntax.op) with cmovo => OF | _ => CF end in
    v <- Symeval (selectznz@(flag, dst, src));
    SetOperand dst v
  | cmovnz, [dst; src] =>
    v <- Symeval (selectznz@(ZF, src, dst));
    SetOperand dst v
  | seto, [dst] =>
    of <- GetFlag OF;
    SetOperand dst of
  | setc, [dst] =>
    cf <- GetFlag CF;
    SetOperand dst cf
  | Syntax.add, [dst; src] =>
    v <- Symeval (add s@(dst, src));
    c <- Symeval (addcarry s@(dst, src));
    o <- Symeval (addoverflow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | Syntax.adc, [dst; src] =>
    v <- Symeval (add s@(dst, src, CF));
    c <- Symeval (addcarry s@(dst, src, CF));
    o <- Symeval (addoverflow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | (adcx|adox) as op, [dst; src] =>
    let f := match op with adcx => CF | _ => OF end in
    v <- Symeval (add s@(dst, src, f));
    c <- Symeval (addcarry s@(dst, src, f));
    _ <- SetOperand dst v;
    SetFlag f c
  | Syntax.sub, [dst; src] =>
    v <- Symeval (add       s@(dst, PreApp (neg s) [PreARG src]));
    c <- Symeval (subborrow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | Syntax.sbb, [dst; src] =>
    v <- Symeval (add         s@(dst, PreApp (neg s) [PreARG src], PreApp (neg s) [PreFLG CF]));
    c <- Symeval (subborrow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | lea, [reg dst; mem src] =>
    a <- Address src;
    SetOperand dst a
  | imul, ([dst as src1; src2] | [dst; src1; src2]) =>
    v <- Symeval (mulZ@(src1,src2));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.xor, [dst; src] =>
    v <- Symeval (xorZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
  | Syntax.and, [dst; src] =>
    v <- Symeval (andZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil); _ <- SetFlag CF zero; SetFlag OF zero
  | Syntax.or, [dst; src] => (* side effects of "or" are identical to side effects of "and" and "xor", according to https://en.wikibooks.org/wiki/X86_Assembly/Logic *)
    v <- Symeval (orZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil); _ <- SetFlag CF zero; SetFlag OF zero
  | Syntax.bzhi, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    v <- Symeval (andZ@(src,PreApp (const (Z.ones (Z.land cnt (Z.ones 8)))) nil));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- App (const 0, nil); SetFlag OF zero
  | Syntax.rcr, [dst; cnt] =>
    x <- GetOperand dst;
    cf <- GetFlag CF;
    cnt <- GetOperand cnt; cnt <- RevealConst cnt; let cnt := rcrcnt s cnt in
    cntv <- App (const cnt, nil);
    y <- App (rcr s, [x; cf; cntv]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if (cnt =? 1)%Z
    then cf <- App ((slice 0 1), cons (x) nil); SetFlag CF cf
    else ret tt
  | mulx, [hi; lo; src2] =>
    let src1 : ARG := rdx in
    v  <- Symeval (mulZ@(src1,src2));
    vh <- Symeval (shrZ@(v,PreARG (Z.of_N s)));
    _ <- SetOperand lo v;
         SetOperand hi vh
  | (Syntax.mul | imul), [src2] =>
    let src1 : ARG := rax in
    v  <- Symeval (mulZ@(src1,src2));
    vh <- Symeval (shrZ@(v,PreARG (Z.of_N s)));
    lo <- resize_reg rax;
    hi <- (if (s =? 8)%N
           then ret ah
           else resize_reg rdx);
    _ <- SetOperand (lo:ARG) v;
    _ <- SetOperand (hi:ARG) vh;
    HavocFlags (* This is conservative and can be made more precise *)
  | Syntax.shl, [dst; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shl s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.shlx, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    let cnt' := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shl s@(src, cnt'));
    SetOperand dst v
  | Syntax.shr, [dst; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shr s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.sar, [dst; cnt] =>
    x <- GetOperand dst;
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    c <- Symeval cnt; rc <- Reveal 1 c;
    y <- App (sar s, [x; c]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if expr_beq rc (ExprApp (const 1%Z, nil))
    then (
      cf <- App ((slice 0 1), cons (x) nil);
      _ <- SetFlag CF cf;
      zero <- App (const 0, nil); SetFlag OF zero)
    else ret tt
  | shrd, [lo as dst; hi; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    let cnt' := addZ@(Z.of_N s, PreApp negZ [cnt]) in
    v <- Symeval (or s@(shr s@(lo, cnt), shl s@(hi, cnt')));
    _ <- SetOperand dst v;
    HavocFlags
  | inc, [dst] =>
    v <- Symeval (add s@(dst, PreARG 1%Z));
    o <- Symeval (addoverflow s@(dst, PreARG 1%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | dec, [dst] =>
    v <- Symeval (add s@(dst, PreARG (-1)%Z));
    o <- Symeval (addoverflow s@(dst, PreARG (-1)%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | test, [ea;eb] =>
    a <- GetOperand ea;
    b <- GetOperand eb;
    zero <- App (const 0, nil);
    _ <- HavocFlags;
    _ <- SetFlag CF zero;
    _ <- SetFlag OF zero;
    if Equality.ARG_beq ea eb
    then zf <- App (iszero, [a]); SetFlag ZF zf
    else ret tt
  | clc, [] => zero <- Merge (@ExprApp (const 0, nil)); SetFlag CF zero
  | push, [src]
    => v    <- GetOperand src;
       rsp' <- GetOperand (s:=stack_addr_size) rsp;
       rsp' <- Symeval (s:=stack_addr_size) (add stack_addr_size@(rsp', PreARG (-(Z.of_N s/8))%Z));
       _    <- SetOperand rsp rsp';
               SetOperand (mem_of_reg rsp) v
  | pop, [dst]
    => v    <- GetOperand (mem_of_reg rsp);
       rsp' <- GetOperand (s:=stack_addr_size) rsp;
       rsp' <- Symeval (s:=stack_addr_size) (add stack_addr_size@(rsp', PreARG ((Z.of_N s/8)%Z)));
       _    <- SetOperand rsp rsp';
               SetOperand dst v
  | _, _ => err (error.unimplemented_instruction instr)
 end
  | Some prefix => err (error.unimplemented_prefix instr) end
  | None => err (error.ambiguous_operation_size instr) end%N%x86symex.

Definition SymexRawLine {opts : symbolic_options_computed_opt} {descr:description} (rawline : RawLine) : M unit :=
  match rawline with
  | EMPTY
  | LABEL _
    => ret tt
  | INSTR instr
    => SymexNormalInstruction instr
  | SECTION _
  | GLOBAL _
  | ALIGN _
  | DEFAULT_REL
      => err (error.unsupported_line rawline)
  end.

Definition SymexLine {opts : symbolic_options_computed_opt} line :=
  let descr:description := Build_description (Parse.show_Line_with_line_number line) false in
  SymexRawLine line.(rawline).

Fixpoint SymexLines {opts : symbolic_options_computed_opt} (lines : Lines) : M unit
  := match lines with
     | [] => ret tt
     | line :: lines
       => (st <- SymexLine line;
          SymexLines lines)
     end.
End WithDag.
Export Old.
Include WithDag dag.
