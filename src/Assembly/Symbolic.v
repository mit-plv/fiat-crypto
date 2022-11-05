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
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Ones.
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
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Lxor.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.Bool.Reflect.
Require Import coqutil.Z.bitblast.
Require Import Coq.Strings.String Crypto.Util.Strings.Show.
Require Import Crypto.Assembly.Syntax.
Import ListNotations.
Definition idx := N.
Local Set Decidable Equality Schemes.
Definition symbol := N.

Print fold_left.

Compute (fold_left (fun l x => x :: l) [1;2;3;4;5] []).

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

Definition associative o := match o with add _|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ=> true | _ => false end.
Definition commutative o := match o with add _|addcarry _|addoverflow _|addZ|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ => true | _ => false end.
Definition identity o := match o with mul N0 => Some 0%Z| mul _|mulZ=>Some 1%Z |add _|addZ|or _|orZ|xor _|xorZ|addcarry _|addcarryZ _|addoverflow _ => Some 0%Z | and s => Some (Z.ones (Z.of_N s))|andZ => Some (-1)%Z |_=> None end.
Definition sum o := match o with add _|addZ => true | _ => false end.
(* identity, but not in the first slot *)
Definition identity_after_0 o := match o with subborrow _|subborrowZ _ => Some 0%Z | _=> None end.
Definition unary_truncate_size o := match o with add s|and s|or s|xor s|mul s => Some (Z.of_N s) | addZ|mulZ|andZ|orZ|xorZ => Some (-1)%Z | _ => None end.
Definition op_always_interps o := match o with add _|addcarry _|addoverflow _|and _|or _|xor _|mul _|addZ|mulZ|andZ|orZ|xorZ|addcarryZ _ => true | _ => false end.
Definition combines_to o := match o with add s => Some (mul s) | addZ => Some mulZ | _ => None end.

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
         => let o : string := Option.invert_Some (show_infix_op o) in
            match args with
            | nil => fun _ => o ++ "[]"
            | x :: nil => fun _ => o ++ "[" ++ show x ++ "]"
            | _ => fun _ => "(" ++ String.concat (" " ++ o ++ " ") (List.map show args) ++ ")"
            end
       | ExprApp ((neg _|negZ) as o, args)
         => let '(o, lvl) := Option.invert_Some (show_prefix_op o) in
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
  Definition interp_op o (args : list Z) : option Z :=
    let keep n x := Z.land x (Z.ones (Z.of_N n)) in
    match o, args with
    | old s x, nil => match ctx x with Some v => Some (keep s v) | None => None end
    | const z, nil => Some z
    | add s, args => Some (keep s (List.fold_right Z.add 0 args))
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
    | and s, args => Some (keep s (List.fold_right Z.land (-1) args))
    | or s, args => Some (keep s (List.fold_right Z.lor 0 args))
    | xor s, args => Some (keep s (List.fold_right Z.lxor 0 args))
    | slice lo sz, [a] => Some (keep sz (Z.shiftr a (Z.of_N lo)))
    | mul s, args => Some (keep s (List.fold_right Z.mul 1 args))
    | set_slice lo sz, [a; b] =>
        Some (Z.lor (Z.shiftl (keep sz b) (Z.of_N lo))
                    (Z.ldiff a (Z.shiftl (Z.ones (Z.of_N sz)) (Z.of_N lo))))
    | selectznz, [c; a; b] => Some (if Z.eqb c 0 then a else b)
    | iszero, [a] => Some (Z.b2z (Z.eqb a 0))
    | addZ, args => Some (List.fold_right Z.add 0 args)
    | mulZ, args => Some (List.fold_right Z.mul 1 args)
    | negZ, [a] => Some (Z.opp a)
    | shlZ, [a; b] => Some (Z.shiftl a b)
    | shrZ, [a; b] => Some (Z.shiftr a b)
    | andZ, args => Some (List.fold_right Z.land (-1) args)
    | orZ, args => Some (List.fold_right Z.lor 0 args)
    | xorZ, args => Some (List.fold_right Z.lxor 0 args)
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

Definition keep n x := Z.land x (Z.ones (Z.of_N n)).

Local Open Scope Z_scope.

Definition in_bounds (x : Z) (r : option (Z*Z)) :=
  match r with
  | None => True
  | Some (min, max) => min <= x <= max
  end.

Ltac inv H := inversion H; subst; clear H.

Definition subset bound1 bound2 := (fst bound2 <=? fst bound1) && (snd bound1 <=? snd bound2).

Lemma subset_bounds bounds1 bounds2 :
  subset bounds1 bounds2 = true ->
  fst bounds2 <= fst bounds1 /\ snd bounds1 <= snd bounds2.
Proof.
  intros. cbv [subset] in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; assumption.
Qed.

Definition contains_multiple_of bounds n := fst bounds <=? (snd bounds / n) * n.

Lemma Z_land_ones' : forall (s : N) (a : Z), Z.land a (Z.ones (Z.of_N s)) = (a mod 2 ^ Z.of_N s)%Z.
Proof. intros. assert (E: Z.le 0 (Z.of_N s)) by lia. auto using Z.land_ones. Qed.

Lemma mod_bounded : forall v s, 0 <= Z.land v (Z.ones (Z.of_N s)) <= Z.ones (Z.of_N s).
Proof.
  intros. rewrite Z_land_ones'. cbv [Z.ones]. rewrite Z.shiftl_1_l. assert (H: 2^ Z.of_N s > 0) by lia.
  apply Z_mod_lt with (a := v) in H. lia.
Qed.

Lemma div_mul_le x y : 0 < y -> x / y * y <= x.
Proof.
  intros H. assert (H': y <> 0) by lia. apply Z.mod_bound_or with (a := x) in H'.
  destruct H' as [H'|H'].
  - rewrite Zmod_eq in H' by lia. destruct H' as [H' _]. lia.
  - lia.
Qed.

Lemma has_multiple bounds x :
  0 < x ->
  contains_multiple_of bounds x = true ->
  fst bounds <= (snd bounds) / x * x <= snd bounds.
Proof.
  destruct bounds as [min max]. cbv [contains_multiple_of]. simpl. intros. apply Z.leb_le in H0.
  split; try assumption. apply div_mul_le. apply H.
Qed.

Lemma has_no_multiple bounds m :
  0 < m ->
  contains_multiple_of bounds m = false ->
  forall y,
  fst bounds <= y <= snd bounds ->
  ~ (y mod m = 0).
Proof.
  intros. intros H'. cbv [contains_multiple_of] in H0. assert (m | y). { apply Znumtheory.Zmod_divide; lia. }
  cbv [Z.divide] in H2. destruct H2 as [z H2]. clear H'. apply Z.leb_nle in H0.
  assert (H': y <= snd bounds / m * m \/ snd bounds / m * m < y) by lia. destruct H' as [H'|H'].
  - apply H0. lia.
  - subst. assert (snd bounds / m < z). { apply Zmult_lt_reg_r with (p := m); assumption. }
    clear H0 H'. destruct H1 as [_ H1].
    remember (Z.div_le_mono _ _ _ H H1) as H1'. clear HeqH1' H1.
    rewrite Z_div_mult in H1' by lia. lia.
Qed.

Lemma nondecreasing_max' (a b : Z) (f : Z -> Z) :
  (forall x, a <= x < b -> f x <= f (x + 1)) ->
  (forall y, a <= y < b -> f y <= f b).
Proof.
  intros. assert (0 <= b - a) by lia. apply Z_of_nat_complete in H1. destruct H1 as [n H1]. assert (b = a + Z.of_nat n) by lia.
  subst. clear H1. generalize dependent y. induction n as [| n'].
  - simpl. intros. assert (y = a) by lia. subst. rewrite Z.add_0_r. lia.
  - intros. destruct (y =? a + Z.of_nat n') eqn: E.
    + apply Z.eqb_eq in E. subst. rewrite Nat2Z.inj_succ. cbv [Z.succ]. rewrite Z.add_assoc. apply H. apply H0.
    + apply Z.eqb_neq in E. apply Z.le_trans with (m := f (a + Z.of_nat n')).
      -- apply IHn'.
        ++ intros. apply H. lia.
        ++ lia.
      -- rewrite Nat2Z.inj_succ. cbv [Z.succ]. rewrite Z.add_assoc. apply H. lia.
Qed.

Lemma nondecreasing_max (a b : Z) (f : Z -> Z) :
  (forall x, a <= x < b -> f x <= f (x + 1)) ->
  (forall y, a <= y <= b -> f y <= f b).
Proof.
  intros. destruct (y =? b) eqn:E.
  - apply Z.eqb_eq in E. subst. lia.
  - apply Z.eqb_neq in E. apply nondecreasing_max' with (a := a); try lia. apply H.
Qed.

Lemma nondecreasing_bounds (a b : Z) (f : Z -> Z) :
  (forall x, a <= x < b -> f x <= f (x + 1)) ->
  forall y,
  a <= y <= b ->
  f a <= f y <= f b.
Proof.
  intros. split.
  - apply nondecreasing_max with (a := a); try lia. intros. apply H. lia.
  - apply nondecreasing_max with (a := a); try lia. intros. apply H. lia.
Qed.

Lemma mod_nondecreasing (a b : Z) :
  b > 0 ->
  ~ ((a + 1) mod b = 0) ->
  a mod b <= (a + 1) mod b.
Proof.
  intros. rewrite PullPush.Z.add_mod_l.
  assert (H': 0 <= a mod b + 1 < b).
  - assert (0 <= a mod b < b). { apply Z.mod_pos_bound. lia. }
    split; try lia. destruct (a mod b =? b - 1) eqn:E.
    + apply Z.eqb_eq in E. rewrite PullPush.Z.add_mod_l in H0. rewrite E in H0. simpl in H0. replace (b - 1 + 1) with (b) in H0 by lia.
      apply Z_mod_same in H. exfalso. auto.
    + apply Z.eqb_neq in E. lia.
  - apply Z.mod_small in H'. rewrite H'. lia.
Qed.

Lemma no_multiple_bounds lower upper m :
  0 < m ->
  contains_multiple_of (lower + 1, upper) m = false ->
  forall x,
  lower <= x <= upper ->
  lower mod m <= x mod m <= upper mod m.
Proof.
  intros. remember (fun x => x mod m) as f. assert (forall x, f x = x mod m). { rewrite Heqf. reflexivity. }
  repeat rewrite <- H2. clear H2. apply nondecreasing_bounds with (a := lower); try lia.
    intros. subst. apply mod_nondecreasing; try lia. apply has_no_multiple with (bounds := (lower + 1, upper)); try lia.
  - assumption.
  - simpl. lia.
Qed.

Definition bounds_modulo Z_bounds modulus :=
 if contains_multiple_of (fst Z_bounds + 1, snd Z_bounds) modulus then
   (0, modulus - 1)
  else
   (fst Z_bounds mod modulus, snd Z_bounds mod modulus).

Lemma bounds_modulo_bounds b m x :
  0 < m ->
  in_bounds x (Some b) ->
  in_bounds (x mod m) (Some (bounds_modulo b m)).
Proof.
  simpl. destruct b as [min max]. intros. destruct (bounds_modulo (min, max) m) as [min' max'] eqn:E.
  cbv [bounds_modulo] in E. simpl in E. destruct (contains_multiple_of (min + 1, max) m) eqn:E'.
  - inv E. apply Z.mod_pos_bound with (a := x) in H. lia.
  - inv E. apply no_multiple_bounds; try lia. assumption.
Qed.

Definition plain_arg_bounds arg_bounds : option (list (Z*Z)) :=
  fold_right (fun maybe_bound result =>
                  match maybe_bound, result with
                  | Some bound, Some bounds => Some (bound :: bounds)
                  | _, None => None
                  | None, _ => None
                  end) (Some []) arg_bounds.

Lemma plain_bounds_bound :
  forall args arg_bounds plain_bounds,
  plain_arg_bounds arg_bounds = Some plain_bounds ->
  Forall2 in_bounds args arg_bounds ->
  Forall2 in_bounds args (map Some plain_bounds).
Proof.
  intros args. induction args as [| arg args' IHargs'].
  - intros. inv H0. inv H. constructor.
  - intros. inv H0. rename y into arg_bound. rename l' into arg_bounds'. simpl in H.
    destruct arg_bound as [plain_bound|]; destruct (plain_arg_bounds arg_bounds') as [plain_bounds'|] eqn:E.
    + inv H. rewrite map_cons. constructor; try assumption. apply IHargs' with (arg_bounds := arg_bounds');
      assumption.
    + discriminate H.
    + discriminate H.
    + discriminate H.
Qed.

Definition accumulate (f : Z -> Z -> Z) (a0 : Z*Z) (args : list (Z*Z)) : Z*Z :=
  fold_right (fun bound bound' => (f (fst bound) (fst bound'), f (snd bound) (snd bound'))) a0 args.

Lemma sum_bounded plain_bounds:
  forall args : list Z,
  Forall2 in_bounds args (map Some plain_bounds) ->
  in_bounds (fold_right Z.add 0 args) (Some (accumulate Z.add (0, 0) plain_bounds)).
Proof.
  induction plain_bounds as [| pb pbs'].
  - intros. inv H. simpl. lia.
  - intros. rewrite map_cons in H. inv H. rename x into arg. rename l into args'. apply IHpbs' in H4.
    clear IHpbs'. simpl in *. destruct pb as [min1 max1]. destruct (accumulate _ _ pbs') as [min2 max2]. simpl. lia.
Qed.

Definition bounds_positive (plain_bounds : list (Z*Z)) :=
  fold_right (fun bound pos_so_far => (0 <=? fst bound) && pos_so_far) true plain_bounds.

Lemma pos_prod_pos bounds :
  bounds_positive bounds = true ->
  0 <= fst (accumulate Z.mul (1, 1) bounds).
Proof.
  induction bounds as [|bound bounds'].
  - intros. simpl. lia.
  - intros. simpl in H. apply andb_prop in H. destruct H as [H1 H2]. apply IHbounds' in H2. apply Z.leb_le in H1.
    simpl. lia.
Qed.

Lemma product_bounded plain_bounds:
  bounds_positive plain_bounds = true ->
  forall args : list Z,
  Forall2 in_bounds args (map Some plain_bounds) ->
  in_bounds (fold_right Z.mul 1 args) (Some (accumulate Z.mul (1, 1) plain_bounds)).
Proof.
  induction plain_bounds as [| pb pbs'].
  - intros. inv H0. simpl. lia.
  - intros. rewrite map_cons in H0. inv H0. rename x into arg. rename l into args'. simpl in H.
    apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
    apply (IHpbs' H2) in H5. clear IHpbs'. simpl in H5. simpl in H4. destruct pb as [min1 max1]. simpl.
    apply pos_prod_pos in H2. simpl in *. destruct (accumulate _ _ pbs') as [min2 max2]. simpl in *.
    split.
    + apply Z.le_trans with (m := arg * min2).
      -- apply Z.mul_le_mono_nonneg_r; lia.
      -- apply Z.mul_le_mono_nonneg_l; lia.
    + apply Z.le_trans with (m := arg * max2).
      -- apply Z.mul_le_mono_nonneg_l; lia.
      -- apply Z.mul_le_mono_nonneg_r; lia.
Qed.

(* input bounds should be nonnegative.  if lower bound is less than zero, returns None *)
Definition bound_node (o : op) (arg_bounds : list (option (Z*Z))) : option (Z*Z) :=
  match o, (plain_arg_bounds arg_bounds) with
  | old s _, Some nil => Some (0, Z.ones (Z.of_N s))
  | const n, Some nil => Some (n, n)
  | add s, Some actual_bounds =>  let Z_bounds := (accumulate Z.add (0, 0) actual_bounds) in Some (bounds_modulo Z_bounds (2 ^ (Z.of_N s)))
  | addcarry s, Some actual_bounds => let addZ_bounds := accumulate Z.add (0, 0) actual_bounds in
                                      if subset addZ_bounds (0, Z.ones (Z.of_N s)) then Some (0, 0) else Some (0, 1)
  | addcarry s, None => Some (0, 1)
  | shr s, Some [a; b] => if (0 <=? fst a) && (0 <=? fst b) then
                            let Z_bounds := (Z.shiftr (fst a) (snd b), Z.shiftr (snd a) (fst b)) in Some (bounds_modulo Z_bounds (2 ^ (Z.of_N s)))
                          else
                            Some (0, Z.ones (Z.of_N s))
  | mul s, Some actual_bounds =>  if bounds_positive actual_bounds then
                                    let Z_bounds := accumulate Z.mul (1, 1) actual_bounds in Some (bounds_modulo Z_bounds (2 ^ Z.of_N s))
                                  else
                                    Some (0, Z.ones (Z.of_N s))
  | slice lo sz, Some [a] => let Z_bounds := (Z.shiftr (fst a) (Z.of_N lo), Z.shiftr (snd a) (Z.of_N lo)) in Some (bounds_modulo Z_bounds (2 ^ Z.of_N sz))
  | addZ, Some actual_bounds => Some (accumulate Z.add (0, 0) actual_bounds)
  | mulZ, Some actual_bounds => if bounds_positive actual_bounds then
                                  Some (accumulate Z.mul (1, 1) actual_bounds)
                                else
                                  None
  | (old s _ | slice _ s | mul s | shl s | shr s | sar s | neg s | and s | or s | xor s), _ => Some (0, Z.ones (Z.of_N s))
  | _, _ => None
  end.

Ltac thing:= match goal with
  | H : Forall2 _ _ _ |- _ => inversion H; clear H; subst
  end.

Lemma interp_bound_node ctx o args arg_bounds n :
  Forall2 in_bounds args arg_bounds ->
  interp_op ctx o args = Some n ->
  in_bounds n (bound_node o arg_bounds).
Proof.
  intros H1 H2. destruct (plain_arg_bounds arg_bounds) as [plain_bounds|] eqn:E.
  - remember (plain_bounds_bound _ _ _ E H1) as H_p. clear HeqH_p. cbv [bound_node]. rewrite E. simpl.
    clear H1 E arg_bounds. destruct o eqn:Eo; try apply I; simpl in H2; try (inv H2; apply mod_bounded);
    try (destruct args as [| arg1 args1]; try destruct args1 as [| arg2 args2]; try destruct args2 as [| arg3 args3]; inv H2; apply mod_bounded).
    + (* o = old s s0 *)
      destruct args as [| arg args']; try discriminate H2. destruct plain_bounds as [|pb pbs']; try apply I; try apply mod_bounded.
      -- destruct (ctx s0) as [v|]; try discriminate H2. inv H2. simpl. apply mod_bounded.
      -- destruct (ctx s0) as [v|]; try discriminate H2. inv H2. simpl. apply mod_bounded.
    + (* o = const z *)
      destruct args as [| arg args']; try discriminate H2. destruct plain_bounds as [|pb pbs']; try apply I. inv H2. simpl. lia.
    + (* o = add s *)
      inv H2. rewrite Z_land_ones'. apply bounds_modulo_bounds; try lia. apply sum_bounded. assumption.
    + (* o = addcarry s *)
      destruct (subset _ _) eqn:E.
      -- simpl. assert (n = 0); try lia. inv H2. rewrite Z.shiftr_div_pow2; try lia.
         replace (_ / _) with 0; try apply Zmod_0_l. symmetry. apply Zdiv_small.
         apply sum_bounded in H_p. destruct (accumulate _ _ _) as [min max]. cbv [subset] in E. simpl in *.
         apply andb_prop in E. destruct E as [E1 E2].
         apply Z.leb_le in E1. apply Z.leb_le in E2. cbv [Z.ones] in E2. rewrite Z.shiftl_1_l in E2. lia.
      -- clear E H_p plain_bounds. simpl. assert (0 <= n < 2); try lia. inv H2. apply Z.mod_pos_bound. lia.
    + (* o = shr s *)
      destruct plain_bounds as [| pb1 [| pb2 [| pbs'] ] ].
      -- inv H_p. congruence.
      -- inv H_p. inv H4. congruence.
      -- inv H_p. inv H4. inv H6. inv H2. rewrite Z_land_ones'. destruct (_ && _) eqn:E.
        ++ apply bounds_modulo_bounds; try lia. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1.
           apply Z.leb_le in E2. simpl in *. destruct pb1 as [min1 max1]. destruct pb2 as [min2 max2]. simpl in *.
           repeat rewrite Z.shiftr_div_pow2 by lia. split.
          --- apply Z.le_trans with (m := min1 / 2 ^ x0).
            +++ apply Z.div_le_compat_l; try lia. split; try lia.
              apply Z.pow_le_mono_r; lia.
            +++ apply Z.div_le_mono; lia.
          --- apply Z.le_trans with (m := x / 2 ^ min2).
            +++ apply Z.div_le_compat_l; try lia. split; try lia. apply Z.pow_le_mono_r; lia.
            +++ apply Z.div_le_mono; lia.
        ++ clear H3 H5 E. simpl. rewrite <- Z_land_ones'. apply mod_bounded.
      -- inv H_p. inv H4. inv H6. congruence.
    + (* o = slice lo sz *)
      destruct plain_bounds as [| pb1 [| pb2 pbs'] ].
      -- repeat thing. congruence.
      -- repeat thing. inv H2.
          rewrite Z_land_ones'. apply bounds_modulo_bounds; try lia. simpl. repeat rewrite Z.shiftr_div_pow2 by lia.
          simpl in H3. destruct pb1 as [min max]. simpl. split.
        ++ apply Z.div_le_mono; lia.
        ++ apply Z.div_le_mono; lia.
      -- repeat (thing; try congruence).
    + (* o = mul s *)
      destruct (bounds_positive plain_bounds) eqn:E.
      -- inv H2. rewrite Z_land_ones'. apply bounds_modulo_bounds; try lia. simpl. apply product_bounded; assumption.
      -- simpl. inv H2. apply mod_bounded.
    + (* o = addZ *) simpl. inv H2. apply sum_bounded; assumption.
    + (* o = mulZ *) destruct (bounds_positive plain_bounds) eqn:E; try apply I. simpl. inv H2. apply product_bounded; assumption.
  - simpl in E. cbv [bound_node]. rewrite E.
    destruct o eqn:Eo; try apply I.
    all: destruct args as [| arg1 [| arg2 [| arg3 args3] ] ]; try (inv H2; apply mod_bounded).
    all: try (simpl in H2; destruct (ctx s0); inv H2; apply mod_bounded).
    all: try (simpl; assert (0 <= n < 2); try lia; inv H2; apply Z.mod_pos_bound; lia).
    + (* and s *) cbv [interp_op] in H2. rewrite Z.land_m1'_l in H2. inv H2. simpl. cbv [Z.ones]. repeat rewrite Z.shiftl_1_l. lia.
    + (* or s *) cbv [interp_op] in H2. simpl in H2. inv H2. simpl.  cbv [Z.ones]. repeat rewrite Z.shiftl_1_l. lia.
    + (* xor s *) cbv [interp_op] in H2. simpl in H2. inv H2. simpl.  cbv [Z.ones]. repeat rewrite Z.shiftl_1_l. lia.
    + (* mul s *) cbv [interp_op] in H2. rewrite Z_land_ones' in H2. inv H2. simpl. cbv [Z.ones]. rewrite Z.shiftl_1_l.
      assert (0 <= 1 mod 2^Z.of_N s < 2 ^ Z.of_N s); try lia. apply Z.mod_bound_pos; lia.
Qed.

Class description := descr : option ((unit -> string) * bool (* always show *)).
Class extra_rewrite_rules := errules : list string.
Typeclasses Opaque description.
Definition eager_description := option (string * bool).
Notation Build_description descr always_show := (Some (fun 'tt => descr, always_show)) (only parsing).
Notation no_description := None (only parsing).

(* fresh symbols must have value <= their index, so that fresh symbols are truly fresh *)
Definition node_ok (i : idx) (n : node idx) := forall w s args, n = (old w s, args) -> (s <= i)%N.
Lemma new_node_ok n (pf : match n with (old _ _, _) => False | _ => True end) i : node_ok i n.
Proof. repeat intro; subst; assumption. Qed.
Existing Class node_ok.
Hint Extern 1 (node_ok ?i ?n) => exact (@new_node_ok n I i) : typeclass_instances.
Module Old.
Module dag.
  Definition t : Type := list (node idx * description * (option (Z*Z))).
  Definition empty : t := nil.
  Definition size (d : t) : N := N.of_nat (List.length d).
  Definition lookup (d : t) (i : idx) : option (node idx)
    := option_map (fun x => fst (fst x)) (List.nth_error d (N.to_nat i)).
  Definition lookup_bounds (d : t) (i : idx) : option (Z*Z)
    :=  match (List.nth_error d (N.to_nat i)) with
        | Some thing => snd thing
        | None => None
        end.
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := option_map N.of_nat (List.indexof (fun '(n', _, _) => node_beq N.eqb i n') d).
  Definition size_ok (d : t) : Prop
    := True.
  Definition all_nodes_ok (d : t) : Prop
    := forall i r, lookup d i = Some r -> node_ok i r.
  Definition ok (d : t) : Prop
  := size_ok d
     /\ (forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n)
     /\ (forall i n, lookup d i = Some n -> (i < size d)%N).
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => (size d, d ++ [(n, descr, bound_node (fst n) (map (lookup_bounds d) (snd n)))])
       end.
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

  Module eager.
    Definition t := list (idx * node idx * eager_description * option (Z*Z)).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr, bounds)) => (N.of_nat idx, n, force_description descr, bounds))
                  (List.enumerate d).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _, _) => idx) (List.filter (fun '(_, _, descr', _) => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
  End eager.

  Definition M T := t -> T * t.
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun d => let '(v, d) := v d in f v d.
  Definition ret {A} (v : A) : M A
    := fun d => (v, d).

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
                   | progress cbv [option_map Option.value Option.sequence idx] in *
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

  Lemma reverse_lookup_gensym s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.reverse_lookup d (gensym s d) = None.
  Proof.
    cbv [dag.all_nodes_ok] in *.
    destruct (reverse_lookup d (gensym s d)) as [i|] eqn:H; [ | reflexivity ].
    rewrite iff_reverse_lookup_lookup in H by assumption.
    cbv [node_ok gensym] in *.
    specialize_under_binders_by eassumption.
    specialize_under_binders_by reflexivity.
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
    break_innermost_match; try reflexivity; reflect_hyps; subst.
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

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite nth_error_nil_error. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. reflexivity. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; rewrite ?app_length; cbn [List.length]; lia.
  Qed.

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
    repeat apply conj; cbv [size empty]; intros *; cbv [lookup];
      rewrite ?nth_error_nil_error; cbn; try exact I;
      intuition first [ congruence | lia ].
  Qed.
  Global Instance empty_all_nodes_ok : all_nodes_ok empty | 10.
  Proof.
    repeat intro; subst; rewrite lookup_empty in *; congruence.
  Qed.
  Global Instance merge_node_ok {descr:description} {n:node idx} {d : t} {dok : ok d} : ok (snd (merge_node n d)) | 10.
  Proof.
    repeat apply conj; cbv [size empty size_ok]; intros *.
    all: rewrite ?lookup_merge_node, ?reverse_lookup_merge_node by assumption.
    all: let tac :=
           repeat first [ progress cbv [ok size_ok size merge_node lookup reverse_lookup] in *
                        | progress destruct_head'_and
                        | progress inversion_option
                        | progress subst
                        | exfalso; assumption
                        | progress inversion_pair
                        | progress cbn [fst snd List.length] in *
                        | break_innermost_match_step
                        | progress intros
                        | progress destruct_head'_ex
                        | progress destruct_head'_and
                        | progress reflect_hyps
                        | progress split_iff
                        | apply conj
                        | exact I
                        | progress cbv [option_map idx] in *
                        | progress break_match
                        | progress break_match_hyps
                        | lia
                        | congruence
                        | rewrite Nat2N.id in *
                        | rewrite N2Nat.id in *
                        | rewrite app_length
                        | progress specialize_under_binders_by reflexivity
                        | progress specialize_under_binders_by rewrite Nat2N.id
                        | progress destruct_head'_prod
                        | match goal with
                          | [ H : forall i n, match nth_error _ (N.to_nat i) with _ => _ end = _ -> _ |- _ ]
                            => specialize (fun i => H (N.of_nat i))
                          | [ H : _ = Some _ |- _ ] => rewrite H in *
                          | [ H : N.of_nat _ = N.of_nat _ |- _ ] => apply (f_equal N.to_nat) in H
                          end
                        | solve [ exfalso; auto ] ] in
         tac;
         repeat match goal with
                | [ H : _ = Some _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                end;
         tac.
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
    cbv [node_ok]; intros * H.
    inversion H; subst; reflexivity.
  Qed.
  Global Hint Extern 1 (node_ok (size _) (gensym _ _)) => exact (@gensym_node_ok _ _) : typeclass_instances.

  Lemma eq_fst_merge_node_change_descr {descr1 descr2 : description} (n : node idx) (d : t)
    : fst (@merge_node descr1 n d) = fst (@merge_node descr2 n d).
  Proof.
    cbv [merge_node]; break_innermost_match; reflexivity.
  Qed.

  (* lemmas below here don't unfold the definitions *)
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
End dag.
End Old.
Module New.
Module dag.
  Module IdxMap <: UsualS := NMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module ListIdxMap <: UsualS := ListNMap.
  Module NodeIdxMap <: UsualS := ProdUsualMap OpMap ListIdxMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module IdxMapProperties := FMapFacts.OrdProperties IdxMap <+ OrdProperties_RemoveHints IdxMap.
  Module NodeIdxMapProperties := FMapFacts.OrdProperties NodeIdxMap <+ OrdProperties_RemoveHints NodeIdxMap.

  Definition t : Type := NodeIdxMap.t idx * IdxMap.t (node idx * description) * N (* size *).
  Definition empty : t := (@NodeIdxMap.empty _, @IdxMap.empty _, 0%N).
  Definition size (d : t) : N := let '(_, _, sz) := d in sz.
  Definition lookup (d : t) (i : idx) : option (node idx)
    := let '(_, d, _) := d in option_map (@fst _ _) (IdxMap.find i d).
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := let '(d, _, _) := d in NodeIdxMap.find i d.
  Definition size_ok (d : t) : Prop
    := let '(im, nm, n) := d in
       NodeIdxMap.cardinal im = N.to_nat (size d)
       /\ IdxMap.cardinal nm = N.to_nat (size d).
  Definition all_nodes_ok (d : t) : Prop
    := forall i r, lookup d i = Some r -> node_ok i r.
  Definition ok (d : t) : Prop
  := size_ok d
     /\ (forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n)
     /\ (forall i n, lookup d i = Some n -> (i < size d)%N).
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => let '(d, d', sz) := d in
            (sz, (NodeIdxMap.add n sz d, IdxMap.add sz (n, descr) d', N.succ sz))
       end.
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

  Module eager.
    Definition t := list (idx * node idx * eager_description).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr)) => (idx, n, force_description descr))
                  (IdxMap.elements (let '(_, d, _) := d in d)).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _) => idx) (List.filter (fun '(_, _, descr') => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
  End eager.

  Definition M T := t -> T * t.
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun d => let '(v, d) := v d in f v d.
  Definition ret {A} (v : A) : M A
    := fun d => (v, d).

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
                   | progress cbn [fst snd option_map] in *
                   | rewrite IdxMap.add_o
                   | break_innermost_match_step ].
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

  Lemma reverse_lookup_gensym s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.reverse_lookup d (gensym s d) = None.
  Proof.
    cbv [dag.all_nodes_ok] in *.
    destruct (reverse_lookup d (gensym s d)) as [i|] eqn:H; [ | reflexivity ].
    rewrite iff_reverse_lookup_lookup in H by assumption.
    cbv [node_ok gensym] in *.
    specialize_under_binders_by eassumption.
    specialize_under_binders_by reflexivity.
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
    break_innermost_match; try reflexivity; reflect_hyps; subst.
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

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite IdxMap.find_empty. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. cbv [empty reverse_lookup]; now rewrite NodeIdxMap.find_empty. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; try reflexivity.
  Qed.

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
    repeat apply conj; cbv [size empty].
    { apply NodeIdxMapProperties.P.cardinal_1, NodeIdxMap.empty_1. }
    { apply IdxMapProperties.P.cardinal_1, IdxMap.empty_1. }
    all: cbv [lookup reverse_lookup]; intros *.
    all: rewrite ?NodeIdxMap.empty_o, ?IdxMap.empty_o; cbn; intuition congruence.
  Qed.
  Global Instance empty_all_nodes_ok : all_nodes_ok empty | 10.
  Proof.
    repeat intro; subst; rewrite lookup_empty in *; congruence.
  Qed.
  Global Instance merge_node_ok {descr:description} {n:node idx} {d : t} {dok : ok d} : ok (snd (merge_node n d)) | 10.
  Proof.
    repeat apply conj; cbv [size empty size_ok]; intros *.
    all: rewrite ?lookup_merge_node, ?reverse_lookup_merge_node by assumption.
    all: repeat first [ progress cbv [ok size_ok size merge_node lookup reverse_lookup] in *
                      | progress destruct_head'_and
                      | progress inversion_option
                      | progress subst
                      | exfalso; assumption
                      | progress inversion_pair
                      | progress cbn [fst snd] in *
                      | break_innermost_match_step
                      | progress intros
                      | progress reflect_hyps
                      | progress split_iff
                      | apply conj
                      | rewrite NodeIdxMap.cardinal_add, NodeIdxMap.mem_find_b
                      | rewrite IdxMap.cardinal_add, IdxMap.mem_find_b
                      | rewrite N2Nat.inj_succ
                      | lia
                      | congruence
                      | solve [ auto ]
                      | match goal with
                        | [ H : ?x = Some _ |- _ ] => rewrite H in *
                        end
                      | progress specialize_under_binders_by reflexivity
                      | match goal with
                        | [ H : _ |- _ ] => progress specialize_all_ways_under_binders_by exact H
                        | [ H : _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                        end ].
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
    cbv [node_ok]; intros * H.
    inversion H; subst; reflexivity.
  Qed.
  Global Hint Extern 1 (node_ok (size _) (gensym _ _)) => exact (@gensym_node_ok _ _) : typeclass_instances.

  Lemma eq_fst_merge_node_change_descr {descr1 descr2 : description} (n : node idx) (d : t)
    : fst (@merge_node descr1 n d) = fst (@merge_node descr2 n d).
  Proof.
    cbv [merge_node]; break_innermost_match; reflexivity.
  Qed.

  (* lemmas below here don't unfold the definitions *)
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
End dag.
End New.
Export Old.
Global Arguments dag.t : simpl never.
Global Arguments dag.empty : simpl never.
Global Arguments dag.size : simpl never.
Global Arguments dag.lookup : simpl never.
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
        dag.reverse_lookup
        dag.ok
        dag.all_nodes_ok
        dag.merge_node
        dag.gensym
    ].
Notation dag := dag.t.
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

Require Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Global Set Default Goal Selector "1".

Local Open Scope Z_scope.

Fixpoint bound_expr e : option Z := (* e <= r *)
  match e with
  | ExprApp (const v, _) => if Z.leb 0 v then Some v else None
  | ExprApp (add s, args) =>
      Some  match Option.List.lift (List.map bound_expr args) with
            | Some bounds => Z.min (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
            | None => Z.ones (Z.of_N s)
            end
  | ExprApp (selectznz, [c;a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.max a b)
      | _, _ => None
      end
  | ExprApp (set_slice 0 w, [a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.lor
                                  (Z.land (Z.ones (Z.succ (Z.log2 b))) (Z.ones (Z.of_N w)))
                                  (Z.ldiff (Z.ones (Z.succ (Z.log2 a))) (Z.ones (Z.of_N w))))
      | _, _ => None
      end
  | ExprApp ((old s _ | slice _ s | mul s | shl s | shr s | sar s | neg s | and s | or s | xor s), _) => Some (Z.ones (Z.of_N s))
  | ExprApp ((addcarry _ | subborrow _ | addoverflow _ | iszero), _) => Some 1
  | _ => None
  end%Z.

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
  es (He : Forall (fun e => forall b, bound_expr e = Some b ->
       forall (d : dag) (v : Z), eval G d e v -> (0 <= v <= b)%Z) es)
  : forall
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  , (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof using Type.
  induction He; cbn in *; repeat t.
  { cbv [fold_right]; Lia.lia. }
  destruct (bound_expr _) eqn:? in *; cbn in *; repeat t.
  destruct (fold_right (B:=option _) _) eqn:? in *; cbn in *; repeat t.
  specialize (IHHe _ ltac:(eassumption) _ ltac:(eassumption)); cbn.
  specialize (H _ ltac:(exact eq_refl) _ _ ltac:(eassumption)).
  Lia.lia.
Qed.

Require Import Util.ZRange.LandLorBounds.
Lemma eval_bound_expr G e b : bound_expr e = Some b ->
  forall d v, eval G d e v -> (0 <= v <= b)%Z.
Proof using Type.
  revert b; induction e; simpl bound_expr; BreakMatch.break_match;
    inversion 2; intros; inversion_option; subst;
    try match goal with H : context [set_slice] |- _ => shelve end;
    cbv [interp_op] in *;
    BreakMatch.break_match_hyps; inversion_option; subst;
    rewrite ?Z.ldiff_ones_r, ?Z.land_ones, ?Z.ones_equiv;
    cbv [Z.b2z];
    try match goal with |- context [(?a mod ?b)%Z] => unshelve epose proof Z.mod_pos_bound a b ltac:(eapply Z.pow_pos_nonneg; Lia.lia) end;
    repeat t;
    try (Z.div_mod_to_equations; Lia.lia).
  { clear dependent args'0.
    epose proof bound_sum' _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption).
    split; try Lia.lia.
    eapply Z.min_glb_iff; split; try Lia.lia.
    etransitivity. eapply Zmod_le.
    all : try Lia.lia. }
  Unshelve. {
    repeat t.
    pose proof Z.log2_nonneg z; pose proof Z.log2_nonneg z0.
    rewrite !Z.shiftl_0_r.
    split.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    eapply Z.le_bitwise.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg;
        left; try eapply Z.ones_nonneg; Lia.lia. }
    { intros i Hi.
      Z.rewrite_bitwise.
      destr (i <? Z.of_N sz);
        rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r.
      { clear -H Hi.
        destr (i <? Z.succ (Z.log2 z0)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H as [H' H]; eapply Z.log2_le_mono in H. Lia.lia. }
      { clear -H0 Hi.
        destr (i <? Z.succ (Z.log2 z)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H0 as [? H0]; eapply Z.log2_le_mono in H0. Lia.lia. } } }
Qed.

Lemma bound_sum G d es
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  : (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof using Type.
  eapply bound_sum' in Hb; eauto.
  eapply Forall_forall; intros.
  eapply eval_bound_expr; eauto.
Qed.

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

Lemma eval_permute_commutative ctx d o args1 args2 n :
  commutative o = true ->
  Permutation.Permutation args1 args2 ->
  eval ctx d (ExprApp (o, args1)) n ->
  eval ctx d (ExprApp (o, args2)) n.
Proof.
  intros. inv H1. apply (Permutation_Forall2 H0) in H4.
  destruct H4 as [args2' [H4 H5] ]. apply EApp with (args' := args2').
  - assumption.
  - apply permute_commutative with (args := args'); assumption.
Qed.

Definition bounds_ok (d : dag) := forall G i n, eval G d (ExprRef i) n -> in_bounds n (dag.lookup_bounds d i).
(* the gensym state cannot map anything past the end of the dag *)
Definition gensym_ok (G : symbol -> option Z) (d : dag) := forall s _v, G s = Some _v -> (s < dag.size d)%N.
Definition dag_ok G (d : dag) := bounds_ok d /\ dag.ok d /\ dag.all_nodes_ok d /\ forall i r, dag.lookup d i = Some r -> exists v, eval G d (ExprRef i) v.
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

  cbv [bounds_ok]. intros. inv H. rewrite dag.lookup_empty in H1. discriminate H1.
Qed.

Lemma split_lookup_bounds d1 d2 i :
  dag.lookup_bounds (d1 ++ d2) i = if N.ltb i (dag.size d1) then dag.lookup_bounds d1 i else dag.lookup_bounds d2 (i - dag.size d1)%N.
Proof.
  destruct (i <? dag.size d1)%N eqn:E.
  - cbv [dag.lookup_bounds]. rewrite nth_error_app. destruct (lt_dec _ _).
    + reflexivity.
    + apply N.ltb_lt in E. exfalso. apply n. cbv [dag.size] in E. lia.
  - cbv [dag.lookup_bounds]. rewrite nth_error_app. destruct (lt_dec _ _).
    + apply N.ltb_nlt in E. exfalso. apply E. cbv [dag.size]. lia.
    + cbv [dag.size]. replace (N.to_nat (i - N.of_nat (Datatypes.length d1))) with (N.to_nat i - Datatypes.length d1)%nat by lia. reflexivity.
Qed.

Lemma split_lookup d1 d2 i :
  dag.lookup (d1 ++ d2) i = if N.ltb i (dag.size d1) then dag.lookup d1 i else dag.lookup d2 (i - dag.size d1)%N.
Proof.
  destruct (i <? dag.size d1)%N eqn:E.
  - cbv [dag.lookup]. rewrite nth_error_app. destruct (lt_dec _ _).
    + reflexivity.
    + apply N.ltb_lt in E. exfalso. apply n. cbv [dag.size] in E. lia.
  - cbv [dag.lookup]. rewrite nth_error_app. destruct (lt_dec _ _).
    + apply N.ltb_nlt in E. exfalso. apply E. cbv [dag.size]. lia.
    + cbv [dag.size]. replace (N.to_nat (i - N.of_nat (Datatypes.length d1))) with (N.to_nat i - Datatypes.length d1)%nat by lia. reflexivity.
Qed.

Lemma something ctx G d1 d2 i v n0 :
  eval ctx d1 (ExprRef i) v ->
  eval G (d1 ++ d2) (ExprRef i) n0 ->
  eval G d1 (ExprRef i) n0.
Proof.
  intros. generalize dependent n0. remember (ExprRef i) as e. generalize dependent i. induction H.
  - intros. inv H2. rewrite split_lookup in H4. destruct (i <? dag.size d1)%N eqn:E.
    + rewrite H4 in H. clear E. inv H. apply ERef with (op := op0) (args := args) (args' := args'0).
      -- apply H4.
      -- clear H4 H1 H6. generalize dependent args'. generalize dependent args'0. induction args as [| arg morargs IHmorargs].
        ++ intros. inv H5. constructor.
        ++ intros. simpl in *. inv H5. inv H0. destruct H3 as [H3 H5]. constructor.
          --- apply H5 with (i := arg); try reflexivity. apply H2.
          --- apply IHmorargs with (args' := l'0).
            +++ assumption.
            +++ assumption.
      -- assumption.
    + exfalso. clear H0 H1 H4 H5 H6 n0 op1 args0 args'0. cbv [dag.lookup] in H. destruct (nth_error _ _) as [sth|] eqn:E'.
      -- clear H. apply N.ltb_nlt in E. apply E; clear E. cbv [dag.size]. apply nth_error_value_length in E'.
         lia.
      -- discriminate.
  - intros. discriminate Heqe.
Qed.

Lemma much_something ctx d1 d2 args' args G :
  (forall (i : idx) (r : node idx), dag.lookup d1 i = Some r -> exists v : Z, eval ctx d1 (ExprRef i) v) ->
  Forall (fun j : N => (j < dag.size d1)%N) args ->
  Forall2 (eval G (d1 ++ d2)) (map ExprRef args) args' ->
  Forall2 (eval G d1) (map ExprRef args) args'.
Proof.
  intros. generalize dependent args'. induction args as [| arg args1 IHargs1].
  - intros. inv H1. constructor.
  - intros. inv H0. inv H1. constructor.
    + clear IHargs1 H7 H5. remember H3 as H3'; clear HeqH3'. inv H3. rewrite split_lookup in H1.
      destruct (arg <? dag.size d1)%N eqn:E.
      -- clear E H4. apply H in H1. clear H. destruct H1 as [v H1]. apply something with (ctx := ctx) (d2 := d2) (v := v); assumption.
      -- exfalso. apply N.ltb_nlt in E. apply E. apply H4.
    + apply IHargs1; assumption.
Qed.

Lemma node_doesnt_reference_self G d o args i n :
  eval G d (ExprRef i) n ->
  dag.lookup d i = Some (o, args) ->
  Forall (fun j => j <> i) args.
Proof.
  intros. remember (ExprRef i) as e. rewrite Forall_Exists_neg. intros H3. induction H.
  - inv Heqe. rewrite H0 in H. inv H. clear H0.
    assert (H4: forall a b, (fun (e : expr) (n : Z) => eval G d e n /\ (e = ExprRef i -> False)) a b ->
                            (fun (e : expr) (n : Z) => (e = ExprRef i -> False)) a b) by intuition.
    apply (Forall2_weaken H4) in H1. clear H4. apply Forall2_Forall_ignore_l in H1. destruct H1 as [_ H1].
    apply Exists_exists in H3. rewrite Forall_map in H1. rewrite Forall_forall in H1. destruct H3 as [x [H3 H4] ].
    apply H1 with (x := x).
    + assumption.
    + f_equal. assumption.
  - discriminate Heqe.
Qed.

Lemma args_in_bounds G d o args i n :
  eval G d (ExprRef i) n ->
  dag.lookup d i = Some (o, args) ->
  Forall (fun j => N.lt j (dag.size d)) args.
Proof.
  intros. inv H. rewrite H0 in H2. inv H2. clear H0 H4. generalize dependent args'.
  induction args0 as [| arg0 args0' IHargs0'].
  - constructor.
  - intros. inv H3. constructor.
    + inv H1. cbv [dag.size]. assert (N.to_nat arg0 < Datatypes.length d)%nat; try lia. cbv [dag.lookup] in H0.
      destruct (nth_error _ _) as [sth|] eqn:E; try discriminate H0. clear H0. apply nth_error_value_length with (x := sth).
      assumption.
    + apply IHargs0' with (args' := l'). apply H4.
Qed.

Lemma merge_node_bounds_ok {descr : description} ctx d n :
  dag_ok ctx d ->
  bounds_ok (snd (dag.merge_node n d)).
Proof.
  intros. cbv [dag_ok] in H. destruct H as [H1 [_ [_ H2] ] ].
  cbv [bounds_ok] in *. intros. destruct n as [o args].
  remember (dag.merge_node (o, args) d) as i_d'. cbv [dag.merge_node] in Heqi_d'.
  destruct (dag.reverse_lookup _ _) as [new_i|].
  - subst. simpl in *. apply H1 with (G := G). apply H.
  - subst. simpl in *. remember H as H'; clear HeqH'. inv H. rewrite split_lookup_bounds. remember H3 as H3'; clear HeqH3'.
    rewrite split_lookup in H3.
    destruct (i <? dag.size d)%N eqn:E'.
    + remember (H2 _ _ H3) as H6; clear HeqH6 H2. destruct H6 as [v H6]. apply (something _ _ _ _ _ _ _ H6) in H'.
      apply H1 with (G := G). apply H'.
    + remember (map _ _) as no. cbv [dag.lookup_bounds]. subst. cbv [dag.lookup] in H3.
      destruct (N.to_nat _) as [| [| n''] ] eqn:E''; try discriminate H3. simpl in H3. simpl. inv H3.
      apply N.ltb_nlt in E'. assert (E1'': i = dag.size d) by lia.
      clear E' E''. subst. remember H' as H''; clear HeqH''. inv H'. rewrite H0 in H3'. inv H3'. clear H3 H6.
      remember (node_doesnt_reference_self _ _ _ _ _ _ H'' H0) as H3; clear HeqH3.
      remember (args_in_bounds _ _ _ _ _ _ H'' H0) as H6; clear HeqH6.
      assert (E: Forall (fun j : N => N.lt j (dag.size d)) args0).
      { rewrite Forall_forall in H3. rewrite Forall_forall in H6. rewrite Forall_forall. intros.
        remember (H3 _ H) as H7; clear HeqH7. apply H6 in H. cbv [dag.size] in H.
        rewrite app_length in H. simpl in H. cbv [dag.size] in H7. cbv [dag.size]. clear H4 H5 H'' H0 H3 H6. lia. }
      apply (much_something _ _ _ _ _ _ H2 E) in H4.
      apply interp_bound_node with (ctx := G) (args := args').
      -- clear H2 E H5 H3 H6 H0 H''. generalize dependent args'. induction args0 as [| arg0 args0' IHargs0'].
        ++ intros. inv H4. constructor.
        ++ intros. inv H4. constructor.
          --- apply H1 with (G := G). apply H2.
          --- apply IHargs0'. apply H5.
      -- assumption.
Qed.

Lemma eval_merge_node {descr descr' descr'' descr'''} :
  forall G d, gensym_dag_ok G d ->
  forall op args n, let e := (op, args) in
  eval G d (ExprApp (op, List.map ExprRef args)) n ->
  eval G (snd (@merge_node descr e d)) (ExprRef (fst (@merge_node descr' e d))) n /\
  gensym_dag_ok G (snd (@merge_node descr'' e d)) /\
  forall i e', eval G d i e' -> eval G (snd (@merge_node descr''' e d)) i e'.
Proof using Type.
  intros. destruct H as [H H'].
  cbv beta delta [merge_node].
  inversion H0; subst.
  cbv [gensym_dag_ok dag_ok] in *; destruct_head'_and.
  repeat match goal with |- _ /\ _ => split end; try exact _.
  1: econstructor; try eassumption.
  all: eauto using Forall2_weaken, eval_weaken_merge_node.
  all: try now apply gensym_ok_merge_node.
  { now rewrite dag.lookup_merge_node' by assumption. }
  { apply merge_node_bounds_ok with (ctx := G); repeat (try split; try assumption). }
  { apply @dag.merge_node_all_nodes_ok; try assumption.
    cbv [e node_ok]; intros; inversion_pair; subst; cbn [interp_op] in *.
    break_innermost_match_hyps; inversion_option; subst.
    cbv [gensym_ok] in *.
    specialize_under_binders_by eassumption; lia. }
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

(* begin addcarry stuff *)

Print bound_node.

Fixpoint bound_expr' d e : option (Z * Z) :=
  match e with
  | ExprApp (o, args) => bound_node o (map (bound_expr' d) args)
  | ExprRef i => dag.lookup_bounds d i
  end.

Search bound_node.
Check eval.

Lemma eval_bound_expr' ctx d e :
  bounds_ok d ->
  forall n,
  eval ctx d e n ->
  forall l u,
  bound_expr' d e = Some (l, u) ->
  l <= n <= u.
Proof.
  intros H_ok. unfold bounds_ok in H_ok. induction e.
  - intros n H2 l u H1. simpl in H1. apply H_ok in H2. unfold in_bounds in H2. rewrite H1 in H2. apply H2.
  - intros n_ H2 l u H1. clear H_ok. inv H2. simpl in H. simpl in H1. Search bound_node.
    assert (Forall2 in_bounds args' (map (bound_expr' d) args)).
    + clear H4 H1. generalize dependent args'. induction args as [|arg args1 IHargs1].
      -- intros args' H2. inv H2. simpl. constructor.
      -- intros args' H2. inv H. inv H2. simpl. constructor.
        ++ clear IHargs1 H6 H4. cbv [in_bounds]. destruct (bound_expr' d arg) eqn:E; try reflexivity.
           destruct p as [min max]. apply H3.
          --- assumption.
          --- reflexivity.
        ++ apply IHargs1; clear IHargs1.
          --- assumption.
          --- assumption.
    + Search bound_node. apply (interp_bound_node _ _ _ _ _ H0) in H4. rewrite H1 in H4. simpl in H4. apply H4.
Qed.

Definition is_bounded_by (d : dag) (m : Z) (i : idx) : bool :=
  match dag.lookup_bounds d i with (* we only reveal one layer here.  That could be changed. *)
  | None => false
  | Some bounds => subset bounds (0, m)
  end.

(* range of addends does not matter. *)
Fixpoint list_of_addends (d : dag) (f : nat) (s : OperationSize) (i : idx) : list idx :=
  match f with
  | S f' =>
    match dag.lookup d i with
    | Some (o, args) =>
        match o with
        | add s' => if N.leb s s' then fold_right (@app idx) [] (map (list_of_addends d f' s) args) else [i]
        | addZ => fold_right (@app idx) [] (map (list_of_addends d f' s) args)
        | _ => [i]
        end
    | None => [i]
    end
  | O => [i]
  end.

Local Open Scope Z_scope.

Lemma break_addZ_small : forall l1 l2,
  (fold_right Z.add 0 l1) + (fold_right Z.add 0 l2) = fold_right Z.add 0 (l1 ++ l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- IHl1. lia.
Qed.

Lemma break_add (m1 m2 n : Z) ctx d s l1 l2:
  interp_op (fun _ => None) (add s) [m1; m2] = Some n ->
  eval ctx d (ExprApp (add s, l1)) m1 ->
  eval ctx d (ExprApp (add s, l2)) m2 ->
  eval ctx d (ExprApp (add s, l1 ++ l2)) n.
Proof.
  simpl. intros. inversion H0; subst. inversion H1; subst.
  apply (EApp _ _ _ _ (args' ++ args'0)).
  - apply Forall2_app.
    + apply H4.
    + apply H5.
  - simpl. f_equal. injection H as H. rewrite <- H. injection H6 as H6. injection H8 as H8.
    rewrite <- H6. rewrite <- H8. rewrite Z.add_0_r. repeat rewrite Z_land_ones'. rewrite <- break_addZ_small.
    rewrite <- PullPush.Z.add_mod_full. reflexivity.
Qed.

Lemma break_addZ (m1 m2 n : Z) ctx d l1 l2:
  interp_op (fun _ => None) addZ [m1; m2] = Some n ->
  eval ctx d (ExprApp (addZ, l1)) m1 ->
  eval ctx d (ExprApp (addZ, l2)) m2 ->
  eval ctx d (ExprApp (addZ, l1 ++ l2)) n.
Proof.
  simpl. intros. inversion H0; subst. inversion H1; subst.
  apply (EApp _ _ _ _ (args' ++ args'0)).
  - apply Forall2_app.
    + apply H4.
    + apply H5.
  - simpl. f_equal. injection H as H. rewrite <- H. injection H6 as H6. injection H8 as H8.
    rewrite <- H6. rewrite <- H8. symmetry. rewrite Z.add_0_r. apply break_addZ_small.
Qed.

Lemma break_add_backwards (n : Z) ctx d s l1 l2:
  eval ctx d (ExprApp (add s, l1 ++ l2)) n ->
  exists m1 m2,
  interp_op (fun _ => None) (add s) [m1; m2] = Some n /\
  eval ctx d (ExprApp (add s, l1)) m1 /\
  eval ctx d (ExprApp (add s, l2)) m2.
Proof.
  intros. inversion H; subst. apply Forall2_app_inv_l in H2.
  destruct H2 as [l1' [l2' [H1 [H2 H3] ] ] ].
  assert (E1: exists m1, interp_op ctx (add s) l1' = Some m1). { simpl. eauto. }
  assert (E2: exists m2, interp_op ctx (add s) l2' = Some m2). { simpl. eauto. }
  destruct E1 as [m1 E1]. destruct E2 as [m2 E2].
  exists m1. exists m2. split.
  - simpl. f_equal. rewrite Z.add_0_r. simpl in H4. injection H4 as H4. simpl in E1. simpl in E2. subst.
    injection E1 as E1. injection E2 as E2. subst. repeat rewrite Z_land_ones'. rewrite <- break_addZ_small.
    rewrite <- PullPush.Z.add_mod_full. reflexivity.
  - split.
    + apply EApp with (args' := l1'); assumption.
    + apply EApp with (args' := l2'); assumption.
Qed.

Lemma break_addZ_backwards (n : Z) ctx d l1 l2:
  eval ctx d (ExprApp (addZ, l1 ++ l2)) n ->
  exists m1 m2,
  interp_op (fun _ => None) addZ [m1; m2] = Some n /\
  eval ctx d (ExprApp (addZ, l1)) m1 /\
  eval ctx d (ExprApp (addZ, l2)) m2.
Proof.
  intros. inversion H; subst. apply Forall2_app_inv_l in H2.
  destruct H2 as [l1' [l2' [H1 [H2 H3] ] ] ].
  assert (E1: exists m1, interp_op ctx (addZ) l1' = Some m1). { simpl. eauto. }
  assert (E2: exists m2, interp_op ctx (addZ) l2' = Some m2). { simpl. eauto. }
  destruct E1 as [m1 E1]. destruct E2 as [m2 E2].
  exists m1. exists m2. split.
  - simpl. f_equal. rewrite Z.add_0_r. simpl in H4. injection H4 as H4. simpl in E1. simpl in E2. subst.
    injection E1 as E1. injection E2 as E2. subst. rewrite <- break_addZ_small. reflexivity.
  - split.
    + apply EApp with (args' := l1'); assumption.
    + apply EApp with (args' := l2'); assumption.
Qed.

Lemma app_is_cons {X} (x : X) (l : list X):
  x :: l = [x] ++ l.
Proof. reflexivity. Qed.

Lemma and_pos : forall x y,
  Z.le 0 y -> Z.le 0 (Z.land x y).
Proof.
  intros. cbv [Z.land]. destruct x as [| a| a]; destruct y as [| b| b]; lia.
Qed.

Lemma le_and_ones y n:
  Z.le 0 y /\ Z.le y (Z.ones (Z.of_N n)) -> Z.land y (Z.ones (Z.of_N n)) = y.
Proof.
  intros. assert (E: Z.le 0 (Z.of_N n)) by lia. apply (Z.land_ones y) in E.
  rewrite E. clear E. apply Z.mod_small. cbv [Z.ones] in H. rewrite Z.shiftl_1_l in H.
  lia.
Qed.

Lemma small_sum ctx s0 args' y:
  interp_op ctx (add s0) args' = Some y ->
   Z.le 0 y /\ Z.le y (Z.ones (Z.of_N s0)).
Proof.
  intros. simpl in H. injection H as H. split.
  - rewrite <- H. apply and_pos. apply Z.ones_nonneg. lia.
  - assert (H' : (0 <= Z.of_N s0)%Z) by lia. apply (Z.land_ones (fold_right Z.add 0%Z args')) in H'.
    rewrite H in H'. clear H. remember (fold_right Z.add 0%Z args') as sth. clear Heqsth. assert (H'' : (2 ^ Z.of_N s0 > 0)%Z).
    + lia.
    + apply (Z_mod_lt sth) in H''. destruct H'' as [_ H'']. subst. cbv [Z.ones]. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma collapse_op ctx d i n op args:
  eval ctx d (ExprRef i) n ->
  dag.lookup d i = Some (op, args) ->
  eval ctx d (ExprApp (op, map ExprRef args)) n.
Proof.
  intros.
  inv H. rewrite H0 in H2. clear H0. injection H2; clear H2; intros; subst.
  apply EApp with (args' := args'); assumption.
Qed.

Lemma collapse_op' ctx d i n op1 op2 args:
  eval ctx d (ExprApp (op1, [ExprRef i])) n ->
  dag.lookup d i = Some (op2, args) ->
  eval ctx d (ExprApp (op1, [ExprApp (op2, map ExprRef args)])) n.
Proof.
  intros.
  inv H. inv H3. apply (collapse_op _ _ _ _ _ _ H2) in H0. inv H6.
  apply EApp with (args' := [y]).
  - constructor.
    + assumption.
    + constructor.
  - assumption.
Qed.

Lemma mod_add_eq ctx d i n m s:
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, [ExprRef i])) m ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. simpl in H0. inv H0. inv H3. inv H6. apply (eval_eval _ _ _ _ H) in H2. clear H.
  subst. injection H5 as H5. subst. rewrite Z_land_ones'. f_equal. lia.
Qed.

Lemma mod_add_eq'' ctx d i n s:
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, [ExprRef i])) (n mod 2 ^ Z.of_N s).
Proof.
  intros. apply EApp with (args' := [n]).
  - constructor.
    + apply H.
    + constructor.
  - simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. reflexivity.
Qed.

(* Lemma mod_add_eq''_backwards ctx d i n s:
  eval ctx d (ExprApp (add s, [ExprRef i])) (n mod 2 ^ Z.of_N s) ->
  eval ctx d (ExprRef i) n.
Proof.
  intros. inv H. inv H2. inv H5. simpl in H4. injection H4 as H4. rewrite Z.add_0_r in H4.
  rewrite Z_land_ones' in H4. apply EApp with (args' := [n]).
  - constructor.
    + apply H.
    + constructor.
  - simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. reflexivity.
Qed. *)

Lemma mod_add_eq_backwards ctx d i m s:
  eval ctx d (ExprApp (add s, [ExprRef i])) m ->
  exists n,
  eval ctx d (ExprRef i) n /\
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H. inv H2. inv H5. exists y. split.
  - apply H1.
  - injection H4 as H4. rewrite <- H4. rewrite Z_land_ones'. f_equal; lia.
Qed.

Lemma mod_addZ_eq_backwards ctx d i m:
  eval ctx d (ExprApp (addZ, [ExprRef i])) m ->
  exists n,
  eval ctx d (ExprRef i) n /\
  n = m.
Proof.
  intros. inv H. inv H2. inv H5. exists y. split.
  - apply H1.
  - injection H4 as H4. rewrite <- H4. lia.
Qed.

Lemma mod_add_eq' ctx d n m s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s, args)) m ->
  eval ctx d (ExprApp (add s0, args)) n ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H0. inv H1. apply (eval_eval_Forall2 _ _ _ _ H4) in H3. subst. clear H4.
  injection H6 as H6. injection H7 as H7. rewrite <- H6. rewrite <- H7. clear H6 H7.
  rewrite <- Z_land_ones'. rewrite <- Z.land_assoc. rewrite Z.land_ones_ones.
  replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
  replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia. reflexivity.
Qed.

Lemma mod_add_eq''' ctx d n s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s0, args)) n ->
  eval ctx d (ExprApp (add s, args)) (n mod 2 ^ Z.of_N s).
Proof.
  intros. inv H0. apply EApp with (args' := args').
  - assumption.
  - simpl. f_equal. injection H5 as H5; subst. clear H3.
    rewrite <- Z_land_ones'. rewrite <- Z.land_assoc. rewrite Z.land_ones_ones.
    replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
    replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia. reflexivity.
Qed.

Lemma mod_addZ_eq''' ctx d n s args:
  eval ctx d (ExprApp (addZ, args)) n ->
  eval ctx d (ExprApp (add s, args)) (n mod 2 ^ Z.of_N s).
Proof.
  intros. inv H. apply EApp with (args' := args').
  - assumption.
  - simpl. f_equal. injection H4 as H4; subst. clear H2.
    rewrite <- Z_land_ones'. reflexivity.
Qed.

Lemma mod_add_eq'''_backwards ctx d n s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s, args)) n ->
  exists m,
  eval ctx d (ExprApp (add s0, args)) m /\
  n = m mod (2 ^ Z.of_N s).
Proof.
  intros. inv H0. simpl in H5. exists (Z.land (fold_right Z.add 0 args') (Z.ones (Z.of_N s0))). split.
  - apply EApp with (args' := args').
    + assumption.
    + reflexivity.
  - rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.
    repeat rewrite Z.land_ones_ones.
    replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
    replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.
    injection H5 as H5; subst. reflexivity.
Qed.

Lemma mod_addZ_eq'''_backwards ctx d n s args:
  eval ctx d (ExprApp (add s, args)) n ->
  exists m,
  eval ctx d (ExprApp (addZ, args)) m /\
  n = m mod (2 ^ Z.of_N s).
Proof.
  intros. inv H. simpl in H4. exists (fold_right Z.add 0 args'). split.
  - apply EApp with (args' := args').
    + assumption.
    + reflexivity.
  - injection H4 as H4; subst. rewrite <- Z_land_ones'. reflexivity.
Qed.

Lemma mod_addZ_eq' ctx d n m s args:
  eval ctx d (ExprApp (add s, args)) m ->
  eval ctx d (ExprApp (addZ, args)) n ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H. inv H0. apply (eval_eval_Forall2 _ _ _ _ H2) in H3. subst. clear H2.
  injection H5 as H5. injection H6 as H6. rewrite <- H5. rewrite <- H6. clear H5 H6.
  rewrite <- Z_land_ones'. reflexivity.
Qed.

Lemma eval_list_of_addends'' (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) (n mod (2 ^ Z.of_N s)).
Proof.
  induction f as [| f' IHf'].
  - intros. simpl. apply (mod_add_eq'' _ _ _ _ _ H).
  - intros. simpl. destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply (mod_add_eq'' _ _ _ _ _ H).
    + destruct o; try apply (mod_add_eq'' _ _ _ _ _ H).
      -- destruct (s <=? s0)%N eqn:E; try apply (mod_add_eq'' _ _ _ _ _ H). apply N.leb_le in E.
         apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl. apply (mod_add_eq''' _ _ _ _ _ _ E E1).
        ++ intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
           apply break_add_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           injection H4 as H4; subst.
           apply (mod_add_eq''' _ _ _ _ _ _ E) in H5. apply (mod_add_eq''' _ _ _ _ _ _ E) in H6.
           apply mod_add_eq_backwards in H5. destruct H5 as [n1' [H5 H5'] ].
           apply (mod_add_eq'''_backwards _ _ _ _ _ _ E) in H6.
           destruct H6 as [n2' [H6 H6'] ].
           apply (break_add (n1' mod 2 ^ Z.of_N s) (n2' mod (2 ^ Z.of_N s))).
           --- simpl. f_equal. repeat rewrite Z_land_ones'. repeat rewrite Z.add_0_r. rewrite <- Zplus_mod.
               repeat rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.
               repeat rewrite Z.land_ones_ones.
           replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
           replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.

           repeat rewrite Z_land_ones'. rewrite Zplus_mod. rewrite H5'. rewrite <- H6'. (*  rewrite Z.mod_mod by lia.  *)rewrite <- Zplus_mod. reflexivity.
           --- apply IHf'. apply H5.
           --- apply IHargs1. apply H6.
      -- apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl. apply (mod_addZ_eq''' _ _ _ _ _ E1).
        ++ intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
           apply break_addZ_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           injection H4 as H4; subst.
           apply mod_addZ_eq''' with (s := s) in H5. apply mod_addZ_eq''' with (s := s) in H6.
           apply mod_add_eq_backwards in H5. destruct H5 as [n1' [H5 H5'] ].
           apply (mod_addZ_eq'''_backwards) in H6.
           destruct H6 as [n2' [H6 H6'] ].
           apply (break_add (n1' mod 2 ^ Z.of_N s) (n2' mod (2 ^ Z.of_N s))).
           --- simpl. f_equal. repeat rewrite Z_land_ones'. repeat rewrite Z.add_0_r. rewrite H5'. rewrite <- H6'. rewrite <- Zplus_mod.
               reflexivity.
           --- apply IHf'. apply H5.
           --- apply IHargs1. apply H6.
Qed.

Fixpoint withadc_without (d : dag) (s : OperationSize) (args : list idx) : (list (list (list idx))) * (list idx) :=
  match args with
  | [] => ([], [])
  | i :: args' =>
    let (withadc', without') := withadc_without d s args' in
    match dag.lookup d i with
    | Some (o, args'') =>
      match o, args'' with
      | addcarry s', (x :: y :: []) =>
        if N.eqb s' s && fold_right andb true (map (is_bounded_by d (2 ^ Z.of_N s - 1)) [x; y]) then
          (map (list_of_addends d (N.to_nat (dag.size d)) s) [x; y] :: withadc', without')
        else
          (withadc', i :: without')
      | _, _ => (withadc', i :: without')
      end
    | None => (withadc', i :: without')
    end
  end.

Definition expr_of_a_carry (s : OperationSize) (carry : list (list idx)) : expr :=
  let with_small_adds := map (fun addends => ExprApp (add s, map ExprRef addends)) carry in
  ExprApp (shrZ, [ExprApp (addZ, with_small_adds); ExprApp (const (Z.of_N s), [])]).

Lemma eval_is_bounded_by ctx d m x i :
  bounds_ok d ->
  is_bounded_by d m i = true ->
  eval ctx d (ExprRef i) x ->
  0 <= x <= m.
Proof.
  intros. apply H in H1. cbv [is_bounded_by] in H0. destruct (dag.lookup_bounds d i) as [bounds|]; try discriminate H0.
  apply subset_bounds in H0. cbv [in_bounds] in H1. destruct bounds as [min max]. simpl in H0.  lia.
Qed.

Lemma eval_expr_of_a_carry'' ctx d s f arg1 arg2 n :
  bounds_ok d ->
  is_bounded_by d (2 ^ Z.of_N s - 1) arg1 = true ->
  is_bounded_by d (2 ^ Z.of_N s - 1) arg2 = true ->
  eval ctx d (ExprApp (addcarry s, map ExprRef [arg1; arg2])) n ->
  eval ctx d (expr_of_a_carry s (map (list_of_addends d f s) [arg1; arg2])) n.
Proof.
  simpl. intros H_bounds E1 E2. cbv [expr_of_a_carry]. simpl. intros. inv H.
  inv H2. inv H5. inv H6.
  remember (eval_is_bounded_by _ _ _ _ _ H_bounds E1 H1) as E1'. clear HeqE1' E1.
  remember (eval_is_bounded_by _ _ _ _ _ H_bounds E2 H2) as E2'. clear HeqE2' E2.
  apply eval_list_of_addends'' with (s := s) (f := f) in H1.
  apply eval_list_of_addends'' with (s := s) (f := f) in H2.
  apply EApp with (args' := [(y mod 2 ^ Z.of_N s) + (y0 mod 2 ^ Z.of_N s); Z.of_N s]).
  - apply Forall2_cons.
    + apply EApp with (args' := [y mod 2 ^ Z.of_N s; y0 mod 2 ^ Z.of_N s]).
      -- apply Forall2_cons.
        ++ apply H1.
        ++ apply Forall2_cons.
          --- apply H2.
          --- apply Forall2_nil.
      -- simpl. f_equal. lia.
    + apply Forall2_cons.
      -- apply EApp with (args' := []).
        ++ apply Forall2_nil.
        ++ simpl. reflexivity.
      -- apply Forall2_nil.
  - simpl. f_equal. injection H4 as H4; subst. rewrite Z.add_0_r. repeat rewrite Z.mod_small by lia.
    destruct E1' as [E1 E1']. destruct E2' as [E2 E2'].
    assert (E : y + y0 < 2 * (2 ^ Z.of_N s)) by lia. assert ((y + y0) / 2 ^ Z.of_N s < 2).
    { apply Z.div_lt_upper_bound; lia. }
    repeat rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small. split.
    + apply Z.div_pos; lia.
    + apply H.
Qed.

Definition exprs_of_carries (s : OperationSize) (carries : list (list (list idx))) : list expr :=
  map (expr_of_a_carry s) carries.

Lemma evalZ_withadc_without (ctx : symbol -> option Z) (d : dag) (s : OperationSize):
  bounds_ok d ->
  forall args n,
  eval ctx d (ExprApp (addZ, map ExprRef args)) n ->
  let (withadc, without) := withadc_without d s args in
  eval ctx d (ExprApp (addZ, map ExprRef without ++ exprs_of_carries s withadc)) n.
Proof.
  intros H_bounds args. induction args as [| i args'].
  - simpl. intros. apply H.
  - destruct (withadc_without d s (i :: args')) as [withadc without] eqn:E. simpl in E.
    destruct (withadc_without d s args') as [withadc' without'] eqn:E1.
    intros.
    assert (Lemma: (withadc, without) = (withadc', i :: without') ->
                   eval ctx d (ExprApp (addZ, map ExprRef without ++ exprs_of_carries s withadc)) n).
    { clear E. intros E. injection E as E E'. rewrite E in *. rewrite E' in *. clear E E'.

      rewrite app_is_cons in H. rewrite map_app in H. apply break_addZ_backwards in H.
      destruct H as [n_0 [n_1 [H2 [H3 H4] ] ] ]. simpl in H2. injection H2 as H2. subst.
      apply IHargs' in H4. clear IHargs'.

      simpl. rewrite app_is_cons. apply break_addZ with (m1 := n_0) (m2 := n_1).
      - simpl. reflexivity.
      - assumption.
      - assumption.
    }
    destruct (dag.lookup d i) as [ [op op_args]|] eqn:E_dlook.
    + destruct op_args as [| arg1 [| arg2 [| arg3 op_args'] ] ] eqn:E_op_args.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- destruct op; try (apply Lemma; rewrite <- E; reflexivity).
         destruct (s0 =? s)%N eqn:Es; destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg1) eqn:Eb1;
         destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg2) eqn:Eb2; try (apply Lemma; rewrite <- E; reflexivity).
         clear Lemma. simpl in E. injection E as E E_. apply N.eqb_eq in Es. subst.
         simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H.
         destruct H as [n_0 [n_1 [H1 [H2 H3] ] ] ]. apply IHargs' in H3. clear IHargs'.
         apply break_addZ_backwards in H3. destruct H3 as [n_1_0 [n_1_1 [H3 [H4 H5] ] ] ].
         injection H1 as H1; subst. injection H3 as H3; subst.
         apply break_addZ with (m1 := n_1_0) (m2 := n_0 + n_1_1 + 0).
         ++ simpl. f_equal. lia.
         ++ apply H4.
         ++ simpl. rewrite app_is_cons. apply break_addZ with (m1 := n_0) (m2 := n_1_1).
           --- simpl. f_equal. lia.
           --- inv H2. inv H1. inv H7. injection H6 as H6; subst.
               apply (collapse_op _ _ _ _ _ _ H2) in E_dlook. clear H2.
               apply EApp with (args' := [y]).
              +++ constructor.
                ---- apply eval_expr_of_a_carry''; assumption.
                ---- constructor.
              +++ simpl. reflexivity.
           --- assumption.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
    + apply Lemma. rewrite E. reflexivity.
Qed.

Local Open Scope nat_scope.

Require Import Coq.Sorting.Mergesort.

Module listAddendListOrder <: TotalLeBool.
  Definition t : Type := list (list idx).
  Fixpoint total_length {X} (l : list (list X)) : nat :=
    match l with
    | [] => O
    | x :: l' => length x + total_length l'
    end.
  Definition leb (x y : t) : bool :=
    total_length x <=? total_length y.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall x y, x <=? y = true \/ y <=? x = true.
  Proof. intros. unfold leb. repeat rewrite Nat.leb_le. lia. Qed.
End listAddendListOrder.
Module Import listAddendListSort := Sort listAddendListOrder.

Definition merge_list (l : list (list idx)) : list idx :=
  let l' := fold_right (@app idx) [] l in
  N.sort l'.

(* for example, insert_small [[6], [7]] [[[6, 7], [8]], ...] => [[[6], [7], [8]], ...] *)
Fixpoint insert_small (small : list (list idx)) (big : list (list idx)) (* : option (list (list idx)) *) :=
  let small_all := merge_list small in
  match big with
  | [] => None
  | maybe_small :: big' =>
    if (list_beq N (N.eqb) maybe_small (merge_list small))
    then
      Some (small ++ big')
    else
      match insert_small small big' with
      | Some new_big' => Some (maybe_small :: new_big')
      | None => None
      end
  end.

Lemma lists_equal (l1 l2 : list N) :
  l1 = l2 <->
  list_beq N N.eqb l1 l2 = true.
Proof.
  intros. apply Bool.reflect_iff. apply reflect_eq_list.
Qed.

Local Open Scope Z_scope.

Lemma break_expr_of_a_carry' ctx d s l1 l2 n1 n2 :
  eval ctx d (expr_of_a_carry s l1) n1 ->
  eval ctx d (expr_of_a_carry s l2) n2 ->
  exists m1 m2,
  n1 = m1 / 2 ^ Z.of_N s /\
  n2 = m2 / 2 ^ Z.of_N s /\
  eval ctx d (expr_of_a_carry s (l1 ++ l2)) ((m1 + m2) / 2 ^ Z.of_N s).
Proof.
  intros.
  inv H. inv H3. inv H6. inv H7.
  inv H3. inv H4. inv H7. rename y into m1.
  inv H0. inv H3. inv H7. inv H8.
  inv H3. inv H4. inv H8. inv H6. inv H5. rename y into m2.
  exists m1. exists m2. split.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - split.
    + rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    + cbv [expr_of_a_carry]. apply EApp with (args' := [m1 + m2; Z.of_N s]).
      -- constructor.
        ++ rewrite map_app. apply break_addZ with (m1 := m1) (m2 := m2).
          --- simpl. f_equal. lia.
          --- assumption.
          --- assumption.
        ++ constructor.
          --- apply EApp with (args' := []).
            +++ constructor.
            +++ reflexivity.
          --- constructor.
      -- simpl. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma eval_app_list ctx d s small n :
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) small)) n ->
  eval ctx d (ExprApp (add s, map ExprRef (fold_right (app (A:=idx)) [] small))) (n mod 2 ^ Z.of_N s).
Proof.
  generalize dependent n. induction small as [| first small' IHsmall'].
    + simpl. intros. apply EApp with (args' := []).
      -- constructor.
      -- inv H. inv H2. inv H4. reflexivity.
    + intros. simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H. destruct H as [n1 [n2 [H1 [H2 H3] ] ] ].
      apply IHsmall' in H3. clear IHsmall'.
      inv H2. inv H4. inv H7. inv H6. inv H1. repeat rewrite Z.add_0_r.
      simpl. rewrite map_app. apply break_add with (m1 := y) (m2 := n2 mod 2 ^ Z.of_N s).
      -- simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. apply Zplus_mod_idemp_r.
      -- apply H2.
      -- apply H3.
Qed.

Lemma eval_merge_list ctx d s small n :
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) small)) n ->
  eval ctx d (ExprApp (add s, map ExprRef (merge_list small))) (n mod 2 ^ Z.of_N s).
Proof.
  intros. cbv [merge_list]. apply eval_permute_commutative with (args1 := map ExprRef (fold_right (app (A:=idx)) [] small)).
  - reflexivity.
  - apply Permutation_map. apply N.Sort.Permuted_sort.
  - apply eval_app_list. apply H.
Qed.

Lemma mod_unchanged ctx d s small :
  forall big new_big n m,
  insert_small small big = Some new_big ->
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) big)) n ->
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) new_big)) m ->
  n mod 2 ^ Z.of_N s = m mod 2 ^ Z.of_N s.
Proof.
  intros big. induction big as [| maybe_small big' IHbig'].
  - intros. simpl in H. discriminate H.
  - intros. simpl in H.
    rewrite app_is_cons in H0.
    rewrite map_app in H0. apply break_addZ_backwards in H0. destruct H0 as [n1 [n2 [H2 [H3 H4] ] ] ].
     inv H2. simpl in H3.
    destruct (list_beq N N.eqb maybe_small (merge_list small)) eqn:E.
    + clear IHbig'. rewrite <- lists_equal in E. subst. inv H.
      rewrite map_app in H1. apply break_addZ_backwards in H1. destruct H1 as [m1 [m2 [H5 [H6 H7] ] ] ].
      inv H5. apply eval_merge_list in H6. simpl in H3. inv H3. inv H1. inv H8. inv H5. rename y into n1.
      apply (eval_eval _ _ _ _ H2) in H6. clear H2. subst. apply (eval_eval _ _ _ _ H4) in H7.
      clear H4. subst. repeat rewrite Z.add_0_r. rewrite Zplus_mod_idemp_l. reflexivity.
    + clear E. destruct (insert_small small big') as [new_big'|].
      -- inv H.
         rewrite app_is_cons in H1. rewrite map_app in H1. apply break_addZ_backwards in H1.
         destruct H1 as [m1 [m2 [H5 [H6 H7] ] ] ]. simpl in H6. assert (H: n2 mod 2 ^ Z.of_N s = m2 mod 2 ^ Z.of_N s).
         ++ apply IHbig' with (new_big := new_big').
           --- reflexivity.
           --- assumption.
           --- assumption.
         ++ clear H4 H7 IHbig'. inv H5. apply (eval_eval _ _ _ _ H3) in H6. clear H3. subst.
            repeat rewrite Z.add_0_r. rewrite Zplus_mod.
            rewrite H. rewrite <- Zplus_mod. reflexivity.
      -- discriminate H.
Qed.

Lemma eval_insert_small' ctx d s :
  forall small big n1 n2 new_big,
  eval ctx d (expr_of_a_carry s small) n1 ->
  eval ctx d (expr_of_a_carry s big) n2 ->
  insert_small small big = Some new_big ->
  eval ctx d (expr_of_a_carry s new_big) (n1 + n2).
Proof.
  intros small big. generalize dependent small.
  induction big as [| maybe_small big' IHbig'].
  - simpl. intros. discriminate H1.
  - intros. simpl in H1. destruct (list_beq N N.eqb maybe_small (merge_list small)) eqn:E.
    + rewrite <- lists_equal in E. subst. injection H1 as H1. subst. clear IHbig'.
      inv H. inv H3. inv H6. inv H7.
      inv H3. inv H5. inv H4. inv H7.
      inv H0. inv H3. inv H6. inv H7. inv H3. inv H4. inv H7. inv H5.
      rewrite app_is_cons in H1. apply break_addZ_backwards in H1.
      destruct H1 as [sm_mod_d [big_sum [H3 [H4 H5] ] ] ]. rename y into small_sum. inv H3.
      cbv [expr_of_a_carry]. repeat rewrite Z.add_0_r. apply EApp with (args' := [small_sum + big_sum; Z.of_N s]).
        ++ constructor.
          --- rewrite map_app. apply break_addZ with (m1 := small_sum) (m2 := big_sum).
            +++ simpl. f_equal. lia.
            +++ assumption.
            +++ assumption.
          --- constructor.
            +++ eapply EApp; auto.
            +++ constructor.
        ++ inv H4. inv H1. inv H7. inv H6. apply eval_merge_list in H2.
           apply (eval_eval _ _ _ _ H2) in H3. clear H2. subst.
           simpl. f_equal. repeat rewrite Z.shiftr_div_pow2 by lia. rewrite Z.add_0_r.
           rewrite Div.Z.div_add_mod_cond_l by lia. lia.
    + destruct (insert_small small big') as [new_big' |] eqn:E'.
      -- clear E. inv H0. inv H4. inv H7. inv H8. inv H4. inv H5. inv H8.  simpl. inv H1.
         rewrite app_is_cons in H3. apply break_addZ_backwards in H3.
         destruct H3 as [maybe_small_sum [big'_sum [H1 [H2 H3] ] ] ]. inv H1. inv H6.
         assert (eval ctx d (expr_of_a_carry s big') (Z.shiftr (big'_sum) (Z.of_N s))).
         {  cbv [expr_of_a_carry]. apply EApp with (args' := [big'_sum; Z.of_N s]).
            - constructor.
              + assumption.
              + constructor.
                -- apply EApp with (args' := []).
                  ++ constructor.
                  ++ reflexivity.
                -- constructor.
            - reflexivity. }
          remember (IHbig' _ _ _ _ H H0 E') as E''. clear HeqE'' H H0 IHbig'. rewrite Z.add_0_r.
          cbv [expr_of_a_carry]. cbv [expr_of_a_carry] in E'.
          inv E''. inv H5. inv H1. inv H7. inv H8. inv H4. inv H6. inv H8. rename y into new_big'_sum.
          apply EApp with (args' := [maybe_small_sum + new_big'_sum; Z.of_N s]).
          ++ constructor.
            --- rewrite app_is_cons. rewrite map_app. apply break_addZ with (m1 := maybe_small_sum) (m2 := new_big'_sum).
                +++ simpl. f_equal. lia.
                +++ simpl. assumption.
                +++ assumption.
            --- constructor.
              +++ apply EApp with (args' := []).
                ---- constructor.
                ---- reflexivity.
              +++ constructor.
          ++ simpl. f_equal. simpl in H0. injection H0 as H0.
             apply (mod_unchanged _ _ _ _ _ _ _ _ E' H3) in H5. clear H2 H3 E'.
             repeat rewrite Z.shiftr_div_pow2 in * by lia. rewrite Div.Z.div_add_mod_cond_r by lia. rewrite H0.
             rewrite <- H5. rewrite (Z.add_comm n1). rewrite Z.add_assoc. rewrite <- Div.Z.div_add_mod_cond_r by lia.
             lia.
      -- discriminate H1.
Qed.

(* returns Some (big, l - big) if there exists a big in l that small can be inserted into.  else, returns None *)
Fixpoint big_merged_thing (small : list (list idx)) (l : list (list (list idx))) : option ((list (list idx)) * list (list (list idx))) :=
  match l with
  | [] => None
  | maybe_big :: l' =>
    match insert_small small maybe_big with
    | Some big_thing => Some (big_thing, l')
    | None =>
      match big_merged_thing small l' with
      | Some (big_thing, l'') =>
        Some (big_thing, maybe_big :: l'')
      | None => None
      end
    end
  end.

Lemma eval_big_merged_thing ctx d s small :
  forall carries big_thing remaining n1 n2,
  eval ctx d (expr_of_a_carry s small) n1 ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s carries)) n2 ->
  big_merged_thing small carries = Some (big_thing, remaining) ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (big_thing :: remaining))) (n1 + n2).
Proof.
  intros carries. induction carries as [| carry carries' IHcarries'].
  - intros. simpl in H1. discriminate H1.
  - intros. simpl in H1. destruct (insert_small small carry) as [big_thing'|] eqn:E.
    + inv H1. clear IHcarries'.
      simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0. destruct H0 as [n2_1 [n2_2 [H1 [H2 H3] ] ] ].
      inv H1. inv H2. inv H4. inv H7. inv H6. apply (eval_insert_small' _ _ _ _ _ _ _ _ H H2) in E.
      simpl. rewrite app_is_cons. apply break_addZ with (m1 := n1 + y) (m2 := n2_2).
      -- simpl. repeat rewrite Z.add_0_r. f_equal. lia.
      -- apply EApp with (args' := [n1 + y]).
        ++ constructor.
          --- assumption.
          --- constructor.
        ++ simpl. f_equal. lia.
      -- assumption.
    + destruct (big_merged_thing small carries') as [ [big_thing_ l'']|] eqn:E'.
      -- inv H1. clear E. simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0.
         destruct H0 as [n2_1 [n2_2 [H1 [H2 H3] ] ] ].
         assert (Some (big_thing, l'') = Some (big_thing, l'')) by reflexivity.
         apply (IHcarries' _ _ _ _ H H3) in H0. clear IHcarries' H H3. inv H1.
         simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0.
         destruct H0 as [m1 [m2 [H3 [H4 H5] ] ] ].
         simpl. rewrite app_is_cons. apply break_addZ with (m1 := m1) (m2 := m2 + n2_1).
        ++ simpl. f_equal. simpl in H3. injection H3 as H3. lia.
        ++ assumption.
        ++ rewrite app_is_cons. apply break_addZ with (m1 := n2_1) (m2 := m2).
          --- simpl. f_equal. lia.
          --- assumption.
          --- assumption.
      -- discriminate H1.
Qed.

(* assumes the list, and its elements, to be sorted *)
Fixpoint merge_carries_aux (l : list (list (list idx))) (len : nat) : list (list (list idx)) :=
  match len with
  | O => l
  | S len' =>
    match l with
    | [] => []
    | maybe_small :: l' =>
      match big_merged_thing maybe_small l' with
      | Some (big_thing, remaining) => merge_carries_aux (merge [big_thing] remaining) len'
      | None => maybe_small :: (merge_carries_aux l' len')
      end
    end
  end.

Lemma eval_merge_carries_aux ctx d s n carries len:
  eval ctx d (ExprApp (addZ, exprs_of_carries s carries)) n ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (merge_carries_aux carries len))) n.
Proof.
  generalize dependent n. generalize dependent carries. induction len as [| len'].
  - simpl. intros. apply H.
  - simpl. intros. destruct carries as [|maybe_small carries'].
    + apply H.
    + simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H.
         destruct H as [n1 [n2 [H1 [H2 H3] ] ] ]. inv H1.
         destruct (big_merged_thing maybe_small carries') as [ [big_thing remaining] |] eqn:E.
      -- inv H2. inv H1. inv H6. inv H5. rename y into n1.
         remember (merge [big_thing] remaining) as l. simpl in Heql.
         assert (merge [big_thing] remaining = l). { rewrite Heql. reflexivity. }
         subst. rewrite <- H. clear H. apply IHlen'.
         apply (eval_big_merged_thing _ _ _ _ _ _ _ _ _ H2 H3) in E. clear H2 H3.
         apply eval_permute_commutative with (args1 := exprs_of_carries s (big_thing :: remaining)).
        ++ reflexivity.
        ++ cbv [exprs_of_carries]. apply Permutation_map. rewrite app_is_cons. apply Permuted_merge.
        ++ repeat rewrite Z.add_0_r. apply E.
      -- simpl. rewrite app_is_cons. apply break_addZ with (m1 := n1) (m2 := n2).
        ++ simpl. reflexivity.
        ++ apply H2.
        ++ apply IHlen'. apply H3.
Qed.

Definition merge_carries (l : list (list (list idx))) : list (list (list idx)) :=
  let l := map (fun (a : list (list idx)) => (map (fun (b : list idx) => N.sort b) a)) l in
  let l := sort l in
  merge_carries_aux l (length l).

Lemma eval_merge_carries ctx d s n carries:
  eval ctx d (ExprApp (addZ, exprs_of_carries s carries)) n ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (merge_carries carries))) n.
Proof.
  intros. cbv [merge_carries]. apply eval_merge_carries_aux.
  apply eval_permute_commutative with (args1 := exprs_of_carries s ((map (fun a : list (list idx) => map (fun b : list idx => N.sort b) a) carries))).
  - reflexivity.
  - cbv [exprs_of_carries]. apply Permutation_map. apply Permuted_sort.
  - generalize dependent n. induction carries as [| carry carries' IHcarries'].
    + intros. simpl. simpl in H. apply H.
    + intros. simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H.
      destruct H as [n1 [n2 [H1 [H2 H3] ] ] ]. inv H1. apply IHcarries' in H3. clear IHcarries'.
      simpl. rewrite app_is_cons. apply break_addZ with (m1 := n1) (m2 := n2).
      -- simpl. reflexivity.
      -- clear H3. inv H2. inv H1. inv H5. inv H4. apply EApp with (args' := [y]).
        ++ constructor.
          --- inv H2. inv H1. inv H5. inv H6. inv H1. inv H3. inv H6. inv H4.
              apply EApp with (args' := [y0; Z.of_N s]).
            +++ constructor.
              ---- generalize dependent y0. induction carry as [| addend addends' IHaddends'].
                ++++ simpl. intros. apply H2.
                ++++ simpl. intros. rewrite app_is_cons in H2. apply break_addZ_backwards in H2.
                     destruct H2 as [y0_1 [y0_2 [H1 [H2 H3] ] ] ]. inv H1. apply IHaddends' in H3.
                     clear IHaddends'. rewrite app_is_cons. apply break_addZ with (m1 := y0_1) (m2 := y0_2).
                  ----- simpl. reflexivity.
                  ----- clear H3. inv H2. inv H1. inv H5. inv H4. apply EApp with (args' := [y]).
                    +++++ constructor.
                      ------ apply eval_permute_commutative with (args1 := (map ExprRef addend)).
                        ++++++ reflexivity.
                        ++++++ apply Permutation_map. apply N.Sort.Permuted_sort.
                        ++++++ apply H2.
                      ------ constructor.
                    +++++ simpl. reflexivity.
                  ----- apply H3.
              ---- constructor.
                ++++ apply EApp with (args' := []).
                  ----- constructor.
                  ----- simpl. reflexivity.
                ++++ constructor.
            +++ simpl. reflexivity.
          --- constructor.
        ++ reflexivity.
      -- apply H3.
Qed.

Definition sum_idx {descr : description} (d : dag) (s : OperationSize) (indices : list idx) : idx * dag :=
  match indices with
  | [] => merge_node (add s, []) d (* should never happen *)
  | i :: [] => if is_bounded_by d (2 ^ Z.of_N s - 1) i then (i, d) else merge_node (add s, indices) d
  | _ => merge_node (add s, indices) d
  end.

(* list of things to be added *)
Fixpoint split_carry_aux {descr : description} (d : dag) (s : OperationSize) (carry : list (list idx)) : list idx * dag :=
  match carry with
  | [] => ([], d) (* should actually never happen *)
  | i :: [] => ([], d) (* should never happen on the initial call; should happen on recursive calls *)
  | x :: more_stuff =>
    let (adc_arg_1, d1) := sum_idx d s x in
    let (adc_arg_2, d2) := sum_idx d1 s (fold_right (@app idx) [] more_stuff) in
    let (i, d3) := merge_node (addcarry s, [adc_arg_1; adc_arg_2]) d2 in
    let (is, d4) := split_carry_aux d3 s more_stuff in
    (i :: is, d4)
  end.

Module lexOrder <: TotalLeBool.
  Definition t : Type := list idx.
  Fixpoint leb (x y : t) : bool :=
    match x, y with
    | [], _ => true
    | x0 :: x', [] => false
    | x0 :: x', y0 :: y' => if N.eqb x0 y0 then leb x' y' else N.leb x0 y0
    end.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall x y, x <=? y = true \/ y <=? x = true.
  Proof.
    intros x. induction x as [| x0 x' IHx'].
    - intros y. left. reflexivity.
    - intros y. destruct y as [|y0 y'].
      + right. reflexivity.
      + simpl. rewrite <- (N.eqb_sym x0 y0). destruct (x0 =? y0)%N.
        -- apply IHx'.
        --  unfold leb. repeat rewrite N.leb_le. lia. Qed.
End lexOrder.
Module Import lexSort := Sort lexOrder.

(* merges the addcarries that make up the carry into the dag, returns a list of index references to the addcarries *)
Definition split_carry {descr : description} (d : dag) (s : OperationSize) (carry : list (list idx)) : list idx * dag :=
  let carry := map (fun x => N.sort x) carry in
  let carry := sort carry in
  split_carry_aux d s carry.

Fixpoint split_carries {descr : description} (d : dag) (s : OperationSize) (l : list (list (list idx))) : list idx * dag :=
  match l with
  | [] => ([], d)
  | carry :: more =>
    let (some_addends, d') := split_carry d s carry in
    let (more_addends, d'') := split_carries d' s more in
    (some_addends ++ more_addends, d'')
  end.

Lemma carry_one_thing_zero ctx d s sum n :
  eval ctx d (expr_of_a_carry s [sum]) n ->
  n = 0.
Proof.
  intros. inv H. inv H2. inv H5. inv H6. inv H4. inv H2. inv H3. inv H5. inv H1. inv H2. inv H5. inv H4. inv H1.
  apply small_sum in H4. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. cbv [Z.ones] in H4.
  rewrite Z.shiftl_1_l in H4. lia.
Qed.

Lemma eval_sum_idx {descr : description} ctx d s addends n :
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (add s, map ExprRef addends)) n ->
  forall sum d',
  sum_idx d s addends = (sum, d') ->
  gensym_dag_ok ctx d' /\
  (forall i e', eval ctx d i e' -> eval ctx d' i e') /\
  eval ctx d' (ExprRef sum) n.
Proof.
  intros H_ok. intros. cbv [sum_idx] in H0. destruct addends as [| a [| b addends''] ].
  - remember (eval_merge_node _ _ H_ok _ _ _ H) as H'.
    clear H_ok HeqH'. destruct H' as [H1 [H2 H2'] ]. rewrite H0 in *. simpl in H1. simpl in H2. split.
    + apply H2.
    + split.
      -- intros. simpl in H2'. apply H2'. apply H3.
      -- apply H1.
  - destruct (is_bounded_by d (2 ^ Z.of_N s - 1) a) eqn:E.
    + symmetry in H0. inv H0. split.
      -- apply H_ok.
      -- split.
        ++ intros. apply H0.
        ++ destruct H_ok as [_ [H_bounds _] ]. inv H. inv H2. inv H5. inv H4.
           remember (eval_is_bounded_by _ _ _ _ _ H_bounds E H1) as H2. clear HeqH2.
           rewrite Z_land_ones'. rewrite Z.add_0_r. rewrite Z.mod_small by lia. apply H1.
    + remember (eval_merge_node _ _ H_ok _ _ _ H) as H'. clear H_ok HeqH'. destruct H' as [H1 [H2 H3] ]. rewrite H0 in *.
    clear H0. simpl in H1. simpl in H2. split.
      -- apply H2.
      -- split.
        ++ simpl in H3. apply H3.
        ++ apply H1.
  - remember (eval_merge_node _ _ H_ok _ _ _ H) as H'. clear H_ok HeqH'. destruct H' as [H1 [H2 H3] ]. rewrite H0 in *.
    clear H0. simpl in H1. simpl in H2. split.
    + apply H2.
    + split.
      -- simpl in H3. apply H3.
      -- apply H1.
Qed.

Lemma eval_split_carry_aux {descr : description} ctx d s carry n :
  gensym_dag_ok ctx d ->
  eval ctx d (expr_of_a_carry s carry) n ->
  forall addends d',
  split_carry_aux d s carry = (addends, d') ->
  eval ctx d' (ExprApp (addZ, map ExprRef addends)) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros H_ok. generalize dependent n. generalize dependent d. induction carry as [|sum carry' IHcarry'].
  - simpl. intros d H_ok. intros. inv H0. cbv [expr_of_a_carry] in H. simpl in H.
    inv H. inv H2. inv H5. inv H6. inv H2. inv H3. inv H6. inv H4.
    inv H1. inv H2. inv H4. simpl. split.
    + apply EApp with (args' := []).
      -- constructor.
      -- simpl. rewrite Z.shiftr_0_l. reflexivity.
    + split.
      -- apply H_ok.
      -- intros. apply H.
  - intros d H_ok. intros. simpl in H0. destruct carry' as [| first_bit last_bits].
    + symmetry in H0. inv H0. split.
      -- apply IHcarry' with (d := d).
        ++ apply H_ok.
        ++ clear IHcarry'. apply carry_one_thing_zero in H. subst. apply EApp with (args' := [0; Z.of_N s]).
          --- simpl. constructor.
            +++ apply EApp with (args' := []).
              ---- constructor.
              ---- reflexivity.
            +++ constructor.
              ---- apply EApp with (args' := []).
                ++++ constructor.
                ++++ constructor.
              ---- constructor.
          --- simpl. f_equal. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_0_l. lia.
        ++ reflexivity.
      -- split.
        ++ apply H_ok.
        ++ intros i e' H'. apply H'.
    + remember (first_bit :: last_bits) as carry'. clear first_bit last_bits Heqcarry'.
      destruct (sum_idx d s sum) as [adc_arg_1 d1] eqn:E1.
      destruct (sum_idx d1 s (fold_right (@app idx) [] carry')) as [adc_arg_2 d2] eqn:E2.
      destruct (merge_node (addcarry s, [adc_arg_1; adc_arg_2]) d2) as [one_addend d3] eqn:E3.
      destruct (split_carry_aux d3 s carry') as [more_addends d4] eqn:E4. symmetry in H0. inv H0.
      inv H. inv H2.  inv H5. inv H6. inv H2. inv H3. inv H6. inv H4. rewrite app_is_cons in H1.
      apply break_addZ_backwards in H1. destruct H1 as [y1 [y2 [H1 [H2 H3] ] ] ]. inv H1.
      inv H2. inv H1. inv H6. inv H5.
      assert (E': 0 <= y <= Z.ones (Z.of_N s)). { inv H2. apply small_sum in H5. apply H5. }
      apply (eval_sum_idx _ _ _ _ _ H_ok H2) in E1.
      clear H_ok H2.  destruct E1 as [H_ok1 [H_eval1 H5] ].
      remember H3 as H3'. clear HeqH3'.
      apply eval_app_list in H3. apply H_eval1 in H3. apply (eval_sum_idx _ _ _ _ _ H_ok1 H3) in E2.
      apply H_eval1 in H3'. clear H_ok1 H3.
      destruct E2 as [H_ok2 [H_eval2 H7] ].
      apply H_eval2 in H5. apply H_eval2 in H3'.
      assert (H': eval ctx d2 (ExprApp (addcarry s, map ExprRef [adc_arg_1; adc_arg_2])) (Z.shiftr (y + (y2 mod 2 ^ Z.of_N s)) (Z.of_N s) mod 2)).
      { apply EApp with (args' := [y; y2 mod 2 ^ Z.of_N s]).
        - constructor.
          + assumption.
          + constructor.
            -- assumption.
            -- constructor.
        - simpl. rewrite Z.add_0_r. reflexivity. }
      apply (eval_merge_node _ _ H_ok2) in H'. rewrite E3 in H'. simpl in H'.
      clear E3 H_ok2 H5 H7. destruct H' as [H1 [H_ok3 H_eval3] ]. apply H_eval3 in H3'.
      assert (H'': eval ctx d3 (expr_of_a_carry s carry') (Z.shiftr y2 (Z.of_N s))).
      { apply EApp with (args' := [y2; Z.of_N s]).
        - constructor.
          + assumption.
          + constructor.
            -- apply EApp with (args' := []).
              ++ constructor.
              ++ simpl. reflexivity.
            -- constructor.
        - simpl. reflexivity. }
        clear H3'. apply (IHcarry' _ H_ok3 _  H'') in E4. clear H_ok3 H'' IHcarry'.
        destruct E4 as [H2 [H_ok4 H_eval4] ]. split.
        -- simpl. rewrite app_is_cons. apply H_eval4 in H1.
           apply break_addZ with (m1 := Z.shiftr (y + y2 mod 2 ^ Z.of_N s) (Z.of_N s) mod 2) (m2 := Z.shiftr y2 (Z.of_N s)).
           ++ simpl. f_equal. repeat rewrite Z.add_0_r. repeat rewrite Z.shiftr_div_pow2 by lia.
              assert (0<= y2 mod 2 ^ Z.of_N s < 2 ^ Z.of_N s). { apply Z_mod_lt. lia. }
              cbv [Z.ones] in E'. rewrite Z.shiftl_1_l in E'. assert (0 <= y + y2 mod 2 ^ Z.of_N s < 2 * 2 ^ Z.of_N s) by lia.
              assert (0 <= (y + y2 mod 2 ^ Z.of_N s) / 2 ^ Z.of_N s < 2).
              { split.
                - apply Z.div_pos; lia.
                - apply Z.div_lt_upper_bound; lia. }
              rewrite (Z.mod_small _ 2) by lia.
              rewrite <- Div.Z.div_add_mod_cond_r by lia. reflexivity.
          ++ apply EApp with (args' := [Z.shiftr (y + y2 mod 2 ^ Z.of_N s) (Z.of_N s) mod 2]).
            --- constructor.
              +++ assumption.
              +++ constructor.
            --- simpl. rewrite Z.add_0_r. reflexivity.
          ++ assumption.
        -- split.
          ++ apply H_ok4.
          ++ intros i e' H'. apply (H_eval4 _ _ (H_eval3 _ _ (H_eval2 _ _ (H_eval1 _ _ H') ) ) ).
Qed.

Lemma sorting_irrelevant ctx d s carry n :
  eval ctx d (expr_of_a_carry s carry) n ->
  eval ctx d (expr_of_a_carry s (sort (map (fun x : list N => N.sort x) carry))) n.
Proof.
  intros. inv H. inv H2. inv H5. inv H6. inv H2. inv H3. inv H6. inv H4.
  cbv [expr_of_a_carry]. apply EApp with (args' := [y; Z.of_N s]).
  - constructor.
    + apply eval_permute_commutative with
      (args1 := map (fun addends : list idx => ExprApp (add s, map ExprRef addends))
                    (map (fun x : list N => N.sort x) carry)).
      -- reflexivity.
      -- apply Permutation_map. apply Permuted_sort.
      -- generalize dependent y. induction carry as [| addend carry' IHcarry'].
        ++ intros. simpl. simpl in H1. apply H1.
        ++ intros. simpl in H1. rewrite app_is_cons in H1.  apply break_addZ_backwards in H1.
           destruct H1 as [y1 [y2 [H1 [H2 H3] ] ] ]. apply IHcarry' in H3. clear IHcarry'. inv H1.
           simpl. rewrite app_is_cons. apply break_addZ with (m1 := y1) (m2 := y2).
          --- simpl. reflexivity.
          --- inv H2. inv H1. inv H6. inv H5. rename y into y1. apply EApp with (args' := [y1]).
            +++ constructor.
              ---- apply eval_permute_commutative with (args1 := (map ExprRef addend)).
                ++++ reflexivity.
                ++++ apply Permutation_map. apply N.Sort.Permuted_sort.
                ++++ apply H2.
              ---- constructor.
            +++ simpl. reflexivity.
          --- apply H3.
    + constructor.
      -- apply EApp with (args' := []).
        ++ constructor.
        ++ simpl. reflexivity.
      -- constructor.
  - simpl. reflexivity.
Qed.

Lemma eval_split_carry {descr : description} ctx d s carry n :
  gensym_dag_ok ctx d ->
  eval ctx d (expr_of_a_carry s carry) n ->
  forall addends d',
  split_carry d s carry = (addends, d') ->
  eval ctx d' (ExprApp (addZ, map ExprRef addends)) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. cbv [split_carry] in H1. apply sorting_irrelevant in H0.
  apply (eval_split_carry_aux _ _ _ _ _ H H0) in H1. apply H1.
Qed.

Lemma eval_split_carries {descr : description} ctx d s carries n :
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s carries)) n ->
  forall idxs d',
  split_carries d s carries = (idxs, d') ->
  eval ctx d' (ExprApp (addZ, map ExprRef idxs)) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. generalize dependent n. generalize dependent d. generalize dependent d'. generalize dependent idxs.
  induction carries as [| carry carries' IHcarries'].
  - intros. simpl in H1. inv H1. auto.
  - intros. simpl in H1. inv H1. destruct (split_carry d s carry) as [some_addends d1] eqn:E1.
    destruct (split_carries d1 s carries') eqn:E2. inv H3.
    simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0. destruct H0 as [n1 [n2 [H1 [H2 H3] ] ] ].
    inv H1. inv H2. inv H4. inv H7. inv H6. apply (eval_split_carry _ _ _ _ _ H H2) in E1.
    clear H H2. destruct E1 as [H [H_ok1 H_eval1] ]. apply H_eval1 in H3. apply (IHcarries' _ _ _ H_ok1 E2) in H3.
    clear IHcarries' H_ok1. destruct H3 as [H' [H_ok' H_eval'] ]. split.
    + rewrite map_app. apply break_addZ with (m1 := y) (m2 := n2).
      -- simpl. f_equal. lia.
      -- apply H_eval'. apply H.
      -- apply H'.
    + split.
      -- apply H_ok'.
      -- auto.
Qed.

Definition standardize_adc_sum {descr : description} (d : dag) (idxs : list idx) (s : OperationSize) : list idx * dag :=
  let (withadc, without) := withadc_without d s idxs in
  let (standard_withadc, d') := split_carries d s (merge_carries withadc) in
  (standard_withadc ++ without, d').

Lemma evalZ_standardize_adc_sum {descr : description} ctx d s idxs n :
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (addZ, map ExprRef idxs)) n ->
  let (idxs', d') := standardize_adc_sum d idxs s in
  eval ctx d' (ExprApp (addZ, map ExprRef idxs')) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. destruct (standardize_adc_sum d idxs s) as [idxs' d'] eqn:E. cbv [standardize_adc_sum] in E.
  destruct (withadc_without d s idxs) as [withadc without] eqn:E1.
  destruct (split_carries d s (merge_carries withadc)) as [standard_withadc d1] eqn:E2.
  remember H as H_bounds; clear HeqH_bounds. destruct H_bounds as [_ [H_bounds _] ].
  apply (evalZ_withadc_without _ _ s H_bounds) in H0. clear H_bounds.
  rewrite E1 in *. clear E1. apply break_addZ_backwards in H0.
  destruct H0 as [n1 [n2 [H1 [H2 H3] ] ] ]. inv H1. apply eval_merge_carries in H3.
  apply (eval_split_carries _ _ _ _ _ H H3) in E2. destruct E2 as [H4 [H_ok1 H_eval1] ]. inv E. split.
  - rewrite map_app. apply break_addZ with (m1 := n2) (m2 := n1).
    + simpl. f_equal. lia.
    + apply H4.
    + apply H_eval1. apply H2.
  - auto.
Qed.

Lemma addZ_to_adds ctx d s args n :
  eval ctx d (ExprApp (addZ, args)) n ->
  eval ctx d (ExprApp (add s, args)) (n mod (2 ^ Z.of_N s)).
Proof.
  intros. inv H. apply EApp with (args' := args').
  - apply H2.
  - inv H4. simpl. rewrite Z_land_ones'. reflexivity.
Qed.

Lemma adds_to_addZ ctx d s args n :
  eval ctx d (ExprApp (add s, args)) n ->
  exists m,
  n = m mod (2 ^ Z.of_N s) /\
  eval ctx d (ExprApp (addZ, args)) m.
Proof.
  intros. inv H. exists (fold_right Z.add 0 args'). inv H4. split.
  - rewrite Z_land_ones'. reflexivity.
  - apply EApp with (args' := args').
    + apply H2.
    + simpl. reflexivity.
Qed.

Lemma evals_standardize_adc_sum {descr : description} ctx d s s0 idxs n :
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (add s0, map ExprRef idxs)) n ->
  let (idxs', d') := standardize_adc_sum d idxs s in
  eval ctx d' (ExprApp (add s0, map ExprRef idxs')) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. apply adds_to_addZ in H0. destruct H0 as [m [H1 H2] ].
  apply (evalZ_standardize_adc_sum _ _ s _ _ H) in H2. destruct (standardize_adc_sum d idxs s) as [idxs'Z d'Z].
  destruct H2 as [H2 H3]. apply addZ_to_adds with (s := s0) in H2. subst. auto.
Qed.

Lemma eval_standardize_adc_sum {descr : description} ctx d s idxs n op :
  sum op = true ->
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (op, map ExprRef idxs)) n ->
  let (idxs', d') := standardize_adc_sum d idxs s in
  eval ctx d' (ExprApp (op, map ExprRef idxs')) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. destruct op; try discriminate H.
  - apply evals_standardize_adc_sum; auto.
  - apply evalZ_standardize_adc_sum; auto.
Qed.

Definition bitwidths_to_standardize d idxs :=
  let f :=  fun idx l =>
              match (reveal d 1 idx) with
              | ExprApp (addcarry s, _) => s :: l
              | _ => l
              end
            in
  let bitwidths := fold_right f [] idxs in
  let bitwidths_that_occur_at_least_twice := filter (fun i => 2 <=? Z.of_nat (count_occ N.eq_dec bitwidths i)) bitwidths in
  nodup N.eq_dec bitwidths_that_occur_at_least_twice.

Definition standardize_adc_sums {descr : description} (d : dag) (idxs : list idx) : list idx * dag :=
  let f := fun (s : OperationSize) (lidx_dag : list idx * dag) =>
    standardize_adc_sum (snd lidx_dag) (fst lidx_dag) s in
  fold_right f (idxs, d) (bitwidths_to_standardize d idxs).

Lemma eval_standardize_adc_sums {descr : description} ctx d idxs n op :
  sum op = true ->
  gensym_dag_ok ctx d ->
  eval ctx d (ExprApp (op, map ExprRef idxs)) n ->
  let (idxs', d') := standardize_adc_sums d idxs in
  eval ctx d' (ExprApp (op, map ExprRef idxs')) n
  /\ gensym_dag_ok ctx d'
  /\ forall i e', eval ctx d i e' -> eval ctx d' i e'.
Proof.
  intros. destruct (standardize_adc_sums d idxs) as [idxs' d'] eqn:E. cbv [standardize_adc_sums] in E.
  generalize dependent idxs'. generalize dependent d'.
  induction (bitwidths_to_standardize d idxs) as [| s l' IHl'].
  - intros. simpl in E. inv E. auto.
  - intros. simpl in E. destruct (fold_right _ _ l') as [idxs1 d1]. simpl in E.
    assert (H': (idxs1, d1) = (idxs1, d1)) by reflexivity.
    apply IHl' in H'. clear IHl'. destruct H' as [H2 [H_ok1 H_eval1] ].
    apply (eval_standardize_adc_sum _ _ s _ _ _ H H_ok1) in H2. rewrite E in H2. clear E H H_ok1.
    destruct H2 as [H2 [H3 H4] ]. auto.
Qed.

(* end addcarry stuff *)

Fixpoint merge {descr : description} (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let idxs_d' :=
                if sum op
                then standardize_adc_sums (snd idxs_d) (fst idxs_d)
                else idxs_d in
    let idxs := if commutative op
                then N.sort (fst idxs_d')
                else (fst idxs_d') in
    merge_node (op, idxs) (snd idxs_d')
  end.

Lemma eval_merge {descr:description} G :
  forall e n,
  forall d, gensym_dag_ok G d ->
  eval G d e n ->
  eval G (snd (merge e d)) (ExprRef (fst (merge e d))) n /\
  gensym_dag_ok G (snd (merge e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge e d)) i e'.
Proof using Type.
  intros e. induction e as [i| [o args] IH] (* writing "eqn:E" here screws things up. why? *); intros.
  - auto.
  - inv H0. simpl in IH. remember (merge (ExprApp (o, args)) d) as m eqn:Em.
    simpl in Em. remember (foldmap merge args d) as idxs_d.
    remember (if (sum o) then _ else _) as idxs_d'.
    assert (H': gensym_dag_ok G (snd idxs_d) /\
    Forall2 (fun i v => eval G (snd idxs_d) (ExprRef i) v) (fst idxs_d) args' /\
    forall i e', eval G d i e' -> eval G (snd idxs_d) i e').
    { clear n H5. rewrite Heqidxs_d in *. clear Heqidxs_d Heqidxs_d' Em. generalize dependent args'.
      induction args as [| arg args1 IHargs1].
      - simpl. subst. simpl. split; auto. split; auto. inv H3. constructor.
      - intros. inv IH. inv H3.
        apply (IHargs1 H4) in H7. clear IHargs1 H4. destruct H7 as [H_ok1 [H7 H_eval1] ].
        simpl. remember ((foldmap merge args1 d)) as idxs_d1. apply H_eval1 in H5.
        apply (H2 _ _ H_ok1) in H5. clear H2 H_ok1. destruct H5 as [H5 [H_ok' H_eval'] ].
        split; auto. split; auto. clear H_eval1 H_ok' Heqidxs_d1. constructor.
        + apply H5.
        + apply @Forall2_weaken with (P := (fun (i : idx) (v : Z) => eval G (snd idxs_d1) (ExprRef i) v)).
          -- intros. apply H_eval'; assumption.
          -- assumption.
    }
    clear args IH H3 Heqidxs_d. destruct H' as [H_ok0 [H0 H_eval0] ].
    assert (H'': eval G (snd idxs_d) (ExprApp (o, map ExprRef (fst idxs_d))) n).
    { apply EApp with (args' := args').
      - rewrite -> Forall2_map_l. apply H0.
      - apply H5.
    }
    clear H0 H5.

    assert (H''': gensym_dag_ok G (snd idxs_d') /\
    eval G (snd idxs_d') (ExprApp (o, map ExprRef (fst idxs_d'))) n /\
    forall i e', eval G d i e' -> eval G (snd idxs_d') i e').
    { clear Em. destruct (sum o) eqn:Eo.
      - apply (eval_standardize_adc_sums _ _ _ _ _ Eo H_ok0) in H''.
        clear Eo H_ok0. rewrite <- Heqidxs_d' in *. clear Heqidxs_d'. destruct idxs_d' as [idxs' d'].
        simpl. destruct H'' as [H1 [H2 H3] ]. auto.
      - subst. auto.
    }
    clear H_ok0 H_eval0 H'' Heqidxs_d' H. destruct H''' as [H_ok' [H' H_eval'] ].
    remember H_ok' as bounds_ok'; clear Heqbounds_ok'. destruct bounds_ok' as [_ [bounds_ok' _] ].
    destruct (commutative o) eqn:Eo.
    + assert (Hperm: Permutation (map ExprRef (fst idxs_d')) (map ExprRef (N.sort (fst idxs_d')))).
      { apply Permutation_map. apply N.Sort.Permuted_sort. }
      apply (eval_permute_commutative _ _ _ _ _ _ Eo Hperm) in H'.
      apply (eval_merge_node _ _ H_ok') in H'. subst. destruct H' as [H1 [H2 H3] ]. auto.
    + apply (eval_merge_node _ _ H_ok') in H'. subst. destruct H' as [H1 [H2 H3] ]. auto.
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


Definition isCst (e : expr) :=
  match e with ExprApp ((const _), []) => true | _ => false end.

Module Rewrite.
Class Ok r := rwok : forall G d e v, eval G d e v -> eval G d (r e) v.
Class Ok_d r := rwdok : forall G d e v, eval G d e v -> eval G d (r d e) v.

Ltac resolve_match_using_hyp :=
  match goal with |- context[match ?x with _ => _ end] =>
  match goal with H : x = ?v |- _ =>
      let h := Head.head v in
      is_constructor h;
      rewrite H
  end end.

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
  | H: bound_expr _ = Some _ |- _ => eapply eval_bound_expr in H; eauto; [ ]

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
  end.

Ltac Econstructor :=
  match goal with
  | |- Forall2 (eval _ _) _ _ =>  econstructor
  | |- eval _ _ ?e _ => econstructor
  end.

Ltac t := repeat (step || Econstructor || eauto || (progress cbn [interp0_op interp_op] in * ) ).

Definition slice0 :=
  fun e => match e with
    ExprApp (slice 0 s, [(ExprApp ((addZ|mulZ|negZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args))]) =>
        ExprApp ((match o with addZ=>add s|mulZ=>mul s|negZ=>neg s|shlZ=>shl s|shrZ => shr s|andZ => and s| orZ => or s|xorZ => xor s |_=>old 0%N 999999%N end), args)
      | _ => e end.
Global Instance slice0_ok : Ok slice0. Proof using Type. t. Qed.

Definition slice01_addcarryZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (addcarryZ s, args))]) =>
        ExprApp (addcarry s, args)
      | _ => e end.
Global Instance slice01_addcarryZ_ok : Ok slice01_addcarryZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice01_subborrowZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (subborrowZ s, args))]) =>
        ExprApp (subborrow s, args)
      | _ => e end.
Global Instance slice01_subborrowZ_ok : Ok slice01_subborrowZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice_set_slice :=
  fun e => match e with
    ExprApp (slice 0 s1, [ExprApp (set_slice 0 s2, [_; e'])]) =>
      if N.leb s1 s2 then ExprApp (slice 0 s1, [e']) else e | _ => e end.
Global Instance slice_set_slice_ok : Ok slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice_set_slice :=
  fun e => match e with
    ExprApp (set_slice lo1 s1, [ExprApp (set_slice lo2 s2, [x; e']); y]) =>
      if andb (N.eqb lo1 lo2) (N.leb s2 s1) then ExprApp (set_slice lo1 s1, [x; y]) else e | _ => e end.
Global Instance set_slice_set_slice_ok : Ok set_slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice0_small :=
  fun e => match e with
    ExprApp (set_slice 0 s, [x; y]) =>
      match bound_expr x, bound_expr y with Some a, Some b =>
      if Z.leb a (Z.ones (Z.of_N s)) && Z.leb b (Z.ones (Z.of_N s)) then y
      else e | _, _ => e end | _ => e end%bool.
Global Instance set_slice0_small_ok : Ok set_slice0_small.
Proof using Type.
  t.
  eapply Zle_bool_imp_le in H0; rewrite Z.ones_equiv in H0; eapply Z.lt_le_pred in H0.
  eapply Zle_bool_imp_le in H1; rewrite Z.ones_equiv in H1; eapply Z.lt_le_pred in H1.
  assert ((0 <= y < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z.
  assert ((0 <= y0 < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z0.
  rewrite ?Z.shiftl_0_r, Z.land_ones, Z.mod_small by Lia.lia.
  destruct (Z.eq_dec y 0); subst.
  { rewrite Z.ldiff_0_l, Z.lor_0_r; trivial. }
  rewrite Z.ldiff_ones_r_low, Z.lor_0_r; try Lia.lia.
  eapply Z.log2_lt_pow2; Lia.lia.
Qed.

Definition truncate_small :=
  fun e => match e with
    ExprApp (slice 0%N s, [e']) =>
      match bound_expr e' with Some b =>
      if Z.leb b (Z.ones (Z.of_N s))
      then e'
      else e | _ => e end | _ => e end.
Global Instance truncate_small_ok : Ok truncate_small. Proof using Type. t; []. cbn in *; eapply Z.land_ones_low_alt_ones; eauto. firstorder. Lia.lia. Qed.

Definition addcarry_bit :=
  fun e => match e with
    ExprApp (addcarry s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1) then
      match interp0_op (addcarry s) [a; 0], interp0_op (addcarry s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addcarry_bit_ok : Ok addcarry_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1%Z)) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addoverflow_bit :=
  fun e => match e with
    ExprApp (addoverflow s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1%Z) then
      match interp0_op (addoverflow s) [a; 0] , interp0_op (addoverflow s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addoverflow_bit_ok : Ok addoverflow_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1)%Z) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addbyte_small :=
  fun e => match e with
    ExprApp (add (8%N as s), args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then ExprApp (add 64%N, args)
          else e | _ => e end | _ =>  e end.
Global Instance addbyte_small_ok : Ok addbyte_small.
Proof using Type.
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite !Z.land_ones, !Z.mod_small; try Lia.lia;
    replace (Z.of_N 8) with 8 in * by (vm_compute; reflexivity);
    replace (Z.of_N 64) with 64 in * by (vm_compute; reflexivity); Lia.lia.
Qed.

Definition addcarry_small :=
  fun e => match e with
    ExprApp (addcarry s, args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addcarry_small_ok : Ok addcarry_small.
Proof using Type.
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite Z.shiftr_div_pow2, Z.div_small; cbn; Lia.lia.
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

Definition addoverflow_small :=
  fun e => match e with
    ExprApp (addoverflow s, ([_]|[_;_]|[_;_;_]) as args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s-1))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addoverflow_small_ok : Ok addoverflow_small.
Proof using Type.
  t; cbv [Option.List.lift Option.bind fold_right] in *;
  BreakMatch.break_match_hyps; Option.inversion_option; t;
  epose proof Z.ones_equiv (Z.of_N s -1).
  all : rewrite Z.land_ones, !Z.mod_small, !signed_small, !Z.eqb_refl; trivial.
  all : try split; try Lia.lia.
  all : replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia;
  rewrite Z.pow_add_r; try Lia.lia.
  all : destruct s; cbn in E0; Lia.lia.
Qed.

Definition constprop :=
  fun e => match interp0_expr e with
           | Some v => ExprApp (const v, nil)
           | _ => e end.
Global Instance constprop_ok : Ok constprop.
Proof using Type. t. f_equal; eauto using eval_eval. Qed.

(* convert unary operations to slice *)
Definition unary_truncate :=
  fun e => match e with
    ExprApp (o, [x]) =>
    match unary_truncate_size o with
    | Some (-1)%Z => x
    | Some 0%Z => ExprApp (const 0, nil)
    | Some (Zpos p)
      => ExprApp (slice 0%N (Npos p), [x])
    | _ => e end | _ => e end.

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
Hint Rewrite signed_0 : zsimplify_const zsimplify zsimplify_fast.
Global Hint Resolve signed_0 : zarith.

Lemma interp_op_drop_identity o id : identity o = Some id ->
  forall G xs, interp_op G o xs = interp_op G o (List.filter (fun v => negb (Z.eqb v id)) xs).
Proof using Type.
  destruct o; cbn [identity]; intro; inversion_option; subst; intros G xs; cbn [interp_op]; f_equal.
  all: break_innermost_match_hyps; inversion_option; subst.
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
  destruct o; cbn [identity] in *; break_innermost_match_hyps; inversion_option; subst; cbn [interp_op fold_right]; f_equal.
  all: cbn [interp_op fold_right]; autorewrite with zsimplify_const; try reflexivity.
  { cbn [identity]; break_innermost_match; try reflexivity.
    rewrite Z.land_ones by lia; Z.rewrite_mod_small; try reflexivity;
      (* compat with older versions of Coq (needed for 8.11, not for 8.13) *)
      rewrite Z.mod_small; rewrite ?Z.log2_lt_pow2; cbn [Z.log2]; try lia. }
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
    eexists; split; eauto; f_equal; try ring; try solve [Z.bitblast].
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
  destruct o; inversion H; cbn [interp_op Option.bind fold_right]; f_equal.
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
  cbv [is_Some]; break_innermost_match; try reflexivity.
  exfalso.
  clear -H1.
  revert dependent vxs; induction xs as [|?? IH]; cbn in *; intros; inversion_option.
  unfold Option.bind at 1 in H1; break_innermost_match_hyps; eauto.
Qed.

Lemma interp_op_associative_spec_assoc o : associative o = true ->
  forall G ys vys, interp_op G o ys = Some vys ->
  forall   zs vzs, interp_op G o zs = Some vzs ->
  forall x, ((xy <- interp_op G o [x; vys]; interp_op G o [xy; vzs]) = (yz <- interp_op G o [vys; vzs]; interp_op G o [x; yz]))%option.
Proof.
  destruct o; inversion 1; intros * H1 * H2; cbn [interp_op fold_right Option.bind] in *.
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
  destruct (Option.List.lift (map (interp_op G o) xs)) as [vxs|]; cbn [Option.bind].
  { revert vxs; clear xs.
    induction x as [|x xs IHxs]; intro vxs.
    { cbn [fold_right].
      destruct (interp_op G o []) as [id|] eqn:H'; cbn [Option.bind].
      { etransitivity; erewrite interp_op_drop_identity by (erewrite <- interp_op_associative_spec_id; eassumption); [ | reflexivity ].
        cbn [List.filter]; unfold negb at 2; break_innermost_match_step; reflect_hyps; try congruence. }
      { pose proof (interp_op_associative_identity_Some o H G vxs) as H1.
        rewrite interp_op_associative_spec_id in * by assumption.
        rewrite H' in *.
        cbn [is_Some] in *.
        destruct interp_op; try reflexivity; specialize (H1 _ eq_refl); congruence. } }
    { cbn [fold_right].
      rewrite IHxs; clear IHxs.
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      unfold Option.bind at 2; break_innermost_match_step; cbn [Option.bind]; [ | reflexivity ].
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      symmetry.
      setoid_rewrite interp_op_associative_spec_fold at 2; [ | assumption ].
      cbn [fold_right].
      setoid_rewrite <- interp_op_associative_spec_fold; [ | assumption ].
      destruct (interp_op G o vxs) eqn:?; cbn [Option.bind]; [ | cbv [Option.bind]; break_match; reflexivity ].
      eapply interp_op_associative_spec_assoc; eassumption. } }
  { etransitivity; [ | cbv [Option.bind]; break_innermost_match; reflexivity ].
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
    cbv [Option.bind]; break_innermost_match; reflexivity. }
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
  rewrite List.app_nil_r, H1 in H2; cbn [Option.bind] in *; congruence.
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
  rewrite !H1, H2; cbn [Option.bind].
  reflexivity.
Qed.

Definition flatten_associative :=
  fun e => match e with
    ExprApp (o, args) =>
    if associative o then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end.
Global Instance flatten_associative_ok : Ok flatten_associative.
Proof using Type.
  repeat step.
  revert dependent v; induction H2; cbn.
  { econstructor; eauto. }
  intros ? H4.
  pose proof H4.
  eapply invert_interp_op_associative in H4; eauto. destruct H4 as (?&?&?).
  specialize (IHForall2 _ ltac:(eassumption)).
  inversion IHForall2; subst.
  destruct x as [i|[o' args''] ].
  { econstructor. { econstructor. eauto. eauto. }
    erewrite interp_op_associative_cons; eauto. }
  { destruct (op_beq_spec o o'); subst; cycle 1.
    { econstructor. { econstructor. eauto. eauto. }
      erewrite interp_op_associative_cons; eauto. }
    inversion H; clear H; subst.
    econstructor; eauto using Forall2_app.
    erewrite interp_op_associative_app; eauto. }
Qed.

Definition consts_commutative :=
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

Global Instance consts_commutative_ok : Ok consts_commutative.
Proof using Type.
  step.
  destruct e; trivial.
  destruct n.
  destruct commutative eqn:?; trivial.
  inversion H; clear H; subst.
  epose proof Permutation_partition l isCst.
  eapply Permutation.Permutation_Forall2 in H2; [|eassumption].
  DestructHead.destruct_head'_ex; DestructHead.destruct_head'_and.
  epose proof permute_commutative  _ _ _ _ Heqb H4 _ H0.
  repeat Econstructor; eauto.
  destruct associative eqn:?; [|solve[repeat Econstructor; eauto] ].
  BreakMatch.break_match; [|solve[repeat Econstructor; eauto] ].

  set (fst (partition isCst l)) as csts in *; clearbody csts.
  set (snd (partition isCst l)) as exps in *; clearbody exps.
  clear dependent l. clear dependent args'.
  move o at top; move Heqb0 at top; move Heqb at top.
  eapply eval_interp0_expr in Heqo0; instantiate (1:=d) in Heqo0; instantiate (1:=G) in Heqo0.

  eapply Forall2_app_inv_l in H1; destruct H1 as (?&?&?&?&?); subst.
  rename x0 into xs. rename x1 into ys.
  econstructor. { econstructor. econstructor. econstructor. exact eq_refl. eassumption. }

  inversion Heqo0; clear Heqo0; subst.
  eapply eval_eval_Forall2 in H; eauto; subst.
  clear dependent exps. clear dependent csts.
  clear -H2 H6 Heqb Heqb0.

  change (?x :: ?xs) with ([x] ++ xs).
  rewrite interp_op_associative_app_bind in * by assumption.
  erewrite interp_op_associative_idempotent by eassumption; cbn [Option.bind].
  unfold Option.bind in * |- .
  break_innermost_match_hyps; inversion_option; subst; cbn [Option.bind].
  assumption.
Qed.

Definition neqconst i := fun a : expr => negb (option_beq Z.eqb (interp0_expr a) (Some i)).
Definition drop_identity :=
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

Definition fold_consts_to_and :=
  fun e => match consts_commutative e with
           | ExprApp ((and _ | andZ) as o, ExprApp (const v, nil) :: args)
             => let v' := match o with
                          | and sz => Z.land v (Z.ones (Z.of_N sz))
                          | _ => v
                          end in
                if (v' <? 0)%Z
                then if (v' =? -1)%Z
                     then ExprApp (andZ, args)
                     else ExprApp (andZ, ExprApp (const v', nil) :: args)
                else let v_sz := (1 + Z.log2 v') in
                     if (v' =? Z.ones v_sz)%Z
                     then ExprApp (and (Z.to_N v_sz), args)
                     else ExprApp (and (Z.to_N v_sz), ExprApp (const v', nil) :: args)
           | _ => e
           end.

Global Instance fold_consts_to_and_Ok : Ok fold_consts_to_and.
Proof using Type.
  repeat (step; eauto; []).
  break_innermost_match; try assumption; reflect_hyps.
  all: match goal with
       | [ H : eval _ _ ?e _, H' : consts_commutative ?e = _ |- _ ]
         => apply consts_commutative_ok in H; rewrite H' in H; clear e H'
       end.
  all: repeat (step; eauto; []).
  all: cbn [interp_op fold_right] in *; inversion_option; subst.
  all: repeat first [ match goal with
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
                      end
                    | progress autorewrite with zsimplify_const
                    | apply (f_equal (@Some _))
                    | progress cbn [fold_right]
                    | rewrite Z2N.id by auto with zarith
                    | solve [ t ]
                    | solve [ Z.bitblast; now rewrite Z.bits_above_log2 by lia ]
                    | t ].
Qed.

Definition xor_same :=
  fun e => match e with ExprApp (xor _,[x;y]) =>
    if expr_beq x y then ExprApp (const 0, nil) else e | _ => e end.
Global Instance xor_same_ok : Ok xor_same.
Proof using Type.
  t; cbn [fold_right]. rewrite Z.lxor_0_r, Z.lxor_nilpotent; trivial.
Qed.

Definition shift_to_mul :=
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
Global Instance shift_to_mul_ok : Ok shift_to_mul.
Proof. t; cbn in *; rewrite ?Z.shiftl_mul_pow2, ?Z.land_0_r by lia; repeat (lia + f_equal). Qed.

Print eval.

(* o is like mul *)
(* invariant: Forall2 (fun x '(y, z) => eval (o x i) matches eval (o y z)) input output *)
Definition split_consts (o : op) (i : Z) : list expr -> list (expr * Z)
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
Definition group_consts (ls : list (expr * Z)) : list (expr * list Z)
  := Option.List.map
       (fun xs => match xs with
                  | [] => None
                  | (e, z) :: xs => Some (e, z :: List.map snd xs)
                  end)
       (List.groupAllBy (fun x y => expr_beq (fst x) (fst y)) ls).

(* o is like add *)
(* spec: if interp0_op o zs is always Some _, then Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) input output *)
Definition compress_consts (o : op) (ls : list (expr * list Z)) : list (expr * Z)
  := List.flat_map
       (fun '(e, zs) => match interp0_op o zs with
                        | None => List.map (pair e) zs
                        | Some z => [(e, z)]
                        end)
       ls.

(* o is like mul *)
(* spec is that Forall (fun '(e, z) e' => o (eval e) z matches eval e') inputs outputs *)
Definition app_consts (o : op) (ls : list (expr * Z)) : list expr
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

Definition combine_consts_pre : expr -> expr :=
  fun e => match e with ExprApp (o, args) =>
    if commutative o && associative o && op_always_interps o then match combines_to o with
    | Some o' => match identity o' with
    | Some idv =>
        ExprApp (o, app_consts o' (compress_consts o (group_consts (split_consts o' idv args))))
    | None => e end | None => e end else e | _ => e end%bool.

(* Definition distribute_const_mul : expr -> expr :=
  let simplify_addend := List.fold_left (fun e f => f e) [consts_commutative; flatten_associative] in (* should other rewrite rules be used here? *)
  fun e =>
  match e with
  | ExprApp (mul s, [ExprApp (const c, []); ExprApp (add s', args)]) =>
      if N.eqb s s' then
        ExprApp (add s, map (fun arg => simplify_addend (ExprApp (mul s, [ExprApp (const c, []); arg]))) args)
      else
        e
  | ExprApp (mulZ, [ExprApp (const c, []); ExprApp (addZ, args)]) =>
        ExprApp (addZ, map (fun arg => simplify_addend (ExprApp (mulZ, [ExprApp (const c, []); arg]))) args)
  | _ => e
  end. *)


Definition a := ExprApp (const 5, []).
Definition b := ExprApp (const 4, []).
Definition c := ExprApp (add 64%N, [ExprRef 1%N; ExprRef 2%N]).
Definition d := ExprApp (mul 64%N, [a; c]).
Definition e := ExprApp (mul 64%N, [b; c]).
Definition f := ExprApp (add 64%N, [ExprRef 1%N; ExprRef 2%N; e]).
Definition g := ExprApp (add 64%N, [a; b; c]).
Definition h := ExprApp (mul 64%N, [a; b; c]).

Compute f.
Compute (combine_consts_pre f).
Compute (split_consts (mul 64%N) 1 [ExprRef 1%N; ExprRef 2%N; b; c]).
Compute (group_consts (split_consts (mul 64%N) 1 [c; b; b; c])).
Compute (compress_consts (add 64%N) (group_consts (split_consts (mul 64%N) 1 [b; b; c]))).
Compute (app_consts (mul 64%N) (compress_consts (add 64%N) (group_consts (split_consts (mul 64%N) 1 [b; b; c])))).

Definition cleanup_combine_consts : expr -> expr :=
  let simp_outside := List.fold_left (fun e f => f e) [flatten_associative] in
  let simp_inside := List.fold_left (fun e f => f e) [constprop;drop_identity;unary_truncate;truncate_small] in
  fun e => simp_outside match e with ExprApp (o, args)  =>
    ExprApp (o, List.map simp_inside args)
                   | _ => e end.
Compute (cleanup_combine_consts (combine_consts_pre f)).

Definition combine_consts : expr -> expr := fun e => cleanup_combine_consts (combine_consts_pre e).

Lemma split_consts_correct o i ls G d argsv
      (H : Forall2 (eval G d) ls argsv)
      (Hi : identity o = Some i)
  : Forall2 (fun '(e, z) v => exists v',
    eval G d e v' /\
    (interp_op G o [v'; z] = Some v \/ (z = i /\ (v = v' \/ interp_op G o [v'] = Some v)))) (split_consts o i ls) argsv.
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

Lemma group_consts_Permutation ls
  : Permutation (List.concat (List.map (fun '(e, zs) => List.map (pair e) zs) (group_consts ls))) ls.
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

Lemma group_consts_nonempty ls
  : Forall (fun '(e, zs) => zs <> nil) (group_consts ls).
Proof.
  cbv [group_consts].
  let fv := match goal with |- context[List.groupAllBy ?f ls] => f end in
  pose proof (@List.Forall_groupAllBy_full _ fv ls) as H;
  generalize dependent (List.groupAllBy fv ls); intro gfls; intros.
  induction gfls as [|x xs IH]; cbn [list_rect Option.List.map fold_right] in *; break_innermost_match; destruct_head'_and; destruct_head'_False;
    constructor; try congruence; eauto.
Qed.

Lemma compress_consts_correct o ls
      (Ho : op_always_interps o = true)
  : Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) ls (compress_consts o ls).
Proof.
  cbv [compress_consts].
  induction ls as [|x xs IH]; cbn [List.flat_map]; break_innermost_match; cbn [List.app];
    try solve [ exfalso; eapply interp0_op_always_interps; eassumption ]; constructor; eauto.
Qed.

(* in a more specific, usable form *)
Lemma compress_consts_correct_alt G d o' o ls argsv
      (Ho : op_always_interps o = true)
      (H : Forall2 (fun '(e, zs) v => exists z, interp0_op o zs = Some z /\ exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) ls argsv)
  : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) (compress_consts o ls) argsv.
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
      (H : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o xs = Some z) /\ eval G d e v' /\ interp_op G o [v'; z] = Some v) ls argsv)
  : Forall2 (eval G d) (app_consts o ls) argsv.
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
  all: cbn [interp_op fold_right] in *; inversion_option; subst; apply f_equal.
  all: autorewrite with zsimplify_const in *.
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
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
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
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
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
         | [ |- eval _ _ (?r ?e) _ ]
           => apply (_:Ok r)
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
  | H : eval ?c ?d ?e _ |- context[?r ?e] =>
    let Hr := fresh in epose proof ((_:Ok r) _ _ _ _ H) as Hr; clear H
  end.
  assumption.
Qed.

Global Instance combine_consts_pre_Ok : Ok combine_consts_pre.
Proof using Type.
  repeat (step; eauto; []).
  match goal with
  | [ |- context[split_consts ?o ?i ?l] ]
    => pose proof (@split_consts_correct o i l _ _ _ ltac:(eassumption) ltac:(assumption)) as Hs
  end.
  match goal with
  | [ |- context[group_consts ?ls] ]
    => pose proof (@group_consts_Permutation ls) as Hg;
       pose proof (@group_consts_nonempty ls) as Hg'
  end.
  eapply Permutation_Forall2 in Hs; [ | symmetry; exact Hg ].
  destruct Hs as [? [? Hs] ].
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

(* Begin or-to-add stuff *)

Definition is_power_of_2 bound :=
  if fst bound =? snd bound then
    2^(Z.log2 (fst bound)) =? fst bound
  else false.

(* Definition left_shift d i :=
  match dag.lookup_bounds d i with
  | Some bounds => if (fst bounds =? snd bounds) && (2^(Z.log2 (fst bounds)) =? fst bounds) then
    Z.log2 (fst bounds) else 0
  | None => 0
  end. *)

Definition left_shift d e :=
  match bound_expr' d e with
  | Some bounds => if (fst bounds =? snd bounds) && (2^(Z.log2 (fst bounds)) =? fst bounds) then
    Z.log2 (fst bounds) else 0
  | None => 0
  end.

Lemma left_shifted ctx d e n :
  bounds_ok d ->
  eval ctx d e n ->
  ((2 ^ (left_shift d e)) | n)%Z.
Proof.
  intros H_bounds H. cbv [left_shift]. Search bound_expr'. destruct (bound_expr' d e) as [bounds|] eqn:E.
  - destruct (_ && _) eqn:E'.
    + Search bound_expr'. remember (eval_bound_expr' ctx d e H_bounds) as H'. clear HeqH' H_bounds.
      destruct bounds as [l u]. apply H' with (n := n) in E.
      -- simpl in E'. simpl. Search (_ && _ = _ -> _). apply andb_prop in E'. destruct E' as [E1 E2].
         assert (H1: n = l) by lia. subst. assert (H1: 2^Z.log2 l = l) by lia. rewrite H1.
         exists 1. lia.
      -- assumption.
    + exists n. lia.
  - exists n. lia.
Qed.

Lemma left_shift_nonneg d e :
  0 <= left_shift d e.
Proof.
  cbv [left_shift]. destruct (bound_expr' d e) as [bounds|]; try lia. destruct (_ && _); try lia. apply Z.log2_nonneg.
Qed.

(* Definition left_shifts (d : dag) (i : idx) :=
  match dag.lookup d i with
  | Some ((mul _ | mulZ), args) =>
    fold_right Z.add 0 (map (left_shift d) args)
  | _ => 0
  end. *)

Definition left_shifts (d : dag) (e : expr) :=
  let e' := match e with (* should use reveal_node here, or something? *)
            | ExprRef i =>
              match dag.lookup d i with
              | None => e
              | Some (o, args) => ExprApp (o, map ExprRef args)
              end
            | _ => e
            end
  in
  match e' with
  | ExprApp ((mul _ | mulZ), args) =>
    fold_right Z.add 0 (map (left_shift d) args)
  | _ => 0
  end.

Lemma abs_mod_0 a b :
  (Z.abs a) mod (Z.abs b) = 0 ->
  a mod b = 0.
Proof.
  destruct (b =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. intros. rewrite Zmod_0_r in *. rewrite <- Z.abs_0_iff. apply H.
  - intros. apply Z.eqb_neq in E. remember E as E'; clear HeqE'.
    apply Z.rem_mod with (a := a) in E. rewrite H in E. apply Z.rem_mod_eq_0 with (a := a) in E'. rewrite <- E'.
    lia.
Qed.

Lemma divide_mod a e b e' :
  (a ^ e | b)%Z ->
  (a ^ e | b mod (a ^ e'))%Z.
Proof.
  intros. destruct (0 <=? e') eqn:E0.
  - apply Z.leb_le in E0. destruct (b =? 0) eqn:E0'.
    + apply Z.eqb_eq in E0'. subst. rewrite Zmod_0_l. exists 0. lia.
    + apply Z.eqb_neq in E0'. destruct (0 <=? e) eqn:E1.
      -- apply Z.leb_le in E1. destruct (e <=? e') eqn:E2.
        ++ apply Z.leb_le in E2. apply Z.divide_add_cancel_r with (m := a ^ e' * (b / a ^ e')).
          --- exists (a ^ (e' - e) * (b / a ^ e')). replace (a ^ e') with (a ^ e * a ^ (e' - e)); try lia.
         rewrite <- Z.pow_add_r; try lia. f_equal. lia.
          --- rewrite <- Z_div_mod_eq_full. apply H.
        ++ apply Z.leb_nle in E2. replace (b mod a ^ e') with 0.
          --- exists 0. lia.
          --- symmetry. apply abs_mod_0. rewrite Znumtheory.Zmod_div_mod with (m := Z.abs b).
            +++ rewrite Z_mod_same_full. rewrite Zmod_0_l. reflexivity.
            +++ remember (Z.abs_nonneg (a ^ e')) as H1; clear HeqH1. assert (a ^ e' <> 0).
              ---- intros H'. rewrite Z.pow_eq_0_iff in H'. destruct H' as [H'|H'].
                ++++ lia.
                ++++ assert (H'': e <> 0) by lia. destruct H' as [_ H']. subst. apply Z.pow_0_l' in H''.
                     rewrite H'' in H. destruct H as [x H]. lia.
              ---- rewrite <- Z.abs_0_iff in H0. lia.
            +++ remember (Z.abs_nonneg b) as H1; clear HeqH1. rewrite <- Z.abs_0_iff in E0'. lia.
            +++ rewrite Z.divide_abs_l. rewrite Z.divide_abs_r.
                replace e with (e' + (e - e')) in H by lia. rewrite Z.pow_add_r in H by lia.
                destruct H as [x H]. exists (x * a ^ (e - e')). lia.
      -- apply Z.leb_nle in E1. replace (a ^ e) with 0 in H.
              ---- destruct H as [x H].  lia.
              ---- symmetry. apply Z.pow_neg_r. lia.
  - apply Z.leb_nle in E0. replace (a ^ e') with 0.
    + rewrite Zmod_0_r. assumption.
    + symmetry. apply Z.pow_neg_r. lia.
Qed.

Lemma sum_nonneg l :
  Forall (fun x => 0 <= x) l ->
  0 <= fold_right Z.add 0 l.
Proof.
  induction l as [|x l' IHl'].
  - intros. simpl. lia.
  - intros. inv H. apply IHl' in H3. simpl. lia.
Qed.

Lemma exp_sum a l :
  Forall (fun x => 0 <= x) l ->
  a ^ fold_right Z.add 0 l = fold_right Z.mul 1 (map (fun x => a ^ x) l).
Proof.
  intros. induction l as [| x l' IHl'].
  - simpl. reflexivity.
  - simpl. inv H. remember (sum_nonneg _ H3) as H3'; clear HeqH3'. rewrite Z.pow_add_r by assumption.
    apply IHl' in H3. rewrite H3. reflexivity.
Qed.

Lemma product_divide l1 l2 :
  Forall2 (fun a b => Z.divide a b) l1 l2 ->
  (fold_right Z.mul 1 l1 | fold_right Z.mul 1 l2).
Proof.
  generalize dependent l2. induction l1 as [|x l1' IHl1'].
  - intros. inv H. simpl. exists 1. lia.
  - intros. inv H. simpl. apply IHl1' in H4. destruct H2 as [x1 H2]. destruct H4 as [x2 H4]. exists (x2 * x1). lia.
Qed.

(* this is atrocious; wrote same long proof twice in case analysis.  should refactor. *)
Lemma lefts_shifted ctx d e n :
  bounds_ok d ->
  eval ctx d e n ->
  (2^(left_shifts d e) | n)%Z.
Proof.
  intros H_bounds H. cbv [left_shifts].
  destruct e as [i | [o args] ].
  - destruct (dag.lookup d i) as [ [o args]|] eqn:E.
    + inv H. rewrite H1 in E. inv E.
    assert (H': (2 ^ fold_right Z.add 0 (map (left_shift d) (map ExprRef args)) | fold_right Z.mul 1 args')).
       -- assert (H4: Forall (fun x => 0 <= x) (map (left_shift d) (map ExprRef args))).
        { clear H1 H2. induction args as [|arg args1 IHargs1].
          - constructor.
          - constructor.
            + apply left_shift_nonneg.
            + apply IHargs1.
        }
        rewrite (exp_sum _ _ H4). clear H4. rewrite map_map. apply product_divide. clear H1 H3. generalize dependent args'.
        induction args as [| arg args1 IHargs1].
          ++ intros. inv H2. constructor.
          ++ intros. inv H2. constructor.
            --- apply left_shifted with (ctx := ctx); assumption.
            --- apply IHargs1. assumption.
      -- destruct o; try (exists n; subst; lia).
        ++ inv H3. rewrite Z_land_ones'. apply divide_mod. apply H'.
        ++ inv H3. apply H'.
    + exists n. lia.
  - inv H.
    assert (H': (2 ^ fold_right Z.add 0 (map (left_shift d) args) | fold_right Z.mul 1 args')).
       -- assert (H5: Forall (fun x => 0 <= x) (map (left_shift d) args)).
        { clear H2 H4. induction args as [|arg args1 IHargs1].
          - constructor.
          - constructor.
            + apply left_shift_nonneg.
            + apply IHargs1.
        }
        rewrite (exp_sum _ _ H5). clear H5. rewrite map_map. apply product_divide. clear H4. generalize dependent args'.
        induction args as [| arg args1 IHargs1].
          ++ intros. inv H2. constructor.
          ++ intros. inv H2. constructor.
            --- apply left_shifted with (ctx := ctx); assumption.
            --- apply IHargs1. assumption.
      -- destruct o; try (exists n; subst; lia).
        ++ inv H4. rewrite Z_land_ones'. apply divide_mod. apply H'.
        ++ inv H4. apply H'.
Qed.

Definition or_is_add (d : dag) (args : list expr) : bool :=
  match args with
  | [arg1; arg2] =>
    match bound_expr' d arg1 with
    | Some bounds => if subset bounds (0, 2 ^ left_shifts d arg2 - 1) then true else
      match bound_expr' d arg2 with
      | Some bounds => if subset bounds (0, 2 ^ left_shifts d arg1 - 1) then true else false
      | _ => false
      end
    | None => match bound_expr' d arg2 with
              | Some bounds => if subset bounds (0, 2 ^ left_shifts d arg1 - 1) then true else false
              | _ => false
              end
    end
  | _ => false
  end.

Lemma or_is_add_arith a b x :
  (2 ^ x | a) ->
  0 <= b < 2 ^ x ->
  Z.lor a b = Z.add a b.
Proof.
  intros. destruct (0 <=? x) eqn:E.
  - apply Z.leb_le in E. apply Z.or_to_plus. rewrite <- (Z.land_ones_low_alt b x); try lia.
    rewrite (Z.land_comm b). rewrite Z.land_assoc. rewrite Z.land_ones; try assumption.
      rewrite Znumtheory.Zdivide_mod by assumption. apply Z.land_0_l.
  - apply Z.leb_nle in E. rewrite Z.pow_neg_r in H0 by lia. lia.
Qed.

Lemma eval_orZ_is_addZ d args ctx n :
  bounds_ok d ->
  or_is_add d args = true ->
  eval ctx d (ExprApp (orZ, args)) n ->
  eval ctx d (ExprApp (addZ, args)) n.
Proof.
  intros. cbv [or_is_add] in H0. destruct args as [| arg1 [| arg2 [| args'] ] ]; try discriminate H0.
  inv H1. remember H4 as H5; clear HeqH5. inv H4. inv H8. inv H9. inv H6. rename y into arg1'. rename y0 into arg2'.
  cbv [bounds_ok] in H. Search bound_expr'. remember (eval_bound_expr' _ _ _ H _ H3) as H3'. remember (eval_bound_expr' _ _ _ H _ H4) as H4'.
  remember (lefts_shifted _ _ _ _ H H3) as H3''. remember (lefts_shifted _ _ _ _ H H4) as H4''. clear HeqH3' HeqH4' HeqH3'' HeqH4''.
  apply EApp with (args' := [arg1'; arg2']); try assumption. simpl. f_equal. rewrite Z.add_0_r. rewrite Z.lor_0_r.
  destruct (bound_expr' d arg1) as [bounds|] eqn:E1.
  - destruct (subset bounds (0, 2 ^ left_shifts d arg2 - 1)) eqn:E2.
    + symmetry. rewrite Z.lor_comm. rewrite Z.add_comm. apply or_is_add_arith with (x := left_shifts d arg2).
      -- apply H4''.
      -- apply subset_bounds in E2. simpl in H3'. destruct bounds as [min max]. simpl in *.
         assert (H3''' : min <= arg1' <= max). { apply H3'. reflexivity. } lia.
    + destruct (bound_expr' d arg2) eqn:E3.
      -- destruct (subset p _) eqn:E4.
        ++ clear H0. symmetry. apply or_is_add_arith with (x := left_shifts d arg1).
          --- apply H3''.
          --- apply subset_bounds in E4. simpl in H4'. destruct p as [min max]. cbv [subset] in E4. simpl in *.
              assert (H4''' : min <= arg2' <= max). {apply H4'. reflexivity. } lia.
        ++ discriminate H0.
      -- discriminate H0.
  - destruct (bound_expr' d arg2) as [bounds|] eqn:E2.
    + destruct (subset bounds (0, 2 ^ left_shifts d arg1 - 1)) eqn:E3.
      -- clear H0. symmetry. apply or_is_add_arith with (x := left_shifts d arg1).
        ++ apply H3''.
        ++ apply subset_bounds in E3. simpl in H4'. destruct bounds as [min max]. simpl in *.
           assert (H4''' : min <= arg2' <= max). { apply H4'. reflexivity. } lia.
      -- discriminate H0.
    + discriminate H0.
Qed.

Lemma ors_to_orZ ctx d s args n :
  eval ctx d (ExprApp (or s, args)) n ->
  exists m,
  n = m mod (2 ^ Z.of_N s) /\
  eval ctx d (ExprApp (orZ, args)) m.
Proof.
  intros. inv H. exists (fold_right Z.lor 0 args'). inv H4. split.
  - rewrite Z_land_ones'. reflexivity.
  - apply EApp with (args' := args').
    + apply H2.
    + simpl. reflexivity.
Qed.

Lemma eval_ors_is_adds d args ctx n s :
  bounds_ok d ->
  or_is_add d args = true ->
  eval ctx d (ExprApp (or s, args)) n ->
  eval ctx d (ExprApp (add s, args)) n.
Proof.
  intros. apply ors_to_orZ in H1. destruct H1 as [m [H1 H2] ]. subst. apply addZ_to_adds. apply eval_orZ_is_addZ; assumption.
Qed.

Definition new_op (d : dag) (o : op) (args : list idx) : op :=
  match o with
(*   | or s => if or_is_add d args then add s else or s *)
(*   | orZ => if or_is_add d args then addZ else orZ *)
  | _ => o
  end.

(* Definition new_op (d : dag) (o : op) (args : list idx) : op :=
  match o with
(*   | or s => if or_is_add d args then add s else or s *)
(*   | orZ => if or_is_add d args then addZ else orZ *)
  | _ => o
  end. *)

Definition or_to_add (d : dag) (e : expr) : expr :=
  match e with
  | ExprApp (or s, args) => ExprApp(if or_is_add d args then add s else or s, args)
  | ExprApp (orZ, args) => ExprApp(if or_is_add d args then addZ else orZ, args)
  | _ => e
  end.

Lemma eval_or_to_add ctx d e n :
  bounds_ok d ->
  eval ctx d e n ->
  eval ctx d (or_to_add d e) n.
Proof.
  intros. cbv [or_to_add]. destruct e as [i| [o args] ]; try apply H0. destruct o; try apply H0.
  - destruct (or_is_add _ _) eqn:E; try apply H0. apply eval_ors_is_adds; assumption.
  - destruct (or_is_add _ _) eqn:E; try apply H0. apply eval_orZ_is_addZ; assumption.
Qed.

(* end or-to-add stuff *)

Check in_dec.
Search (string -> string -> bool).

(* "named" rewrite rules are off by default and can be turned on using the commmand-line option*)
Definition rewrite_rules_and_names (d : dag) : list ((expr -> expr) * option string) :=
  [
  (constprop, None)
  ;(slice0, None)
  ;(slice01_addcarryZ, None)
  ;(slice01_subborrowZ, None)
  ;(set_slice_set_slice, None)
  ;(slice_set_slice, None)
  ;(set_slice0_small, None)
  ;(shift_to_mul, None)
  ;(flatten_associative, None)
  ;(consts_commutative, None)
  ;(fold_consts_to_and, None)
  ;(drop_identity, None)
  ;(unary_truncate, None)
  ;(truncate_small, None)
  ;(combine_consts, None)
(*   ;(distribute_const_mul, None) *)
  ;(or_to_add d, Some "or-to-add")
  ;(addoverflow_bit, None)
  ;(addcarry_bit, None)
  ;(addcarry_small, None)
  ;(addoverflow_small, None)
  ;(addbyte_small, None)
  ;(xor_same, None)
  ]%string.

Search (map (filter _)).

Check List.fold_right.

Definition rules_to_use {errules : extra_rewrite_rules} d : list (expr -> expr) :=
  map fst (filter (fun f_name => match f_name with
                        | (f, None) => true
                        | (f, Some name) => (0 <? count_occ string_dec errules name)%nat
                        end) (rewrite_rules_and_names d)).

Definition expr {errules : extra_rewrite_rules} (d : dag) : expr -> expr :=
  List.fold_left (fun e f => f e) (rules_to_use d).

Lemma property_fold_left {X} (P : X -> Prop) fs :
  Forall (fun f => (forall e : X, P e -> P (f e))) fs ->
  forall e : X,
  P e -> P (fold_left (fun e' f => f e') fs e).
Proof.
  intros H. induction fs as [|f fs' IHfs'].
  - simpl. intros. assumption.
  - simpl. intros. inv H. apply IHfs'; auto.
Qed.

Lemma rules_subset {errules : extra_rewrite_rules} d :
  incl (rules_to_use d) (map fst (rewrite_rules_and_names d)).
Proof.
  apply incl_map. apply incl_filter.
Qed.

Lemma all_rewrite_rules_ok ctx d n :
  gensym_dag_ok ctx d ->
  Forall (fun f => forall e, eval ctx d e n -> eval ctx d (f e) n) (map fst (rewrite_rules_and_names d)).
Proof.
  intros Hdag. repeat constructor. all: intros; simpl; try apply ((_:Ok _) _ _ _ _ H).
  - cbv [gensym_dag_ok dag_ok] in Hdag. apply eval_or_to_add; intuition.
Qed.

Lemma eval_expr {errules : extra_rewrite_rules} c d (Hdag : gensym_dag_ok c d) e v : eval c d e v -> eval c d (expr d e) v.
Proof using Type.
  intros H; cbv [expr]. apply property_fold_left; try assumption. Check incl_Forall.
  apply (incl_Forall (rules_subset d)). apply all_rewrite_rules_ok. assumption.
Qed.

End Rewrite.

Definition simplify {errules : extra_rewrite_rules} (dag : dag) (e : node idx) :=
  Rewrite.expr dag (reveal_node_at_least dag 3 e).

Lemma eval_simplify {errules : extra_rewrite_rules} G d n v :
  gensym_dag_ok G d ->
  eval_node G d n v ->
  eval G d (simplify d n) v.
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
    ++List.map (fun '(i, v, descr, bounds) =>"(*"++show i ++"*) " ++ show v++";"
                                         ++ "(((" ++ show bounds ++ ")))" ++
                                            ((* if dag.get_eager_description_always_show descr
                                             then *) match dag.get_eager_description_description descr with
                                                  | Some descr => " " ++ String.Tab ++ "(*" ++ descr ++ "*)"
                                                  | None => ""
                                                  end
                                             (* else "" *)))%string (dag.eager.force d)
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
Definition App {descr : description} {errules : extra_rewrite_rules} (n : node idx) : M idx :=
  fun s => Merge (simplify s n) s.
Definition Reveal n (i : idx) : M expr :=
  fun s => Success (reveal s n i, s).
Definition RevealConst (i : idx) : M Z :=
  x <- Reveal 1 i;
  match x with
  | ExprApp (const n, nil) => ret n
  | _ => err (error.expected_const i x)
  end.

Definition GetReg {descr:description} {errules : extra_rewrite_rules} r : M idx :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  v <- GetReg64 rn;
  App ((slice lo sz), [v]).
Definition SetReg {descr:description} {errules : extra_rewrite_rules} r (v : idx) : M unit :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  if N.eqb sz 64
  then v <- App (slice 0 64, [v]);
       SetReg64 rn v (* works even if old value is unspecified *)
  else old <- GetReg64 rn;
       v <- App ((set_slice lo sz), [old; v]);
       SetReg64 rn v.

Class AddressSize := address_size : OperationSize.
Definition Address {descr:description} {sa : AddressSize} {errules : extra_rewrite_rules} (a : MEM) : M idx :=
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

Definition Load {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Load64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Remove {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Remove64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Store {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (a : MEM) v : M unit :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  old <- Load64 addr;
  v <- App (slice 0 (Syntax.operand_size a s), [v]);
  v <- App (set_slice 0 (Syntax.operand_size a s), [old; v])%N;
  Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App (zconst s a, [])
  | mem a => Load a
  | reg r => GetReg r
  | label l => err (error.unsupported_label_argument l)
  end.

Definition SetOperand {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (o : ARG) (v : idx) : M unit :=
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

Fixpoint Symeval {descr:description} {s : OperationSize} {sa : AddressSize} {errules : extra_rewrite_rules} (e : pre_expr) : M idx :=
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
Definition SymexNormalInstruction {descr:description} {errules : extra_rewrite_rules} (instr : NormalInstruction) : M unit :=
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
    =>
    v <- Symeval (selectznz@(CF, dst, src));
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

Definition SymexRawLine {descr:description} {errules : extra_rewrite_rules} (rawline : RawLine) : M unit :=
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

Definition SymexLine {errules : extra_rewrite_rules} line :=
  let descr:description := Build_description (show line) false in
  SymexRawLine line.(rawline).

Fixpoint SymexLines {errules : extra_rewrite_rules} (lines : Lines) : M unit
  := match lines with
     | [] => ret tt
     | line :: lines
       => (st <- SymexLine line;
          SymexLines lines)
     end.
