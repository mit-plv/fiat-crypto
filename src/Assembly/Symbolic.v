Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Module Import List.
  Definition option_all [A] : list (option A) -> option (list A) := OptionList.Option.List.lift.
  Lemma option_all_Some [A] ol l (H : @option_all A ol = Some l)
    : forall i a, nth_error l i = Some a -> nth_error ol i = (Some (Some a)).
  Admitted.
  Lemma option_all_None [A] ol (H : @option_all A ol = None)
    : exists j, nth_error ol j = None.
  Admitted.

  Section IndexOf.
    Context [A] (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_none l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Admitted.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a -> f a = true.
    Admitted.
    Lemma indexof_first l i (H : indexof l = Some i) :
      forall j a, j < i -> nth_error l j = Some a -> f a = false.
    Admitted.
  End IndexOf.


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let b_s := f a s in
          let bs_s := foldmap l (snd b_s) in
          (cons (fst b_s) (fst bs_s), snd bs_s)
      end.
  End FoldMap.
End List.

Require Import Crypto.Assembly.Syntax.
Definition idx := Z.
Local Set Boolean Equality Schemes.
Variant opname := old (_:REG*option nat) | const (_ : Z) | add | sub | slice (lo sz : N) | set_slice (lo sz : N)(* | ... *).
Class OperationSize := operation_size : N.
Definition op : Set := opname * OperationSize.

Definition node (A : Set) : Set := op * list A.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).
  (* Note: need custom induction principle *)
Local Unset Elimination Schemes.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.

Definition node_eqb [A : Set] (arg_eqb : A -> A -> bool) : node A -> node A -> bool := 
  Prod.prod_beq _ _ (Prod.prod_beq _ _ opname_beq N.eqb) (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Section Reveal.
  Context (dag : dag).
  Definition reveal_step reveal (i : idx) : expr :=
    match List.nth_error dag (Z.to_nat i) with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Definition reveal_expr_step reveal reveal_expr (e : expr) : expr :=
    match e with
    | ExprRef i => reveal i
    | ExprApp (op, args) => ExprApp (op, List.map reveal_expr args)
    end.
  Fixpoint reveal_expr (n : nat) (e : expr) {struct n} : expr :=
    match n with
    | O => e
    | S n => reveal_expr_step (reveal n) (reveal_expr n) e
    end.
End Reveal.

Fixpoint merge (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let d : dag := snd idxs_d in
    let n : node idx := (op, fst idxs_d) in
    match List.indexof (node_eqb Z.eqb n) d with
    | Some i => (Z.of_nat i, d)
    | None => (Z.of_nat (length d), List.app d (cons n nil))
    end
  end.

Lemma reveal_merge : forall d e, exists n, reveal (snd (merge e d)) n (fst (merge e d)) = e.
Proof.
Admitted.

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

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).

Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreFlag (_:FLAG)
| PreReg (_:nat) (* 0 <= i < 16 *)
| PreMem {s: OperationSize} (_ : pre_expr)
| PreApp (_:node pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.

Require Import Crypto.Util.Option Crypto.Util.Notations.

Import ListNotations.

Section WithDag.
  Context (dag : dag).

  Definition simplify (e : expr) : expr :=
    List.fold_right (fun f e => f e) (reveal_expr dag 5 e)
    [fun e => match e with
      ExprApp (((add|sub),s), [a; ExprApp ((const 0, _), []) ]) =>
        if N.eqb s 64 then a else e | _ => e end
    ;fun e => match e with
      ExprApp ((sub,s)as op, [ExprApp ((add, s'), [a; b]); a']) =>
        if N.eqb s s' && expr_beq a a' then b else e | _ => e end
    ;fun e => match e with
      ExprApp ((sub,s), [a; b]) =>
        if expr_beq a b then ExprApp ((const 0, s), []) else e | _ => e end]%bool.
End WithDag.

Section WithSymbolicState.
  Context (st : symbolic_state).
  Local Open Scope option_scope.

  Definition load (sa : N) (e : expr) : option idx :=
    option_map snd (find (fun ptsto => expr_beq
          (simplify st (ExprApp ((sub, sa), [e; ExprRef (fst ptsto)])))
          (ExprApp ((const 0, sa), nil))) st.(symbolic_mem_state)).

  Definition store (sa : N) (e : expr) (v : idx) : option symbolic_state :=
    n <- (indexof (fun ptsto => expr_beq
          (simplify st (ExprApp ((sub, sa), [e; ExprRef (fst ptsto)])))
          (ExprApp ((const 0, sa), nil))) st.(symbolic_mem_state));
    Some (update_mem_with st (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)))).
      
  (* note: it would be more powerful to fuse this with [merge], but hopefully we don't have to *)
  Fixpoint symeval_pre (r : pre_expr) : option expr :=
    option_map (simplify st)
    match r with
    | PreFlag f => i <- get_flag st f; Some (ExprRef i)
    | PreReg r =>
        match List.nth_error (Tuple.to_list _ st.(symbolic_reg_state)) r with
        | Some (Some i) => Some (ExprRef i)
        | _ => None
        end
    | PreMem s e =>
        addr <- symeval_pre e;
        option_map ExprRef (load s addr)
    | PreApp (op, args) =>
        args <- List.option_all (List.map symeval_pre args);
        Some (ExprApp (op, args))
    end.
End WithSymbolicState.

Class AddressSize := address_size : N.
Definition PreAddress {sa : AddressSize} (a : MEM) : pre_expr :=
  PreApp (add, sa,
  [PreApp (add, sa,
   [PreReg (reg_index (mem_reg a));
   match mem_extra_reg a with
   | Some _ => PreReg (reg_index (mem_reg a))
   | None => PreApp ((const 0, sa), nil)
   end]);
   PreApp ((const match mem_offset a with Some z => z | _ => 0 end, sa), nil)]).

Section WithOperationSize.
  Context {sa : AddressSize} {s : OperationSize}.
  Definition PreOperand (a : ARG) : pre_expr :=
    match a with
    | reg a => PreReg (reg_index a)
    | mem a => PreMem (s:=s) (PreAddress (sa:=sa) a)
    | Syntax.const a => PreApp ((const a, s), nil)
  end.
  Definition symeval st a := symeval_pre st (PreOperand a).
  Definition symaddr st a := symeval_pre st (PreAddress a).

  Definition SetOperand (st : symbolic_state) (a : ARG) (e : expr) : option symbolic_state :=
    match a with
    | Syntax.const a => None
    | mem a =>
        addr <- symaddr st a;
        old <- load st sa addr;
        let e := if mem_is_byte a
             then simplify st (ExprApp ((set_slice 0 8, 64%N), [ExprRef old ;e]))
             else e in
        let i_dag := merge e st.(dag_state) in
        let i := fst i_dag in
        let st := update_dag_with st (fun _ => snd i_dag) in
        store st sa addr i
    | reg a =>
        let '(a, lo, sz) := index_and_shift_and_bitcount_of_reg a in
        e <- if N.eqb sz 64 then Some e else
             old <- get_reg st a;
             Some (simplify st (ExprApp ((set_slice lo sz, 64%N), [ExprRef old; e])));
        let i_dag := merge e st.(dag_state) in
        let i := fst i_dag in
        let st := update_dag_with st (fun _ => snd i_dag) in
        Some (update_reg_with st (fun rs => set_reg rs a i))
    end.

End WithOperationSize.

Definition SymexNormalInstruction (st : symbolic_state) (instr : NormalInstruction) : option symbolic_state :=
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some (Some s) =>
  let s : OperationSize := s in
  match instr.(Syntax.op), instr.(args) with
  | mov, [dst; src] => (* Note: unbundle when switching from N to Z *)
    e <- symeval st src;
    SetOperand st dst e
  | lea, [dst; mem src] => (* Flags Affected: None *)
    e <- symaddr st src;
    SetOperand st dst e
  | _, _ => None
 end | _ => None end%N%option.

Fixpoint SymexNormalInstructions st instrs : option symbolic_state :=
  match instrs with
  | nil => Some st
  | cons instr instrs =>
      st <- SymexNormalInstruction st instr;
      SymexNormalInstructions st instrs
  end.

Definition init
  (arrays : list (REG * nat)) (* full 64-bit registers only *)
  (stack : nat)
  : symbolic_state :=
  let sz := 64%N in
  let dag := List.map (fun i =>
    ((old (widest_register_of_index i,None), 64%N),[])) (seq 0 16) in
  let arrayentries := List.flat_map (fun r_n =>
    List.map (fun i => (fst r_n, i)) (List.seq 0 (snd r_n))) arrays in
  let heap_dag := foldmap (fun r_i dag => let r := fst r_i in
       let p_dag := merge (ExprApp ((add, sz),[ExprRef (Z.of_nat (reg_index r)); ExprApp ((const (8 * Z.of_nat (snd r_i)), sz), [])])) dag in
       let v_dag := merge (ExprApp ((old (r, Some (snd r_i)), sz),[])) (snd p_dag) in
       ((fst p_dag, fst v_dag), snd p_dag)
       ) arrayentries dag in
  let stack_dag := foldmap (fun i dag => let r := rsp in
       let p_dag := merge (ExprApp ((sub, sz),[ExprRef (Z.of_nat (reg_index r)); ExprApp ((const (8*Z.of_nat i), sz), [])])) dag in
       let v_dag := merge (ExprApp ((old (r, Some i), sz),[])) (snd p_dag) in
       ((fst p_dag, fst v_dag), snd p_dag)
       ) (seq 0 stack) (snd heap_dag) in
  let regs := List.map (fun i => Some (Z.of_nat i)) (seq 0 16) in
  {|
    dag_state := snd stack_dag;
    symbolic_reg_state := Tuple.from_list _ regs eq_refl;
    symbolic_mem_state := fst heap_dag ++ fst stack_dag;
    symbolic_flag_state := Tuple.repeat None 6
  |}.

Example test1 : match (
  let st := init [(rsi, 4)] 0 in
  (SymexNormalInstructions st
    [Build_NormalInstruction lea [reg rax; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction mov [reg rbx; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction lea [reg rcx; mem (Build_MEM false rsi (Some rbx) (Some 7%Z))]
    ;Build_NormalInstruction mov [         mem (Build_MEM false rsi None (Some 24%Z)); reg rcx]
    ])
) with None => False | Some st => True end. native_cast_no_check I. Qed.

Definition opt2err {Err T} (e : Err) (r : option T) :=
  match r with
  | None => Error e
  | Some r => Success r
  end.

Fixpoint SymexLines st (lines : list Syntax.Line) : ErrorT _ symbolic_state :=
  match lines with
  | nil => Success st
  | (cons line lines) as s =>
      match line.(rawline) with
      | INSTR instr => 
          st <- opt2err (st, s) (SymexNormalInstruction st instr);
          SymexLines st lines
      | _ => SymexLines st lines
      end
  end.

Require Crypto.Assembly.Parse Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.
Definition lines' := Eval native_compute in
  Assembly.Parse.parse
  Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.example.
Definition lines := Eval cbv in ErrorT.invert_result lines'.
Import Coq.Strings.String.
Local Open Scope string_scope.
(*
Compute
  let st := init [(rsi, 4); (rdi, 4)] 48 in
  SymexLines st lines.
*)
