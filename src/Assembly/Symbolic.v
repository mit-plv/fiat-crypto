Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
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
Variant opname := input (_:nat*nat) | const (_ : Z) | add | sub | slice (lo sz : Z) | set_slice (lo sz : Z)(* | ... *).
Class OperationSize := operation_size : Z.
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
  Prod.prod_beq _ _ (Prod.prod_beq _ _ opname_beq Z.eqb) (ListUtil.list_beq _ arg_eqb).

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
Definition mem_state := list (idx * list (option idx)).

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
    match reveal_expr dag 2 e with
    | ExprApp (((add|sub),s), [a; ExprApp ((const 0, _), []) ]) =>
        if Z.eqb s 64 then a else e
    | ExprApp ((sub,s)as op, [ExprApp ((add, s'), [a; b]); a']) =>
        if Z.eqb s s' && expr_beq a a' then b else e
    | _ => e
    end%bool.
  (* note: from Python script, calls [reveal] *)
End WithDag.

Section WithSymbolicState.
  Context (st : symbolic_state).

  (* Some = defined and specified, Some None = defined but unspecified, None = udnefined *)
  Definition load (sa : Z) (e : expr) : option (option expr) :=
    match
      Option.List.map (fun array =>
        let base := fst array in
        match simplify st (ExprApp ((sub, sa), [e; ExprRef base])) with
        | ExprApp ((const offset, _), nil) =>
            if (offset mod 8 =? 0)%Z then (* note: generalize mem repr? *)
            match nth_error (snd array) (Z.to_nat (offset/8)) with
            | Some (Some i) =>  Some (Some (ExprRef i))
            | Some None => Some None
            | _ => None
            end
            else None
        | _ => None
        end)
      st.(symbolic_mem_state)
    with
    | nil => None
    | cons r nil => Some r
    | _ => None (* multiple arrays match same address -- contradiction *)
    end.

  Definition unchecked_store (sa : Z) (e : expr) (v : idx) : symbolic_state :=
    update_mem_with st (List.map (fun array =>
      let base := fst array in
      match simplify st (ExprApp ((sub, sa), [e; ExprRef base])) with
      | ExprApp ((const offset, _), nil) =>
          if (offset mod 8 =? 0)%Z (* note: generalize mem repr? *)
          then (base, ListUtil.set_nth (Z.to_nat (offset/8)) (Some v) (snd array))
          else array
      | _ => array
      end)).
      
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
        v <- load s addr;
        v
    | PreApp (op, args) =>
        args <- List.option_all (List.map symeval_pre args);
        Some (ExprApp (op, args))
    end.
End WithSymbolicState.

Class AddressSize := address_size : Z.
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
        maybeold <- load st sa addr;
        e <- if mem_is_byte a
             then old <- maybeold; Some (simplify st (ExprApp ((set_slice 0 8, 64%Z), [old ;e])))
             else Some e;
        let i_dag := merge e st.(dag_state) in
        let i := fst i_dag in
        let st := update_dag_with st (fun _ => snd i_dag) in
        Some (unchecked_store st sa addr i)
    | reg a =>
        let '(a, lo, sz) := index_and_shift_and_bitcount_of_reg a in
        e <- if N.eqb sz 64 then Some e else
             old <- get_reg st a;
             Some (simplify st (ExprApp ((set_slice (Z.of_N lo) (Z.of_N sz), 64%Z), [ExprRef old; e])));
        let i_dag := merge e st.(dag_state) in
        let i := fst i_dag in
        let st := update_dag_with st (fun _ => snd i_dag) in
        Some (update_reg_with st (fun rs => set_reg rs a i))
    end.

End WithOperationSize.

Definition SymexNormalInstruction (st : symbolic_state) (instr : NormalInstruction) : option symbolic_state :=
  let sa : AddressSize := 64%Z in
  match Syntax.operation_size instr with Some (Some s) =>
  let s : OperationSize := Z.of_N s in
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

Compute
           load
             {|
               dag_state :=
                 [(input (0, 0), 64%Z, []); (input (1, 0), 64%Z, []);
                 (input (1, 1), 64%Z, []); (input (1, 2), 64%Z, []);
                 (input (1, 3), 64%Z, [])];
               symbolic_reg_state :=
                 (None, None, None, None, None, None, None, None, None,
                 Some 0%Z, None, None, None, None, None, None);
               symbolic_flag_state := (None, None, None, None, None, None);
               symbolic_mem_state :=
                 [(0%Z, [Some 1%Z; Some 2%Z; Some 3%Z; Some 4%Z])]
             |} 64
             (ExprApp
                (add, 64%Z, [ExprRef 0%Z; ExprApp (const 16, 64%Z, [])]))
                .

Eval cbv -[load] in
  let st := {|
          dag_state :=
            [(input (0, 0), 64%Z, []); (input (1, 0), 64%Z, []);
            (input (1, 1), 64%Z, []); (input (1, 2), 64%Z, []);
            (input (1, 3), 64%Z, [])];
          symbolic_reg_state :=
            (None, None, None, None, None, None, None, None, None, 
            Some 0%Z, None, None, None, None, None, None);
          symbolic_flag_state := (None, None, None, None, None, None);
          symbolic_mem_state :=
            [(0%Z, [Some 1%Z; Some 2%Z; Some 3%Z; Some 4%Z])]
        |} in
  SymexNormalInstructions st
    [Build_NormalInstruction mov [mem (Build_MEM true rsi None (Some 16%Z)); Syntax.const 0%Z] ].


Compute
  let inputs := [(0,0); (1,0); (1,1); (1,2); (1,3)] in
  let (inputs, dag) := foldmap merge (List.map (fun p => ExprApp ((input p,64%Z),[])) inputs) [] in
  let p := hd 0%Z inputs in
  let st := {|
    dag_state := dag;
    symbolic_reg_state := set_reg (Tuple.repeat None 16) (reg_index rsi) p;
    symbolic_flag_state := Tuple.repeat None 6;
    symbolic_mem_state := [(p, List.map Some (tl inputs))]
  |} in
  (st, SymexNormalInstructions st
    [Build_NormalInstruction lea [reg rax; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction mov [reg rbx; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction lea [reg rcx; mem (Build_MEM false rsi (Some rbx) (Some 7%Z))]
    ;Build_NormalInstruction mov [         mem (Build_MEM false rsi None (Some 24%Z)); reg rcx]
    ]).

