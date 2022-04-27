Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.
Require Import Crypto.Assembly.Syntax.
Require Crypto.Util.Tuple.
Import ListNotations.

Local Set Primitive Projections.

Local Open Scope list_scope.

Local Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Local Set Primitive Projections.

(** denotational semantics *)

Definition flag_state := Tuple.tuple (option bool) 6.
Definition get_flag (st : flag_state) (f : FLAG) : option bool
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option bool) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : bool) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).

Definition reg_state := Tuple.tuple Z 16.
Definition bitmask_of_reg (r : REG) : Z
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     Z.shiftl (Z.ones (Z.of_N bitcount)) (Z.of_N shift).
Definition get_reg (st : reg_state) (r : REG) : Z
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
  let rv := Tuple.nth_default 0%Z idx st in
  Z.land (Z.shiftr rv (Z.of_N shift)) (Z.ones (Z.of_N bitcount)).
Definition set_reg (st : reg_state) (r : REG) (v : Z) : reg_state
  := let '(idx, shift, bitcount) := index_and_shift_and_bitcount_of_reg r in
     Tuple.from_list_default 0%Z _ (ListUtil.update_nth
       idx
       (fun curv => Z.lor (Z.shiftl (Z.land v (Z.ones (Z.of_N bitcount))) (Z.of_N shift))
                          (Z.ldiff curv (Z.shiftl (Z.ones (Z.of_N bitcount)) (Z.of_N shift))))
       (Tuple.to_list _ st)).
Definition annotate_reg_state (st : reg_state) : list (REG * Z)
  := List.map (fun '(n, v) => (widest_register_of_index n, v)) (enumerate (Tuple.to_list _ st)).
Ltac print_reg_state st := let st' := (eval cbv in (annotate_reg_state st)) in idtac st'.

(* Kludge since [byte] isn't present in Coq 8.9 *)
Module Byte.
  Notation byte := Z (only parsing).
  Definition to_Z (x : byte) : Z := x.
  Definition of_Z (x : Z) : option byte
    := if (x <? 2^256)%Z then Some x else None.
  Notation x00 := 0%Z (only parsing).
End Byte.

Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface. (* coercions *)
Require Import coqutil.Word.LittleEndianList.
Require Import bedrock2.Memory. Import WithoutTuples.
Require coqutil.Word.Naive coqutil.Map.SortedListWord.
Definition mem_state := (SortedListWord.map (Naive.word 64) Byte.byte).

Definition get_mem (st : mem_state) (addr : Z) (nbytes : nat) : option Z
  := (bs <- load_bytes st (word.of_Z addr) nbytes; Some (LittleEndianList.le_combine bs))%option.
Definition set_mem (st : mem_state) (addr : Z) (nbytes : nat) (v : Z) : option mem_state
  := store_bytes st (word.of_Z addr) (LittleEndianList.le_split nbytes v).

Record machine_state := { machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.
Definition update_reg_with (st : machine_state) (f : reg_state -> reg_state) : machine_state
  := {| machine_reg_state := f st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_flag_with (st : machine_state) (f : flag_state -> flag_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := f st.(machine_flag_state) ; machine_mem_state := st.(machine_mem_state) |}.
Definition update_mem_with (st : machine_state) (f : mem_state -> mem_state) : machine_state
  := {| machine_reg_state := st.(machine_reg_state) ; machine_flag_state := st.(machine_flag_state) ; machine_mem_state := f st.(machine_mem_state) |}.

Definition DenoteConst (sz : N) (a : CONST) : Z :=
  Z.land a (Z.ones (Z.of_N sz)).

Definition DenoteAddress (sa : N) (st : machine_state) (a : MEM) : Z :=
  Z.land (
    match mem_base_reg  a with Some     r  => get_reg st r                    | _ => 0 end +
    match mem_scale_reg a with Some (z, r) => get_reg st r * DenoteConst sa z | _ => 0 end +
    match mem_offset    a with Some  z     =>                DenoteConst sa z | _ => 0 end
  ) (Z.ones (Z.of_N sa)).

Definition DenoteOperand (sa s : N) (st : machine_state) (a : ARG) : option Z :=
  match a with
  | reg a => Some (get_reg st a)
  | mem a => get_mem st (DenoteAddress sa st a) (N.to_nat (N.div (operand_size a s) 8))
  | const a => Some (DenoteConst (operand_size a s) a)
  | label _ => None
  end.

Definition SetMem (st : machine_state) (addr : Z) (nbytes : nat) (v : Z) : option machine_state :=
  ms <- set_mem st addr nbytes v;
  Some (update_mem_with st (fun _ => ms)).

Definition SetOperand (sa s : N) (st : machine_state) (a : ARG) (v : Z) : option machine_state :=
  match a with
  | reg a => Some (update_reg_with st (fun rs => set_reg rs a v))
  | mem a => SetMem st (DenoteAddress sa st a) (N.to_nat (N.div (operand_size a s) 8)) v
  | const a => None
  | label _ => None
  end.

Definition result_flags s v :=
  (* note: AF and PF remain undefined *)
  let fs := set_flag havoc_flags ZF (Z.eqb v 0) in
  let fs := set_flag fs SF (Z.testbit v (Z.of_N s-1)) in
  fs.

Definition SetFlag (st : machine_state) (f : FLAG) (b : bool) :=
  update_flag_with st (fun fs => set_flag fs f b).
Definition HavocFlag st f : machine_state :=
  update_flag_with st (fun fs => havoc_flag fs f).
Definition HavocFlags st : machine_state :=
  update_flag_with st (fun _ => havoc_flags).
Definition HavocFlagsFromResult s st v : machine_state :=
  update_flag_with st (fun _ => result_flags s v).
Definition PreserveFlag (st : machine_state) (f : FLAG) st' :=
  update_flag_with st (fun fs => set_flag_internal fs f (get_flag st' f)).

Definition signed (s : N) (z : Z) : Z :=
  Z.land (Z.shiftl 1 (Z.of_N s-1) + z) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1).

Definition rcrcnt s cnt : Z :=
  if N.eqb s 8 then Z.land cnt 0x1f mod 9 else
  if N.eqb s 16 then Z.land cnt 0x1f mod 17 else
  Z.land cnt (Z.of_N s-1).

(* NOTE: currently immediate operands are treated as if sign-extension has been
 * performed ahead of time. *)
Definition DenoteNormalInstruction (st : machine_state) (instr : NormalInstruction) : option machine_state :=
  let sa := 64%N in
  let stack_addr_size := 64%N in
  match operation_size instr with Some s =>
  let resize_reg r := reg_of_index_and_shift_and_bitcount_opt (reg_index r, 0%N (* offset *), s) in
  match instr.(prefix) with None =>
  match instr.(op), instr.(args) with
  | (mov | movzx), [dst; src] => (* Note: unbundle when switching from N to Z *)
    v <- DenoteOperand sa s st src;
    SetOperand sa s st dst v
  | xchg, [a; b] => (* Flags Affected: None *)
    va <- DenoteOperand sa s st a;
    vb <- DenoteOperand sa s st b;
    st <- SetOperand sa s st b va;
    SetOperand sa s st a vb
  | (setc | seto) as opc, [dst] => (* Flags Affected: None *)
    let flag := match opc with setc => CF | _ => OF end in
    b <- get_flag st flag;
    SetOperand sa s st dst (Z.b2z b)
  | clc, [] => Some (update_flag_with st (fun fs =>
    set_flag fs CF false))
  | cmovc, [dst; src] (* Flags Affected: None *)
  | cmovb, [dst; src] (* Flags Affected: None *)
    =>
    v <- DenoteOperand sa s st src;
    cf <- get_flag st CF;
    if cf
    then SetOperand sa s st dst v
    else Some st
  | cmovnz, [dst; src] => (* Flags Affected: None *)
    v <- DenoteOperand sa s st src;
    zf <- get_flag st ZF;
    if negb zf
    then SetOperand sa s st dst v
    else Some st

  | lea, [reg dst; mem src] => (* Flags Affected: None *)
    Some (update_reg_with st (fun rs => set_reg rs dst (DenoteAddress sa st src)))
  | (add | adc) as opc, [dst; src] =>
    c <- (match opc with adc => get_flag st CF | _ => Some false end);
    let c := Z.b2z c in
    v1 <- DenoteOperand sa s st dst;
    v2 <- DenoteOperand sa s st src;
    let v := v1 + v2 + c in
    let v := Z.land v (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    let st := HavocFlagsFromResult s st v in
    let st := SetFlag st CF (Z.odd (Z.shiftr (v1 + v2 + c) (Z.of_N s))) in
    Some (SetFlag st OF (negb (signed s v =? signed s v1 + signed s v2 + signed s c)%Z))
  | (adcx | adox) as opc, [dst; src] =>
    let flag := match opc with adcx => CF | _ => OF end in
    v1 <- DenoteOperand sa s st dst;
    v2 <- DenoteOperand sa s st src;
    c <- get_flag st flag; let c := Z.b2z c in
    let v := v1 + v2 + c in
    let v := Z.land v (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    Some (SetFlag st flag (Z.odd (Z.shiftr (v1 + v2 + c) (Z.of_N s))))
  | (sbb | sub) as opc, [dst; src] =>
    c <- (match opc with sbb => get_flag st CF | _ => Some false end);
    let c := Z.b2z c in
    v1 <- DenoteOperand sa s st dst;
    v2 <- DenoteOperand sa s st src;
    let v := Z.land (v1 - (v2 + c)) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    let st := HavocFlagsFromResult s st v in
    let st := SetFlag st CF (Z.odd (Z.shiftr (v1 - (v2 + c)) (Z.of_N s))) in
    Some (SetFlag st OF (negb (signed s v =? signed s v1 - (signed s v2 + c))%Z))
  | dec, [dst] =>
    v1 <- DenoteOperand sa s st dst;
    let v := Z.land (v1 - 1) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    let st := PreserveFlag (HavocFlagsFromResult s st v) CF st in
    Some (SetFlag st OF (negb (signed s v =? signed s v1 - 1)%Z))
  | inc, [dst] =>
    v1 <- DenoteOperand sa s st dst;
    let v := Z.land (v1 + 1) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    let st := PreserveFlag (HavocFlagsFromResult s st v) CF st in
    Some (SetFlag st OF (negb (signed s v =? signed s v1 + 1)%Z))
  | mulx, [hi; lo; src2] => (* Flags Affected: None *)
    let src1 : ARG := rdx in (* Note: assumes s=64 *)
    v1 <- DenoteOperand sa s st src1;
    v2 <- DenoteOperand sa s st src2;
    let v := v1 * v2 in
    st <- SetOperand sa s st lo v;
    SetOperand sa s st hi (Z.shiftr v (Z.of_N s))
  | (Syntax.mul | imul), [src2] =>
    let src1 : ARG := rax in
    v1 <- DenoteOperand sa s st src1;
    v2 <- DenoteOperand sa s st src2;
    let v := v1 * v2 in
    lo <- resize_reg rax;
    hi <- (if (s =? 8)%N
           then Some ah
           else resize_reg rdx);
    st <- SetOperand sa s st lo v;
    st <- SetOperand sa s st hi (Z.shiftr v (Z.of_N s));
    Some (HavocFlags st) (* conservative *)
  | imul, ([src1 as dst; src2] | [dst; src1; src2]) =>
    v1 <- DenoteOperand sa s st src1;
    v2 <- DenoteOperand sa s st src2;
    let v := v1 * v2 in
    st <- SetOperand sa s st dst v;
    let c := negb (v =? Z.land v (Z.ones (Z.of_N s)))%Z in
    Some (SetFlag (SetFlag (HavocFlags st) CF c) OF c)
  | sar, [dst; cnt] =>
    v1 <- DenoteOperand sa s st dst;
    cnt' <- DenoteOperand sa s st cnt;
    let cnt := Z.land cnt' (Z.of_N s-1) in
    let v := Z.land (Z.shiftr (signed s v1) cnt) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    Some (if cnt =? 0 then st else
      let st := HavocFlagsFromResult s st v in
      let st := if cnt =? 1 then SetFlag st OF false else st in
      let st := if cnt <? Z.of_N s then SetFlag st CF (Z.testbit v1 (cnt-1)) else st in
      HavocFlag st AF)
  | shl, [dst; cnt] =>
    v1 <- DenoteOperand sa s st dst;
    cnt <- DenoteOperand sa s st cnt;
    let v := Z.land (Z.shiftl v1 (Z.land cnt (Z.of_N s-1))) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    Some (if cnt =? 0 then st else
      let st := HavocFlagsFromResult s st v in
      let st := if cnt =? 1 then SetFlag st OF (xorb (Z.testbit v1 (Z.of_N s-2)) (Z.testbit v1 (Z.of_N s-1))) else st in
      let st := if cnt <? Z.of_N s then SetFlag st CF (Z.testbit v1 (65-cnt)) else st in
      HavocFlag st AF)
  | shlx, [dst; src; cnt] =>
    v1 <- DenoteOperand sa s st src;
    cnt <- DenoteOperand sa s st cnt;
    let v := Z.land (Z.shiftl v1 (Z.land cnt (Z.of_N s-1))) (Z.ones (Z.of_N s)) in
    SetOperand sa s st dst v
  | shr, [dst; cnt] =>
    v1 <- DenoteOperand sa s st dst;
    cnt <- DenoteOperand sa s st cnt;
    let v := Z.land (Z.shiftr v1 (Z.land cnt (Z.of_N s-1))) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    Some (if cnt =? 0 then st else
      let st := HavocFlagsFromResult s st v in
      let st := if cnt =? 1 then SetFlag st OF (Z.testbit v1 (Z.of_N s-1)) else st in
      let st := if cnt <? Z.of_N s then SetFlag st CF (Z.testbit v1 (cnt-1)) else st in
      HavocFlag st AF)
  | rcr, [dst; cnt] =>
    v1 <- DenoteOperand sa s st dst;
    cnt <- DenoteOperand sa s st cnt;
    let cnt := rcrcnt s cnt in
    c <- get_flag st CF;
    let v1c := Z.lor v1 (Z.shiftl (Z.b2z c) (Z.of_N s)) in
    let l := Z.lor v1c (Z.shiftl v1 (1+Z.of_N s)) in
    let v := Z.land (Z.shiftr l cnt) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    Some (
      if cnt =? 0 then st else
      let st := SetFlag st CF (Z.testbit v1c (cnt-1)) in
      if cnt =? 1 then SetFlag st OF (xorb (Z.testbit v (Z.of_N s-1)) (Z.testbit v (Z.of_N s-2))) else st)
  | shrd, [dst as lo; hi; cnt] =>
    lv <- DenoteOperand sa s st lo;
    hv <- DenoteOperand sa s st hi;
    cnt <- DenoteOperand sa s st cnt;
    let l := Z.lor lv (Z.shiftl hv (Z.of_N s)) in
    let v := Z.land (Z.shiftr l (Z.land cnt (Z.of_N s-1))) (Z.ones (Z.of_N s)) in
    st <- SetOperand sa s st dst v;
    if cnt =? 0 then Some st else
    if Z.of_N s <? cnt then Some (HavocFlags st) else
      let st := HavocFlagsFromResult s st l in
      let signchange := xorb (signed s lv <? 0)%Z (signed s v <? 0)%Z in
      (* Note: IA-32 SDM does not make it clear what sign change is in question *)
      let st := if cnt =? 1 then SetFlag st OF signchange else st in
      let st := SetFlag st CF (Z.testbit l (cnt-1)) in
      Some (HavocFlag st AF)
  | (and | xor) as opc, [dst; src] =>
    let f := match opc with and => Z.land | _ => Z.lxor end in
    v1 <- DenoteOperand sa s st dst;
    v2 <- DenoteOperand sa s st src;
    let v := f v1 v2 in
    st <- SetOperand sa s st dst v;
    let st := HavocFlagsFromResult s st v in
    let st := SetFlag st CF false in
    let st := SetFlag st OF false in
    Some (HavocFlag st AF)
  | bzhi, [dst; src1; src2] =>
    v1 <- DenoteOperand sa s st src1;
    v2 <- DenoteOperand sa s st src2;
    let n := Z.land v2 (Z.ones 8) in
    let v := Z.land v1 (Z.ones n) in
    st <- SetOperand sa s st dst v;
    let st := HavocFlagsFromResult s st v in
    let st := SetFlag st CF (((Z.of_N (operand_size src1 s)) - 1) <? v) in
    Some (SetFlag st OF false)
  | test, [src1; src2] =>
    v1 <- DenoteOperand sa s st src1;
    v2 <- DenoteOperand sa s st src2;
    let v := Z.land v1 v2 in
    let st := HavocFlagsFromResult s st v in
    let st := SetFlag st CF false in
    let st := SetFlag st OF false in
    Some (HavocFlag st AF)
  | push, [src]
    => v    <- DenoteOperand sa s st src;
       rsp' <- DenoteOperand sa stack_addr_size st rsp;
       let rsp' := Z.land (rsp' - (Z.of_N s / 8)) (Z.ones (Z.of_N stack_addr_size)) in (* we don't actually need to truncate here, but it makes proofs a bit easier *)
       st   <- SetOperand stack_addr_size s st rsp rsp';
               SetOperand sa s st (mem_of_reg rsp) v
  | pop, [dst]
    => v    <- DenoteOperand sa s st (mem_of_reg rsp);
       rsp' <- DenoteOperand sa stack_addr_size st rsp;
       let rsp' := Z.land (rsp' + (Z.of_N s / 8)) (Z.ones (Z.of_N stack_addr_size)) in (* we don't actually need to truncate here, but it makes proofs a bit easier *)
       st   <- SetOperand stack_addr_size s st rsp rsp';
               SetOperand sa s st dst v

  | ret, _ => None (* not sure what to do with this ret, maybe exlude it? *)

  | adc, _
  | adcx, _
  | add, _
  | adox, _
  | and, _
  | bzhi, _
  | db, _
  | dw, _
  | dd, _
  | dq, _
  | mulx, _
  | mul, _
  | call, _
  | cmp, _
  | je, _
  | jmp, _
  | cmovc, _
  | cmovb, _
  | cmovnz, _
  | setc, _
  | seto, _
  | clc, _
  | dec, _
  | lea, _
  | mov, _
  | movzx, _
  | imul, _
  | inc, _
  | push, _
  | pop, _
  | sar, _
  | rcr, _
  | sbb, _
  | shl, _
  | shlx, _
  | shr, _
  | shrx, _
  | shrd, _
  | sub, _
  | test, _
  | xor, _
  | xchg, _ => None
 end | _ => None end | _ => None end%Z%option.


Definition DenoteRawLine (st : machine_state) (rawline : RawLine) : option machine_state :=
  match rawline with
  | EMPTY
  | LABEL _
    => Some st
  | INSTR instr
    => DenoteNormalInstruction st instr
  | SECTION _
  | GLOBAL _
  | ALIGN _
  | DEFAULT_REL
    => None
  end.

Definition DenoteLine (st : machine_state) (line : Line) : option machine_state
  := DenoteRawLine st line.(rawline).

Fixpoint DenoteLines (st : machine_state) (lines : Lines) : option machine_state
  := match lines with
     | [] => Some st
     | line :: lines
       => (st <- DenoteLine st line;
          DenoteLines st lines)
     end%option.
