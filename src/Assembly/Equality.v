Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Prod.
Require Import Crypto.Assembly.Syntax.

Local Ltac t_dec :=
  lazymatch goal with
  | [ |- ?beq ?x ?y = true -> ?x = ?y ]
    => is_var x; is_var y; destruct x, y; cbv [beq]
  | [ |- ?x = ?y -> ?beq ?x ?y = true ]
    => is_var x; is_var y; destruct x; cbv [beq]; intros; subst
  end;
  simpl;
  rewrite ?Bool.andb_true_iff; intros; destruct_head'_and;
  repeat apply conj; try reflexivity;
  reflect_hyps; subst;
  try solve [ reflexivity
            | exfalso; assumption
            | apply unreflect_bool; reflexivity ].

Declare Scope REG_scope.
Delimit Scope REG_scope with REG.
Bind Scope REG_scope with REG.

Infix "=?" := REG_beq : REG_scope.

Global Instance REG_beq_spec : reflect_rel (@eq REG) REG_beq | 10
  := reflect_of_beq internal_REG_dec_bl internal_REG_dec_lb.
Definition REG_beq_eq x y : (x =? y)%REG = true <-> x = y := conj (@internal_REG_dec_bl _ _) (@internal_REG_dec_lb _ _).
Lemma REG_beq_neq x y : (x =? y)%REG = false <-> x <> y.
Proof. rewrite <- REG_beq_eq; destruct (x =? y)%REG; intuition congruence. Qed.
Global Instance REG_beq_compat : Proper (eq ==> eq ==> eq) REG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Definition CONST_beq : CONST -> CONST -> bool := Z.eqb.
Definition CONST_dec_bl (x y : CONST) : CONST_beq x y = true -> x = y := proj1 (Z.eqb_eq x y).
Definition CONST_dec_lb (x y : CONST) : x = y -> CONST_beq x y = true := proj2 (Z.eqb_eq x y).
Definition CONST_eq_dec (x y : CONST) : {x = y} + {x <> y} := Z.eq_dec x y.

Declare Scope CONST_scope.
Delimit Scope CONST_scope with CONST.
Bind Scope CONST_scope with CONST.

Infix "=?" := CONST_beq : CONST_scope.

Global Instance CONST_beq_spec : reflect_rel (@eq CONST) CONST_beq | 10
  := reflect_of_beq CONST_dec_bl CONST_dec_lb.
Definition CONST_beq_eq x y : (x =? y)%CONST = true <-> x = y := conj (@CONST_dec_bl _ _) (@CONST_dec_lb _ _).
Lemma CONST_beq_neq x y : (x =? y)%CONST = false <-> x <> y.
Proof. rewrite <- CONST_beq_eq; destruct (x =? y)%CONST; intuition congruence. Qed.
Global Instance CONST_beq_compat : Proper (eq ==> eq ==> eq) CONST_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope JUMP_LABEL_scope.
Delimit Scope JUMP_LABEL_scope with JUMP_LABEL.
Bind Scope JUMP_LABEL_scope with JUMP_LABEL.

Definition JUMP_LABEL_beq (x y : JUMP_LABEL) : bool
  := ((Bool.eqb x.(jump_near) y.(jump_near))
      && (x.(label_name) =? y.(label_name))%string).
Global Arguments JUMP_LABEL_beq !_ !_ / .

Infix "=?" := JUMP_LABEL_beq : JUMP_LABEL_scope.
Lemma JUMP_LABEL_dec_bl (x y : JUMP_LABEL) : JUMP_LABEL_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma JUMP_LABEL_dec_lb (x y : JUMP_LABEL) : x = y -> JUMP_LABEL_beq x y = true.
Proof. t_dec. Qed.
Definition JUMP_LABEL_eq_dec (x y : JUMP_LABEL) : {x = y} + {x <> y}
  := (if (x =? y)%JUMP_LABEL as b return (x =? y)%JUMP_LABEL = b -> _
      then fun pf => left (@JUMP_LABEL_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@JUMP_LABEL_dec_lb _ _ pf'))))
       eq_refl.

Global Instance JUMP_LABEL_beq_spec : reflect_rel (@eq JUMP_LABEL) JUMP_LABEL_beq | 10
  := reflect_of_beq JUMP_LABEL_dec_bl JUMP_LABEL_dec_lb.
Definition JUMP_LABEL_beq_eq x y : (x =? y)%JUMP_LABEL = true <-> x = y := conj (@JUMP_LABEL_dec_bl _ _) (@JUMP_LABEL_dec_lb _ _).
Lemma JUMP_LABEL_beq_neq x y : (x =? y)%JUMP_LABEL = false <-> x <> y.
Proof. rewrite <- JUMP_LABEL_beq_eq; destruct (x =? y)%JUMP_LABEL; intuition congruence. Qed.
Global Instance JUMP_LABEL_beq_compat : Proper (eq ==> eq ==> eq) JUMP_LABEL_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.
Declare Scope AccessSize_scope.
Delimit Scope AccessSize_scope with AccessSize.
Bind Scope AccessSize_scope with AccessSize.

Infix "=?" := AccessSize_beq : AccessSize_scope.

Global Instance AccessSize_beq_spec : reflect_rel (@eq AccessSize) AccessSize_beq | 10
  := reflect_of_beq internal_AccessSize_dec_bl internal_AccessSize_dec_lb.
Definition AccessSize_beq_eq x y : (x =? y)%AccessSize = true <-> x = y := conj (@internal_AccessSize_dec_bl _ _) (@internal_AccessSize_dec_lb _ _).
Lemma AccessSize_beq_neq x y : (x =? y)%AccessSize = false <-> x <> y.
Proof. rewrite <- AccessSize_beq_eq; destruct (x =? y)%AccessSize; intuition congruence. Qed.
Global Instance AccessSize_beq_compat : Proper (eq ==> eq ==> eq) AccessSize_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope MEM_scope.
Delimit Scope MEM_scope with MEM.
Bind Scope MEM_scope with MEM.

Definition MEM_beq (x y : MEM) : bool
  := ((option_beq AccessSize_beq x.(mem_bits_access_size) y.(mem_bits_access_size))
      && option_beq String.eqb x.(mem_base_label) y.(mem_base_label)
      && (option_beq REG_beq x.(mem_base_reg) y.(mem_base_reg))
      && (option_beq (prod_beq _ _ Z.eqb REG_beq) x.(mem_scale_reg) y.(mem_scale_reg))
      && (option_beq Z.eqb x.(mem_offset) y.(mem_offset)))%bool.
Global Arguments MEM_beq !_ !_ / .

Infix "=?" := MEM_beq : MEM_scope.

Lemma MEM_dec_bl (x y : MEM) : MEM_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma MEM_dec_lb (x y : MEM) : x = y -> MEM_beq x y = true.
Proof. t_dec. Qed.
Definition MEM_eq_dec (x y : MEM) : {x = y} + {x <> y}
  := (if (x =? y)%MEM as b return (x =? y)%MEM = b -> _
      then fun pf => left (@MEM_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@MEM_dec_lb _ _ pf'))))
       eq_refl.

Global Instance MEM_beq_spec : reflect_rel (@eq MEM) MEM_beq | 10
  := reflect_of_beq MEM_dec_bl MEM_dec_lb.
Definition MEM_beq_eq x y : (x =? y)%MEM = true <-> x = y := conj (@MEM_dec_bl _ _) (@MEM_dec_lb _ _).
Lemma MEM_beq_neq x y : (x =? y)%MEM = false <-> x <> y.
Proof. rewrite <- MEM_beq_eq; destruct (x =? y)%MEM; intuition congruence. Qed.
Global Instance MEM_beq_compat : Proper (eq ==> eq ==> eq) MEM_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope FLAG_scope.
Delimit Scope FLAG_scope with FLAG.
Bind Scope FLAG_scope with FLAG.

Infix "=?" := FLAG_beq : FLAG_scope.

Global Instance FLAG_beq_spec : reflect_rel (@eq FLAG) FLAG_beq | 10
  := reflect_of_beq internal_FLAG_dec_bl internal_FLAG_dec_lb.
Definition FLAG_beq_eq x y : (x =? y)%FLAG = true <-> x = y := conj (@internal_FLAG_dec_bl _ _) (@internal_FLAG_dec_lb _ _).
Lemma FLAG_beq_neq x y : (x =? y)%FLAG = false <-> x <> y.
Proof. rewrite <- FLAG_beq_eq; destruct (x =? y)%FLAG; intuition congruence. Qed.
Global Instance FLAG_beq_compat : Proper (eq ==> eq ==> eq) FLAG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope OpCode_scope.
Delimit Scope OpCode_scope with OpCode.
Bind Scope OpCode_scope with OpCode.

Infix "=?" := OpCode_beq : OpCode_scope.

Global Instance OpCode_beq_spec : reflect_rel (@eq OpCode) OpCode_beq | 10
  := reflect_of_beq internal_OpCode_dec_bl internal_OpCode_dec_lb.
Definition OpCode_beq_eq x y : (x =? y)%OpCode = true <-> x = y := conj (@internal_OpCode_dec_bl _ _) (@internal_OpCode_dec_lb _ _).
Lemma OpCode_beq_neq x y : (x =? y)%OpCode = false <-> x <> y.
Proof. rewrite <- OpCode_beq_eq; destruct (x =? y)%OpCode; intuition congruence. Qed.
Global Instance OpCode_beq_compat : Proper (eq ==> eq ==> eq) OpCode_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope OpPrefix_scope.
Delimit Scope OpPrefix_scope with OpPrefix.
Bind Scope OpPrefix_scope with OpPrefix.

Infix "=?" := OpPrefix_beq : OpPrefix_scope.

Global Instance OpPrefix_beq_spec : reflect_rel (@eq OpPrefix) OpPrefix_beq | 10
  := reflect_of_beq internal_OpPrefix_dec_bl internal_OpPrefix_dec_lb.
Definition OpPrefix_beq_eq x y : (x =? y)%OpPrefix = true <-> x = y := conj (@internal_OpPrefix_dec_bl _ _) (@internal_OpPrefix_dec_lb _ _).
Lemma OpPrefix_beq_neq x y : (x =? y)%OpPrefix = false <-> x <> y.
Proof. rewrite <- OpPrefix_beq_eq; destruct (x =? y)%OpPrefix; intuition congruence. Qed.
Global Instance OpPrefix_beq_compat : Proper (eq ==> eq ==> eq) OpPrefix_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope ARG_scope.
Delimit Scope ARG_scope with ARG.
Bind Scope ARG_scope with ARG.

Definition ARG_beq (x y : ARG) : bool
  := match x, y with
     | reg x, reg y => REG_beq x y
     | mem x, mem y => MEM_beq x y
     | const x, const y => CONST_beq x y
     | label x, label y => JUMP_LABEL_beq x y
     | reg _, _
     | mem _, _
     | const _, _
     | label _, _
       => false
     end.
Global Arguments ARG_beq !_ !_ / .

Infix "=?" := ARG_beq : ARG_scope.

Lemma ARG_dec_bl (x y : ARG) : ARG_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma ARG_dec_lb (x y : ARG) : x = y -> ARG_beq x y = true.
Proof. t_dec. Qed.
Definition ARG_eq_dec (x y : ARG) : {x = y} + {x <> y}
  := (if (x =? y)%ARG as b return (x =? y)%ARG = b -> _
      then fun pf => left (@ARG_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@ARG_dec_lb _ _ pf'))))
       eq_refl.

Global Instance ARG_beq_spec : reflect_rel (@eq ARG) ARG_beq | 10
  := reflect_of_beq ARG_dec_bl ARG_dec_lb.
Definition ARG_beq_eq x y : (x =? y)%ARG = true <-> x = y := conj (@ARG_dec_bl _ _) (@ARG_dec_lb _ _).
Lemma ARG_beq_neq x y : (x =? y)%ARG = false <-> x <> y.
Proof. rewrite <- ARG_beq_eq; destruct (x =? y)%ARG; intuition congruence. Qed.
Global Instance ARG_beq_compat : Proper (eq ==> eq ==> eq) ARG_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope NormalInstruction_scope.
Delimit Scope NormalInstruction_scope with NormalInstruction.
Bind Scope NormalInstruction_scope with NormalInstruction.

Definition NormalInstruction_beq (x y : NormalInstruction) : bool
  := (option_beq OpPrefix_beq x.(prefix) y.(prefix)
      && (x.(op) =? y.(op))%OpCode
      && list_beq _ ARG_beq x.(args) y.(args))%bool.
Global Arguments NormalInstruction_beq !_ !_ / .

Infix "=?" := NormalInstruction_beq : NormalInstruction_scope.

Lemma NormalInstruction_dec_bl (x y : NormalInstruction) : NormalInstruction_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma NormalInstruction_dec_lb (x y : NormalInstruction) : x = y -> NormalInstruction_beq x y = true.
Proof. t_dec. Qed.
Definition NormalInstruction_eq_dec (x y : NormalInstruction) : {x = y} + {x <> y}
  := (if (x =? y)%NormalInstruction as b return (x =? y)%NormalInstruction = b -> _
      then fun pf => left (@NormalInstruction_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@NormalInstruction_dec_lb _ _ pf'))))
       eq_refl.

Global Instance NormalInstruction_beq_spec : reflect_rel (@eq NormalInstruction) NormalInstruction_beq | 10
  := reflect_of_beq NormalInstruction_dec_bl NormalInstruction_dec_lb.
Definition NormalInstruction_beq_eq x y : (x =? y)%NormalInstruction = true <-> x = y := conj (@NormalInstruction_dec_bl _ _) (@NormalInstruction_dec_lb _ _).
Lemma NormalInstruction_beq_neq x y : (x =? y)%NormalInstruction = false <-> x <> y.
Proof. rewrite <- NormalInstruction_beq_eq; destruct (x =? y)%NormalInstruction; intuition congruence. Qed.
Global Instance NormalInstruction_beq_compat : Proper (eq ==> eq ==> eq) NormalInstruction_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope RawLine_scope.
Delimit Scope RawLine_scope with RawLine.
Bind Scope RawLine_scope with RawLine.

Definition RawLine_beq (x y : RawLine) : bool
  := match x, y with
     | SECTION x, SECTION y => String.eqb x y
     | GLOBAL x, GLOBAL y => String.eqb x y
     | LABEL x, LABEL y => String.eqb x y
     | EMPTY, EMPTY => true
     | DEFAULT_REL, DEFAULT_REL => true
     | INSTR x, INSTR y => NormalInstruction_beq x y
     | ALIGN x, ALIGN y => String.eqb x y
     | SECTION _, _
     | GLOBAL _, _
     | LABEL _, _
     | EMPTY, _
     | INSTR _, _
     | ALIGN _, _
     | DEFAULT_REL, _
       => false
     end.
Global Arguments RawLine_beq !_ !_ / .

Infix "=?" := RawLine_beq : RawLine_scope.

Lemma RawLine_dec_bl (x y : RawLine) : RawLine_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma RawLine_dec_lb (x y : RawLine) : x = y -> RawLine_beq x y = true.
Proof. t_dec. Qed.
Definition RawLine_eq_dec (x y : RawLine) : {x = y} + {x <> y}
  := (if (x =? y)%RawLine as b return (x =? y)%RawLine = b -> _
      then fun pf => left (@RawLine_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@RawLine_dec_lb _ _ pf'))))
       eq_refl.

Global Instance RawLine_beq_spec : reflect_rel (@eq RawLine) RawLine_beq | 10
  := reflect_of_beq RawLine_dec_bl RawLine_dec_lb.
Definition RawLine_beq_eq x y : (x =? y)%RawLine = true <-> x = y := conj (@RawLine_dec_bl _ _) (@RawLine_dec_lb _ _).
Lemma RawLine_beq_neq x y : (x =? y)%RawLine = false <-> x <> y.
Proof. rewrite <- RawLine_beq_eq; destruct (x =? y)%RawLine; intuition congruence. Qed.
Global Instance RawLine_beq_compat : Proper (eq ==> eq ==> eq) RawLine_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope Line_scope.
Delimit Scope Line_scope with Line.
Bind Scope Line_scope with Line.

Definition Line_beq (x y : Line) : bool
  := ((x.(indent) =? y.(indent))%string
      && (x.(rawline) =? y.(rawline))%RawLine
      && (x.(pre_comment_whitespace) =? y.(pre_comment_whitespace))%string
      && option_beq String.eqb x.(comment) y.(comment))%bool.
Global Arguments Line_beq !_ !_ / .

Infix "=?" := Line_beq : Line_scope.

Lemma Line_dec_bl (x y : Line) : Line_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma Line_dec_lb (x y : Line) : x = y -> Line_beq x y = true.
Proof. t_dec. Qed.
Definition Line_eq_dec (x y : Line) : {x = y} + {x <> y}
  := (if (x =? y)%Line as b return (x =? y)%Line = b -> _
      then fun pf => left (@Line_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@Line_dec_lb _ _ pf'))))
       eq_refl.

Global Instance Line_beq_spec : reflect_rel (@eq Line) Line_beq | 10
  := reflect_of_beq Line_dec_bl Line_dec_lb.
Definition Line_beq_eq x y : (x =? y)%Line = true <-> x = y := conj (@Line_dec_bl _ _) (@Line_dec_lb _ _).
Lemma Line_beq_neq x y : (x =? y)%Line = false <-> x <> y.
Proof. rewrite <- Line_beq_eq; destruct (x =? y)%Line; intuition congruence. Qed.
Global Instance Line_beq_compat : Proper (eq ==> eq ==> eq) Line_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.

Declare Scope Lines_scope.
Delimit Scope Lines_scope with Lines.
Bind Scope Lines_scope with Lines.

Definition Lines_beq (x y : Lines) : bool
  := list_beq _ Line_beq x y.
Global Arguments Lines_beq !_ !_ / .

Infix "=?" := Lines_beq : Lines_scope.

Lemma Lines_dec_bl (x y : Lines) : Lines_beq x y = true -> x = y.
Proof. t_dec. Qed.
Lemma Lines_dec_lb (x y : Lines) : x = y -> Lines_beq x y = true.
Proof. t_dec. Qed.
Definition Lines_eq_dec (x y : Lines) : {x = y} + {x <> y}
  := (if (x =? y)%Lines as b return (x =? y)%Lines = b -> _
      then fun pf => left (@Lines_dec_bl _ _ pf)
      else fun pf => right (fun pf' => diff_false_true (eq_trans (eq_sym pf) (@Lines_dec_lb _ _ pf'))))
       eq_refl.

Global Instance Lines_beq_spec : reflect_rel (@eq Lines) Lines_beq | 10
  := reflect_of_beq Lines_dec_bl Lines_dec_lb.
Definition Lines_beq_eq x y : (x =? y)%Lines = true <-> x = y := conj (@Lines_dec_bl _ _) (@Lines_dec_lb _ _).
Lemma Lines_beq_neq x y : (x =? y)%Lines = false <-> x <> y.
Proof. rewrite <- Lines_beq_eq; destruct (x =? y)%Lines; intuition congruence. Qed.
Global Instance Lines_beq_compat : Proper (eq ==> eq ==> eq) Lines_beq | 10.
Proof. repeat intro; subst; reflexivity. Qed.
