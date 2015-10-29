
Require Import EqNat Peano_dec.
Require Import Bedrock.Word.

(* Very basic definitions *)

Definition wordSize := 32.

Definition Name := nat.

Definition WordCount := nat.

Definition WordList (words: WordCount) :=
  {x: list (word wordSize) | length x = words}.

Inductive Pointer :=
  | ListPtr: forall n, WordList n -> Pointer.

Definition TypeBindings := Name -> option WordCount.

Definition Bindings := Name -> option Pointer.

(* Primary inductive language definitions *)

Inductive CTerm (words: WordCount) :=
  | CConst : WordList words -> CTerm words
  | CVar : Name -> CTerm words
  | CConcat: forall t1 t2, t1 + t2 = words -> CTerm t1 -> CTerm t2 -> CTerm words
  | CHead: forall n: nat, gt n words -> CTerm n -> CTerm words
  | CTail: forall n: nat, gt n words -> CTerm n -> CTerm words.

Inductive CExpr (words: WordCount) :=
  | CLift : (CTerm words) -> (CExpr words)
  | CNot : (CExpr words) -> (CExpr words)
  | COpp : (CExpr words) -> (CExpr words)
  | COr : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CAnd : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CXor : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CRShift : forall n: nat, (CExpr words) -> (CExpr words)
  | CLShift : forall n: nat, (CExpr words) -> (CExpr words)
  | CPlus : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CMinus : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CMult : forall n: nat,  n*2 = words ->
      (CExpr n) -> (CExpr n) -> (CExpr words)
  | CDiv : (CExpr words) -> (CExpr words) -> (CExpr words)
  | CMod : (CExpr words) -> (CExpr words) -> (CExpr words).

Definition bindType (name: Name) (type: WordCount) (bindings: TypeBindings)
    : Name -> option WordCount :=
  fun x => if (beq_nat x name) then Some type else bindings x.

Inductive Sub (inputs: TypeBindings) (output: WordCount) :=
  | CRet : CExpr output -> Sub inputs output 
  | CCompose : forall resultName resultSize,
           inputs resultName = None
        -> (Sub inputs resultSize)
        -> (Sub (bindType resultName resultSize inputs) output)
        -> (Sub inputs output)
  | CIte : (Sub inputs 1)    (* condition *)
        -> (Sub inputs output)  (* then *)
        -> (Sub inputs output)  (* else *)
        -> (Sub inputs output)
  | CLet : forall (name: Name) (n: WordCount),
            CExpr n
        -> (Sub (bindType name n inputs) output)
        -> (Sub inputs output)
  | CRepeat : forall (bindOutputTo: Name) (n: nat),
           inputs bindOutputTo <> None
        -> (Sub (bindType bindOutputTo output inputs) output)
        -> (Sub inputs output).

(* Some simple option-monad sugar *)

Definition optionReturn {A} (x : A) := Some x.
 
Definition optionBind {A B} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some x => f x
  | None => None
  end.

Notation "'do' A <- B ; C" := (optionBind B (fun A => C))
    (at level 200, X ident, A at level 100, B at level 200).

Definition optionType {n m} (w: WordList n): option (WordList m).
  destruct (eq_nat_dec n m);
  abstract (try rewrite e in *; first [exact (Some w) | exact None]).
Defined.

Definition wordListConcat {t1 t2 words}:
    t1 + t2 = words -> WordList t1 -> WordList t2 -> WordList words.
  intros; exists ((proj1_sig H0) ++ (proj1_sig H1))%list.
  abstract (destruct H0, H1; simpl;
    rewrite List.app_length; intuition).
Defined.

Definition wordListHead {n words}:
    gt n words -> WordList n -> WordList words.
  intros; exists (List.firstn words (proj1_sig H0)).
  abstract (destruct H0; simpl;
    rewrite List.firstn_length; intuition).
Defined.

Lemma skipnLength: forall A m (x: list A),
  ge (length x) m ->
  length (List.skipn m x) = length x - m.
Proof.
  intros; assert (length x = length (List.firstn m x ++ List.skipn m x)%list).
  - rewrite List.firstn_skipn; trivial.
  - rewrite H0; rewrite List.app_length; rewrite List.firstn_length.
    replace (min m (length x)) with m; try rewrite min_l; intuition.
Qed.

Definition wordListTail {n words}:
    gt n words -> WordList n -> WordList words.
  intros; exists (List.skipn (n - words) (proj1_sig H0)).
  abstract (destruct H0; simpl;
    rewrite skipnLength; rewrite e; intuition).
Defined.

(* Now some basic evaluation routines *)

Fixpoint evalTerm {n} (bindings: Bindings) (term: CTerm n):
    option (WordList n) :=
  match term with
  | CConst lst => Some lst
  | CVar name =>
      do p <- bindings name ;
      match p with
      | ListPtr m lst => optionType lst
      end
  | CConcat t1 t2 pf term1 term2 =>
      do a <- evalTerm bindings term1;
      do b <- evalTerm bindings term2;
      Some (wordListConcat pf a b)%list
  | CHead n pf t =>
      do x <- evalTerm bindings t;
      Some (wordListHead pf x)
  | CTail n pf t =>
      do x <- evalTerm bindings t;
      Some (wordListTail pf x)
  end.

Fixpoint evalExpr {n} (expr: CExpr n): option (word n) :=
  match expr with
  | CLift term => None
  | CNot a => None
  | COpp a => None
  | COr a b =>
      do x <- evalExpr a;
      do y <- evalExpr b;
      Some (x |^ y)%word
  | CAnd a b => None
  | CXor a b => None
  | CRShift shift a => None
  | CLShift shift a => None
  | CPlus a b => None
  | CMinus a b => None
  | CMult _ _ a b => None
  | CDiv a b => None
  | CMod a b => None
  end.

Fixpoint evalSub (inputs: Name -> option WordCount) (output: WordCount) (sub: Sub inputs output)
    : word output :=
  match sub with
  | CRet e => natToWord output 0
  | CCompose resName resSize _ a b => natToWord output 0
  | CIte cond thenSub elseSub => natToWord output 0
  | CLet name wordCount expr inside => natToWord output 0
  | CRepeat inName times _ inside => natToWord output 0
  end.

(* Equivalence Lemmas *)

