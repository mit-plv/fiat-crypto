Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.CPSNotations.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive type := Base | Arrow (s : type) (d : type).
Bind Scope ctype_scope with type.
Delimit Scope ctype_scope with ctype.
Notation "'??'" := Base : ctype_scope.
Infix "->" := Arrow : ctype_scope.

Section ident.
  Local Notation Unit := Base.
  Local Notation Nat := Base.
  Local Notation "A * B" := Base (only parsing) : ctype_scope.
  Local Notation List A := Base (only parsing).
  Local Notation Bool := Base.
  Local Notation A := Base.
  Local Notation B := Base.
  Local Notation P := Base.

  Inductive ident : type -> Type :=
  | O : ident Nat
  | S : ident (Nat -> Nat)
  | NatRect (*{P : base_type}*) : ident ((Unit -> P) -> (Nat -> P -> P) -> Nat -> P)
  | NatEqb : ident (Nat -> Nat -> Bool)
  | Add : ident (Nat -> Nat -> Nat)
  | Pair (*{A B : base_type}*) : ident (A -> B -> A * B)
  | Fst (*{A B}*) : ident (A * B -> A)
  | Snd (*{A B}*) : ident (A * B -> B)
  | MatchPair (*{A B P : base_type}*) : ident ((A -> B -> P) -> A * B -> P)
  | Nil (*{A}*) : ident (List A)
  | Cons (*{A : base_type}*) : ident (A -> List A -> List A)
  | ListMap (*{A B : base_type}*) : ident ((A -> B) -> List A -> List B)
  | ListApp (*{A}*) : ident (List A -> List A -> List A)
  | ListFlatMap (*{A B : base_type}*) : ident ((A -> List B) -> List A -> List B)
  | ListRect (*{A : base_type}*) (*{P : base_type}*) : ident ((Unit -> P) -> (A -> List A -> P -> P) -> List A -> P)
  | ListFoldRight (*{A : base_type}*) (*{B : base_type}*) : ident ((B -> A -> A) -> (Unit -> A) -> List B -> A)
  | ListPartition (*{A : base_type}*) : ident ((A -> Bool) -> List A -> List A * List A)
  | TT : ident Unit
  | iTrue : ident Bool
  | iFalse : ident Bool
  | BoolRect (*{P : base_type}*) : ident ((Unit -> P) -> (Unit -> P) -> Bool -> P)
  | Literal (n : nat) : ident Nat.
End ident.

Show Match ident.
(*
<<<
#!/usr/bin/env python2

show_match_ident = r"""match # with
 | O =>
 | S =>
 | NatRect =>
 | NatEqb =>
 | Add =>
 | Pair =>
 | Fst =>
 | Snd =>
 | MatchPair =>
 | Nil =>
 | Cons =>
 | ListMap =>
 | ListApp =>
 | ListFlatMap =>
 | ListRect =>
 | ListFoldRight =>
 | ListPartition =>
 | TT =>
 | iTrue =>
 | iFalse =>
 | BoolRect =>
 | Literal n =>
 end

"""
ctors = [i.strip('|=> ').split(' ') for i in show_match_ident.split('\n') if i.strip().startswith('|')]
pctors = ['p' + i[0] for i in ctors]
print(r"""(* p for pattern *)
Inductive pident : Type :=
| %s.
""" % '\n| '.join(pctors))
print(r"""Definition pident_ident_beq {t} (X : pident) (Y : ident t) : bool
  := match X, Y with
     | %s
       => true
     | %s
       => false
     end.
""" % ('\n     | '.join(pctor + ', ' + ' '.join([ctor[0]] + ['_'] * (len(ctor)-1))
                        for pctor, ctor in zip(pctors, ctors)),
       '\n     | '.join(pctor + ', _' for pctor in pctors)))
print(r"""Definition eta_ident_cps {T : type -> Type} {t} (idc : ident t)
           (f : forall t', ident t' -> T t')
  : T t
  := match idc with
     | %s
     end.
""" % ('\n     | '.join(' '.join(ctor) + ' => f _ '
                        + (('%s' if len(ctor) == 1 else '(@%s)')
                           % ' '.join(ctor))
                        for ctor in ctors)))
print(r"""Definition eta_all_option_pident_cps {T} (f : pident -> option T)
  : option (pident -> T)
  := (%s;
      Some (fun c
            => match c with
               | %s
               end))%%option.
""" % (';\n      '.join('f' + ctor[0] + ' <- f p' + ctor[0] for ctor in ctors),
       '\n               | '.join('p' + ctor[0] + ' => f' + ctor[0] for ctor in ctors)))
print(r"""Definition pident_of_ident {t} (idc : ident t) : pident
  := match idc with
     | %s
     end.
""" % ('\n     | '.join(' '.join(ctor) + ' => ' + pctor for ctor, pctor in zip(ctors, pctors))))
print(r"""Definition orb_pident (f : pident -> bool) : bool
  := (%s)%%bool.
""" % ' || '.join('f ' + pctor for pctor in pctors))
>>>
*)
(* p for pattern *)
Inductive pident : Type :=
| pO
| pS
| pNatRect
| pNatEqb
| pAdd
| pPair
| pFst
| pSnd
| pMatchPair
| pNil
| pCons
| pListMap
| pListApp
| pListFlatMap
| pListRect
| pListFoldRight
| pListPartition
| pTT
| piTrue
| piFalse
| pBoolRect
| pLiteral.

Definition pident_ident_beq {t} (X : pident) (Y : ident t) : bool
  := match X, Y with
     | pO, O
     | pS, S
     | pNatRect, NatRect
     | pNatEqb, NatEqb
     | pAdd, Add
     | pPair, Pair
     | pFst, Fst
     | pSnd, Snd
     | pMatchPair, MatchPair
     | pNil, Nil
     | pCons, Cons
     | pListMap, ListMap
     | pListApp, ListApp
     | pListFlatMap, ListFlatMap
     | pListRect, ListRect
     | pListFoldRight, ListFoldRight
     | pListPartition, ListPartition
     | pTT, TT
     | piTrue, iTrue
     | piFalse, iFalse
     | pBoolRect, BoolRect
     | pLiteral, Literal _
       => true
     | pO, _
     | pS, _
     | pNatRect, _
     | pNatEqb, _
     | pAdd, _
     | pPair, _
     | pFst, _
     | pSnd, _
     | pMatchPair, _
     | pNil, _
     | pCons, _
     | pListMap, _
     | pListApp, _
     | pListFlatMap, _
     | pListRect, _
     | pListFoldRight, _
     | pListPartition, _
     | pTT, _
     | piTrue, _
     | piFalse, _
     | pBoolRect, _
     | pLiteral, _
       => false
     end.

Definition eta_ident_cps {T : type -> Type} {t} (idc : ident t)
           (f : forall t', ident t' -> T t')
  : T t
  := match idc with
     | O => f _ O
     | S => f _ S
     | NatRect => f _ NatRect
     | NatEqb => f _ NatEqb
     | Add => f _ Add
     | Pair => f _ Pair
     | Fst => f _ Fst
     | Snd => f _ Snd
     | MatchPair => f _ MatchPair
     | Nil => f _ Nil
     | Cons => f _ Cons
     | ListMap => f _ ListMap
     | ListApp => f _ ListApp
     | ListFlatMap => f _ ListFlatMap
     | ListRect => f _ ListRect
     | ListFoldRight => f _ ListFoldRight
     | ListPartition => f _ ListPartition
     | TT => f _ TT
     | iTrue => f _ iTrue
     | iFalse => f _ iFalse
     | BoolRect => f _ BoolRect
     | Literal n => f _ (@Literal n)
     end.

Definition eta_all_option_pident_cps {T} (f : pident -> option T)
  : option (pident -> T)
  := (fO <- f pO;
      fS <- f pS;
      fNatRect <- f pNatRect;
      fNatEqb <- f pNatEqb;
      fAdd <- f pAdd;
      fPair <- f pPair;
      fFst <- f pFst;
      fSnd <- f pSnd;
      fMatchPair <- f pMatchPair;
      fNil <- f pNil;
      fCons <- f pCons;
      fListMap <- f pListMap;
      fListApp <- f pListApp;
      fListFlatMap <- f pListFlatMap;
      fListRect <- f pListRect;
      fListFoldRight <- f pListFoldRight;
      fListPartition <- f pListPartition;
      fTT <- f pTT;
      fiTrue <- f piTrue;
      fiFalse <- f piFalse;
      fBoolRect <- f pBoolRect;
      fLiteral <- f pLiteral;
      Some (fun c
            => match c with
               | pO => fO
               | pS => fS
               | pNatRect => fNatRect
               | pNatEqb => fNatEqb
               | pAdd => fAdd
               | pPair => fPair
               | pFst => fFst
               | pSnd => fSnd
               | pMatchPair => fMatchPair
               | pNil => fNil
               | pCons => fCons
               | pListMap => fListMap
               | pListApp => fListApp
               | pListFlatMap => fListFlatMap
               | pListRect => fListRect
               | pListFoldRight => fListFoldRight
               | pListPartition => fListPartition
               | pTT => fTT
               | piTrue => fiTrue
               | piFalse => fiFalse
               | pBoolRect => fBoolRect
               | pLiteral => fLiteral
               end))%option.

Definition pident_of_ident {t} (idc : ident t) : pident
  := match idc with
     | O => pO
     | S => pS
     | NatRect => pNatRect
     | NatEqb => pNatEqb
     | Add => pAdd
     | Pair => pPair
     | Fst => pFst
     | Snd => pSnd
     | MatchPair => pMatchPair
     | Nil => pNil
     | Cons => pCons
     | ListMap => pListMap
     | ListApp => pListApp
     | ListFlatMap => pListFlatMap
     | ListRect => pListRect
     | ListFoldRight => pListFoldRight
     | ListPartition => pListPartition
     | TT => pTT
     | iTrue => piTrue
     | iFalse => piFalse
     | BoolRect => pBoolRect
     | Literal n => pLiteral
     end.

Definition orb_pident (f : pident -> bool) : bool
  := (f pO || f pS || f pNatRect || f pNatEqb || f pAdd || f pPair || f pFst || f pSnd || f pMatchPair || f pNil || f pCons || f pListMap || f pListApp || f pListFlatMap || f pListRect || f pListFoldRight || f pListPartition || f pTT || f piTrue || f piFalse || f pBoolRect || f pLiteral)%bool.

(*===*)

Definition invert_Literal {t} (idc : ident t) : option nat
  := match idc with
     | Literal n => Some n
     | _ => None
     end.

Definition or_opt_pident {T} (f : pident -> option T) : bool
  := orb_pident (fun p => match f p with Some _ => true | None => false end).

Inductive expr {var : type -> Type} : type -> Type :=
| Var {t} (v : var t) : expr t
| Abs {s d} (f : var s -> expr d) : expr (s -> d)
| Ident {t} (idc : ident t) : expr t
| App {s d} (f : expr (s -> d)) (x : expr s) : expr d
| LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B .

Inductive pattern : Type :=
| Wildcard (t : type)
| pIdent (idc : pident)
| pApp (f x : pattern).

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
Notation "# idc" := (Ident idc) : expr_scope.
Notation "## n" := (Ident (Literal n)) : expr_scope.
Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
Infix "@" := App : expr_scope.
Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
Notation "'λ'  x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) ..)) : expr_scope.
Notation "'$' x" := (Var x) (at level 10, format "'$' x") : expr_scope.
Notation "( )" := (#TT)%expr : expr_scope.
Notation "0" := (#O)%expr : expr_scope.
Notation "n '.+1'" := (#S @ n)%expr (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (#Add @ x @ y)%expr : expr_scope.
Notation "( x , y , .. , z )" := (#Pair @ .. (#Pair @ x @ y) .. @ z)%expr : expr_scope.
Notation "x :: xs" := (#Cons @ x @ xs)%expr : expr_scope.
Notation "xs ++ ys" := (#ListApp @ xs @ ys)%expr : expr_scope.
Notation "[ ]" := (#Nil)%expr : expr_scope.
Notation "[ x ]" := (x :: [])%expr : expr_scope.
Notation "[ x ; y ; .. ; z ]" :=  (#Cons @ x @ (#Cons @ y @ .. (#Cons @ z @ []) ..))%expr : expr_scope.


Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "#?" := (pIdent pLiteral) : pattern_scope.
Notation "??{ t }" := (Wildcard t) (format "??{ t }") : pattern_scope.
Notation "??" := (Wildcard Base) : pattern_scope.
Notation "# idc" := (pIdent idc) : pattern_scope.
Infix "@" := pApp : pattern_scope.
Notation "( )" := (#pTT)%pattern : pattern_scope.
Notation "0" := (#pO)%pattern : pattern_scope.
Notation "n '.+1'" := (#pS @ n)%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (#pAdd @ x @ y)%pattern : pattern_scope.
Notation "( x , y , .. , z )" := (#pPair @ .. (#pPair @ x @ y) .. @ z)%pattern : pattern_scope.
Notation "x :: xs" := (#pCons @ x @ xs)%pattern : pattern_scope.
Notation "xs ++ ys" := (#pListApp @ xs @ ys)%pattern : pattern_scope.
Notation "[ ]" := (#pNil)%pattern : pattern_scope.
Notation "[ x ]" := (x :: [])%pattern : pattern_scope.
Notation "[ x ; y ; .. ; z ]" :=  (#pCons @ x @ (#pCons @ y @ .. (#pCons @ z @ []) ..))%pattern : pattern_scope.

(** TODO: MOVEME, FIX NOTATION CLASH *)
Definition cpsbind {A B} (v:~> A) (f:A ~> B) : ~> B
  := fun T k => (a <- v; fa <- f a; k fa)%cps.
Notation "x' <- v ; C" := (cpsbind v%cps (fun x' => C%cps)) : cps_scope.

Notation "x' <-- v ; C" := (cpsbind v%cps (fun x' T k => match x' with Some x' => C%cps T k | None => k None end)) : cps_scope.

(** N.B. The pattern matching compilation algorithm in
    http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf ---
    "Compiling Pattern Matching to Good Decision Trees" by Luc
    Maranget --- is based on manipulating untyped terms, or
    manipulating typed terms in a raw (untyped) syntax tree.  PHOAS
    enforces well-typedness by construction, and we need something
    like this for NBE (normalization by evaluation), which we use for
    reducing applications of lambdas, to work.  So we jump through
    many hoops to cast across types. *)
Module type.
  Fixpoint try_make_transport_cps (P : type -> Type) (t1 t2 : type) : ~> option (P t1 -> P t2)
    := match t1, t2 with
       | Base, Base
         => (return (Some (fun v => v)))
       | Arrow s d, Arrow s' d'
         => (trs <-- try_make_transport_cps (fun s => P (Arrow s _)) _ _;
              trd <-- try_make_transport_cps (fun d => P (Arrow _ d)) _ _;
            return (Some (fun v => trd (trs v))))
       | Base, _
       | Arrow _ _, _
         => (return None)
       end%option%cps.

  Definition try_transport_cps (P : type -> Type) (t1 t2 : type) (v : P t1) : ~> option (P t2)
    := (tr <-- try_make_transport_cps P t1 t2;
        return (Some (tr v)))%cps.
End type.

Module UnderLets.
  Section with_var.
    Context {var : type -> Type}.
    Local Notation expr := (@expr var).

    Inductive UnderLets {T : Type} :=
    | Base (v : T)
    | UnderLet {A} (x : expr A) (f : var A -> UnderLets).

    Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
      := match x with
         | Base v => e v
         | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
         end.

    Fixpoint splice_list {A B} (ls : list (@UnderLets A)) (e : list A -> @UnderLets B) : @UnderLets B
      := match ls with
         | nil => e nil
         | cons x xs
           => splice x (fun x => @splice_list A B xs (fun xs => e (cons x xs)))
         end.

    Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
      := match x with
         | Base v => v
         | UnderLet A x f
           => LetIn x (fun v => @to_expr _ (f v))
         end.
  End with_var.
  Global Arguments UnderLets : clear implicits.
End UnderLets.
Notation UnderLets := UnderLets.UnderLets.
Notation UnderLet := UnderLets.UnderLet.
Delimit Scope under_lets_scope with under_lets.
Bind Scope under_lets_scope with UnderLets.UnderLets.
Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.
Notation "x <--- y ; f" := (UnderLets.splice_list y (fun x => f%under_lets)) : under_lets_scope.

Section with_var.
  Context {var : type -> Type}.
  Local Notation topexpr := expr.
  Local Notation expr := (@expr var).
  Local Notation UnderLets := (@UnderLets var).

  Fixpoint value' (with_lets : bool) (t : type)
    := match t with
       | Base as t
         => if with_lets then UnderLets (expr t) else expr t
       | Arrow s d
         => value' false s -> value' true d
       end.
  Definition value := value' false.
  Definition value_with_lets := value' true.
  Definition Base_value {t} : value t -> value_with_lets t
    := match t with
       | Base => fun v => UnderLets.Base v
       | Arrow _ _ => fun v => v
       end.
  Fixpoint push_lets_value {with_lets} {t} : UnderLets (value' with_lets t) -> value_with_lets t
    := match t, with_lets return UnderLets (value' with_lets t) -> value_with_lets t with
       | Base, true => fun e => e <-- e; e
       | Base, false => fun e => e
       | Arrow s d, _
         => fun f x => @push_lets_value _ d (f <-- f; UnderLets.Base (f x))
       end%under_lets.
  Definition splice_value'_with_lets {t t'} : value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t'
    := match t return value_with_lets t -> (value t -> value_with_lets t') -> value_with_lets t' with
       | Arrow _ _
         => fun e k => k e
       | Base => fun e k => push_lets_value (e <-- e; UnderLets.Base (k e))
       end%under_lets.
  Local Notation "e <---- e' ; f" := (splice_value'_with_lets e' (fun e => f%under_lets)) : under_lets_scope.

  Fixpoint reify {with_lets} {t} : value' with_lets t -> expr t
    := match t, with_lets return value' with_lets t -> expr t with
       | Base, false => fun v => v
       | Base, true => fun v => UnderLets.to_expr v
       | Arrow s d, _
         => fun f => λ x , @reify _ d (f (@reflect _ s ($x)))
       end%expr
  with reflect {with_lets} {t} : expr t -> value' with_lets t
       := match t, with_lets return expr t -> value' with_lets t with
          | Base, false => fun v => v
          | Base, true => fun v => UnderLets.Base v
          | Arrow s d, _
            => fun f (x : value' _ _) => @reflect _ d (f @ (@reify _ s x))
          end%expr.

  Inductive rawexpr : Type :=
  | rIdent {t} (idc : ident t) {t'} (alt : expr t')
  | rApp (f x : rawexpr) {t} (alt : expr t)
  | rExpr {t} (e : expr t)
  | rValue {t} (e : value t).

  Definition type_of_rawexpr (e : rawexpr) : type
    := match e with
       | rIdent t idc t' alt => t'
       | rApp f x t alt => t
       | rExpr t e => t
       | rValue t e => t
       end.
  Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
    := match e with
       | rIdent t idc t' alt => alt
       | rApp f x t alt => alt
       | rExpr t e => e
       | rValue t e => reify e
       end.
  Definition value_of_rawexpr (e : rawexpr) : value (type_of_rawexpr e)
    := Eval cbv [expr_of_rawexpr] in
        match e with
        | rValue t e => e
        | e => reflect (expr_of_rawexpr e)
        end.
  Definition rValueOrExpr {t} : value t -> rawexpr
    := match t with
       | Base => @rExpr _
       | Arrow _ _ => @rValue _
       end.

  Definition try_rExpr_cps {T t} (k : option rawexpr -> T) : expr t -> T
    := match t with
       | Base => fun e => k (Some (rExpr e))
       | Arrow _ _ => fun _ => k None
       end.

  Definition reveal_rawexpr_cps (e : rawexpr) : ~> rawexpr
    := fun T k
       => match e with
          | rExpr _ e as r
          | rValue Base e as r
            => match e with
               | Ident t idc => k (rIdent idc e)
               | App s d f x => k (rApp (rExpr f) (rExpr x) e)
               | _ => k r
               end
          | e' => k e'
          end.

  Fixpoint binding_dataT (p : pattern) : Type
    := match p return Type with
       | Wildcard t => value t
       | pIdent idc => if pident_beq pLiteral idc then nat else unit
       | pApp f x => binding_dataT f * binding_dataT x
       end%type.

  Fixpoint bind_data_cps (e : rawexpr) (p : pattern)
    : ~> option (binding_dataT p)
    := match p, e return ~> option (binding_dataT p) with
       | Wildcard t, _
         => type.try_transport_cps _ _ _ (value_of_rawexpr e)
       | pIdent pidc, rIdent _ idc _ _
         => (if pident_beq pLiteral pidc as b return ~> option (if b then nat else unit)
             then return (invert_Literal idc)
             else if pident_ident_beq pidc idc
                  then return (Some tt)
                  else return None)
       | pApp pf px, rApp f x _ _
         => (f' <-- bind_data_cps f pf;
               x' <-- bind_data_cps x px;
             return (Some (f', x')))
       | pIdent _, _
       | pApp _ _, _
         => (return None)
       end%cps.

  Inductive decision_tree :=
  | TryLeaf (k : nat) (onfailure : decision_tree)
  | Failure
  | Switch (icases : pident -> option decision_tree)
           (app_case : option decision_tree)
           (default : decision_tree)
  | Swap (i : nat) (cont : decision_tree).

  Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
    := match nth_error ls i, nth_error ls j with
       | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
       | _, _ => None
       end.

  Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : option nat -> list rawexpr -> option (unit -> T) -> T) {struct d} : T
    := match d with
       | TryLeaf k onfailure
         => cont (Some k) ctx
                 (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
       | Failure => cont None ctx None
       | Switch icases app_case default_case
         => let default _ := @eval_decision_tree T ctx default_case cont in
            match ctx with
            | nil => cont None ctx None
            | ctx0 :: ctx'
              => reveal_rawexpr_cps
                   ctx0 _
                   (fun ctx0'
                    => match ctx0' with
                       | rIdent t idc t' alt
                         => if or_opt_pident icases
                            then eta_ident_cps
                                   idc
                                   (fun _ idc'
                                    => match icases (pident_of_ident idc') with
                                       | Some icase
                                         => @eval_decision_tree
                                              T ctx' icase
                                              (fun k ctx''
                                               => cont k (rIdent idc' alt :: ctx''))
                                       | None => default tt
                                       end)
                            else default tt
                       | rApp f x t alt
                         => match app_case with
                            | Some app_case
                              => @eval_decision_tree
                                   T (f :: x :: ctx') app_case
                                   (fun k ctx''
                                    => match ctx'' with
                                       | f' :: x' :: ctx'''
                                         => cont k (rApp f' x' alt :: ctx''')
                                       | _ => cont None ctx
                                       end)
                            | None => default tt
                            end
                       | rExpr t e
                       | rValue t e
                         => default tt
                       end)
            end
       | Swap i d'
         => match swap_list 0 i ctx with
            | Some ctx'
              => @eval_decision_tree
                   T ctx' d'
                   (fun k ctx''
                    => match swap_list 0 i ctx'' with
                       | Some ctx''' => cont k ctx'''
                       | None => cont None ctx
                       end)
            | None => cont None ctx None
            end
       end.

  Local Notation opt_anyexprP ivar
    := (fun should_do_again : bool => UnderLets (@topexpr (if should_do_again then ivar else var) Base)).
  Local Notation opt_anyexpr ivar
    := (option (sigT (opt_anyexprP ivar))).

  Local Notation rewrite_rulesT' ivar
    := (list { p : pattern & binding_dataT p -> forall T, (opt_anyexpr ivar  -> T) -> T })
         (only parsing).

  Definition eval_rewrite_rules
             {ivar}
             (do_again : @topexpr ivar Base -> UnderLets (expr Base))
             (maybe_do_again
              := fun (should_do_again : bool)
                 => if should_do_again return ((@topexpr (if should_do_again then ivar else var) Base) -> UnderLets (expr Base))
                    then do_again
                    else UnderLets.Base)
             (d : decision_tree)
             (rew : rewrite_rulesT' ivar)
             (e : rawexpr)
    : UnderLets (expr (type_of_rawexpr e))
    := eval_decision_tree
         (e::nil) d
         (fun k ctx default_on_rewrite_failure
          => match k, ctx return UnderLets (expr (type_of_rawexpr e)) with
             | Some k', e'::nil
               => match nth_error rew k' return UnderLets (expr (type_of_rawexpr e)) with
                  | Some (existT p f)
                    => bind_data_cps
                         e' p _
                         (fun v
                          => match v with
                             | Some v
                               => f v _
                                    (fun fv
                                     => match fv return UnderLets (expr (type_of_rawexpr e)) with
                                        | Some (existT should_do_again fv)
                                          => (fv <-- fv;
                                               fv <-- maybe_do_again should_do_again fv;
                                               type.try_transport_cps
                                                 _ _ _ fv _
                                                 (fun fv'
                                                  => match fv', default_on_rewrite_failure with
                                                    | Some fv'', _ => UnderLets.Base fv''
                                                    | None, Some default => default tt
                                                    | None, None => UnderLets.Base (expr_of_rawexpr e)
                                                    end))%under_lets
                                        | None => match default_on_rewrite_failure with
                                                  | Some default => default tt
                                                  | None => UnderLets.Base (expr_of_rawexpr e)
                                                  end
                                        end)
                             | None => UnderLets.Base (expr_of_rawexpr e)
                             end)
                  | None => UnderLets.Base (expr_of_rawexpr e)
                  end
             | _, _ => UnderLets.Base (expr_of_rawexpr e)
            end).

  Local Notation enumerate ls
    := (List.combine (List.seq 0 (List.length ls)) ls).

  Fixpoint first_satisfying_helper {A B} (f : A -> option B) (ls : list A) : option B
    := match ls with
       | nil => None
       | cons x xs
         => match f x with
            | Some v => Some v
            | None => first_satisfying_helper f xs
            end
       end.

  Definition get_index_of_first_non_wildcard (p : list pattern) : option nat
    := first_satisfying_helper
         (fun '(n, x) => match x with
                         | Wildcard _ => None
                         | _ => Some n
                         end)
         (enumerate p).

  Definition filter_pattern_wildcard (p : list (nat * list pattern)) : list (nat * list pattern)
    := filter (fun '(_, p) => match p with
                              | Wildcard _::_ => true
                              | _ => false
                              end)
              p.

  Definition contains_pattern_pident (pidc : pident) (p : list (nat * list pattern)) : bool
    := existsb (fun '(n, p) => match p with
                               | pIdent pidc'::_ => pident_beq pidc pidc'
                               | _ => false
                               end)
               p.

  Definition contains_pattern_app (p : list (nat * list pattern)) : bool
    := existsb (fun '(n, p) => match p with
                               | pApp _ _::_ => true
                               | _ => false
                               end)
               p.

  Definition refine_pattern_app (p : nat * list pattern) : option (nat * list pattern)
    := match p with
       | (n, Wildcard _::ps)
         => Some (n, Wildcard ?? :: Wildcard ?? :: ps) (* dummy arguments to [Wildcard] *)
       | (n, pApp f x :: ps)
         => Some (n, f :: x :: ps)
       | (_, pIdent _::_)
       | (_, nil)
         => None
       end.

  Definition refine_pattern_pident (pidc : pident) (p : nat * list pattern) : option (nat * list pattern)
    := match p with
       | (n, Wildcard _::ps)
         => Some (n, ps)
       | (n, pIdent pidc'::ps)
         => if pident_beq pidc pidc'
            then Some (n, ps)
            else None
       | (_, pApp _ _::_)
       | (_, nil)
         => None
       end.

  Fixpoint omap {A B} (f : A -> option B) (ls : list A) : list B
    := match ls with
       | nil => nil
       | x :: xs => match f x with
                    | Some fx => fx :: omap f xs
                    | None => omap f xs
                    end
       end.

  Definition compile_rewrites_step
             (compile_rewrites : list (nat * list pattern) -> option decision_tree)
             (pattern_matrix : list (nat * list pattern))
    : option decision_tree
    := match pattern_matrix with
       | nil => Some Failure
       | (n1, p1) :: ps
         => match get_index_of_first_non_wildcard p1 with
            | None (* p1 is all wildcards *)
              => (onfailure <- compile_rewrites ps;
                    Some (TryLeaf n1 onfailure))
            | Some Datatypes.O
              => default_case <- compile_rewrites (filter_pattern_wildcard pattern_matrix);
                   app_case <- (if contains_pattern_app pattern_matrix
                                then option_map Some (compile_rewrites (omap refine_pattern_app pattern_matrix))
                                else Some None);
                   icases
                     <- (if orb_pident (fun pidc => contains_pattern_pident pidc pattern_matrix)
                         then eta_all_option_pident_cps
                                (fun pidc => if contains_pattern_pident pidc pattern_matrix
                                             then option_map Some (compile_rewrites (omap (refine_pattern_pident pidc) pattern_matrix))
                                             else Some None)
                         else Some (fun _ => None));
                   Some (Switch icases app_case default_case)
            | Some i
              => let pattern_matrix'
                     := List.map
                          (fun '(n, ps)
                           => (n,
                               match swap_list 0 i ps with
                               | Some ps' => ps'
                               | None => nil (* should be impossible *)
                               end))
                          pattern_matrix in
                 d <- compile_rewrites pattern_matrix';
                   Some (Swap i d)
            end
       end%option.

  Fixpoint compile_rewrites' (fuel : nat) (pattern_matrix : list (nat * list pattern))
    : option decision_tree
    := match fuel with
       | Datatypes.O => None
       | Datatypes.S fuel' => compile_rewrites_step (@compile_rewrites' fuel') pattern_matrix
       end.

  Definition compile_rewrites {ivar} (fuel : nat) (ps : rewrite_rulesT' ivar)
    := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).

  Fixpoint with_bindingsT (p : pattern) (T : Type)
    := match p return Type with
       | Wildcard t => value t -> T
       | pIdent pLiteral => nat -> T
       | pApp f x => with_bindingsT f (with_bindingsT x T)
       | pIdent _ => T
       end.

  Fixpoint lift_with_bindings {p} {A B : Type} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
    := match p return with_bindingsT p A -> with_bindingsT p B with
       | Wildcard _
       | pIdent pLiteral
         => fun f e => F (f e)
       | pApp f x
         => @lift_with_bindings
              f _ _
              (@lift_with_bindings x _ _ F)
       | pIdent _
         => F
       end.

  Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
    := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
       | Wildcard _
       | pIdent pLiteral
         => fun f => f
       | pApp f x
         => fun F '(vf, vx)
            => @app_binding_data _ x (@app_binding_data _ f F vf) vx
       | pIdent _
         => fun f 'tt => f
       end.

  Definition reify_list (*{t : base_type}*) (ls : list (expr Base)) : expr Base
    := fold_right
         (fun x xs => x :: xs)%expr
         []%expr
         ls.

  Fixpoint reflect_list_cps {t} (e : expr t)
    : ~> option (list (expr Base))
    := match e return ~> option (list (expr Base))
       with
       | [] => (return (Some nil))
       | x :: xs
         => (x' <-- type.try_transport_cps _ _ _ x;
               xs' <-- @reflect_list_cps _ xs;
             return (Some (x' :: xs')%list))
       | _ => (return None)
       end%expr%cps.
  Arguments reflect_list_cps {t} e [T] k.

  (** XXX MOVEME? *)
  Definition mkcast {P : type -> Type} {t1 t2 : type} : ~> (option (P t1 -> P t2))
    := fun T k => type.try_make_transport_cps P t1 t2 _ k.
  Definition cast {P : type -> Type} {t1 t2 : type} (v : P t1) : ~> (option (P t2))
    := fun T k => type.try_transport_cps P t1 t2 v _ k.
  Definition castv {t1 t2} (v : value t1) : ~> (option (value t2))
    := fun T k => type.try_transport_cps value t1 t2 v _ k.
  Definition ret {A} (v : A) : ~> A := fun T k => k v.
  Definition oret {A} (v : A) : ~> (option A) := fun T k => k (Some v).
  Let UnderLetsExpr {ivar t} := @UnderLets.UnderLets ivar (@topexpr ivar t).
  Let BaseWrapExpr {ivar t} (e : @topexpr ivar t) : @UnderLetsExpr ivar t := UnderLets.Base e.
  Let BaseExpr {ivar t} : @topexpr ivar t -> @UnderLets.UnderLets ivar (@topexpr ivar t) := UnderLets.Base.
  Coercion BaseWrapExpr : expr >-> UnderLetsExpr.
  Coercion BaseExpr : expr >-> UnderLets.
  Notation make_rewrite'_cps p f
    := (existT
          (fun p' : pattern => binding_dataT p' ~> (opt_anyexpr value))
          p%pattern
          (fun v T (k : opt_anyexpr value -> T)
           => @app_binding_data _ p%pattern f%expr v T k)).
  Notation make_rewrite' p f
    := (existT
          (fun p' : pattern => binding_dataT p' ~> (opt_anyexpr value))
          p%pattern
          (fun v T (k : opt_anyexpr value -> T)
           => k (@app_binding_data _ p%pattern f%expr v))).
  Notation make_rewrite p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsExpr var Base => Some (existT (opt_anyexprP value) false x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_step p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsExpr value Base => Some (existT (opt_anyexprP value) true x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:~> (option (UnderLets (expr Base))) => (x' <-- x; oret (existT (opt_anyexprP value) false x'))%cps) f%expr) in
        make_rewrite'_cps p f').
  Notation make_rewrite_step_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:~> (option (UnderLets (@topexpr value Base))) => (x' <-- x; oret (existT (opt_anyexprP value) true x'))%cps) f%expr) in
        make_rewrite'_cps p f').
  Definition rewrite_rules : rewrite_rulesT' value
    := [make_rewrite (0 + ??) (fun x => x);
          make_rewrite (?? + 0) (fun x => x);
          make_rewrite (#? + #?) (fun x y => ##(x + y));
          make_rewrite (#? + ??.+1) (fun x y => ##(Datatypes.S x) + y);
          make_rewrite (??.+1 + #?) (fun x y => x + ##(Datatypes.S y));
          make_rewrite (??.+1 + ??.+1) (fun x y => (x+y).+1.+1);
          make_rewrite (??.+1 + ??) (fun x y => (x+y).+1);
          make_rewrite (?? + ??.+1) (fun x y => (x+y).+1);
          make_rewrite (#pNatEqb @ #? @ #?) (fun x y => if Nat.eqb x y return topexpr _ then #iTrue else #iFalse);
          make_rewrite (#pFst @ (??, ??)) (fun x y => x);
          make_rewrite (#pSnd @ (??, ??)) (fun x y => y);
          make_rewrite (#pBoolRect @ ??{?? -> ??} @ ??{?? -> ??} @ #piTrue) (fun t f => t #TT);
          make_rewrite (#pBoolRect @ ??{?? -> ??} @ ??{?? -> ??} @ #piFalse) (fun t f => f #TT);
          make_rewrite (#pMatchPair @ ??{?? -> ?? -> ??} @ (??, ??)) (fun f x y => f x y);
          make_rewrite_cps
            (?? ++ ??)
            (fun xs ys
             => xs <-- reflect_list_cps xs;
                ys <-- reflect_list_cps ys;
                oret (UnderLets.Base (reify_list (List.app xs ys))));
          make_rewrite_step_cps
            (#pListFlatMap @ ??{?? -> ??} @ ??)
            (fun f xs
             => xs <-- reflect_list_cps xs;
                  oret (fxs <--- List.map f xs;
                          UnderLets.Base
                            (#ListFoldRight @ (λ ls1 ls2, $ls1 ++ $ls2) @ (λ _, []) @ $(reify_list fxs))%expr));
          make_rewrite_step_cps
            (#pListPartition @ ??{?? -> ??} @ ??)
            (fun f xs
             => xs <-- reflect_list_cps xs;
                  oret (list_rect
                          _
                          (UnderLets.Base ([], []))
                          (fun x tl partition_tl
                           => partition_tl <-- partition_tl;
                                fx <-- f x;
                                UnderLets.Base
                                  (#MatchPair
                                    @ (λ g d, #BoolRect
                                               @ (λ _, ($x :: $g, $d))
                                               @ (λ _, ($g, $x :: $d))
                                               @ $fx)
                                    @ partition_tl))
                          xs)%expr%under_lets);
          make_rewrite_cps
            (#pListFoldRight @ ??{?? -> ?? -> ??} @ ?? @ ??)
            (fun f init xs
             => xs <-- reflect_list_cps xs;
                  oret (fold_right (fun x y => y <-- y; f x y) (UnderLets.Base init) xs)%under_lets);
          make_rewrite_cps
            (#pListRect @ ??{?? -> ??} @ ??{?? -> ?? -> ?? -> ??} @ ??)
            (fun Pnil Pcons xs
             => xs <-- reflect_list_cps xs;
                  oret (list_rect
                          (fun _ => UnderLets (expr ??))
                          (Pnil #TT)
                          (fun x' xs' rec => rec <-- rec; Pcons x' (reify_list xs') rec)
                          xs)%under_lets);
          make_rewrite_cps
            (#pListMap @ ??{?? -> ??} @ ??)
            (fun f xs
             => xs <-- reflect_list_cps xs;
                  oret (fxs <--- List.map f xs;
                          UnderLets.Base (reify_list fxs))%under_lets);
          make_rewrite_cps
            (#pListMap @ ??{?? -> ??} @ (?? :: ??))
            (fun f x xs
             => oret (fx <-- f x;
                          UnderLets.Base (fx :: #ListMap @ (λ v , UnderLets.to_expr (f ($v))) @ xs)%expr)%under_lets)
       ]%list%pattern%cps%option%under_lets.

  Definition dtree : decision_tree
    := Eval compute in invert_Some (compile_rewrites 100 rewrite_rules).
  Print dtree.
  (*
Fixpoint dorewrite' (e : expr) : expr
  := match e with
     | AppCtor Add (x::y::nil)
       => dlet x' := dorewrite' x in
          dlet y' := dorewrite' y in
          domatch rewrite_rules (AppCtor Add (x' :: y' :: nil))
     | AppCtor c args
       => dlet args' := List.map dorewrite' args in
          AppCtor c args'
     | Literal n => Literal n
     end.

Arguments bind_data_cps / .
Arguments dorewrite' / .
Arguments rewrite_rules / .
Arguments domatch / .
Definition dorewrite
  := Eval cbn [bind_data_cps dorewrite' rewrite_rules domatch ctor_beq ctor_beq_cps list_rect Option.bind] in dorewrite'.
   *)
  Definition default_fuel := Eval compute in List.length rewrite_rules.

  Section with_do_again.
    Context (do_again : @topexpr value Base -> UnderLets (expr Base)).

    Definition dorewrite1 (e : rawexpr) : UnderLets (expr (type_of_rawexpr e))
      := eval_rewrite_rules do_again dtree rewrite_rules e.

    Fixpoint do_rewrite_ident (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t
      := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t with
         | Base
           => fun e k => k (fun t => UnderLets (expr t)) (dorewrite1 e)
         | Arrow s d
           => fun f k (x : value' _ _) => @do_rewrite_ident d (rApp f (rValueOrExpr x) (k _ (expr_of_rawexpr f) @ reify x))%expr (fun _ => id)
         end.

    Fixpoint dorewrite' {t} (e : @topexpr value t) : value_with_lets t
      := match e in topexpr t return value_with_lets t with
         | Ident t idc
           => eta_ident_cps idc (fun t' idc' => do_rewrite_ident t' (rIdent idc' #idc') (fun _ => id))
         | App s d f x => let f : value s -> value_with_lets d := @dorewrite' _ f in x <---- @dorewrite' _ x; f x
         | LetIn A B x f => x <---- @dorewrite' A x;
                             push_lets_value
                               (UnderLet (@reify false _ x)
                                         (fun xv => UnderLets.Base (@dorewrite' B (f (reflect ($xv)%expr)))))
         | Var t v => Base_value v
         | Abs s d f => fun x : value s => @dorewrite' d (f x)
         end%under_lets.

    Fixpoint nbe {t} (e : @topexpr value t) : value_with_lets t
      := match e in topexpr t return value_with_lets t with
         | Ident t idc => reflect (Ident idc)
         | App s d f x => let f : value s -> value_with_lets d := @nbe _ f in x <---- @nbe _ x; f x
         | LetIn A B x f => x <---- @nbe A x;
                             push_lets_value
                               (UnderLet (@reify false _ x)
                                         (fun xv => UnderLets.Base (@nbe B (f (reflect ($xv)%expr)))))
         | Var t v => Base_value v
         | Abs s d f => fun x : value s => @nbe d (f x)
         end%under_lets.
  End with_do_again.

  Fixpoint dorewrite'' (fuel : nat) {t} e : value_with_lets t
    := @dorewrite'
         (fun e'
          => match fuel with
             | Datatypes.O => nbe e'
             | Datatypes.S fuel' => @dorewrite'' fuel' Base e'
             end%under_lets)
         t e.
End with_var.

Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments dorewrite'' / .
Arguments default_fuel / .
Arguments do_rewrite_ident / .
Arguments rewrite_rules / .
(*Arguments domatch / .*)
Arguments eval_rewrite_rules / .
Arguments dtree / .
Arguments eval_decision_tree / .
Arguments eta_ident_cps / .
Arguments eta_all_option_pident_cps / .
Arguments pident_of_ident / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Arguments lift_with_bindings / .
Arguments app_binding_data / .
Arguments type_of_rawexpr / .
Arguments expr_of_rawexpr / .
Arguments reveal_rawexpr_cps / .
Arguments type.try_transport_cps _ !_ !_ _ {_}.
Arguments type.try_make_transport_cps _ !_ !_ {_}.
Arguments orb_pident / .
Arguments or_opt_pident / .
Arguments rValueOrExpr / .
Arguments value_of_rawexpr / .
Arguments cast / .
Arguments castv / .
Arguments ret / .
Arguments oret / .
Arguments default_fuel / .
Arguments cpsreturn / .
Arguments cpsbind / .
Arguments cpscall / .
Arguments invert_Literal / .
Arguments Base_value _ !t.
Arguments push_lets_value _ !_ !t.
Arguments splice_value'_with_lets _ !t.
Set Printing Depth 1000000.
Definition dorewrite''' {var}
  := Eval cbv (*-[value reify default_fuel reflect nbe type.try_transport_base_cps type.try_make_transport_base_cps type.try_make_transport_cps Nat.add List.map list_rect reify reflect reify_list reflect_list_cps List.app]*) (* but we also need to exclude things in the rhs of the rewrite rule *)
          [id cpscall cpsbind cpsreturn orb projT1 projT2 nth_error set_nth update_nth app_binding_data bind_data_cps binding_dataT cast castv dorewrite' dorewrite'' dorewrite1 do_rewrite_ident dtree eta_ident_cps eval_decision_tree eval_rewrite_rules expr_of_rawexpr lift_with_bindings orb_pident oret or_opt_pident pident_ident_beq pident_of_ident reveal_rawexpr_cps rewrite_rules rValueOrExpr swap_list type_of_rawexpr type.try_transport_cps value_of_rawexpr with_bindingsT value_with_lets value value_with_lets fst snd invert_Literal pident_beq]
    in @dorewrite'' var default_fuel.
Arguments dorewrite''' / .
Print dorewrite'''.
Definition dorewrite
  := Eval cbn [dorewrite''' type.try_transport_cps type.try_make_transport_cps Option.bind value value' Base_value push_lets_value reify reflect nbe splice_value'_with_lets UnderLets.splice UnderLets.splice_list UnderLets.to_expr cpscall cpsbind cpsreturn (*default_fuel*)] in @dorewrite'''.
Arguments dorewrite {var t} e.
Local Open Scope expr_scope.
Arguments expr : clear implicits.
Set Printing Width 137.
Print dorewrite.
(*dorewrite =
fun var : type -> Type =>
(fix dorewrite'' (fuel : nat) (t : type) (e : expr (value' false) t) {struct fuel} : value' true t :=
   (fix dorewrite' (t0 : type) (e0 : expr (value' false) t0) {struct e0} : value' true t0 :=
      match e0 in (expr _ t1) return (value' true t1) with
      | @Var _ t1 v => Base_value v
      | @Abs _ s d f => fun x : value' false s => dorewrite' d (f x)
      | #(idc) =>
          match idc in (ident t2) return (value' true t2) with
          | O => UnderLets.Base 0
          | S => fun x : expr var ?? => UnderLets.Base (x.+1)
          | NatRect =>
              fun (x : expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ?? -> expr var ?? -> UnderLets var (expr var ??))
                (x1 : expr var ??) =>
              UnderLets.Base
                (#(NatRect) @ (λ x2 : var ??%ctype,
                               UnderLets.to_expr (x ($x2))) @ (λ x2 x3 : var ??%ctype,
                                                               UnderLets.to_expr (x0 ($x2) ($x3))) @ x1)
          | NatEqb =>
              fun x x0 : expr var ?? =>
              match x with
              | ##(n) =>
                  match x0 with
                  | ##(n0) => UnderLets.Base (if n =? n0 then #(iTrue) else #(iFalse))
                  | _ => UnderLets.Base (#(NatEqb) @ x @ x0)
                  end
              | _ => UnderLets.Base (#(NatEqb) @ x @ x0)
              end
          | Add =>
              fun x x0 : expr var ?? =>
              match x with
              | @Abs _ _ _ _ =>
                  match x0 with
                  | 0 => UnderLets.Base x
                  | @App _ s0 _ #(S) x1 =>
                      type.try_make_transport_cps (value' false) s0 ??
                        (fun a : option (value' false s0 -> expr var ??) =>
                         match a with
                         | Some tr => UnderLets.Base ((x + tr (reflect x1)).+1)
                         | None => UnderLets.Base (x + x0)
                         end)
                  | @App _ s0 _ ($_) _ | @App _ s0 _ (@Abs _ _ _ _) _ | @App _ s0 _ 0 _ | @App _ s0 _ #(NatRect) _ | @App _ s0 _
                    #(NatEqb) _ | @App _ s0 _ #(Add) _ | @App _ s0 _ #(Pair) _ | @App _ s0 _ #(Fst) _ | @App _ s0 _ #
                    (Snd) _ | @App _ s0 _ #(MatchPair) _ | @App _ s0 _ [] _ | @App _ s0 _ #(Cons) _ | @App _ s0 _ #
                    (ListMap) _ | @App _ s0 _ #(ListApp) _ | @App _ s0 _ #(ListFlatMap) _ | @App _ s0 _ #(ListRect) _ | @App _ s0 _
                    #(ListFoldRight) _ | @App _ s0 _ #(ListPartition) _ | @App _ s0 _ ( ) _ | @App _ s0 _ #(iTrue) _ | @App _ s0 _
                    #(iFalse) _ | @App _ s0 _ #(BoolRect) _ | @App _ s0 _ ##(_) _ | @App _ s0 _ (_ @ _) _ | @App _ s0 _
                    (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                  | _ => UnderLets.Base (x + x0)
                  end
              | 0 => UnderLets.Base x0
              | ##(n) =>
                  match x0 with
                  | 0 => UnderLets.Base x
                  | ##(n0) => UnderLets.Base ##(n + n0)
                  | @App _ s _ #(S) x1 =>
                      type.try_make_transport_cps (value' false) s ??
                        (fun a : option (value' false s -> expr var ??) =>
                         match a with
                         | Some tr => UnderLets.Base (##(Datatypes.S n) + tr (reflect x1))
                         | None => UnderLets.Base (x + x0)
                         end)
                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(NatRect) _ | @App _ s _ #
                    (NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(Pair) _ | @App _ s _ #(Fst) _ | @App _ s _ #
                    (Snd) _ | @App _ s _ #(MatchPair) _ | @App _ s _ [] _ | @App _ s _ #(Cons) _ | @App _ s _ #
                    (ListMap) _ | @App _ s _ #(ListApp) _ | @App _ s _ #(ListFlatMap) _ | @App _ s _ #(ListRect) _ | @App _ s _
                    #(ListFoldRight) _ | @App _ s _ #(ListPartition) _ | @App _ s _ ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #
                    (iFalse) _ | @App _ s _ #(BoolRect) _ | @App _ s _ ##(_) _ | @App _ s _ (_ @ _) _ | @App _ s _
                    (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                  | _ => UnderLets.Base (x + x0)
                  end
              | @App _ s _ f x1 =>
                  match x0 with
                  | 0 => UnderLets.Base x
                  | ##(n) =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (value' false) s ??
                            (fun a : option (value' false s -> expr var ??) =>
                             match a with
                             | Some tr => UnderLets.Base (tr (reflect x1) + ##(Datatypes.S n))
                             | None => UnderLets.Base (x + x0)
                             end)
                      | _ => UnderLets.Base (x + x0)
                      end
                  | @App _ s0 _ #(S) x2 =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (value' false) s ??
                            (fun a : option (value' false s -> expr var ??) =>
                             match a with
                             | Some tr =>
                                 type.try_make_transport_cps (value' false) s0 ??
                                   (fun a0 : option (value' false s0 -> expr var ??) =>
                                    match a0 with
                                    | Some tr0 => UnderLets.Base (((tr (reflect x1) + tr0 (reflect x2)).+1).+1)
                                    | None => UnderLets.Base (x + x0)
                                    end)
                             | None => UnderLets.Base (x + x0)
                             end)
                      | _ =>
                          type.try_make_transport_cps (value' false) s0 ??
                            (fun a : option (value' false s0 -> expr var ??) =>
                             match a with
                             | Some tr => UnderLets.Base ((x + tr (reflect x2)).+1)
                             | None => UnderLets.Base (x + x0)
                             end)
                      end
                  | @App _ s0 _ ($_) _ | @App _ s0 _ (@Abs _ _ _ _) _ | @App _ s0 _ 0 _ | @App _ s0 _ #(NatRect) _ | @App _ s0 _
                    #(NatEqb) _ | @App _ s0 _ #(Add) _ | @App _ s0 _ #(Pair) _ | @App _ s0 _ #(Fst) _ | @App _ s0 _ #
                    (Snd) _ | @App _ s0 _ #(MatchPair) _ | @App _ s0 _ [] _ | @App _ s0 _ #(Cons) _ | @App _ s0 _ #
                    (ListMap) _ | @App _ s0 _ #(ListApp) _ | @App _ s0 _ #(ListFlatMap) _ | @App _ s0 _ #(ListRect) _ | @App _ s0 _
                    #(ListFoldRight) _ | @App _ s0 _ #(ListPartition) _ | @App _ s0 _ ( ) _ | @App _ s0 _ #(iTrue) _ | @App _ s0 _
                    #(iFalse) _ | @App _ s0 _ #(BoolRect) _ | @App _ s0 _ ##(_) _ | @App _ s0 _ (_ @ _) _ | @App _ s0 _
                    (@LetIn _ _ _ _ _) _ =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (value' false) s ??
                            (fun a : option (value' false s -> expr var ??) =>
                             match a with
                             | Some tr => UnderLets.Base ((tr (reflect x1) + x0).+1)
                             | None => UnderLets.Base (x + x0)
                             end)
                      | _ => UnderLets.Base (x + x0)
                      end
                  | _ =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (value' false) s ??
                            (fun a : option (value' false s -> expr var ??) =>
                             match a with
                             | Some tr => UnderLets.Base ((tr (reflect x1) + x0).+1)
                             | None => UnderLets.Base (x + x0)
                             end)
                      | _ => UnderLets.Base (x + x0)
                      end
                  end
              | @LetIn _ _ _ _ _ =>
                  match x0 with
                  | 0 => UnderLets.Base x
                  | @App _ s _ #(S) x2 =>
                      type.try_make_transport_cps (value' false) s ??
                        (fun a : option (value' false s -> expr var ??) =>
                         match a with
                         | Some tr => UnderLets.Base ((x + tr (reflect x2)).+1)
                         | None => UnderLets.Base (x + x0)
                         end)
                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(NatRect) _ | @App _ s _ #
                    (NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(Pair) _ | @App _ s _ #(Fst) _ | @App _ s _ #
                    (Snd) _ | @App _ s _ #(MatchPair) _ | @App _ s _ [] _ | @App _ s _ #(Cons) _ | @App _ s _ #
                    (ListMap) _ | @App _ s _ #(ListApp) _ | @App _ s _ #(ListFlatMap) _ | @App _ s _ #(ListRect) _ | @App _ s _
                    #(ListFoldRight) _ | @App _ s _ #(ListPartition) _ | @App _ s _ ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #
                    (iFalse) _ | @App _ s _ #(BoolRect) _ | @App _ s _ ##(_) _ | @App _ s _ (_ @ _) _ | @App _ s _
                    (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                  | _ => UnderLets.Base (x + x0)
                  end
              | _ =>
                  match x0 with
                  | 0 => UnderLets.Base x
                  | @App _ s _ #(S) x1 =>
                      type.try_make_transport_cps (value' false) s ??
                        (fun a : option (value' false s -> expr var ??) =>
                         match a with
                         | Some tr => UnderLets.Base ((x + tr (reflect x1)).+1)
                         | None => UnderLets.Base (x + x0)
                         end)
                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(NatRect) _ | @App _ s _ #
                    (NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(Pair) _ | @App _ s _ #(Fst) _ | @App _ s _ #
                    (Snd) _ | @App _ s _ #(MatchPair) _ | @App _ s _ [] _ | @App _ s _ #(Cons) _ | @App _ s _ #
                    (ListMap) _ | @App _ s _ #(ListApp) _ | @App _ s _ #(ListFlatMap) _ | @App _ s _ #(ListRect) _ | @App _ s _
                    #(ListFoldRight) _ | @App _ s _ #(ListPartition) _ | @App _ s _ ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #
                    (iFalse) _ | @App _ s _ #(BoolRect) _ | @App _ s _ ##(_) _ | @App _ s _ (_ @ _) _ | @App _ s _
                    (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                  | _ => UnderLets.Base (x + x0)
                  end
              end
          | Pair => fun x x0 : expr var ?? => UnderLets.Base (x, x0)
          | Fst =>
              fun x : expr var ?? =>
              match x with
              | @App _ s _ (@App _ s0 _ #(Pair) x1) _ =>
                  type.try_make_transport_cps (value' false) s0 ??
                    (fun a : option (value' false s0 -> expr var ??) =>
                     match a with
                     | Some tr =>
                         type.try_make_transport_cps (value' false) s ??
                           (fun a0 : option (value' false s -> expr var ??) =>
                            match a0 with
                            | Some _ => UnderLets.Base (tr (reflect x1))
                            | None => UnderLets.Base (#(Fst) @ x)
                            end)
                     | None => UnderLets.Base (#(Fst) @ x)
                     end)
              | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(NatRect) _) _ | @App _ s _
                (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(Fst) _) _ | @App _ s _
                (@App _ s0 _ #(Snd) _) _ | @App _ s _ (@App _ s0 _ #(MatchPair) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                (@App _ s0 _ #(Cons) _) _ | @App _ s _ (@App _ s0 _ #(ListMap) _) _ | @App _ s _ (@App _ s0 _ #(ListApp) _) _ | @App _ s
                _ (@App _ s0 _ #(ListFlatMap) _) _ | @App _ s _ (@App _ s0 _ #(ListRect) _) _ | @App _ s _
                (@App _ s0 _ #(ListFoldRight) _) _ | @App _ s _ (@App _ s0 _ #(ListPartition) _) _ | @App _ s _
                (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                (@App _ s0 _ #(BoolRect) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _
                (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ => UnderLets.Base (#(Fst) @ x)
              | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                  UnderLets.Base (#(Fst) @ x)
              | _ => UnderLets.Base (#(Fst) @ x)
              end
          | Snd =>
              fun x : expr var ?? =>
              match x with
              | @App _ s _ (@App _ s0 _ #(Pair) _) x0 =>
                  type.try_make_transport_cps (value' false) s0 ??
                    (fun a : option (value' false s0 -> expr var ??) =>
                     match a with
                     | Some _ =>
                         type.try_make_transport_cps (value' false) s ??
                           (fun a0 : option (value' false s -> expr var ??) =>
                            match a0 with
                            | Some tr0 => UnderLets.Base (tr0 (reflect x0))
                            | None => UnderLets.Base (#(Snd) @ x)
                            end)
                     | None => UnderLets.Base (#(Snd) @ x)
                     end)
              | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(NatRect) _) _ | @App _ s _
                (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(Fst) _) _ | @App _ s _
                (@App _ s0 _ #(Snd) _) _ | @App _ s _ (@App _ s0 _ #(MatchPair) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                (@App _ s0 _ #(Cons) _) _ | @App _ s _ (@App _ s0 _ #(ListMap) _) _ | @App _ s _ (@App _ s0 _ #(ListApp) _) _ | @App _ s
                _ (@App _ s0 _ #(ListFlatMap) _) _ | @App _ s _ (@App _ s0 _ #(ListRect) _) _ | @App _ s _
                (@App _ s0 _ #(ListFoldRight) _) _ | @App _ s _ (@App _ s0 _ #(ListPartition) _) _ | @App _ s _
                (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                (@App _ s0 _ #(BoolRect) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _
                (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ => UnderLets.Base (#(Snd) @ x)
              | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                  UnderLets.Base (#(Snd) @ x)
              | _ => UnderLets.Base (#(Snd) @ x)
              end
          | MatchPair =>
              fun (x : expr var ?? -> expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ??) =>
              match x0 with
              | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                  UnderLets.Base (#(MatchPair) @ (λ x2 x3 : var ??%ctype,
                                                  UnderLets.to_expr (x ($x2) ($x3))) @ x0)
              | @App _ s _ (@App _ s0 _ #(Pair) x2) x1 =>
                  type.try_make_transport_cps (value' false) s0 ??
                    (fun a : option (value' false s0 -> expr var ??) =>
                     match a with
                     | Some tr =>
                         type.try_make_transport_cps (value' false) s ??
                           (fun a0 : option (value' false s -> expr var ??) =>
                            match a0 with
                            | Some tr0 => (fv <-- x (tr (reflect x2)) (tr0 (reflect x1));
                                           UnderLets.Base fv)%under_lets
                            | None => UnderLets.Base (#(MatchPair) @ (λ x3 x4 : var ??%ctype,
                                                                      UnderLets.to_expr (x ($x3) ($x4))) @ x0)
                            end)
                     | None => UnderLets.Base (#(MatchPair) @ (λ x3 x4 : var ??%ctype,
                                                               UnderLets.to_expr (x ($x3) ($x4))) @ x0)
                     end)
              | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(NatRect) _) _ | @App _ s _
                (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(Fst) _) _ | @App _ s _
                (@App _ s0 _ #(Snd) _) _ | @App _ s _ (@App _ s0 _ #(MatchPair) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                (@App _ s0 _ #(Cons) _) _ | @App _ s _ (@App _ s0 _ #(ListMap) _) _ | @App _ s _ (@App _ s0 _ #(ListApp) _) _ | @App _ s
                _ (@App _ s0 _ #(ListFlatMap) _) _ | @App _ s _ (@App _ s0 _ #(ListRect) _) _ | @App _ s _
                (@App _ s0 _ #(ListFoldRight) _) _ | @App _ s _ (@App _ s0 _ #(ListPartition) _) _ | @App _ s _
                (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                (@App _ s0 _ #(BoolRect) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                  UnderLets.Base (#(MatchPair) @ (λ x3 x4 : var ??%ctype,
                                                  UnderLets.to_expr (x ($x3) ($x4))) @ x0)
              | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                  UnderLets.Base (#(MatchPair) @ (λ x4 x5 : var ??%ctype,
                                                  UnderLets.to_expr (x ($x4) ($x5))) @ x0)
              | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                  UnderLets.Base (#(MatchPair) @ (λ x3 x4 : var ??%ctype,
                                                  UnderLets.to_expr (x ($x3) ($x4))) @ x0)
              | @LetIn _ _ _ _ _ => UnderLets.Base (#(MatchPair) @ (λ x2 x3 : var ??%ctype,
                                                                    UnderLets.to_expr (x ($x2) ($x3))) @ x0)
              | _ => UnderLets.Base (#(MatchPair) @ (λ x1 x2 : var ??%ctype,
                                                     UnderLets.to_expr (x ($x1) ($x2))) @ x0)
              end
          | Nil => UnderLets.Base []
          | Cons => fun x x0 : expr var ?? => UnderLets.Base (x :: x0)
          | ListMap =>
              fun (x : expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ??) =>
              reflect_list_cps x0 (UnderLets var (expr var ??))
                (fun a : option (list (expr var ??)) =>
                 match a with
                 | Some xs => (fv <-- (fxs <--- map x xs;
                                       UnderLets.Base (reify_list fxs));
                               UnderLets.Base fv)%under_lets
                 | None =>
                     match x0 with
                     | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                         UnderLets.Base (#(ListMap) @ (λ x2 : var ??%ctype,
                                                       UnderLets.to_expr (x ($x2))) @ x0)
                     | @App _ s _ (@App _ s0 _ #(Cons) x2) x1 =>
                         type.try_make_transport_cps (value' false) s0 ??
                           (fun a0 : option (value' false s0 -> expr var ??) =>
                            match a0 with
                            | Some tr =>
                                type.try_make_transport_cps (value' false) s ??
                                  (fun a1 : option (value' false s -> expr var ??) =>
                                   match a1 with
                                   | Some tr0 =>
                                       (fv <-- (fx <-- x (tr (reflect x2));
                                                UnderLets.Base
                                                  (fx :: #(ListMap) @ (λ v : var ??%ctype,
                                                                       UnderLets.to_expr (x ($v))) @ tr0 (reflect x1)));
                                        UnderLets.Base fv)%under_lets
                                   | None => UnderLets.Base (#(ListMap) @ (λ x3 : var ??%ctype,
                                                                           UnderLets.to_expr (x ($x3))) @ x0)
                                   end)
                            | None => UnderLets.Base (#(ListMap) @ (λ x3 : var ??%ctype,
                                                                    UnderLets.to_expr (x ($x3))) @ x0)
                            end)
                     | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                       (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(NatRect) _) _ | @App _ s _
                       (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(Pair) _) _ | @App _
                       s _ (@App _ s0 _ #(Fst) _) _ | @App _ s _ (@App _ s0 _ #(Snd) _) _ | @App _ s _ (@App _ s0 _ #(MatchPair) _) _ |
                       @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(ListMap) _) _ | @App _ s _
                       (@App _ s0 _ #(ListApp) _) _ | @App _ s _ (@App _ s0 _ #(ListFlatMap) _) _ | @App _ s _
                       (@App _ s0 _ #(ListRect) _) _ | @App _ s _ (@App _ s0 _ #(ListFoldRight) _) _ | @App _ s _
                       (@App _ s0 _ #(ListPartition) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ |
                       @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _ (@App _ s0 _ #(BoolRect) _) _ | @App _ s _
                       (@App _ s0 _ ##(_) _) _ => UnderLets.Base (#(ListMap) @ (λ x3 : var ??%ctype,
                                                                                UnderLets.to_expr (x ($x3))) @ x0)
                     | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                         UnderLets.Base (#(ListMap) @ (λ x4 : var ??%ctype,
                                                       UnderLets.to_expr (x ($x4))) @ x0)
                     | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                         UnderLets.Base (#(ListMap) @ (λ x3 : var ??%ctype,
                                                       UnderLets.to_expr (x ($x3))) @ x0)
                     | @LetIn _ _ _ _ _ => UnderLets.Base (#(ListMap) @ (λ x2 : var ??%ctype,
                                                                         UnderLets.to_expr (x ($x2))) @ x0)
                     | _ => UnderLets.Base (#(ListMap) @ (λ x1 : var ??%ctype,
                                                          UnderLets.to_expr (x ($x1))) @ x0)
                     end
                 end)
          | ListApp =>
              fun x x0 : expr var ?? =>
              reflect_list_cps x (UnderLets var (expr var ??))
                (fun a : option (list (expr var ??)) =>
                 match a with
                 | Some xs =>
                     reflect_list_cps x0 (UnderLets var (expr var ??))
                       (fun a0 : option (list (expr var ??)) =>
                        match a0 with
                        | Some ys => UnderLets.Base (reify_list (xs ++ ys))
                        | None => UnderLets.Base (x ++ x0)
                        end)
                 | None => UnderLets.Base (x ++ x0)
                 end)
          | ListFlatMap =>
              fun (x : expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ??) =>
              reflect_list_cps x0 (UnderLets var (expr var ??))
                (fun a : option (list (expr var ??)) =>
                 match a with
                 | Some xs =>
                     (fv <-- (fxs <--- map x xs;
                              UnderLets.Base
                                (#(ListFoldRight) @ (λ ls1 ls2 : expr var ??,
                                                     $ls1 ++ $ls2) @ (λ _ : expr var ??,
                                                                      []) @ $(reify_list fxs)));
                      fv0 <-- match fuel with
                              | 0 => nbe fv
                              | Datatypes.S fuel' => dorewrite'' fuel' ??%ctype fv
                              end;
                      UnderLets.Base fv0)%under_lets
                 | None => UnderLets.Base (#(ListFlatMap) @ (λ x1 : var ??%ctype,
                                                             UnderLets.to_expr (x ($x1))) @ x0)
                 end)
          | ListRect =>
              fun (x : expr var ?? -> UnderLets var (expr var ??))
                (x0 : expr var ?? -> expr var ?? -> expr var ?? -> UnderLets var (expr var ??)) (x1 : expr var ??) =>
              reflect_list_cps x1 (UnderLets var (expr var ??))
                (fun a : option (list (expr var ??)) =>
                 match a with
                 | Some xs =>
                     (fv <-- list_rect (fun _ : list (expr var ??) => UnderLets var (expr var ??)) (x ( ))
                               (fun (x' : expr var ??) (xs' : list (expr var ??)) (rec : UnderLets var (expr var ??)) =>
                                rec0 <-- rec;
                                x0 x' (reify_list xs') rec0) xs;
                      UnderLets.Base fv)%under_lets
                 | None =>
                     UnderLets.Base
                       (#(ListRect) @ (λ x2 : var ??%ctype,
                                       UnderLets.to_expr (x ($x2))) @
                        (λ x2 x3 x4 : var ??%ctype,
                         UnderLets.to_expr (x0 ($x2) ($x3) ($x4))) @ x1)
                 end)
          | ListFoldRight =>
              fun (x : expr var ?? -> expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ?? -> UnderLets var (expr var ??))
                (x1 : expr var ??) =>
              UnderLets.Base
                (#(ListFoldRight) @ (λ x2 x3 : var ??%ctype,
                                     UnderLets.to_expr (x ($x2) ($x3))) @ (λ x2 : var ??%ctype,
                                                                           UnderLets.to_expr (x0 ($x2))) @ x1)
          | ListPartition =>
              fun (x : expr var ?? -> UnderLets var (expr var ??)) (x0 : expr var ??) =>
              reflect_list_cps x0 (UnderLets var (expr var ??))
                (fun a : option (list (expr var ??)) =>
                 match a with
                 | Some xs =>
                     (fv <-- list_rect (fun _ : list (expr var ??) => UnderLets var (expr (value' false) ??))
                               (UnderLets.Base ([], []))
                               (fun (x1 : expr var ??) (_ : list (expr var ??)) (partition_tl : UnderLets var (expr (value' false) ??))
                                =>
                                partition_tl0 <-- partition_tl;
                                fx <-- x x1;
                                UnderLets.Base
                                  (#(MatchPair) @
                                   (λ g d : expr var ??,
                                    #(BoolRect) @ (λ _ : expr var ??,
                                                   ($x1 :: $g, $d)) @ (λ _ : expr var ??,
                                                                       ($g, $x1 :: $d)) @ $fx) @ partition_tl0)) xs;
                      fv0 <-- match fuel with
                              | 0 => nbe fv
                              | Datatypes.S fuel' => dorewrite'' fuel' ??%ctype fv
                              end;
                      UnderLets.Base fv0)%under_lets
                 | None => UnderLets.Base (#(ListPartition) @ (λ x1 : var ??%ctype,
                                                               UnderLets.to_expr (x ($x1))) @ x0)
                 end)
          | TT => UnderLets.Base ( )
          | iTrue => UnderLets.Base #(iTrue)
          | iFalse => UnderLets.Base #(iFalse)
          | BoolRect =>
              fun (x x0 : expr var ?? -> UnderLets var (expr var ??)) (x1 : expr var ??) =>
              match x1 with
              | #(iTrue) => (fv <-- x ( );
                             UnderLets.Base fv)%under_lets
              | #(iFalse) => (fv <-- x0 ( );
                              UnderLets.Base fv)%under_lets
              | _ @ _ | @LetIn _ _ _ _ _ =>
                  UnderLets.Base
                    (#(BoolRect) @ (λ x3 : var ??%ctype,
                                    UnderLets.to_expr (x ($x3))) @ (λ x3 : var ??%ctype,
                                                                    UnderLets.to_expr (x0 ($x3))) @ x1)
              | _ =>
                  UnderLets.Base
                    (#(BoolRect) @ (λ x2 : var ??%ctype,
                                    UnderLets.to_expr (x ($x2))) @ (λ x2 : var ??%ctype,
                                                                    UnderLets.to_expr (x0 ($x2))) @ x1)
              end
          | Literal n => UnderLets.Base ##(n)
          end
      | @App _ s d f x => splice_value'_with_lets (dorewrite' s x) (fun x0 : value' false s => dorewrite' (s -> d)%ctype f x0)
      | @LetIn _ A B x f =>
          splice_value'_with_lets (dorewrite' A x)
            (fun x0 : value' false A =>
             push_lets_value (UnderLet (reify x0) (fun xv : var A => UnderLets.Base (dorewrite' B (f (reflect ($xv)))))))
      end) t e) default_fuel
     : forall (var : type -> Type) (t : type), expr (value' false) t -> value' true t

Arguments var, t are implicit and maximally inserted
Argument scopes are [function_scope ctype_scope expr_scope]
*)
Timeout 10 Time Eval compute in dorewrite (#ListPartition @ (λ x, #NatEqb @ $x @ ##1) @ [##0; ##1; ##1; ##2])%expr.
