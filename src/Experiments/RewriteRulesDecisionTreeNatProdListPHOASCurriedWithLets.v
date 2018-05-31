Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.CPSNotations.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive base_type := Unit | Bool | Nat | Prod (A B : base_type) | List (A : base_type).
Inductive type := Base (t : base_type) | Arrow (s : type) (d : type).
Coercion Base : base_type >-> type.
Bind Scope ctype_scope with type.
Bind Scope ctype_scope with base_type.
Delimit Scope ctype_scope with ctype.
Infix "->" := Arrow : ctype_scope.
Infix "*" := Prod : ctype_scope.
Notation "( )" := Unit : ctype_scope.

Inductive ident : type -> Type :=
| O : ident Nat
| S : ident (Nat -> Nat)
| NatRect {P : base_type} : ident ((Unit -> P) -> (Nat -> P -> P) -> Nat -> P)
| NatEqb : ident (Nat -> Nat -> Bool)
| Add : ident (Nat -> Nat -> Nat)
| Pair {A B : base_type} : ident (A -> B -> A * B)
| Fst {A B} : ident (A * B -> A)
| Snd {A B} : ident (A * B -> B)
| MatchPair {A B P : base_type} : ident ((A -> B -> P) -> A * B -> P)
| Nil {A} : ident (List A)
| Cons {A : base_type} : ident (A -> List A -> List A)
| ListMap {A B : base_type} : ident ((A -> B) -> List A -> List B)
| ListApp {A} : ident (List A -> List A -> List A)
| ListFlatMap {A B : base_type} : ident ((A -> List B) -> List A -> List B)
| ListRect {A : base_type} {P : base_type} : ident ((Unit -> P) -> (A -> List A -> P -> P) -> List A -> P)
| ListFoldRight {A : base_type} {B : base_type} : ident ((B -> A -> A) -> (Unit -> A) -> List B -> A)
| ListPartition {A : base_type} : ident ((A -> Bool) -> List A -> List A * List A)
| TT : ident Unit
| iTrue : ident Bool
| iFalse : ident Bool
| BoolRect {P : base_type} : ident ((Unit -> P) -> (Unit -> P) -> Bool -> P)
| Literal (n : nat) : ident Nat.

Show Match ident.
(*
<<<
#!/usr/bin/env python2

show_match_ident = r"""match # with
 | O =>
 | S =>
 | NatRect P =>
 | NatEqb =>
 | Add =>
 | Pair A B =>
 | Fst A B =>
 | Snd A B =>
 | MatchPair A B P =>
 | Nil A =>
 | Cons A =>
 | ListMap A B =>
 | ListApp A =>
 | ListFlatMap A B =>
 | ListRect A P =>
 | ListFoldRight A B =>
 | ListPartition A =>
 | TT =>
 | iTrue =>
 | iFalse =>
 | BoolRect P =>
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
     | pNatRect, NatRect _
     | pNatEqb, NatEqb
     | pAdd, Add
     | pPair, Pair _ _
     | pFst, Fst _ _
     | pSnd, Snd _ _
     | pMatchPair, MatchPair _ _ _
     | pNil, Nil _
     | pCons, Cons _
     | pListMap, ListMap _ _
     | pListApp, ListApp _
     | pListFlatMap, ListFlatMap _ _
     | pListRect, ListRect _ _
     | pListFoldRight, ListFoldRight _ _
     | pListPartition, ListPartition _
     | pTT, TT
     | piTrue, iTrue
     | piFalse, iFalse
     | pBoolRect, BoolRect _
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
     | NatRect P => f _ (@NatRect P)
     | NatEqb => f _ NatEqb
     | Add => f _ Add
     | Pair A B => f _ (@Pair A B)
     | Fst A B => f _ (@Fst A B)
     | Snd A B => f _ (@Snd A B)
     | MatchPair A B P => f _ (@MatchPair A B P)
     | Nil A => f _ (@Nil A)
     | Cons A => f _ (@Cons A)
     | ListMap A B => f _ (@ListMap A B)
     | ListApp A => f _ (@ListApp A)
     | ListFlatMap A B => f _ (@ListFlatMap A B)
     | ListRect A P => f _ (@ListRect A P)
     | ListFoldRight A B => f _ (@ListFoldRight A B)
     | ListPartition A => f _ (@ListPartition A)
     | TT => f _ TT
     | iTrue => f _ iTrue
     | iFalse => f _ iFalse
     | BoolRect P => f _ (@BoolRect P)
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
     | NatRect P => pNatRect
     | NatEqb => pNatEqb
     | Add => pAdd
     | Pair A B => pPair
     | Fst A B => pFst
     | Snd A B => pSnd
     | MatchPair A B P => pMatchPair
     | Nil A => pNil
     | Cons A => pCons
     | ListMap A B => pListMap
     | ListApp A => pListApp
     | ListFlatMap A B => pListFlatMap
     | ListRect A P => pListRect
     | ListFoldRight A B => pListFoldRight
     | ListPartition A => pListPartition
     | TT => pTT
     | iTrue => piTrue
     | iFalse => piFalse
     | BoolRect P => pBoolRect
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

Inductive pbase_type := pbAny | pNat | pUnit | pBool | pProd (A B : pbase_type) | pList (A : pbase_type).
Coercion Some_t (t : type) : option type := Some t.
(* N.B. In [pArrow], [None] on the source means "any" *)
Inductive ptype := pAny | pBase (t : pbase_type) | pArrow (s : option type) (d : ptype).
Coercion pBase : pbase_type >-> ptype.
Bind Scope ptype_scope with ptype.
Bind Scope pbtype_scope with pbase_type.
Bind Scope ctype_scope with option type.
Delimit Scope ptype_scope with ptype.
Delimit Scope pbtype_scope with pbtype.
Infix "->" := pArrow : ptype_scope.
Infix "*" := pProd : pbtype_scope.
Infix "*" := pProd : ptype_scope.
Notation "( )" := pUnit : pbtype_scope.
Notation "( )" := pUnit : ptype_scope.
Notation "'??'" := pbAny : pbtype_scope.
Notation "'??'" := pAny : ptype_scope.
Local Set Warnings Append "-notation-overridden".
Notation "'??'" := (@None type) : ctype_scope.
Notation "'??'" := (@None base_type) : ctype_scope.
Notation "'??'" := None (only parsing) : ctype_scope.

Inductive pattern : Type :=
| Wildcard (t : ptype)
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
Notation "??" := (Wildcard (pBase pbAny)) : pattern_scope.
Notation "??ℕ" := (Wildcard (pBase pNat)) : pattern_scope.
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
(** TODO: Would it work to operate on syntax trees which are only
    typed by their arrow structure, and nothing else?  Would it help? *)
Module type.
  Fixpoint try_make_transport_base_cps (P : base_type -> Type) (t1 t2 : base_type) : ~> option (P t1 -> P t2)
    := match t1, t2 with
       | Nat, Nat
       | Unit, Unit
       | Bool, Bool
         => (return (Some (fun v => v)))
       | List A, List A'
         => try_make_transport_base_cps
             (fun A => P (List A)) _ _
       | Prod s d, Prod s' d'
         => (trs <-- try_make_transport_base_cps (fun s => P (Prod s _)) _ _;
              trd <-- try_make_transport_base_cps (fun d => P (Prod _ d)) _ _;
            return (Some (fun v => trd (trs v))))
       | Nat, _
       | Unit, _
       | Bool, _
       | List _, _
       | Prod _ _, _
         => (return None)
       end%option%cps.

  Fixpoint try_make_transport_cps (P : type -> Type) (t1 t2 : type) : ~> option (P t1 -> P t2)
    := match t1, t2 with
       | Base t1, Base t2
         => @try_make_transport_base_cps P t1 t2
       | Arrow s d, Arrow s' d'
         => (trs <-- try_make_transport_cps (fun s => P (Arrow s _)) _ _;
              trd <-- try_make_transport_cps (fun d => P (Arrow _ d)) _ _;
            return (Some (fun v => trd (trs v))))
       | Base _, _
       | Arrow _ _, _
         => (return None)
       end%option%cps.

  Definition try_transport_base_cps (P : base_type -> Type) (t1 t2 : base_type) (v : P t1) : ~> option (P t2)
    := (tr <-- try_make_transport_base_cps P t1 t2;
        return (Some (tr v)))%cps.

  Definition try_transport_cps (P : type -> Type) (t1 t2 : type) (v : P t1) : ~> option (P t2)
    := (tr <-- try_make_transport_cps P t1 t2;
        return (Some (tr v)))%cps.

  Definition try_transport (P : type -> Type) (t1 t2 : type) (v : P t1) : option (P t2)
    := try_transport_cps P t1 t2 v _ id.
End type.

Record > anyexpr {var : type -> Type}
  := wrap { anyexpr_ty : type ; unwrap :> @expr var anyexpr_ty }.
Arguments wrap {_ _} _.

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
  Local Notation topanyexpr := anyexpr.
  Local Notation expr := (@expr var).
  Local Notation anyexpr := (@anyexpr var).
  Local Notation UnderLets := (@UnderLets var).

  Fixpoint value (t : type)
    := match t with
       | Base _ as t
         => expr t
       | Arrow s d => value s -> UnderLets (value d)
       end.

  Definition value_with_lets (t : type)
    := UnderLets (value t).

  Fixpoint value'' (with_lets : bool) (t : type)
    := match t with
       | Base _ as t
         => if with_lets then UnderLets (expr t) else expr t
       | Arrow s d
         => value'' false s -> value'' true d
       end.
  Definition value' := value'' false.
  Definition value'_with_lets := value'' true.
  Definition splice_value'_with_lets {T with_lets0 with_lets1 t} : value'' with_lets0 t -> (value'' with_lets1 t -> UnderLets T) -> UnderLets T
    := match t, with_lets0, with_lets1 return value'' with_lets0 t -> (value'' with_lets1 t -> UnderLets T) -> UnderLets T with
       | _, true, true
       | _, false, false
         => fun e k => k e
       | Base t, true, false => fun e k => e <-- e; k e
       | Base t, false, true => fun e k => k (UnderLets.Base e)
       | Arrow s d,_ , _ => fun f k => k f
       end%under_lets.
  Local Notation "e <---- e' ; f" := (splice_value'_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
  Fixpoint push_lets_value' {t} : UnderLets (value' t) -> value'_with_lets t
    := match t return UnderLets (value' t) -> value'_with_lets t with
       | Base t => fun e => e
       | Arrow s d
         => fun f x => @push_lets_value' d (f <-- f; fx <---- f x; UnderLets.Base fx)
       end%under_lets.

  Fixpoint push_pull_value_lets {t}
    : (value' t -> value t) * (value t -> value' t)
    := match t return (value' t -> value t) * (value t -> value' t) with
       | Base t => (id, id)
       | Arrow s d
         => ((fun f x => fx <---- f (snd (@push_pull_value_lets s) x);
                       UnderLets.Base (fst (@push_pull_value_lets d) fx)),
            (fun f x => push_lets_value'
                       (fx <-- f (fst (@push_pull_value_lets s) x);
                          UnderLets.Base (snd (@push_pull_value_lets d) fx))))
       end%under_lets.
  Definition push_value_lets {t} : value t -> value' t := snd push_pull_value_lets.
  Definition pull_value_lets {t} : value' t -> value t := fst push_pull_value_lets.

  Fixpoint reify {t} : value t -> expr t
    := match t return value t -> expr t with
       | Base t => fun v => v
       | Arrow s d
         => fun f => λ x , UnderLets.to_expr
                         (fx <-- f (@reflect s ($x));
                            UnderLets.Base (@reify d fx))
       end%expr
  with reflect {t} : expr t -> value t
       := match t return expr t -> value t with
          | Base t => fun v => v
          | Arrow s d
            => fun f x => UnderLets.Base (@reflect d (f @ (@reify s x)))
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
       | Base t => @rExpr t
       | Arrow _ _ => @rValue _
       end.

  Definition try_rExpr_cps {T t} (k : option rawexpr -> T) : expr t -> T
    := match t with
       | Base t => fun e => k (Some (rExpr e))
       | Arrow _ _ => fun _ => k None
       end.

  Definition reveal_rawexpr_cps {T}
             (k : rawexpr -> T)
             (e : rawexpr)
    : T
    := match e with
       | rExpr _ e as r
       | rValue (Base _) e as r
         => match e with
            | Ident t idc => k (rIdent idc e)
            | App s d f x => k (rApp (rExpr f) (rExpr x) e)
            | _ => k r
            end
       | e' => k e'
       end.

  Fixpoint pbase_interp (t : pbase_type) : Type
    := match t return Type with
       | pbAny => anyexpr
       | pNat => nat
       | pUnit => unit
       | pBool => bool
       | pProd A B => pbase_interp A * pbase_interp B
       | pList A => list (pbase_interp A)
       end.

  Inductive quant_type := qforall | qexists.

  Fixpoint pbase_type_interp_cps (quant : quant_type) (t : pbase_type) (K : base_type -> Type) : Type
    := match t with
       | pbAny
         => match quant with
            | qforall => forall t : base_type, K t
            | qexists => { t : base_type & K t }
            end
       | pNat => K Nat
       | pUnit => K Unit
       | pBool => K Bool
       | pProd A B
         => @pbase_type_interp_cps
              quant A
              (fun A'
               => @pbase_type_interp_cps
                    quant B (fun B' => K (Prod A' B')))
       | pList A
         => @pbase_type_interp_cps
              quant A (fun A' => K (List A'))
       end.

  Fixpoint ptype_interp_cps (quant : quant_type) (t : ptype) (kt : type -> type) (K : type -> Type) : Type
    := match t with
       | pBase t
         => pbase_type_interp_cps quant t (fun t => K (kt (Base t)))
       | pAny
         => match quant with
            | qforall => forall t : type, K (kt t)
            | qexists => { t : type & K (kt t) }
            end
       | pArrow None d
         => match quant with
            | qforall => forall t : base_type, @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K
            | qexists => { t : base_type & @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K }
            end
       | pArrow (Some t) d => @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K
       end.

  Definition ptype_interp (quant : quant_type) (t : ptype) (K : Type -> Type) : Type
    := ptype_interp_cps quant t id (fun t => K (value t)).

  Fixpoint binding_dataT (p : pattern) : Type
    := match p return Type with
       | Wildcard t => ptype_interp qexists t id
       | pIdent idc => if pident_beq pLiteral idc then nat else unit
       | pApp f x => binding_dataT f * binding_dataT x
       end%type.

  Fixpoint bind_base_cps {t1 t2}
           (K : base_type -> Type)
           (v : K t2)
           {struct t1}
    : ~> option (pbase_type_interp_cps qexists t1 K)
    := match t1 return ~> option (pbase_type_interp_cps qexists t1 K) with
       | pbAny => (return (Some (existT K t2 v)))
       | pNat
         => (v <-- type.try_transport_base_cps _ _ Nat v;
             return (Some v))
       | pUnit
         => (v <-- type.try_transport_base_cps _ _ Unit v;
             return (Some v))
       | pBool
         => (v <-- type.try_transport_base_cps _ _ Bool v;
             return (Some v))
       | pProd A B
         => fun T k
            => match t2 return K t2 -> T with
               | Prod A' B'
                 => fun v
                    => @bind_base_cps
                         B B' (fun B' => K (A' * B')%ctype) v T
                         (fun v'
                          => match v' with
                             | Some v''
                               => @bind_base_cps
                                    A A' (fun A' => pbase_type_interp_cps qexists B (fun B' => K (A' * B')%ctype)) v'' T
                                    k
                             | None => k None
                             end)
               | _ => fun _ => k None
               end v
       | pList A
         => fun T k
            => match t2 return K t2 -> T with
               | List A'
                 => fun v => @bind_base_cps A A' (fun A'' => K (List A'')) v T k
               | _ => fun _ => k None
               end v
       end%cps.

  Fixpoint bind_value_cps {T t1 t2}
           (kt : type -> type)
           (K := fun t => value (kt t))
           (k : option (ptype_interp_cps qexists t1 kt value) -> T)
           (v : K t2)
           {struct t1}
    : T
    := match t1 return (option (ptype_interp_cps qexists t1 kt value) -> T) -> T with
       | pBase t1
         => fun k
            => match t2 return K t2 -> T with
               | Base t2 => fun e => bind_base_cps K e T k
               | Arrow _ _ => fun _ => k None
               end v
       | pAny => fun k => k (Some (existT _ t2 v))
       | pArrow None d
         => fun k
            => match t2 return K t2 -> T with
               | Base _ => fun _ => k None
               | Arrow (Base s) d'
                 => fun v
                    => @bind_value_cps
                         T d d' (fun d => kt (s -> d)%ctype)
                         (fun v'
                          => match v' with
                             | Some v'' => k (Some (existT _ s v''))
                             | None => k None
                             end)
                         v
               | Arrow _ _ => fun _ => k None
               end v
       | pArrow (Some s) d
         => fun k
            => match t2 return K t2 -> T with
               | Base _ => fun _ => k None
               | Arrow s' d'
                 => fun v
                    => type.try_transport_cps
                         (fun s => K (s -> _)%ctype) s' s v _
                         (fun v'
                          => match v' with
                             | Some v''
                               => @bind_value_cps
                                    T d d' (fun d => kt (s -> d)%ctype)
                                    k
                                    v''
                             | None => k None
                             end)
               end v
       end k.

  Fixpoint bind_data_cps (e : rawexpr) (p : pattern)
    : ~> option (binding_dataT p)
    := match p, e return ~> option (binding_dataT p) with
       | Wildcard t, _
         => fun T k => bind_value_cps id k (value_of_rawexpr e)
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
                   ctx0
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
    := (fun should_do_again : bool => UnderLets (@topanyexpr (if should_do_again then ivar else var))).
  Local Notation opt_anyexpr ivar
    := (option (sigT (opt_anyexprP ivar))).

  Local Notation rewrite_rulesT' ivar
    := (list { p : pattern & binding_dataT p -> forall T, (opt_anyexpr ivar  -> T) -> T })
         (only parsing).

  Definition eval_rewrite_rules
             {ivar}
             (do_again : forall t, @topexpr ivar t -> UnderLets (expr t))
             (maybe_do_again
              := fun (should_do_again : bool) t
                 => if should_do_again return ((@topexpr (if should_do_again then ivar else var) t) -> UnderLets (expr t))
                    then do_again t
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
                                               type.try_transport_cps
                                                 _ _ _ (unwrap fv) _
                                                 (fun fv'
                                                  => match fv', default_on_rewrite_failure with
                                                    | Some fv'', _
                                                      => maybe_do_again should_do_again _ fv''
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
         => Some (n, Wildcard pAny :: Wildcard pAny :: ps)
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
       | Wildcard t => ptype_interp qforall t (fun eT => eT -> T)
       | pIdent pLiteral => nat -> T
       | pApp f x => with_bindingsT f (with_bindingsT x T)
       | pIdent _ => T
       end.

  Fixpoint lift_pbase_type_interp_cps {K1 K2} {quant} (F : forall t : base_type, K1 t -> K2 t) {t}
    : pbase_type_interp_cps quant t K1
      -> pbase_type_interp_cps quant t K2
    := match t, quant return pbase_type_interp_cps quant t K1
                             -> pbase_type_interp_cps quant t K2 with
       | pbAny, qforall => fun f t => F t (f t)
       | pbAny, qexists => fun tf => existT _ _ (F _ (projT2 tf))
       | pNat, _
       | pUnit, _
       | pBool, _
         => F _
       | pProd A B, _
         => @lift_pbase_type_interp_cps
              _ _ quant
              (fun A'
               => @lift_pbase_type_interp_cps
                    _ _ quant (fun _ => F _) B)
              A
       | pList A, _
         => @lift_pbase_type_interp_cps
              _ _ quant (fun _ => F _) A
       end.

  Fixpoint lift_ptype_interp_cps {A B : Type} {quant kt} (F : A -> B) {t}
    : ptype_interp_cps quant t kt (fun eT => value eT -> A)
      -> ptype_interp_cps quant t kt (fun eT => value eT -> B)
    := match t, quant return ptype_interp_cps quant t kt (fun eT => value eT -> A)
                             -> ptype_interp_cps quant t kt (fun eT => value eT -> B) with
       | pAny, qforall => fun f t x => F (f t x)
       | pAny, qexists => fun tf => existT (fun t => value (kt t) -> B)
                                           _
                                           (fun x => F (projT2 tf x))
       | pBase t, _
         => lift_pbase_type_interp_cps
              (K1:=fun eT => _ -> A)
              (K2:=fun eT => _ -> B)
              (fun _ f x => F (f x))
       | pArrow None d, qforall
         => fun f t
            => @lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d (f t)
       | pArrow None d, qexists
         => fun tf
            => existT _
                      (projT1 tf)
                      (@lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d (projT2 tf))
       | pArrow (Some s) d, _
         => @lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d
       end.

  Fixpoint lift_with_bindings {p} {A B : Type} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
    := match p return with_bindingsT p A -> with_bindingsT p B with
       | Wildcard t => lift_ptype_interp_cps F
       | pIdent pLiteral => fun f e => F (f e)
       | pApp f x
         => @lift_with_bindings
              f _ _
              (@lift_with_bindings x _ _ F)
       | pIdent _
         => F
       end.

  Fixpoint app_pbase_type_interp_cps {T : Type} {K1 K2 : base_type -> Type}
           (F : forall t, K1 t -> K2 t -> T)
           {t}
    : pbase_type_interp_cps qforall t K1
      -> pbase_type_interp_cps qexists t K2 -> T
    := match t return pbase_type_interp_cps qforall t K1
                      -> pbase_type_interp_cps qexists t K2 -> T with
       | pbAny => fun f tv => F _ (f _) (projT2 tv)
       | pNat
       | pUnit
       | pBool
         => fun f v => F _ f v
       | pProd A B
         => @app_pbase_type_interp_cps
              _
              (fun A' => pbase_type_interp_cps qforall B (fun B' => K1 (A' * B')%ctype))
              (fun A' => pbase_type_interp_cps qexists B (fun B' => K2 (A' * B')%ctype))
              (fun A'
               => @app_pbase_type_interp_cps
                    _
                    (fun B' => K1 (A' * B')%ctype)
                    (fun B' => K2 (A' * B')%ctype)
                    (fun _ => F _)
                    B)
              A
       | pList A
         => @app_pbase_type_interp_cps T (fun A' => K1 (List A')) (fun A' => K2 (List A')) (fun _ => F _) A
       end.

  Fixpoint app_ptype_interp_cps {T : Type} {kt : type -> type} {K : type -> Type}
           {t}
    : ptype_interp_cps qforall t kt (fun eT => K eT -> T)
      -> ptype_interp_cps qexists t kt K -> T
    := match t return ptype_interp_cps qforall t kt (fun eT => K eT -> T)
                      -> ptype_interp_cps qexists t kt K -> T with
       | pAny => fun f tv => f _ (projT2 tv)
       | pBase t
         => app_pbase_type_interp_cps
              (K1:=fun t => K (kt t) -> T)
              (K2:=fun t => K (kt t))
              (fun _ f v => f v)
       | pArrow (Some s) d
         => @app_ptype_interp_cps T (fun d => kt (_ -> d)%ctype) K d
       | pArrow None d
         => fun f tv
            => @app_ptype_interp_cps T (fun d => kt (_ -> d)%ctype) K d (f _) (projT2 tv)
       end.

  Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
    := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
       | pIdent pLiteral
         => fun f => f
       | Wildcard t
         => app_ptype_interp_cps
       | pApp f x
         => fun F '(vf, vx)
            => @app_binding_data _ x (@app_binding_data _ f F vf) vx
       | pIdent _
         => fun f 'tt => f
       end.

  Definition reify_list {t : base_type} (ls : list (expr t)) : expr (List t)
    := fold_right
         (fun x xs => x :: xs)%expr
         []%expr
         ls.

  Fixpoint reflect_list_cps {t} (e : expr t)
    : ~> option (list (expr match t return base_type with
                            | Base (List t) => t
                            | _ => Nat
                            end))
    := match e in topexpr t
             return ~> option (list (expr match t return base_type with
                                          | Base (List t) => t
                                          | _ => Nat
                                          end))
       with
       | [] => (return (Some nil))
       | x :: xs
         => (xs' <-- @reflect_list_cps _ xs;
               xs' <-- type.try_transport_base_cps (fun t => list (expr t)) _ _ xs';
               x' <-- type.try_transport_cps _ _ _ x;
             return (Some (x' :: xs')%list))
       | _ => (return None)
       end%expr%cps.
  Arguments reflect_list_cps {t} e [T] _.

  (** XXX MOVEME? *)
  Definition mkcast {P : type -> Type} {t1 t2 : type} : ~> (option (P t1 -> P t2))
    := fun T k => type.try_make_transport_cps P t1 t2 _ k.
  Definition cast {P : type -> Type} {t1 t2 : type} (v : P t1) : ~> (option (P t2))
    := fun T k => type.try_transport_cps P t1 t2 v _ k.
  Definition caste {t1 t2 : base_type} (v : expr t1) : ~> (option (expr t2))
    := fun T k => type.try_transport_base_cps expr t1 t2 v _ k.
  Definition castv {t1 t2} (v : value t1) : ~> (option (value t2))
    := fun T k => type.try_transport_cps value t1 t2 v _ k.
  Definition ret {A} (v : A) : ~> A := fun T k => k v.
  Definition oret {A} (v : A) : ~> (option A) := fun T k => k (Some v).
  Let UnderLetsAnyExpr {ivar} := @UnderLets.UnderLets ivar (@topanyexpr ivar).
  Let BaseWrapExpr {ivar} {t} (e : @topexpr ivar t) : @UnderLetsAnyExpr ivar := UnderLets.Base (wrap e).
  Let BaseAnyExpr {ivar} : @topanyexpr ivar -> @UnderLets.UnderLets ivar (@topanyexpr ivar) := UnderLets.Base.
  Coercion BaseWrapExpr : expr >-> UnderLetsAnyExpr.
  Coercion BaseAnyExpr : anyexpr >-> UnderLets.
  Let LiftWrapExpr {ivar} {t} (e : @UnderLets.UnderLets ivar (@topexpr ivar t)) : @UnderLetsAnyExpr ivar
    := (e <-- e; UnderLets.Base (wrap e))%under_lets.
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
    := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsAnyExpr var => Some (existT (opt_anyexprP value) false x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_step p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:@UnderLetsAnyExpr value => Some (existT (opt_anyexprP value) true x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:~> (option (UnderLets anyexpr)) => (x' <-- x; oret (existT (opt_anyexprP value) false x'))%cps) f%expr) in
        make_rewrite'_cps p f').
  Notation make_rewrite_step_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:~> (option (UnderLets (@topanyexpr value))) => (x' <-- x; oret (existT (opt_anyexprP value) true x'))%cps) f%expr) in
        make_rewrite'_cps p f').
  Definition rewrite_rules : rewrite_rulesT' value
    := [make_rewrite (0 + ??ℕ) (fun x => x);
          make_rewrite (??ℕ + 0) (fun x => x);
          make_rewrite (#? + #?) (fun x y => ##(x + y));
          make_rewrite (#? + ??ℕ.+1) (fun x y => ##(Datatypes.S x) + y);
          make_rewrite (??ℕ.+1 + #?) (fun x y => x + ##(Datatypes.S y));
          make_rewrite (??ℕ.+1 + ??ℕ.+1) (fun x y => (x+y).+1.+1);
          make_rewrite (??ℕ.+1 + ??ℕ) (fun x y => (x+y).+1);
          make_rewrite (??ℕ + ??ℕ.+1) (fun x y => (x+y).+1);
          make_rewrite (#pNatEqb @ #? @ #?) (fun x y => if Nat.eqb x y return topexpr _ then #iTrue else #iFalse);
          make_rewrite (#pFst @ (??, ??)) (fun tx x ty y => x);
          make_rewrite (#pSnd @ (??, ??)) (fun tx x ty y => y);
          make_rewrite (#pBoolRect @ ??{Unit -> pBase ??} @ ??{Unit -> pBase ??} @ #piTrue) (fun _ t _ f => LiftWrapExpr (t #TT));
          make_rewrite (#pBoolRect @ ??{Unit -> pBase ??} @ ??{Unit -> pBase ??} @ #piFalse) (fun _ t _ f => LiftWrapExpr (f #TT));
          make_rewrite_cps
            (#pMatchPair @ ??{?? -> ?? -> pBase ??} @ (??, ??))
            (fun _ _ _ f _ x _ y
             => x <-- caste x;
                  y <-- caste y;
                  oret (LiftWrapExpr (push_value_lets f x y)));
          make_rewrite_cps
            (??{pList ??} ++ ??{pList ??})
            (fun _ xs _ ys
             => xs <-- @caste _ (List _) xs;
                xs <-- reflect_list_cps xs;
                ys <-- reflect_list_cps ys;
                oret (UnderLets.Base (wrap (reify_list (List.app xs ys)))));
          make_rewrite_step_cps
            (#pListFlatMap @ ??{?? -> pList ??} @ ??{pList ??})
            (fun _ _ f _ xs
             => xs <-- @caste _ (List _) xs;
                  xs <-- reflect_list_cps xs;
                  oret (fxs <--- List.map f xs;
                          UnderLets.Base
                            (wrap (#ListFoldRight @ (λ ls1 ls2, $ls1 ++ $ls2) @ (λ _, []) @ $(reify_list fxs))%expr)));
          make_rewrite_step_cps
            (#pListPartition @ ??{?? -> pBool} @ ??{pList ??})
            (fun _ f _ xs
             => xs <-- @caste _ (List _) xs;
                  xs <-- reflect_list_cps xs;
                  oret (v <-- (list_rect
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
                                 xs)%expr;
                          UnderLets.Base (wrap v))%under_lets);
          make_rewrite_cps
            (#pListFoldRight @ ??{?? -> ?? -> ??} @ ?? @ ??{pList ??})
            (fun _ _ _ f A init B xs
             => f <-- @castv _ (B -> A -> A)%ctype f;
                  xs <-- reflect_list_cps xs;
                  oret (v <-- (fold_right
                                 (fun x y => y <-- y; push_value_lets f x y)
                                 (UnderLets.Base init)
                                 xs);
                          UnderLets.Base (wrap v))%under_lets);
          make_rewrite_cps
            (#pListRect @ ??{Unit -> pBase ??} @ ??{?? -> ?? -> ?? -> ??} @ ??{pList ??})
            (fun P Pnil _ _ _ _ Pcons A xs
             => Pcons <-- @castv _ (A -> List A -> P -> P)%ctype Pcons;
                  xs <-- reflect_list_cps xs;
                  oret (v <-- (list_rect
                                 (fun _ => UnderLets (expr P))
                                 (Pnil #TT)
                                 (fun x' xs' rec => rec <-- rec; push_value_lets Pcons x' (reify_list xs') rec)
                                 xs);
                          UnderLets.Base (wrap v))%under_lets);
          make_rewrite_cps
            (#pListMap @ ??{?? -> pBase ??} @ ??{pList ??})
            (fun _ _ f _ xs
             => xs <-- @caste _ (List _) xs;
                  xs <-- reflect_list_cps xs;
                  oret (fxs <--- List.map f xs;
                          UnderLets.Base (wrap (reify_list fxs)))%under_lets);
          make_rewrite_cps
            (#pListMap @ ??{?? -> pBase ??} @ (?? :: ??))
            (fun _ _ f _ x _ xs
             => xs <-- @caste _ (List _) xs;
                  x <-- caste x;
                  oret (fx <-- f x;
                          UnderLets.Base (wrap (fx :: #ListMap @ (λ v , UnderLets.to_expr (f ($v))) @ xs))%expr)%under_lets)
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
    Context (do_again : forall t, @topexpr value t -> UnderLets (expr t)).

    Definition dorewrite1 (e : rawexpr) : UnderLets (expr (type_of_rawexpr e))
      := eval_rewrite_rules do_again dtree rewrite_rules e.

    Fixpoint do_rewrite_ident (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t
      := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value_with_lets t with
         | Base _
           => fun e k => k (fun t => UnderLets (expr t)) (dorewrite1 e)
         | Arrow s d
           => fun f k => UnderLets.Base
                           (fun x => @do_rewrite_ident d (rApp f (rValueOrExpr x) (k _ (expr_of_rawexpr f) @ reify x))%expr (fun _ => id))
         end.

    Fixpoint dorewrite' {t} (e : @topexpr value t) : value_with_lets t
      := match e in topexpr t return value_with_lets t with
         | Ident t idc
           => eta_ident_cps idc (fun t' idc' => do_rewrite_ident t' (rIdent idc' #idc') (fun _ => id))
         | App s d f x => f <-- @dorewrite' _ f; x <-- @dorewrite' _ x; f x
         | LetIn A B x f => x <-- @dorewrite' A x;
                              UnderLet (reify x)
                                       (fun xv => @dorewrite' B (f (reflect ($xv)%expr)))
         | Var t v => UnderLets.Base v
         | Abs s d f => UnderLets.Base (fun x : value s => @dorewrite' d (f x))
         end%under_lets.

    Fixpoint nbe {t} (e : @topexpr value t) : value_with_lets t
      := match e in topexpr t return value_with_lets t with
         | Abs s d f => UnderLets.Base (fun x : value s => @nbe d (f x))
         | App s d f x => f <-- @nbe _ f; x <-- @nbe _ x; f x
         | Var t v => UnderLets.Base v
         | Ident t idc => UnderLets.Base (reflect (Ident idc))
         | LetIn A B x f => x <-- @nbe A x;
                              UnderLet (reify x)
                                       (fun xv => @nbe B (f (reflect ($xv)%expr)))
         end%under_lets.
  End with_do_again.
End with_var.

Fixpoint dorewrite'' (fuel : nat) {var t} e : @value_with_lets var t
  := @dorewrite'
       var
       (fun t' e'
        => match fuel with
           | Datatypes.O
             => e'' <-- nbe e'; UnderLets.Base (reify e'')
           | Datatypes.S fuel' => e'' <-- @dorewrite'' fuel' var t' e'; UnderLets.Base (reify e'')
           end%under_lets)
       t e.

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
Arguments bind_value_cps / .
Arguments bind_base_cps / .
Arguments app_ptype_interp_cps / .
Arguments app_binding_data / .
Arguments anyexpr_ty / .
Arguments unwrap / .
Arguments type_of_rawexpr / .
Arguments expr_of_rawexpr / .
Arguments reveal_rawexpr_cps / .
Arguments type.try_transport_cps _ !_ !_ _ {_}.
Arguments type.try_transport_base_cps _ !_ !_ _ {_}.
Arguments type.try_make_transport_cps _ !_ !_ {_}.
Arguments type.try_make_transport_base_cps _ !_ !_ {_}.
Arguments orb_pident / .
Arguments or_opt_pident / .
Arguments rValueOrExpr / .
Arguments Some_t / .
Arguments value_of_rawexpr / .
Arguments cast / .
Arguments caste / .
Arguments castv / .
Arguments ret / .
Arguments oret / .
Arguments lift_ptype_interp_cps / .
Arguments lift_pbase_type_interp_cps / .
Arguments app_pbase_type_interp_cps / .
Arguments pbase_type_interp_cps / .
Arguments ptype_interp / .
Arguments ptype_interp_cps / .
Arguments default_fuel / .
Arguments cpsreturn / .
Arguments cpsbind / .
Arguments cpscall / .
Arguments invert_Literal / .
Set Printing Depth 1000000.
Definition dorewrite''' {var}
  := Eval cbv (*-[value reify default_fuel reflect nbe type.try_transport_base_cps type.try_make_transport_base_cps type.try_make_transport_cps Nat.add List.map list_rect reify reflect reify_list reflect_list_cps List.app]*) (* but we also need to exclude things in the rhs of the rewrite rule *)
          [id cpscall cpsbind cpsreturn orb projT1 projT2 nth_error set_nth update_nth anyexpr_ty app_binding_data app_pbase_type_interp_cps app_ptype_interp_cps bind_base_cps bind_data_cps binding_dataT bind_value_cps cast caste castv dorewrite' dorewrite'' dorewrite1 do_rewrite_ident dtree eta_ident_cps eval_decision_tree eval_rewrite_rules expr_of_rawexpr lift_pbase_type_interp_cps lift_ptype_interp_cps lift_with_bindings orb_pident oret or_opt_pident pbase_type_interp_cps pident_ident_beq pident_of_ident ptype_interp ptype_interp_cps reveal_rawexpr_cps rewrite_rules rValueOrExpr swap_list type_of_rawexpr type.try_transport_cps unwrap value_of_rawexpr with_bindingsT Some_t value_with_lets value' value'_with_lets splice_value'_with_lets push_lets_value' push_pull_value_lets push_value_lets pull_value_lets fst snd invert_Literal pident_beq]
    in @dorewrite'' default_fuel var.
Arguments dorewrite''' / .
Print dorewrite'''.
Definition dorewrite
  := Eval cbn [dorewrite''' type.try_transport_cps type.try_transport_base_cps type.try_make_transport_cps type.try_make_transport_base_cps Option.bind value value'' reify reflect nbe UnderLets.splice UnderLets.splice_list UnderLets.to_expr cpscall cpsbind cpsreturn (*default_fuel*)] in @dorewrite'''.
Arguments dorewrite {var t} e.
Local Open Scope expr_scope.
Arguments expr : clear implicits.
Set Printing Width 137.
Print dorewrite.
(*dorewrite =
fun var : type -> Type =>
(fix dorewrite'' (fuel : nat) (var0 : type -> Type) (t : type) (e : expr value t) {struct fuel} : UnderLets var0 (value t) :=
   (fix dorewrite' (t0 : type) (e0 : expr value t0) {struct e0} : UnderLets var0 (value t0) :=
      match e0 in (expr _ t1) return (UnderLets var0 (value t1)) with
      | @Var _ t1 v => UnderLets.Base v
      | @Abs _ s d f => UnderLets.Base (fun x : value s => dorewrite' d (f x))
      | #(idc) =>
          match idc in (ident t2) return (UnderLets var0 (value t2)) with
          | O => UnderLets.Base 0
          | S => UnderLets.Base (fun x : expr var0 Nat => UnderLets.Base (x.+1))
          | @NatRect P =>
              UnderLets.Base
                (fun x : expr var0 ( ) -> UnderLets var0 (expr var0 P) =>
                 UnderLets.Base
                   (fun x0 : expr var0 Nat -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)) =>
                    UnderLets.Base
                      (fun x1 : expr var0 Nat =>
                       UnderLets.Base
                         (#(NatRect) @ (λ x2 : var0 ( )%ctype,
                                        UnderLets.to_expr (fx <-- x ($x2);
                                                           UnderLets.Base fx)) @
                          (λ x2 : var0 Nat,
                           UnderLets.to_expr
                             (fx <-- x0 ($x2);
                              UnderLets.Base (λ x3 : var0 P,
                                              UnderLets.to_expr (fx0 <-- fx ($x3);
                                                                 UnderLets.Base fx0)))) @ x1))))
          | NatEqb =>
              UnderLets.Base
                (fun x : expr var0 Nat =>
                 UnderLets.Base
                   (fun x0 : expr var0 Nat =>
                    match x with
                    | ##(n) =>
                        match x0 with
                        | ##(n0) => UnderLets.Base (if n =? n0 then #(iTrue) else #(iFalse))
                        | _ => UnderLets.Base (#(NatEqb) @ x @ x0)
                        end
                    | _ => UnderLets.Base (#(NatEqb) @ x @ x0)
                    end))
          | Add =>
              UnderLets.Base
                (fun x : expr var0 Nat =>
                 UnderLets.Base
                   (fun x0 : expr var0 Nat =>
                    match x with
                    | $_ =>
                        match x0 with
                        | 0 => UnderLets.Base x
                        | @App _ s _ #(S) x1 =>
                            match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                            | Base t4 =>
                                fun e1 : expr var0 t4 =>
                                type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                  (fun a : option (expr var0 Nat) =>
                                   match a with
                                   | Some v0 => UnderLets.Base ((x + v0).+1)
                                   | None => UnderLets.Base (x + x0)
                                   end)
                            | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                            end (reflect x1)
                        | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(@NatRect _) _ | @App _ s _
                          #(NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _
                          #(@Snd _ _) _ | @App _ s _ #(@MatchPair _ _ _) _ | @App _ s _ [] _ | @App _ s _ #(@Cons _) _ | @App _ s _
                          #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _ s _
                          #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ #(@ListPartition _) _ | @App _ s _
                          ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #(iFalse) _ | @App _ s _ #(@BoolRect _) _ | @App _ s _ ##
                          (_) _ | @App _ s _ (_ @ _) _ | @App _ s _ (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                        | _ => UnderLets.Base (x + x0)
                        end
                    | @Abs _ _ _ _ =>
                        match x0 with
                        | 0 => UnderLets.Base x
                        | @App _ s0 _ #(S) x1 =>
                            match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                            | Base t3 =>
                                fun e1 : expr var0 t3 =>
                                type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t3 Nat e1
                                  (fun a : option (expr var0 Nat) =>
                                   match a with
                                   | Some v => UnderLets.Base ((x + v).+1)
                                   | None => UnderLets.Base (x + x0)
                                   end)
                            | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                            end (reflect x1)
                        | @App _ s0 _ ($_) _ | @App _ s0 _ (@Abs _ _ _ _) _ | @App _ s0 _ 0 _ | @App _ s0 _ #
                          (@NatRect _) _ | @App _ s0 _ #(NatEqb) _ | @App _ s0 _ #(Add) _ | @App _ s0 _ #(@Pair _ _) _ | @App _ s0 _
                          #(@Fst _ _) _ | @App _ s0 _ #(@Snd _ _) _ | @App _ s0 _ #(@MatchPair _ _ _) _ | @App _ s0 _ [] _ | @App _ s0 _
                          #(@Cons _) _ | @App _ s0 _ #(@ListMap _ _) _ | @App _ s0 _ #(@ListApp _) _ | @App _ s0 _ #
                          (@ListFlatMap _ _) _ | @App _ s0 _ #(@ListRect _ _) _ | @App _ s0 _ #(@ListFoldRight _ _) _ | @App _ s0 _
                          #(@ListPartition _) _ | @App _ s0 _ ( ) _ | @App _ s0 _ #(iTrue) _ | @App _ s0 _ #
                          (iFalse) _ | @App _ s0 _ #(@BoolRect _) _ | @App _ s0 _ ##(_) _ | @App _ s0 _ (_ @ _) _ | @App _ s0 _
                          (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                        | _ => UnderLets.Base (x + x0)
                        end
                    | 0 => UnderLets.Base x0
                    | ##(n) =>
                        match x0 with
                        | 0 => UnderLets.Base x
                        | ##(n0) => UnderLets.Base ##(n + n0)
                        | @App _ s _ #(S) x1 =>
                            match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                            | Base t4 =>
                                fun e1 : expr var0 t4 =>
                                type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                  (fun a : option (expr var0 Nat) =>
                                   match a with
                                   | Some v => UnderLets.Base (##(Datatypes.S n) + v)
                                   | None => UnderLets.Base (x + x0)
                                   end)
                            | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                            end (reflect x1)
                        | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(@NatRect _) _ | @App _ s _
                          #(NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _
                          #(@Snd _ _) _ | @App _ s _ #(@MatchPair _ _ _) _ | @App _ s _ [] _ | @App _ s _ #(@Cons _) _ | @App _ s _
                          #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _ s _
                          #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ #(@ListPartition _) _ | @App _ s _
                          ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #(iFalse) _ | @App _ s _ #(@BoolRect _) _ | @App _ s _ ##
                          (_) _ | @App _ s _ (_ @ _) _ | @App _ s _ (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                        | _ => UnderLets.Base (x + x0)
                        end
                    | @App _ s _ f x1 =>
                        match x0 with
                        | $_ =>
                            match f with
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v0 => UnderLets.Base ((v0 + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @Abs _ _ _ _ =>
                            match f with
                            | #(S) =>
                                match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | 0 => UnderLets.Base x
                        | ##(n) =>
                            match f with
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base (v + ##(Datatypes.S n))
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @App _ s0 _ ($_) _ =>
                            match f with
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v0 => UnderLets.Base ((v0 + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @App _ s0 _ (@Abs _ _ _ _) _ =>
                            match f with
                            | #(S) =>
                                match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s2 -> d2)%ctype => fun _ : value s2 -> UnderLets var0 (value d2) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @App _ s0 _ #(S) x2 =>
                            match f with
                            | $_ =>
                                match s0 as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v0 => UnderLets.Base ((x + v0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x2)
                            | @Abs _ _ _ _ =>
                                match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((x + v).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s2 -> d2)%ctype => fun _ : value s2 -> UnderLets var0 (value d2) => UnderLets.Base (x + x0)
                                end (reflect x2)
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v =>
                                           match s0 as t5 return (value t5 -> UnderLets var0 (expr var0 Nat)) with
                                           | Base t5 =>
                                               fun e2 : expr var0 t5 =>
                                               type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t5 Nat e2
                                                 (fun a0 : option (expr var0 Nat) =>
                                                  match a0 with
                                                  | Some v0 => UnderLets.Base (((v + v0).+1).+1)
                                                  | None => UnderLets.Base (x + x0)
                                                  end)
                                           | (s1 -> d1)%ctype =>
                                               fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                           end (reflect x2)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ @ _ =>
                                match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x4 : base_type => expr var0 x4) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((x + v).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s2 -> d2)%ctype => fun _ : value s2 -> UnderLets var0 (value d2) => UnderLets.Base (x + x0)
                                end (reflect x2)
                            | @LetIn _ _ _ _ _ =>
                                match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x4 : base_type => expr var0 x4) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((x + v).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x2)
                            | _ =>
                                match s0 as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((x + v).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x2)
                            end
                        | @App _ s0 _ 0 _ | @App _ s0 _ #(@NatRect _) _ | @App _ s0 _ #(NatEqb) _ | @App _ s0 _ #
                          (Add) _ | @App _ s0 _ #(@Pair _ _) _ | @App _ s0 _ #(@Fst _ _) _ | @App _ s0 _ #(@Snd _ _) _ | @App _ s0 _
                          #(@MatchPair _ _ _) _ | @App _ s0 _ [] _ | @App _ s0 _ #(@Cons _) _ | @App _ s0 _ #
                          (@ListMap _ _) _ | @App _ s0 _ #(@ListApp _) _ | @App _ s0 _ #(@ListFlatMap _ _) _ | @App _ s0 _
                          #(@ListRect _ _) _ | @App _ s0 _ #(@ListFoldRight _ _) _ | @App _ s0 _ #(@ListPartition _) _ | @App _ s0 _
                          ( ) _ | @App _ s0 _ #(iTrue) _ | @App _ s0 _ #(iFalse) _ | @App _ s0 _ #(@BoolRect _) _ | @App _ s0 _ ##
                          (_) _ =>
                            match f with
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @App _ s0 _ (_ @ _) _ =>
                            match f with
                            | #(S) =>
                                match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x4 : base_type => expr var0 x4) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s2 -> d2)%ctype => fun _ : value s2 -> UnderLets var0 (value d2) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @App _ s0 _ (@LetIn _ _ _ _ _) _ =>
                            match f with
                            | #(S) =>
                                match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x4 : base_type => expr var0 x4) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | @LetIn _ _ _ _ _ =>
                            match f with
                            | #(S) =>
                                match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t3 =>
                                    fun e1 : expr var0 t3 =>
                                    type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        | _ =>
                            match f with
                            | #(S) =>
                                match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                                | Base t4 =>
                                    fun e1 : expr var0 t4 =>
                                    type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                      (fun a : option (expr var0 Nat) =>
                                       match a with
                                       | Some v => UnderLets.Base ((v + x0).+1)
                                       | None => UnderLets.Base (x + x0)
                                       end)
                                | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                                end (reflect x1)
                            | _ => UnderLets.Base (x + x0)
                            end
                        end
                    | @LetIn _ _ _ _ _ =>
                        match x0 with
                        | 0 => UnderLets.Base x
                        | @App _ s _ #(S) x2 =>
                            match s as t3 return (value t3 -> UnderLets var0 (expr var0 Nat)) with
                            | Base t3 =>
                                fun e1 : expr var0 t3 =>
                                type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 Nat e1
                                  (fun a : option (expr var0 Nat) =>
                                   match a with
                                   | Some v => UnderLets.Base ((x + v).+1)
                                   | None => UnderLets.Base (x + x0)
                                   end)
                            | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                            end (reflect x2)
                        | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(@NatRect _) _ | @App _ s _
                          #(NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _
                          #(@Snd _ _) _ | @App _ s _ #(@MatchPair _ _ _) _ | @App _ s _ [] _ | @App _ s _ #(@Cons _) _ | @App _ s _
                          #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _ s _
                          #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ #(@ListPartition _) _ | @App _ s _
                          ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #(iFalse) _ | @App _ s _ #(@BoolRect _) _ | @App _ s _ ##
                          (_) _ | @App _ s _ (_ @ _) _ | @App _ s _ (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                        | _ => UnderLets.Base (x + x0)
                        end
                    | _ =>
                        match x0 with
                        | 0 => UnderLets.Base x
                        | @App _ s _ #(S) x1 =>
                            match s as t4 return (value t4 -> UnderLets var0 (expr var0 Nat)) with
                            | Base t4 =>
                                fun e1 : expr var0 t4 =>
                                type.try_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 Nat e1
                                  (fun a : option (expr var0 Nat) =>
                                   match a with
                                   | Some v => UnderLets.Base ((x + v).+1)
                                   | None => UnderLets.Base (x + x0)
                                   end)
                            | (s0 -> d0)%ctype => fun _ : value s0 -> UnderLets var0 (value d0) => UnderLets.Base (x + x0)
                            end (reflect x1)
                        | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(@NatRect _) _ | @App _ s _
                          #(NatEqb) _ | @App _ s _ #(Add) _ | @App _ s _ #(@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _
                          #(@Snd _ _) _ | @App _ s _ #(@MatchPair _ _ _) _ | @App _ s _ [] _ | @App _ s _ #(@Cons _) _ | @App _ s _
                          #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _ s _
                          #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ #(@ListPartition _) _ | @App _ s _
                          ( ) _ | @App _ s _ #(iTrue) _ | @App _ s _ #(iFalse) _ | @App _ s _ #(@BoolRect _) _ | @App _ s _ ##
                          (_) _ | @App _ s _ (_ @ _) _ | @App _ s _ (@LetIn _ _ _ _ _) _ => UnderLets.Base (x + x0)
                        | _ => UnderLets.Base (x + x0)
                        end
                    end))
          | @Pair A B => UnderLets.Base (fun x : expr var0 A => UnderLets.Base (fun x0 : expr var0 B => UnderLets.Base (x, x0)))
          | @Fst A B =>
              UnderLets.Base
                (fun x : expr var0 (A * B) =>
                 match x with
                 | @App _ s _ (@App _ s0 _ #(@Pair _ _) x1) x0 =>
                     match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 A)) with
                     | Base t3 =>
                         fun e1 : expr var0 t3 =>
                         match s as t4 return (value t4 -> UnderLets var0 (expr var0 A)) with
                         | Base t4 =>
                             fun _ : expr var0 t4 =>
                             type.try_make_transport_base_cps (fun x2 : base_type => expr var0 x2) t3 A
                               (fun a : option (expr var0 t3 -> expr var0 A) =>
                                match a with
                                | Some tr => UnderLets.Base (tr e1)
                                | None => UnderLets.Base (#(Fst) @ x)
                                end)
                         | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (#(Fst) @ x)
                         end (reflect x0)
                     | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (#(Fst) @ x)
                     end (reflect x1)
                 | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                   (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(@NatRect _) _) _ | @App _ s _
                   (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _
                   s _ (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _
                   (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@Cons _) _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ | @App
                   _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                   (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                   (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ |
                   @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _ (@App _ s0 _ #(@BoolRect _) _) _ | @App _ s _
                   (@App _ s0 _ ##(_) _) _ | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                     UnderLets.Base (#(Fst) @ x)
                 | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                     UnderLets.Base (#(Fst) @ x)
                 | _ => UnderLets.Base (#(Fst) @ x)
                 end)
          | @Snd A B =>
              UnderLets.Base
                (fun x : expr var0 (A * B) =>
                 match x with
                 | @App _ s _ (@App _ s0 _ #(@Pair _ _) x1) x0 =>
                     match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 B)) with
                     | Base t3 =>
                         fun _ : expr var0 t3 =>
                         match s as t4 return (value t4 -> UnderLets var0 (expr var0 B)) with
                         | Base t4 =>
                             fun e2 : expr var0 t4 =>
                             type.try_make_transport_base_cps (fun x2 : base_type => expr var0 x2) t4 B
                               (fun a : option (expr var0 t4 -> expr var0 B) =>
                                match a with
                                | Some tr => UnderLets.Base (tr e2)
                                | None => UnderLets.Base (#(Snd) @ x)
                                end)
                         | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (#(Snd) @ x)
                         end (reflect x0)
                     | (s1 -> d1)%ctype => fun _ : value s1 -> UnderLets var0 (value d1) => UnderLets.Base (#(Snd) @ x)
                     end (reflect x1)
                 | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                   (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(@NatRect _) _) _ | @App _ s _
                   (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _
                   s _ (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _
                   (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@Cons _) _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ | @App
                   _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                   (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                   (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _ (@App _ s0 _ #(iTrue) _) _ |
                   @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _ (@App _ s0 _ #(@BoolRect _) _) _ | @App _ s _
                   (@App _ s0 _ ##(_) _) _ | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                     UnderLets.Base (#(Snd) @ x)
                 | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                     UnderLets.Base (#(Snd) @ x)
                 | _ => UnderLets.Base (#(Snd) @ x)
                 end)
          | @MatchPair A B P =>
              UnderLets.Base
                (fun x : expr var0 A -> UnderLets var0 (expr var0 B -> UnderLets var0 (expr var0 P)) =>
                 UnderLets.Base
                   (fun x0 : expr var0 (A * B) =>
                    match x0 with
                    | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x2 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x2);
                               UnderLets.Base (λ x3 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x3);
                                                                  UnderLets.Base fx0)))) @ x0)
                    | @App _ s _ (@App _ s0 _ #(@Pair _ _) x2) x1 =>
                        match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 P)) with
                        | Base t3 =>
                            fun e1 : expr var0 t3 =>
                            match s as t4 return (value t4 -> UnderLets var0 (expr var0 P)) with
                            | Base t4 =>
                                fun e2 : expr var0 t4 =>
                                type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 A e1
                                  (fun a : option (expr var0 A) =>
                                   match a with
                                   | Some x3 =>
                                       type.try_transport_base_cps (fun x4 : base_type => expr var0 x4) t4 B e2
                                         (fun a0 : option (expr var0 B) =>
                                          match a0 with
                                          | Some y =>
                                              (fv <-- (e3 <-- (f1 <-- (fx <-- x x3;
                                                                       UnderLets.Base
                                                                         (fun x4 : expr var0 B => fx0 <-- fx x4;
                                                                                                  UnderLets.Base fx0));
                                                               e3 <-- f1 y;
                                                               UnderLets.Base e3);
                                                       UnderLets.Base e3);
                                               type.try_make_transport_cps (expr var0) (let (anyexpr_ty, _) := fv in anyexpr_ty) P
                                                 (fun a1 : option (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr var0 P)
                                                  =>
                                                  match a1 with
                                                  | Some tr =>
                                                      UnderLets.Base
                                                        (tr
                                                           (let
                                                              (anyexpr_ty, unwrap) as a2
                                                               return (expr var0 (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                            unwrap))
                                                  | None =>
                                                      UnderLets.Base
                                                        (#(MatchPair) @
                                                         (λ x4 : var0 A,
                                                          UnderLets.to_expr
                                                            (fx <-- x ($x4);
                                                             UnderLets.Base
                                                               (λ x5 : var0 B,
                                                                UnderLets.to_expr (fx0 <-- fx ($x5);
                                                                                   UnderLets.Base fx0)))) @ x0)
                                                  end))%under_lets
                                          | None =>
                                              UnderLets.Base
                                                (#(MatchPair) @
                                                 (λ x4 : var0 A,
                                                  UnderLets.to_expr
                                                    (fx <-- x ($x4);
                                                     UnderLets.Base
                                                       (λ x5 : var0 B,
                                                        UnderLets.to_expr (fx0 <-- fx ($x5);
                                                                           UnderLets.Base fx0)))) @ x0)
                                          end)
                                   | None =>
                                       UnderLets.Base
                                         (#(MatchPair) @
                                          (λ x3 : var0 A,
                                           UnderLets.to_expr
                                             (fx <-- x ($x3);
                                              UnderLets.Base (λ x4 : var0 B,
                                                              UnderLets.to_expr (fx0 <-- fx ($x4);
                                                                                 UnderLets.Base fx0)))) @ x0)
                                   end)
                            | (s1 -> d1)%ctype =>
                                fun _ : value s1 -> UnderLets var0 (value d1) =>
                                UnderLets.Base
                                  (#(MatchPair) @
                                   (λ x3 : var0 A,
                                    UnderLets.to_expr
                                      (fx <-- x ($x3);
                                       UnderLets.Base (λ x4 : var0 B,
                                                       UnderLets.to_expr (fx0 <-- fx ($x4);
                                                                          UnderLets.Base fx0)))) @ x0)
                            end (reflect x1)
                        | (s1 -> d1)%ctype =>
                            fun _ : value s1 -> UnderLets var0 (value d1) =>
                            UnderLets.Base
                              (#(MatchPair) @
                               (λ x3 : var0 A,
                                UnderLets.to_expr
                                  (fx <-- x ($x3);
                                   UnderLets.Base (λ x4 : var0 B,
                                                   UnderLets.to_expr (fx0 <-- fx ($x4);
                                                                      UnderLets.Base fx0)))) @ x0)
                        end (reflect x2)
                    | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                      (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(@NatRect _) _) _ | @App _ s _
                      (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ |
                      @App _ s _ (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _
                      (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@Cons _) _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ |
                      @App _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                      (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                      (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _
                      (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _ (@App _ s0 _ #(@BoolRect _) _)
                      _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x3 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x3);
                               UnderLets.Base (λ x4 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x4);
                                                                  UnderLets.Base fx0)))) @ x0)
                    | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x4 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x4);
                               UnderLets.Base (λ x5 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x5);
                                                                  UnderLets.Base fx0)))) @ x0)
                    | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x3 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x3);
                               UnderLets.Base (λ x4 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x4);
                                                                  UnderLets.Base fx0)))) @ x0)
                    | @LetIn _ _ _ _ _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x2 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x2);
                               UnderLets.Base (λ x3 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x3);
                                                                  UnderLets.Base fx0)))) @ x0)
                    | _ =>
                        UnderLets.Base
                          (#(MatchPair) @
                           (λ x1 : var0 A,
                            UnderLets.to_expr
                              (fx <-- x ($x1);
                               UnderLets.Base (λ x2 : var0 B,
                                               UnderLets.to_expr (fx0 <-- fx ($x2);
                                                                  UnderLets.Base fx0)))) @ x0)
                    end))
          | @Nil A => UnderLets.Base []
          | @Cons A => UnderLets.Base (fun x : expr var0 A => UnderLets.Base (fun x0 : expr var0 (List A) => UnderLets.Base (x :: x0)))
          | @ListMap A B =>
              UnderLets.Base
                (fun x : expr var0 A -> UnderLets var0 (expr var0 B) =>
                 UnderLets.Base
                   (fun x0 : expr var0 (List A) =>
                    type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                      (fun a : option (expr var0 (List A) -> expr var0 (List A)) =>
                       match a with
                       | Some tr =>
                           reflect_list_cps (tr x0) (UnderLets var0 (expr var0 (List B)))
                             (fun a0 : option (list (expr var0 A)) =>
                              match a0 with
                              | Some xs =>
                                  (fv <-- (fxs <--- map x xs;
                                           UnderLets.Base (reify_list fxs));
                                   type.try_make_transport_cps (expr var0) (let (anyexpr_ty, _) := fv in anyexpr_ty)
                                     (List B)
                                     (fun a1 : option (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr var0 (List B)) =>
                                      match a1 with
                                      | Some tr0 =>
                                          UnderLets.Base
                                            (tr0
                                               (let
                                                  (anyexpr_ty, unwrap) as a2
                                                   return (expr var0 (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                unwrap))
                                      | None =>
                                          match x0 with
                                          | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x2 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x2);
                                                                                  UnderLets.Base fx)) @ x0)
                                          | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                                              match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 (List B))) with
                                              | Base t3 =>
                                                  fun e1 : expr var0 t3 =>
                                                  match s as t4 return (value t4 -> UnderLets var0 (expr var0 (List B))) with
                                                  | Base t4 =>
                                                      fun e2 : expr var0 t4 =>
                                                      type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4
                                                        (List A) e2
                                                        (fun a2 : option (expr var0 (List A)) =>
                                                         match a2 with
                                                         | Some xs0 =>
                                                             type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 A e1
                                                               (fun a3 : option (expr var0 A) =>
                                                                match a3 with
                                                                | Some x3 =>
                                                                    fv0 <-- (fx <-- x x3;
                                                                             UnderLets.Base
                                                                               (fx
                                                                                :: #(ListMap) @
                                                                                   (λ v : var0 A,
                                                                                    UnderLets.to_expr (x ($v))) @ xs0));
                                                                    type.try_make_transport_cps (expr var0)
                                                                      (let (anyexpr_ty, _) := fv0 in anyexpr_ty)
                                                                      (List B)
                                                                      (fun
                                                                         a4 : option
                                                                                (expr var0 (let (anyexpr_ty, _) := fv0 in anyexpr_ty) ->
                                                                                 expr var0 (List B)) =>
                                                                       match a4 with
                                                                       | Some tr0 =>
                                                                           UnderLets.Base
                                                                             (tr0
                                                                                (let
                                                                                   (anyexpr_ty, unwrap) as a5
                                                                                    return
                                                                                      (expr var0
                                                                                         (let (anyexpr_ty, _) := a5 in anyexpr_ty)) :=
                                                                                   fv0 in
                                                                                 unwrap))
                                                                       | None =>
                                                                           UnderLets.Base
                                                                             (#(ListMap) @
                                                                              (λ x4 : var0 A,
                                                                               UnderLets.to_expr (fx <-- x ($x4);
                                                                                                  UnderLets.Base fx)) @ x0)
                                                                       end)
                                                                | None =>
                                                                    UnderLets.Base
                                                                      (#(ListMap) @
                                                                       (λ x3 : var0 A,
                                                                        UnderLets.to_expr (fx <-- x ($x3);
                                                                                           UnderLets.Base fx)) @ x0)
                                                                end)
                                                         | None =>
                                                             UnderLets.Base
                                                               (#(ListMap) @
                                                                (λ x3 : var0 A,
                                                                 UnderLets.to_expr (fx <-- x ($x3);
                                                                                    UnderLets.Base fx)) @ x0)
                                                         end)
                                                  | (s1 -> d1)%ctype =>
                                                      fun _ : value s1 -> UnderLets var0 (value d1) =>
                                                      UnderLets.Base
                                                        (#(ListMap) @
                                                         (λ x3 : var0 A,
                                                          UnderLets.to_expr (fx <-- x ($x3);
                                                                             UnderLets.Base fx)) @ x0)
                                                  end (reflect x1)
                                              | (s1 -> d1)%ctype =>
                                                  fun _ : value s1 -> UnderLets var0 (value d1) =>
                                                  UnderLets.Base
                                                    (#(ListMap) @ (λ x3 : var0 A,
                                                                   UnderLets.to_expr (fx <-- x ($x3);
                                                                                      UnderLets.Base fx)) @ x0)
                                              end (reflect x2)
                                          | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                                            (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _
                                            (@App _ s0 _ #(@NatRect _) _) _ | @App _ s _ (@App _ s0 _ #(NatEqb) _) _ | @App _ s _
                                            (@App _ s0 _ #(Add) _) _ | @App _ s _ (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _
                                            (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _
                                            (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                                            (@App _ s0 _ #(@ListMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _
                                            (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListRect _ _) _) _ | @App
                                            _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                                            (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _
                                            (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                                            (@App _ s0 _ #(@BoolRect _) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x3 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x3);
                                                                                  UnderLets.Base fx)) @ x0)
                                          | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x4 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x4);
                                                                                  UnderLets.Base fx)) @ x0)
                                          | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x3 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x3);
                                                                                  UnderLets.Base fx)) @ x0)
                                          | @LetIn _ _ _ _ _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x2 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x2);
                                                                                  UnderLets.Base fx)) @ x0)
                                          | _ =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x1 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x1);
                                                                                  UnderLets.Base fx)) @ x0)
                                          end
                                      end))%under_lets
                              | None =>
                                  match x0 with
                                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x2 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x2);
                                                                          UnderLets.Base fx)) @ x0)
                                  | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                                      match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 (List B))) with
                                      | Base t3 =>
                                          fun e1 : expr var0 t3 =>
                                          match s as t4 return (value t4 -> UnderLets var0 (expr var0 (List B))) with
                                          | Base t4 =>
                                              fun e2 : expr var0 t4 =>
                                              type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4
                                                (List A) e2
                                                (fun a1 : option (expr var0 (List A)) =>
                                                 match a1 with
                                                 | Some xs =>
                                                     type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 A e1
                                                       (fun a2 : option (expr var0 A) =>
                                                        match a2 with
                                                        | Some x3 =>
                                                            (fv <-- (fx <-- x x3;
                                                                     UnderLets.Base
                                                                       (fx
                                                                        :: #(ListMap) @ (λ v : var0 A,
                                                                                         UnderLets.to_expr (x ($v))) @ xs));
                                                             type.try_make_transport_cps (expr var0)
                                                               (let (anyexpr_ty, _) := fv in anyexpr_ty) (List B)
                                                               (fun
                                                                  a3 : option
                                                                         (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) ->
                                                                          expr var0 (List B)) =>
                                                                match a3 with
                                                                | Some tr0 =>
                                                                    UnderLets.Base
                                                                      (tr0
                                                                         (let
                                                                            (anyexpr_ty, unwrap) as a4
                                                                             return
                                                                               (expr var0 (let (anyexpr_ty, _) := a4 in anyexpr_ty)) :=
                                                                            fv in
                                                                          unwrap))
                                                                | None =>
                                                                    UnderLets.Base
                                                                      (#(ListMap) @
                                                                       (λ x4 : var0 A,
                                                                        UnderLets.to_expr (fx <-- x ($x4);
                                                                                           UnderLets.Base fx)) @ x0)
                                                                end))%under_lets
                                                        | None =>
                                                            UnderLets.Base
                                                              (#(ListMap) @
                                                               (λ x3 : var0 A,
                                                                UnderLets.to_expr (fx <-- x ($x3);
                                                                                   UnderLets.Base fx)) @ x0)
                                                        end)
                                                 | None =>
                                                     UnderLets.Base
                                                       (#(ListMap) @
                                                        (λ x3 : var0 A,
                                                         UnderLets.to_expr (fx <-- x ($x3);
                                                                            UnderLets.Base fx)) @ x0)
                                                 end)
                                          | (s1 -> d1)%ctype =>
                                              fun _ : value s1 -> UnderLets var0 (value d1) =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x3 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x3);
                                                                                  UnderLets.Base fx)) @ x0)
                                          end (reflect x1)
                                      | (s1 -> d1)%ctype =>
                                          fun _ : value s1 -> UnderLets var0 (value d1) =>
                                          UnderLets.Base
                                            (#(ListMap) @ (λ x3 : var0 A,
                                                           UnderLets.to_expr (fx <-- x ($x3);
                                                                              UnderLets.Base fx)) @ x0)
                                      end (reflect x2)
                                  | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                                    (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(@NatRect _) _)
                                    _ | @App _ s _ (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _
                                    (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _
                                    (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _
                                    (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ | @App _ s _
                                    (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                                    (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                                    (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _
                                    (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                                    (@App _ s0 _ #(@BoolRect _) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x3 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x3);
                                                                          UnderLets.Base fx)) @ x0)
                                  | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x4 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x4);
                                                                          UnderLets.Base fx)) @ x0)
                                  | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x3 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x3);
                                                                          UnderLets.Base fx)) @ x0)
                                  | @LetIn _ _ _ _ _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x2 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x2);
                                                                          UnderLets.Base fx)) @ x0)
                                  | _ =>
                                      UnderLets.Base
                                        (#(ListMap) @ (λ x1 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x1);
                                                                          UnderLets.Base fx)) @ x0)
                                  end
                              end)
                       | None =>
                           match x0 with
                           | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ =>
                               UnderLets.Base (#(ListMap) @ (λ x2 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x2);
                                                                                UnderLets.Base fx)) @ x0)
                           | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                               match s0 as t3 return (value t3 -> UnderLets var0 (expr var0 (List B))) with
                               | Base t3 =>
                                   fun e1 : expr var0 t3 =>
                                   match s as t4 return (value t4 -> UnderLets var0 (expr var0 (List B))) with
                                   | Base t4 =>
                                       fun e2 : expr var0 t4 =>
                                       type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t4 (List A) e2
                                         (fun a0 : option (expr var0 (List A)) =>
                                          match a0 with
                                          | Some xs =>
                                              type.try_transport_base_cps (fun x3 : base_type => expr var0 x3) t3 A e1
                                                (fun a1 : option (expr var0 A) =>
                                                 match a1 with
                                                 | Some x3 =>
                                                     (fv <-- (fx <-- x x3;
                                                              UnderLets.Base
                                                                (fx :: #(ListMap) @ (λ v : var0 A,
                                                                                     UnderLets.to_expr (x ($v))) @ xs));
                                                      type.try_make_transport_cps (expr var0) (let (anyexpr_ty, _) := fv in anyexpr_ty)
                                                        (List B)
                                                        (fun
                                                           a2 : option
                                                                  (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) ->
                                                                   expr var0 (List B)) =>
                                                         match a2 with
                                                         | Some tr =>
                                                             UnderLets.Base
                                                               (tr
                                                                  (let
                                                                     (anyexpr_ty, unwrap) as a3
                                                                      return (expr var0 (let (anyexpr_ty, _) := a3 in anyexpr_ty)) :=
                                                                     fv in
                                                                   unwrap))
                                                         | None =>
                                                             UnderLets.Base
                                                               (#(ListMap) @
                                                                (λ x4 : var0 A,
                                                                 UnderLets.to_expr (fx <-- x ($x4);
                                                                                    UnderLets.Base fx)) @ x0)
                                                         end))%under_lets
                                                 | None =>
                                                     UnderLets.Base
                                                       (#(ListMap) @
                                                        (λ x3 : var0 A,
                                                         UnderLets.to_expr (fx <-- x ($x3);
                                                                            UnderLets.Base fx)) @ x0)
                                                 end)
                                          | None =>
                                              UnderLets.Base
                                                (#(ListMap) @ (λ x3 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x3);
                                                                                  UnderLets.Base fx)) @ x0)
                                          end)
                                   | (s1 -> d1)%ctype =>
                                       fun _ : value s1 -> UnderLets var0 (value d1) =>
                                       UnderLets.Base
                                         (#(ListMap) @ (λ x3 : var0 A,
                                                        UnderLets.to_expr (fx <-- x ($x3);
                                                                           UnderLets.Base fx)) @ x0)
                                   end (reflect x1)
                               | (s1 -> d1)%ctype =>
                                   fun _ : value s1 -> UnderLets var0 (value d1) =>
                                   UnderLets.Base
                                     (#(ListMap) @ (λ x3 : var0 A,
                                                    UnderLets.to_expr (fx <-- x ($x3);
                                                                       UnderLets.Base fx)) @ x0)
                               end (reflect x2)
                           | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                             (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(@NatRect _) _) _ | @App
                             _ s _ (@App _ s0 _ #(NatEqb) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _
                             (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _
                             (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ #(@MatchPair _ _ _) _) _ | @App _ s _
                             (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ | @App _ s _
                             (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                             (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                             (@App _ s0 _ #(@ListPartition _) _) _ | @App _ s _ (@App _ s0 _ ( ) _) _ | @App _ s _
                             (@App _ s0 _ #(iTrue) _) _ | @App _ s _ (@App _ s0 _ #(iFalse) _) _ | @App _ s _
                             (@App _ s0 _ #(@BoolRect _) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                               UnderLets.Base (#(ListMap) @ (λ x3 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x3);
                                                                                UnderLets.Base fx)) @ x0)
                           | @App _ s _ (@App _ s0 _ (_ @ _) _) _ | @App _ s _ (@App _ s0 _ (@LetIn _ _ _ _ _) _) _ =>
                               UnderLets.Base (#(ListMap) @ (λ x4 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x4);
                                                                                UnderLets.Base fx)) @ x0)
                           | @App _ s _ (@LetIn _ _ _ _ _) _ =>
                               UnderLets.Base (#(ListMap) @ (λ x3 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x3);
                                                                                UnderLets.Base fx)) @ x0)
                           | @LetIn _ _ _ _ _ =>
                               UnderLets.Base (#(ListMap) @ (λ x2 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x2);
                                                                                UnderLets.Base fx)) @ x0)
                           | _ =>
                               UnderLets.Base (#(ListMap) @ (λ x1 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x1);
                                                                                UnderLets.Base fx)) @ x0)
                           end
                       end)))
          | @ListApp A =>
              UnderLets.Base
                (fun x : expr var0 (List A) =>
                 UnderLets.Base
                   (fun x0 : expr var0 (List A) =>
                    type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                      (fun a : option (expr var0 (List A) -> expr var0 (List A)) =>
                       match a with
                       | Some tr =>
                           reflect_list_cps (tr x) (UnderLets var0 (expr var0 (List A)))
                             (fun a0 : option (list (expr var0 A)) =>
                              match a0 with
                              | Some xs =>
                                  reflect_list_cps x0 (UnderLets var0 (expr var0 (List A)))
                                    (fun a1 : option (list (expr var0 A)) =>
                                     match a1 with
                                     | Some ys =>
                                         type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                                           (fun a2 : option (expr var0 (List A) -> expr var0 (List A)) =>
                                            match a2 with
                                            | Some tr0 => UnderLets.Base (tr0 (reify_list (xs ++ ys)))
                                            | None => UnderLets.Base (x ++ x0)
                                            end)
                                     | None => UnderLets.Base (x ++ x0)
                                     end)
                              | None => UnderLets.Base (x ++ x0)
                              end)
                       | None => UnderLets.Base (x ++ x0)
                       end)))
          | @ListFlatMap A B =>
              UnderLets.Base
                (fun x : expr var0 A -> UnderLets var0 (expr var0 (List B)) =>
                 UnderLets.Base
                   (fun x0 : expr var0 (List A) =>
                    type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                      (fun a : option (expr var0 (List A) -> expr var0 (List A)) =>
                       match a with
                       | Some tr =>
                           reflect_list_cps (tr x0) (UnderLets var0 (expr var0 (List B)))
                             (fun a0 : option (list (expr var0 A)) =>
                              match a0 with
                              | Some xs =>
                                  (fv <-- (fxs <--- map x xs;
                                           UnderLets.Base
                                             (#(ListFoldRight) @ (λ ls1 ls2 : expr var0 (List B),
                                                                  $ls1 ++ $ls2) @ (λ _ : expr var0 ( ),
                                                                                   []) @ $(reify_list fxs)));
                                   type.try_make_transport_cps (expr value) (let (anyexpr_ty, _) := fv in anyexpr_ty)
                                     (List B)
                                     (fun a1 : option (expr value (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr value (List B)) =>
                                      match a1 with
                                      | Some tr0 =>
                                          match fuel with
                                          | 0 =>
                                              e'' <-- nbe
                                                        (tr0
                                                           (let
                                                              (anyexpr_ty, unwrap) as a2
                                                               return (expr value (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                            unwrap));
                                              UnderLets.Base e''
                                          | Datatypes.S fuel' =>
                                              e'' <-- dorewrite'' fuel' var0 (List B)
                                                        (tr0
                                                           (let
                                                              (anyexpr_ty, unwrap) as a2
                                                               return (expr value (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                            unwrap));
                                              UnderLets.Base e''
                                          end
                                      | None =>
                                          UnderLets.Base
                                            (#(ListFlatMap) @ (λ x1 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x1);
                                                                                  UnderLets.Base fx)) @ x0)
                                      end))%under_lets
                              | None =>
                                  UnderLets.Base
                                    (#(ListFlatMap) @ (λ x1 : var0 A,
                                                       UnderLets.to_expr (fx <-- x ($x1);
                                                                          UnderLets.Base fx)) @ x0)
                              end)
                       | None =>
                           UnderLets.Base (#(ListFlatMap) @ (λ x1 : var0 A,
                                                             UnderLets.to_expr (fx <-- x ($x1);
                                                                                UnderLets.Base fx)) @ x0)
                       end)))
          | @ListRect A P =>
              UnderLets.Base
                (fun x : expr var0 ( ) -> UnderLets var0 (expr var0 P) =>
                 UnderLets.Base
                   (fun
                      x0 : expr var0 A ->
                           UnderLets var0 (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P))) =>
                    UnderLets.Base
                      (fun x1 : expr var0 (List A) =>
                       type.try_make_transport_base_cps
                         (fun x2 : base_type =>
                          expr var0 x2 ->
                          UnderLets var0 (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) A A
                         (fun
                            a : option
                                  ((expr var0 A ->
                                    UnderLets var0 (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) ->
                                   expr var0 A ->
                                   UnderLets var0 (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P))))
                          =>
                          match a with
                          | Some trs =>
                              type.try_make_transport_base_cps
                                (fun A0 : base_type =>
                                 expr var0 A ->
                                 UnderLets var0 (expr var0 (List A0) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) A
                                A
                                (fun
                                   a0 : option
                                          ((expr var0 A ->
                                            UnderLets var0
                                              (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) ->
                                           expr var0 A ->
                                           UnderLets var0
                                             (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) =>
                                 match a0 with
                                 | Some trs0 =>
                                     type.try_make_transport_base_cps
                                       (fun x2 : base_type =>
                                        expr var0 A ->
                                        UnderLets var0
                                          (expr var0 (List A) -> UnderLets var0 (expr var0 x2 -> UnderLets var0 (expr var0 P)))) P P
                                       (fun
                                          a1 : option
                                                 ((expr var0 A ->
                                                   UnderLets var0
                                                     (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) ->
                                                  expr var0 A ->
                                                  UnderLets var0
                                                    (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P))))
                                        =>
                                        match a1 with
                                        | Some trs1 =>
                                            type.try_make_transport_base_cps
                                              (fun x2 : base_type =>
                                               expr var0 A ->
                                               UnderLets var0
                                                 (expr var0 (List A) -> UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 x2))))
                                              P P
                                              (fun
                                                 a2 : option
                                                        ((expr var0 A ->
                                                          UnderLets var0
                                                            (expr var0 (List A) ->
                                                             UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) ->
                                                         expr var0 A ->
                                                         UnderLets var0
                                                           (expr var0 (List A) ->
                                                            UnderLets var0 (expr var0 P -> UnderLets var0 (expr var0 P)))) =>
                                               match a2 with
                                               | Some trd =>
                                                   reflect_list_cps x1 (UnderLets var0 (expr var0 P))
                                                     (fun a3 : option (list (expr var0 A)) =>
                                                      match a3 with
                                                      | Some xs =>
                                                          (fv <-- (v <-- list_rect
                                                                           (fun _ : list (expr var0 A) => UnderLets var0 (expr var0 P))
                                                                           (x ( ))
                                                                           (fun (x' : expr var0 A) (xs' : list (expr var0 A))
                                                                              (rec : UnderLets var0 (expr var0 P)) =>
                                                                            rec0 <-- rec;
                                                                            f <-- (f <-- (fx <-- trd (trs1 (trs0 (trs x0))) x';
                                                                                          UnderLets.Base
                                                                                            (fun (x2 : expr var0 (List A))
                                                                                               (x3 : expr var0 P) =>
                                                                                             f <-- (fx0 <--
                                                                                                    fx x2;
                                                                                                    UnderLets.Base
                                                                                                      (fun x4 : expr var0 P =>
                                                                                                       fx1 <--
                                                                                                       fx0 x4;
                                                                                                       UnderLets.Base fx1));
                                                                                             e1 <-- f x3;
                                                                                             UnderLets.Base e1));
                                                                                   UnderLets.Base (f (reify_list xs')));
                                                                            e1 <-- f rec0;
                                                                            UnderLets.Base e1) xs;
                                                                   UnderLets.Base v);
                                                           type.try_make_transport_cps (expr var0)
                                                             (let (anyexpr_ty, _) := fv in anyexpr_ty) P
                                                             (fun
                                                                a4 : option
                                                                       (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) ->
                                                                        expr var0 P) =>
                                                              match a4 with
                                                              | Some tr =>
                                                                  UnderLets.Base
                                                                    (tr
                                                                       (let
                                                                          (anyexpr_ty, unwrap) as a5
                                                                           return (expr var0 (let (anyexpr_ty, _) := a5 in anyexpr_ty)) :=
                                                                          fv in
                                                                        unwrap))
                                                              | None =>
                                                                  UnderLets.Base
                                                                    (#(ListRect) @
                                                                     (λ x2 : var0 ( )%ctype,
                                                                      UnderLets.to_expr (fx <-- x ($x2);
                                                                                         UnderLets.Base fx)) @
                                                                     (λ x2 : var0 A,
                                                                      UnderLets.to_expr
                                                                        (fx <-- x0 ($x2);
                                                                         UnderLets.Base
                                                                           (λ x3 : var0 (List A),
                                                                            UnderLets.to_expr
                                                                              (fx0 <-- fx ($x3);
                                                                               UnderLets.Base
                                                                                 (λ x4 : var0 P,
                                                                                  UnderLets.to_expr
                                                                                    (fx1 <-- fx0 ($x4);
                                                                                     UnderLets.Base fx1)))))) @ x1)
                                                              end))%under_lets
                                                      | None =>
                                                          UnderLets.Base
                                                            (#(ListRect) @
                                                             (λ x2 : var0 ( )%ctype,
                                                              UnderLets.to_expr (fx <-- x ($x2);
                                                                                 UnderLets.Base fx)) @
                                                             (λ x2 : var0 A,
                                                              UnderLets.to_expr
                                                                (fx <-- x0 ($x2);
                                                                 UnderLets.Base
                                                                   (λ x3 : var0 (List A),
                                                                    UnderLets.to_expr
                                                                      (fx0 <-- fx ($x3);
                                                                       UnderLets.Base
                                                                         (λ x4 : var0 P,
                                                                          UnderLets.to_expr (fx1 <-- fx0 ($x4);
                                                                                             UnderLets.Base fx1)))))) @ x1)
                                                      end)
                                               | None =>
                                                   UnderLets.Base
                                                     (#(ListRect) @
                                                      (λ x2 : var0 ( )%ctype,
                                                       UnderLets.to_expr (fx <-- x ($x2);
                                                                          UnderLets.Base fx)) @
                                                      (λ x2 : var0 A,
                                                       UnderLets.to_expr
                                                         (fx <-- x0 ($x2);
                                                          UnderLets.Base
                                                            (λ x3 : var0 (List A),
                                                             UnderLets.to_expr
                                                               (fx0 <-- fx ($x3);
                                                                UnderLets.Base
                                                                  (λ x4 : var0 P,
                                                                   UnderLets.to_expr (fx1 <-- fx0 ($x4);
                                                                                      UnderLets.Base fx1)))))) @ x1)
                                               end)
                                        | None =>
                                            UnderLets.Base
                                              (#(ListRect) @
                                               (λ x2 : var0 ( )%ctype,
                                                UnderLets.to_expr (fx <-- x ($x2);
                                                                   UnderLets.Base fx)) @
                                               (λ x2 : var0 A,
                                                UnderLets.to_expr
                                                  (fx <-- x0 ($x2);
                                                   UnderLets.Base
                                                     (λ x3 : var0 (List A),
                                                      UnderLets.to_expr
                                                        (fx0 <-- fx ($x3);
                                                         UnderLets.Base
                                                           (λ x4 : var0 P,
                                                            UnderLets.to_expr (fx1 <-- fx0 ($x4);
                                                                               UnderLets.Base fx1)))))) @ x1)
                                        end)
                                 | None =>
                                     UnderLets.Base
                                       (#(ListRect) @ (λ x2 : var0 ( )%ctype,
                                                       UnderLets.to_expr (fx <-- x ($x2);
                                                                          UnderLets.Base fx)) @
                                        (λ x2 : var0 A,
                                         UnderLets.to_expr
                                           (fx <-- x0 ($x2);
                                            UnderLets.Base
                                              (λ x3 : var0 (List A),
                                               UnderLets.to_expr
                                                 (fx0 <-- fx ($x3);
                                                  UnderLets.Base
                                                    (λ x4 : var0 P,
                                                     UnderLets.to_expr (fx1 <-- fx0 ($x4);
                                                                        UnderLets.Base fx1)))))) @ x1)
                                 end)
                          | None =>
                              UnderLets.Base
                                (#(ListRect) @ (λ x2 : var0 ( )%ctype,
                                                UnderLets.to_expr (fx <-- x ($x2);
                                                                   UnderLets.Base fx)) @
                                 (λ x2 : var0 A,
                                  UnderLets.to_expr
                                    (fx <-- x0 ($x2);
                                     UnderLets.Base
                                       (λ x3 : var0 (List A),
                                        UnderLets.to_expr
                                          (fx0 <-- fx ($x3);
                                           UnderLets.Base (λ x4 : var0 P,
                                                           UnderLets.to_expr (fx1 <-- fx0 ($x4);
                                                                              UnderLets.Base fx1)))))) @ x1)
                          end))))
          | @ListFoldRight A B =>
              UnderLets.Base
                (fun x : expr var0 B -> UnderLets var0 (expr var0 A -> UnderLets var0 (expr var0 A)) =>
                 UnderLets.Base
                   (fun x0 : expr var0 ( ) -> UnderLets var0 (expr var0 A) =>
                    UnderLets.Base
                      (fun x1 : expr var0 (List B) =>
                       UnderLets.Base
                         (#(ListFoldRight) @
                          (λ x2 : var0 B,
                           UnderLets.to_expr
                             (fx <-- x ($x2);
                              UnderLets.Base (λ x3 : var0 A,
                                              UnderLets.to_expr (fx0 <-- fx ($x3);
                                                                 UnderLets.Base fx0)))) @
                          (λ x2 : var0 ( )%ctype,
                           UnderLets.to_expr (fx <-- x0 ($x2);
                                              UnderLets.Base fx)) @ x1))))
          | @ListPartition A =>
              UnderLets.Base
                (fun x : expr var0 A -> UnderLets var0 (expr var0 Bool) =>
                 UnderLets.Base
                   (fun x0 : expr var0 (List A) =>
                    type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                      (fun a : option (expr var0 (List A) -> expr var0 (List A)) =>
                       match a with
                       | Some tr =>
                           reflect_list_cps (tr x0) (UnderLets var0 (expr var0 (List A * List A)))
                             (fun a0 : option (list (expr var0 A)) =>
                              match a0 with
                              | Some xs =>
                                  (fv <-- (v <-- list_rect (fun _ : list (expr var0 A) => UnderLets var0 (expr value (List A * List A)))
                                                   (UnderLets.Base ([], []))
                                                   (fun (x1 : expr var0 A) (_ : list (expr var0 A))
                                                      (partition_tl : UnderLets var0 (expr value (List A * List A))) =>
                                                    partition_tl0 <-- partition_tl;
                                                    fx <-- x x1;
                                                    UnderLets.Base
                                                      (#(MatchPair) @
                                                       (λ g d : expr var0 (List A),
                                                        #(BoolRect) @ (λ _ : expr var0 ( ),
                                                                       ($x1 :: $g, $d)) @ (λ _ : expr var0 ( ),
                                                                                           ($g, $x1 :: $d)) @ $fx) @ partition_tl0)) xs;
                                           UnderLets.Base v);
                                   type.try_make_transport_cps (expr value) (let (anyexpr_ty, _) := fv in anyexpr_ty)
                                     (List A * List A)
                                     (fun
                                        a1 : option
                                               (expr value (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr value (List A * List A)) =>
                                      match a1 with
                                      | Some tr0 =>
                                          match fuel with
                                          | 0 =>
                                              e'' <-- nbe
                                                        (tr0
                                                           (let
                                                              (anyexpr_ty, unwrap) as a2
                                                               return (expr value (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                            unwrap));
                                              UnderLets.Base e''
                                          | Datatypes.S fuel' =>
                                              e'' <-- dorewrite'' fuel' var0 (List A * List A)%ctype
                                                        (tr0
                                                           (let
                                                              (anyexpr_ty, unwrap) as a2
                                                               return (expr value (let (anyexpr_ty, _) := a2 in anyexpr_ty)) := fv in
                                                            unwrap));
                                              UnderLets.Base e''
                                          end
                                      | None =>
                                          UnderLets.Base
                                            (#(ListPartition) @ (λ x1 : var0 A,
                                                                 UnderLets.to_expr (fx <-- x ($x1);
                                                                                    UnderLets.Base fx)) @ x0)
                                      end))%under_lets
                              | None =>
                                  UnderLets.Base
                                    (#(ListPartition) @ (λ x1 : var0 A,
                                                         UnderLets.to_expr (fx <-- x ($x1);
                                                                            UnderLets.Base fx)) @ x0)
                              end)
                       | None =>
                           UnderLets.Base (#(ListPartition) @ (λ x1 : var0 A,
                                                               UnderLets.to_expr (fx <-- x ($x1);
                                                                                  UnderLets.Base fx)) @ x0)
                       end)))
          | TT => UnderLets.Base ( )
          | iTrue => UnderLets.Base #(iTrue)
          | iFalse => UnderLets.Base #(iFalse)
          | @BoolRect P =>
              UnderLets.Base
                (fun x : expr var0 ( ) -> UnderLets var0 (expr var0 P) =>
                 UnderLets.Base
                   (fun x0 : expr var0 ( ) -> UnderLets var0 (expr var0 P) =>
                    UnderLets.Base
                      (fun x1 : expr var0 Bool =>
                       match x1 with
                       | #(iTrue) =>
                           (fv <-- (e1 <-- x ( );
                                    UnderLets.Base e1);
                            type.try_make_transport_cps (expr var0) (let (anyexpr_ty, _) := fv in anyexpr_ty) P
                              (fun a : option (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr var0 P) =>
                               match a with
                               | Some tr =>
                                   UnderLets.Base
                                     (tr
                                        (let (anyexpr_ty, unwrap) as a0 return (expr var0 (let (anyexpr_ty, _) := a0 in anyexpr_ty)) :=
                                           fv in
                                         unwrap))
                               | None =>
                                   UnderLets.Base
                                     (#(BoolRect) @ (λ x2 : var0 ( )%ctype,
                                                     UnderLets.to_expr (fx <-- x ($x2);
                                                                        UnderLets.Base fx)) @
                                      (λ x2 : var0 ( )%ctype,
                                       UnderLets.to_expr (fx <-- x0 ($x2);
                                                          UnderLets.Base fx)) @ x1)
                               end))%under_lets
                       | #(iFalse) =>
                           (fv <-- (e1 <-- x0 ( );
                                    UnderLets.Base e1);
                            type.try_make_transport_cps (expr var0) (let (anyexpr_ty, _) := fv in anyexpr_ty) P
                              (fun a : option (expr var0 (let (anyexpr_ty, _) := fv in anyexpr_ty) -> expr var0 P) =>
                               match a with
                               | Some tr =>
                                   UnderLets.Base
                                     (tr
                                        (let (anyexpr_ty, unwrap) as a0 return (expr var0 (let (anyexpr_ty, _) := a0 in anyexpr_ty)) :=
                                           fv in
                                         unwrap))
                               | None =>
                                   UnderLets.Base
                                     (#(BoolRect) @ (λ x2 : var0 ( )%ctype,
                                                     UnderLets.to_expr (fx <-- x ($x2);
                                                                        UnderLets.Base fx)) @
                                      (λ x2 : var0 ( )%ctype,
                                       UnderLets.to_expr (fx <-- x0 ($x2);
                                                          UnderLets.Base fx)) @ x1)
                               end))%under_lets
                       | _ @ _ | @LetIn _ _ _ _ _ =>
                           UnderLets.Base
                             (#(BoolRect) @ (λ x3 : var0 ( )%ctype,
                                             UnderLets.to_expr (fx <-- x ($x3);
                                                                UnderLets.Base fx)) @
                              (λ x3 : var0 ( )%ctype,
                               UnderLets.to_expr (fx <-- x0 ($x3);
                                                  UnderLets.Base fx)) @ x1)
                       | _ =>
                           UnderLets.Base
                             (#(BoolRect) @ (λ x2 : var0 ( )%ctype,
                                             UnderLets.to_expr (fx <-- x ($x2);
                                                                UnderLets.Base fx)) @
                              (λ x2 : var0 ( )%ctype,
                               UnderLets.to_expr (fx <-- x0 ($x2);
                                                  UnderLets.Base fx)) @ x1)
                       end)))
          | Literal n => UnderLets.Base ##(n)
          end
      | @App _ s d f x => (f0 <-- dorewrite' (s -> d)%ctype f;
                           x0 <-- dorewrite' s x;
                           f0 x0)%under_lets
      | @LetIn _ A B x f => (x0 <-- dorewrite' A x;
                             UnderLet (reify x0) (fun xv : var0 A => dorewrite' B (f (reflect ($xv)))))%under_lets
      end) t e) default_fuel var
     : forall (var : type -> Type) (t : type), expr value t -> UnderLets var (value t)

Arguments var, t are implicit and maximally inserted
Argument scopes are [function_scope ctype_scope expr_scope]
*)
Timeout 10 Time Compute dorewrite (#ListPartition @ (λ x, #NatEqb @ $x @ ##1) @ [##0; ##1; ##1; ##2])%expr.
