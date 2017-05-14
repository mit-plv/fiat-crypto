Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Crypto.Compilers.Z.HexNotationConstants.
Require Export Crypto.Util.Notations.

Reserved Notation "T x = A ; b" (at level 200, b at level 200, format "T  x  =  A ; '//' b").
Reserved Notation "T x = A ; 'return' b" (at level 200, b at level 200, format "T  x  =  A ; '//' 'return'  b").
Reserved Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T  x  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "T0 x , T1 y = A ; b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' b").
Reserved Notation "T0 x , T1 y = A ; 'return' b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  b").
Reserved Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "v == 0 ? a : b" (at level 40, a at level 10, b at level 10).
Reserved Notation "x & y" (at level 40).

Global Open Scope expr_scope.

Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b)) : expr_scope.
Notation "T x = A ; 'return' b" := (LetIn (tx:=T) A (fun x => Var b)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair b0%expr b1%expr) .. b2%expr)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair (Var b0) (Var b1)) .. (Var b2))) : expr_scope.
Notation "T0 x , T1 y = A ; b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => b)) : expr_scope.
Notation "T0 x , T1 y = A ; 'return' b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => Var b)) : expr_scope.
(*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair b0%expr b1%expr) .. b2%expr))) : expr_scope.*) (* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *)
(*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair (Var b0) (Var b1)) .. (Var b2)))) : expr_scope.*) (* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *)
(* python:
<<
#!/usr/bin/env python
# -*- coding: utf-8 -*-
types = ('bool', 'uint8_t', 'uint8_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'uint128_t', 'uint256_t')
for lgwordsz in range(0, len(types)):
    print('Notation "\'%s\'" := (Tbase (TWord %d)).' % (types[lgwordsz], lgwordsz))
print('Notation ℤ := (Tbase TZ).')
print('')
cast_pat = "'(%s)' %s"
def at_least_S_pattern(n):
    return '(S ' * n + '_' + ')' * n
for opn, op, lvl in (('*', 'Mul', 40), ('+', 'Add', 50), ('-', 'Sub', 50)):
    for v1 in (False, True):
        for v2 in (False, True):
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "x %s y" := (Op (%s _ _ _) (Pair %s %s)).' % (opn, op, lhs, rhs))
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "%s %s %s" := (Op (%s (TWord _) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (cast_pat % (types[lgwordsz], 'x'), opn, 'y',
                         op, lgwordsz, lhs, rhs, lvl))
                print('Notation "%s %s %s" := (Op (%s (TWord _) (TWord %s) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % ('x', opn, cast_pat % (types[lgwordsz], 'y'),
                         op, at_least_S_pattern(lgwordsz), lgwordsz, lhs, rhs, lvl))
                print('Notation "%s %s %s" := (Op (%s (TWord %s) (TWord %s) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (cast_pat % (types[lgwordsz], 'x'), opn, cast_pat % (types[lgwordsz], 'y'),
                         op, at_least_S_pattern(lgwordsz), at_least_S_pattern(lgwordsz), lgwordsz, lhs, rhs, lvl))
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "x %s y" := (Op (%s (TWord %d) (TWord _) (TWord %d)) (Pair %s %s)).'
                      % (opn,
                         op, lgwordsz, lgwordsz, lhs, rhs))
                print('Notation "x %s y" := (Op (%s (TWord _) (TWord %d) (TWord %d)) (Pair %s %s)).'
                      % (opn,
                         op, lgwordsz, lgwordsz, lhs, rhs))
                print('Notation "%s %s %s" := (Op (%s (TWord %d) (TWord %s) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % ('x', opn, cast_pat % (types[lgwordsz], 'y'),
                         op, lgwordsz, at_least_S_pattern(lgwordsz), lgwordsz, lhs, rhs, lvl))
                print('Notation "%s %s %s" := (Op (%s (TWord %s) (TWord %d) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (cast_pat % (types[lgwordsz], 'x'), opn, 'y',
                         op, at_least_S_pattern(lgwordsz), lgwordsz, lgwordsz, lhs, rhs, lvl))
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "x %s y" := (Op (%s (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)).'
                      % (opn, op, lgwordsz, lgwordsz, lgwordsz, lhs, rhs))
for opn, op, lvl in (('&', 'Land', 40),):
    for v1 in (False, True):
        for v2 in (False, True):
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "x %s y" := (Op (%s _ _ _) (Pair %s %s)).' % (opn, op, lhs, rhs))
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "%s %s %s" := (Op (%s (TWord _) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (cast_pat % (types[lgwordsz], 'x'), opn, cast_pat % (types[lgwordsz], 'y'),
                         op, lgwordsz, lhs, rhs, lvl))
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "%s %s %s" := (Op (%s (TWord %d) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % ('x', opn, cast_pat % (types[lgwordsz], 'y'),
                         op, lgwordsz, lgwordsz, lhs, rhs, lvl))
                print('Notation "%s %s %s" := (Op (%s (TWord _) (TWord %d) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (cast_pat % (types[lgwordsz], 'x'), opn, 'y',
                         op, lgwordsz, lgwordsz, lhs, rhs, lvl))
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "x %s y" := (Op (%s (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)).'
                      % (opn, op, lgwordsz, lgwordsz, lgwordsz, lhs, rhs))
for opn, op, lvl in (('<<', 'Shl', 30),):
    for v1 in (False, True):
        for v2 in (False, True):
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "x %s y" := (Op (%s _ _ _) (Pair %s %s)).' % (opn, op, lhs, rhs))
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "\'(%s)\' x %s y" := (Op (%s (TWord _) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (types[lgwordsz], opn, op, lgwordsz, lhs, rhs, lvl))
                print('Notation "x %s y" := (Op (%s (TWord %d) (TWord _) (TWord %d)) (Pair %s %s)).'
                      % (opn, op, lgwordsz, lgwordsz, lhs, rhs))
for opn, op, lvl in (('>>', 'Shr', 30),):
    for v1 in (False, True):
        for v2 in (False, True):
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "x %s y" := (Op (%s _ _ _) (Pair %s %s)).' % (opn, op, lhs, rhs))
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "\'(%s)\' ( x %s y )" := (Op (%s (TWord _) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d).'
                      % (types[lgwordsz], opn, op, lgwordsz, lhs, rhs, lvl))
                print('Notation "x %s y" := (Op (%s (TWord %d) (TWord _) (TWord %d)) (Pair %s %s)).'
                      % (opn, op, lgwordsz, lgwordsz, lhs, rhs))
for v0 in (False, True):
    for v1 in (False, True):
        for v2 in (False, True):
            tes = ('v' if not v0 else '(Var v)')
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair %s %s) %s)).' % (tes, lhs, rhs))
for lgwordsz in range(0, len(types)):
    for v0 in (False, True):
        for v1 in (False, True):
            for v2 in (False, True):
                tes = ('v' if not v0 else '(Var v)')
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "\'(%s)\' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord %d)) (Pair (Pair %s %s) %s)) (at level 40, x at level 10, y at level 10).' % (types[lgwordsz], lgwordsz, tes, lhs, rhs))
                print('Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord %d) (TWord %d) (TWord %d)) (Pair (Pair %s %s) %s)).' % (lgwordsz, lgwordsz, lgwordsz, tes, lhs, rhs))
print('Notation Return x := (Var x).')
print('Notation C_like := (Expr base_type op _).')
>> *)
Notation "'bool'" := (Tbase (TWord 0)).
Notation "'uint8_t'" := (Tbase (TWord 1)).
Notation "'uint8_t'" := (Tbase (TWord 2)).
Notation "'uint8_t'" := (Tbase (TWord 3)).
Notation "'uint16_t'" := (Tbase (TWord 4)).
Notation "'uint32_t'" := (Tbase (TWord 5)).
Notation "'uint64_t'" := (Tbase (TWord 6)).
Notation "'uint128_t'" := (Tbase (TWord 7)).
Notation "'uint256_t'" := (Tbase (TWord 8)).
Notation ℤ := (Tbase TZ).

Notation "x * y" := (Op (Mul _ _ _) (Pair x y)).
Notation "x * y" := (Op (Mul _ _ _) (Pair x (Var y))).
Notation "x * y" := (Op (Mul _ _ _) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "'(bool)' x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "'(bool)' x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "'(bool)' x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(bool)' x * '(bool)' y" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x * '(bool)' y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x * '(bool)' y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x * '(bool)' y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x * '(bool)' y" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(bool)' x * y" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * '(uint8_t)' y" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x * '(uint8_t)' y" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x * y" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 40).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40).
Notation "'(uint16_t)' x * '(uint16_t)' y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "'(uint16_t)' x * '(uint16_t)' y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "'(uint16_t)' x * '(uint16_t)' y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint16_t)' x * '(uint16_t)' y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x * '(uint16_t)' y" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint16_t)' x * y" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 40).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40).
Notation "'(uint32_t)' x * '(uint32_t)' y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "'(uint32_t)' x * '(uint32_t)' y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "'(uint32_t)' x * '(uint32_t)' y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint32_t)' x * '(uint32_t)' y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x * '(uint32_t)' y" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint32_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 40).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40).
Notation "'(uint64_t)' x * '(uint64_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "'(uint64_t)' x * '(uint64_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "'(uint64_t)' x * '(uint64_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint64_t)' x * '(uint64_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x * '(uint64_t)' y" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint64_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 40).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40).
Notation "'(uint128_t)' x * '(uint128_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "'(uint128_t)' x * '(uint128_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "'(uint128_t)' x * '(uint128_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint128_t)' x * '(uint128_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x * '(uint128_t)' y" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint128_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 40).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40).
Notation "'(uint256_t)' x * '(uint256_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "'(uint256_t)' x * '(uint256_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "'(uint256_t)' x * '(uint256_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint256_t)' x * '(uint256_t)' y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "x * y" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x * '(uint256_t)' y" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint256_t)' x * y" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "x * y" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x * y" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x * y" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add _ _ _) (Pair x y)).
Notation "x + y" := (Op (Add _ _ _) (Pair x (Var y))).
Notation "x + y" := (Op (Add _ _ _) (Pair (Var x) y)).
Notation "x + y" := (Op (Add _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(bool)' x + '(bool)' y" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x + '(bool)' y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x + '(bool)' y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x + '(bool)' y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x + '(bool)' y" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(bool)' x + y" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + '(uint8_t)' y" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x + '(uint8_t)' y" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x + y" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 50).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x + '(uint16_t)' y" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x + '(uint16_t)' y" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x + '(uint16_t)' y" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint16_t)' x + '(uint16_t)' y" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x + '(uint16_t)' y" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint16_t)' x + y" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 50).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x + '(uint32_t)' y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x + '(uint32_t)' y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x + '(uint32_t)' y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint32_t)' x + '(uint32_t)' y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x + '(uint32_t)' y" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint32_t)' x + y" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 50).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x + '(uint64_t)' y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x + '(uint64_t)' y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x + '(uint64_t)' y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint64_t)' x + '(uint64_t)' y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x + '(uint64_t)' y" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint64_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 50).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x + '(uint128_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x + '(uint128_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x + '(uint128_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint128_t)' x + '(uint128_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x + '(uint128_t)' y" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint128_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 50).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x + '(uint256_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x + '(uint256_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x + '(uint256_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint256_t)' x + '(uint256_t)' y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "x + y" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x + y" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x + '(uint256_t)' y" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint256_t)' x + y" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x + y" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x + y" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x + y" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x + y" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub _ _ _) (Pair x y)).
Notation "x - y" := (Op (Sub _ _ _) (Pair x (Var y))).
Notation "x - y" := (Op (Sub _ _ _) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(bool)' x - '(bool)' y" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x - '(bool)' y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x - '(bool)' y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x - '(bool)' y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "x - '(bool)' y" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(bool)' x - y" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - '(uint8_t)' y" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "x - '(uint8_t)' y" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint8_t)' x - y" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 50).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x - '(uint16_t)' y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x - '(uint16_t)' y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x - '(uint16_t)' y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint16_t)' x - '(uint16_t)' y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "x - '(uint16_t)' y" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint16_t)' x - y" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 50).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x - '(uint32_t)' y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x - '(uint32_t)' y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x - '(uint32_t)' y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint32_t)' x - '(uint32_t)' y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "x - '(uint32_t)' y" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint32_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 50).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x - '(uint64_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x - '(uint64_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x - '(uint64_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint64_t)' x - '(uint64_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "x - '(uint64_t)' y" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint64_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 50).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x - '(uint128_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x - '(uint128_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x - '(uint128_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint128_t)' x - '(uint128_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "x - '(uint128_t)' y" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint128_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 50).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x - '(uint256_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x - '(uint256_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x - '(uint256_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint256_t)' x - '(uint256_t)' y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 50).
Notation "x - y" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x - '(uint256_t)' y" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "'(uint256_t)' x - y" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 50).
Notation "x - y" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x - y" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x - y" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x & y" := (Op (Land _ _ _) (Pair x y)).
Notation "x & y" := (Op (Land _ _ _) (Pair x (Var y))).
Notation "x & y" := (Op (Land _ _ _) (Pair (Var x) y)).
Notation "x & y" := (Op (Land _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' x & '(bool)' y" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "'(bool)' x & '(bool)' y" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "'(bool)' x & '(bool)' y" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "'(bool)' x & '(bool)' y" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(bool)' y" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 40).
Notation "'(bool)' x & y" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 40).
Notation "x & '(bool)' y" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "'(bool)' x & y" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 40).
Notation "x & '(bool)' y" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "'(bool)' x & y" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 40).
Notation "x & '(bool)' y" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(bool)' x & y" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & '(uint8_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint8_t)' y" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint8_t)' x & y" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' x & '(uint16_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 40).
Notation "'(uint16_t)' x & '(uint16_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "'(uint16_t)' x & '(uint16_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "'(uint16_t)' x & '(uint16_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint16_t)' y" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (at level 40).
Notation "'(uint16_t)' x & y" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (at level 40).
Notation "x & '(uint16_t)' y" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "'(uint16_t)' x & y" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint16_t)' y" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "'(uint16_t)' x & y" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint16_t)' y" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint16_t)' x & y" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' x & '(uint32_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 40).
Notation "'(uint32_t)' x & '(uint32_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "'(uint32_t)' x & '(uint32_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "'(uint32_t)' x & '(uint32_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint32_t)' y" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (at level 40).
Notation "'(uint32_t)' x & y" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (at level 40).
Notation "x & '(uint32_t)' y" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "'(uint32_t)' x & y" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint32_t)' y" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "'(uint32_t)' x & y" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint32_t)' y" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint32_t)' x & y" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' x & '(uint64_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 40).
Notation "'(uint64_t)' x & '(uint64_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "'(uint64_t)' x & '(uint64_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "'(uint64_t)' x & '(uint64_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint64_t)' y" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (at level 40).
Notation "'(uint64_t)' x & y" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (at level 40).
Notation "x & '(uint64_t)' y" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "'(uint64_t)' x & y" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint64_t)' y" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "'(uint64_t)' x & y" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint64_t)' y" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint64_t)' x & y" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' x & '(uint128_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 40).
Notation "'(uint128_t)' x & '(uint128_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "'(uint128_t)' x & '(uint128_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "'(uint128_t)' x & '(uint128_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint128_t)' y" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (at level 40).
Notation "'(uint128_t)' x & y" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (at level 40).
Notation "x & '(uint128_t)' y" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "'(uint128_t)' x & y" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint128_t)' y" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "'(uint128_t)' x & y" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint128_t)' y" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint128_t)' x & y" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' x & '(uint256_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 40).
Notation "'(uint256_t)' x & '(uint256_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "'(uint256_t)' x & '(uint256_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "'(uint256_t)' x & '(uint256_t)' y" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & '(uint256_t)' y" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (at level 40).
Notation "'(uint256_t)' x & y" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (at level 40).
Notation "x & '(uint256_t)' y" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "'(uint256_t)' x & y" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 40).
Notation "x & '(uint256_t)' y" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "'(uint256_t)' x & y" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 40).
Notation "x & '(uint256_t)' y" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "'(uint256_t)' x & y" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 40).
Notation "x & y" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair x y)).
Notation "x & y" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))).
Notation "x & y" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)).
Notation "x & y" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x << y" := (Op (Shl _ _ _) (Pair x y)).
Notation "x << y" := (Op (Shl _ _ _) (Pair x (Var y))).
Notation "x << y" := (Op (Shl _ _ _) (Pair (Var x) y)).
Notation "x << y" := (Op (Shl _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair x y)).
Notation "'(bool)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))).
Notation "'(bool)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)).
Notation "'(bool)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair x y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair x y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair x y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)).
Notation "'(uint8_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair x y)).
Notation "'(uint16_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))).
Notation "'(uint16_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)).
Notation "'(uint16_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair x y)).
Notation "'(uint32_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))).
Notation "'(uint32_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)).
Notation "'(uint32_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair x y)).
Notation "'(uint64_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))).
Notation "'(uint64_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)).
Notation "'(uint64_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair x y)).
Notation "'(uint128_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))).
Notation "'(uint128_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)).
Notation "'(uint128_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair x y)).
Notation "'(uint256_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))).
Notation "'(uint256_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 30).
Notation "x << y" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)).
Notation "'(uint256_t)' x << y" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 30).
Notation "x << y" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))).
Notation "x >> y" := (Op (Shr _ _ _) (Pair x y)).
Notation "x >> y" := (Op (Shr _ _ _) (Pair x (Var y))).
Notation "x >> y" := (Op (Shr _ _ _) (Pair (Var x) y)).
Notation "x >> y" := (Op (Shr _ _ _) (Pair (Var x) (Var y))).
Notation "'(bool)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair x y)).
Notation "'(bool)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))).
Notation "'(bool)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)).
Notation "'(bool)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair x y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair x y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair x y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)).
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))).
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair x y)).
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))).
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)).
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))).
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair x y)).
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))).
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)).
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))).
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair x y)).
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))).
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)).
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))).
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair x y)).
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))).
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)).
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))).
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair x y)).
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))).
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)).
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 30).
Notation "x >> y" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair v x) y)).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair v x) (Var y))).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair v (Var x)) y)).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair v (Var x)) (Var y))).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair (Var v) x) y)).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair (Var v) x) (Var y))).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair (Var v) (Var x)) y)).
Notation "v == 0 ? x : y" := (Op (Zselect _ _ _ _) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair v x) y)).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair v x) (Var y))).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair v (Var x)) y)).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair (Var v) x) y)).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(bool)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 0)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 0) (TWord 0) (TWord 0)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair v x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair v x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair v (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair (Var v) x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 1)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 1) (TWord 1) (TWord 1)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair v x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair v x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair v (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair (Var v) x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 2)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 2) (TWord 2) (TWord 2)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair v x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair v x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair v (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair (Var v) x) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint8_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 3)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 3) (TWord 3) (TWord 3)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair v x) y)).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair v x) (Var y))).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair v (Var x)) y)).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair (Var v) x) y)).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint16_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 4)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 4) (TWord 4) (TWord 4)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair v x) y)).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair v x) (Var y))).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair v (Var x)) y)).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair (Var v) x) y)).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint32_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 5)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 5) (TWord 5) (TWord 5)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair v x) y)).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair v x) (Var y))).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair v (Var x)) y)).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair (Var v) x) y)).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint64_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 6)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 6) (TWord 6) (TWord 6)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair v x) y)).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair v x) (Var y))).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair v (Var x)) y)).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair (Var v) x) y)).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint128_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 7)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 7) (TWord 7) (TWord 7)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair v x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair v x) y)).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair v x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair v x) (Var y))).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair v (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair v (Var x)) y)).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair v (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair v (Var x)) (Var y))).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair (Var v) x) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair (Var v) x) y)).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair (Var v) x) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair (Var v) x) (Var y))).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair (Var v) (Var x)) y)) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair (Var v) (Var x)) y)).
Notation "'(uint256_t)' ( v == 0 ? x : y )" := (Op (Zselect _ (TWord _) (TWord _) (TWord 8)) (Pair (Pair (Var v) (Var x)) (Var y))) (at level 40, x at level 10, y at level 10).
Notation "v == 0 ? x : y" := (Op (Zselect _ (TWord 8) (TWord 8) (TWord 8)) (Pair (Pair (Var v) (Var x)) (Var y))).
Notation Return x := (Var x).
Notation C_like := (Expr base_type op _).
