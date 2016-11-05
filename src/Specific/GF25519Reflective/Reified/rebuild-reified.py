#!/usr/bin/env python2.7
from __future__ import with_statement

for name, opkind in ([(name, 'BinOp') for name in ('Add', 'Carry_Add', 'Sub', 'Carry_Sub', 'Mul')]
                     + [(name, 'UnOp') for name in ('Opp', 'Carry_Opp', 'Freeze')]
                     + [('Ge_Modulus', 'UnOp_FEToZ'), ('Pack', 'UnOp_FEToWire'), ('Unpack', 'UnOp_WireToFE')]):
    lname = name.lower()
    lopkind = opkind.replace('UnOp', 'unop').replace('BinOp', 'binop')
    uopkind = opkind.replace('_', '')
    with open(name.replace('_', '') + '.v', 'w') as f:
        f.write(r"""Require Import Crypto.Specific.GF25519Reflective.Common.

Definition r%(lname)sZ_sig : rexpr_%(lopkind)s_sig %(lname)s. Proof. reify_sig. Defined.
Definition r%(lname)sW := Eval vm_compute in rword_of_Z r%(lname)sZ_sig.
Lemma r%(lname)sW_correct_and_bounded_gen : correct_and_bounded_genT r%(lname)sW r%(lname)sZ_sig.
Proof. rexpr_correct. Qed.
Definition r%(lname)s_output_bounds := Eval vm_compute in compute_bounds r%(lname)sW Expr%(uopkind)s_bounds.

Local Open Scope string_scope.
Compute ("%(name)s", compute_bounds_for_display r%(lname)sW Expr%(uopkind)s_bounds).
(*Compute ("%(name)s overflows? ", sanity_check r%(lname)sW Expr%(uopkind)s_bounds).*)
""" % locals())
