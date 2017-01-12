#!/usr/bin/env python2.7
from __future__ import with_statement

for name, opkind in ([(name, 'BinOp') for name in ('Add', 'Carry_Add', 'Sub', 'Carry_Sub', 'Mul')]
                     + [(name, 'UnOp') for name in ('Opp', 'Carry_Opp', 'PreFreeze')]
                     + [('Ge_Modulus', 'UnOp_FEToZ'), ('Pack', 'UnOp_FEToWire'), ('Unpack', 'UnOp_WireToFE')]):
    lname = name.lower()
    lopkind = opkind.replace('UnOp', 'unop').replace('BinOp', 'binop')
    uopkind = opkind.replace('_', '')
    extra = ''
    #if name in ('Carry_Add', 'Carry_Sub', 'Mul', 'Carry_Opp', 'Pack', 'Unpack', 'Ge_Modulus', 'PreFreeze'):
    extra = r"""Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition r%(lname)sZ_correct_and_bounded
  := rexpr_correct_and_bounded r%(lname)sZ r%(lname)sZ_Wf Expr%(uopkind)s_bounds.
""" % locals()
    with open(name.replace('_', '') + '.v', 'w') as f:
        f.write(r"""Require Import Crypto.Specific.GF25519Reflective.Common.

Definition r%(lname)sZ_sig : rexpr_%(lopkind)s_sig %(lname)s. Proof. reify_sig. Defined.
Definition r%(lname)sZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig r%(lname)sZ_sig.
Definition r%(lname)sW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes r%(lname)sZ Expr%(uopkind)s_bounds.
Definition r%(lname)sZ_Wf : rexpr_wfT r%(lname)sZ. Proof. prove_rexpr_wfT. Qed.
Definition r%(lname)s_output_bounds
  := Eval vm_compute in compute_bounds r%(lname)sZ Expr%(uopkind)s_bounds.
%(extra)s
Local Open Scope string_scope.
Compute ("%(name)s", compute_bounds_for_display r%(lname)sZ Expr%(uopkind)s_bounds).
Compute ("%(name)s overflows? ", sanity_compute r%(lname)sZ Expr%(uopkind)s_bounds).
Compute ("%(name)s overflows (error if it does)? ", sanity_check r%(lname)sZ Expr%(uopkind)s_bounds).
""" % locals())
