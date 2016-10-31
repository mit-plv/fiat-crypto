#!/usr/bin/env python2.7
from __future__ import with_statement

for name, opkind in ([(name, 'binop') for name in ('Add', 'Carry_Add', 'Sub', 'Carry_Sub', 'Mul')]
                     + [('Opp', 'unop'), ('Carry_Opp', 'unop'), ('Freeze', 'unop'),
                        ('Ge_Modulus', 'unop_FEToZ'), ('Pack', 'unop_FEToWire'), ('Unpack', 'unop_WireToFE')]):
    lname = name.lower()
    with open(name.replace('_', '') + '.v', 'w') as f:
        f.write(r"""Require Import Crypto.Specific.GF25519Reflective.Common.

Definition r%(lname)sZ_sig : rexpr_%(opkind)s_sig %(lname)s. Proof. reify_sig. Defined.
Definition r%(lname)sW := Eval vm_compute in rword_of_Z r%(lname)sZ_sig.
Lemma r%(lname)sW_correct_and_bounded_gen : correct_and_bounded_genT r%(lname)sW r%(lname)sZ_sig.
Proof. rexpr_correct. Qed.
""" % locals())
