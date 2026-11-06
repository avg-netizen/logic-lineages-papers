# Renaming original finite derivations

Baseline: `053dd246327f00a5ede8040182e2de5d0fb455b8`. The paper06
internal arithmetic development needs reindexing of free parameters and fresh
variables to use the original finite existential compiler blocks. The existing
calculus has one-variable rules, but no proved whole-proof renaming operation.
Literal syntax identities alone do not provide a transformed Derivation.

Four exact targets preserve original syntax: arbitrary predicate replacement
(invariants need not be positive), expanded-language PA induction, both
one-body fixed-point schemas, and admissibility for every finite Derivation.
The latter retains the original proof premise and constructs a proof using
ONLY the existing constructors. The body is fixed and unchanged. Noninjective
free-variable maps are permitted; bound variables remain distinct through the
original lifted Sum.map renaming and eigenvariable rules.

This is a proof-transform supplier for later finite-block elimination and
original graph composition. It is NOT a new renaming rule, arithmetic
reflection, PR recursion representability, encoded typed-preservation,
application compatibility, C_tau closure, all-term accessibility, II5 or whole
lem:id1. No missing theorem is assumed or imported from a different calculus.
No existing target/rule/source, manuscript, register, checker, dependency,
root import or CI change. Exact targets precede candidate proof.
