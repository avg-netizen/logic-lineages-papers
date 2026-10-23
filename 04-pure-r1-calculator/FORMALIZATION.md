# Lean proof coverage

The project pins Lean `v4.32.0-rc1` and Mathlib commit
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. Its definitions are in namespace
`R1Calculator`. The modules compile with no admitted proofs or custom axioms.

| Module | Kernel-checked content |
|---|---|
| [Ordinal.lean](lean/R1Calculator/Ordinal.lean) | Structural `lastExponent`, compressed `principalSum`, executable `endpoint` and normal-input `endpointNF`; preservation of normality; ordered principal-summand expansion; equality of the compressed computation's genuine `Ordinal.repr` with the expanded endpoint recursion; the arithmetic interval checker and its ordinal-inequality specification. |
| [Patterns.lean](lean/R1Calculator/Patterns.lean) | Raw Boolean finite tables and optional typed marker; executable validity checks equivalent to strict-upper, nesting, transitivity and respect laws; checked construction; reflexive-closure order laws; covering and induced-map checkers; identities, composition and marker preservation; complete finite existence searches and their correctness; explicit covering-without-induced-embedding and invalid-input examples. |
| [Examples.lean](lean/R1Calculator/Examples.lean) | Executable endpoint, coefficient-order and finite-pattern examples. These supplement the general proofs; they are not their justification. |

Principal arithmetic declarations include `lastExponent_nf`, `principalSum_nf`,
`endpoint_nf`, `principalSummands_repr`, `principalSum_repr`,
`endpoint_recursion`, `endpointNF_recursion`, `repr_le_endpoint` and
`intervalCheck_correct`.

Principal finite-pattern declarations include
`PatternData.check_eq_true_iff_valid`, `validatePattern_isSome_iff_valid`,
`PatternData.checkCovering_eq_true`, `PatternData.checkInduced_eq_true`,
`Covering.comp`, `InducedEmbedding.comp`, `preservesMarker_comp`,
`coversCheck_eq_true`, `embedsCheck_eq_true` and
`markedCoversCheck_eq_true`. Lean's finite existence search enumerates finite
functions and filters them. Python enumerates increasing image lists; no
cross-language refinement or efficiency equivalence is claimed.

The compiled modules print axiom dependencies for the principal results.
They use only Lean/Mathlib's standard foundational declarations
`propext`, `Classical.choice` and `Quot.sound`, with individual theorems often
using fewer. There is no `sorryAx`, added semantic axiom or `native_decide`
substitute for these general proofs. The exact build evidence is in
[VERIFICATION.md](VERIFICATION.md).

Carlson's semantic theorem is outside this formalization. In particular,
`intervalCheck` implements the arithmetic interval; interpreting it as recursive
Sigma-one elementarity uses the cited mathematical characterization. The
development does not construct the semantic proper-class structure or formally
prove its characterization here. Nor does it prove a formal refinement of the
Python parser/interpreter, the general pattern-count formulas, minimum ordinal
realizations, the paper's expanded-tree norm theorem, a running-time bound, or
an order-two ordinal assignment.
