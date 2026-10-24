# Lean proof coverage

The semantic endpoint characterization is proved here, from the constructed
single-relation Sigma-one semantics. Its correctness is not supplied as an
axiom, typeclass field, oracle or hypothesis.

The central declaration in [Correctness.lean](lean/R1Calculator/Correctness.lean)
is `R1Calculator.PureR1.endpoint_semantic`:

```lean
(a : NONote) (β : Ordinal.{0}) :
  PureR1.R1 a.repr β ↔ a.repr ≤ β ∧ β ≤ (endpointNF a).repr
```

Here `NONote` carries a normal hereditary Cantor notation. The right endpoint
`β` is an arbitrary actual ordinal, not a notation-only or finite test input.
`endpoint_isGreatest` proves that the returned endpoint is the greatest such
ordinal. `intervalCheck_iff_R1` and `intervalCheck_iff_sigma1` connect the
executable Lean checker to the actual recursively defined relation and its
initial-segment Sigma-one equation.

## Proof structure

| Modules | Kernel-checked content |
|---|---|
| [Semantics](lean/R1Calculator/Semantics.lean), [SemanticBasics](lean/R1Calculator/SemanticBasics.lean) | Boolean quantifier-free formulas over equality, order and one resemblance relation; arbitrary finite existential blocks; upper-ordinal well-founded construction of actual R1; global semantic equation; recursive uniqueness; transitivity, interval laws and basic exclusions. |
| [FiniteDiagrams](lean/R1Calculator/FiniteDiagrams.lean) | Carlson's finite induced-copy criterion in both directions, including negative atoms, fixed parameters, duplicates and empty cases. It is instantiated with the actual constructed relation. |
| [Ordinal](lean/R1Calculator/Ordinal.lean), [ArithmeticBounds](lean/R1Calculator/ArithmeticBounds.lean), [ArithmeticLaws](lean/R1Calculator/ArithmeticLaws.lean), [EndpointClosure](lean/R1Calculator/EndpointClosure.lean) | Normality and actual ordinal denotation of compressed arithmetic; P-additivity and strict monotonicity; translation and principal-block bounds; rounding and nested endpoint intervals. |
| [NotationCoverage](lean/R1Calculator/NotationCoverage.lean) | Every actual ordinal below a normal notation has a normal notation; coherent order isomorphism onto the entire actual initial segment. No epsilon-zero range assumption is supplied. |
| [ForestWeights](lean/R1Calculator/ForestWeights.lean), [ForestCapacity](lean/R1Calculator/ForestCapacity.lean), [ForestExtraction](lean/R1Calculator/ForestExtraction.lean) | Ordered forest weights; full induced greedy realizations; exact attained minimum extent; root capacity; extraction of every finite arithmetic interval forest; complete signed relation agreement. |
| [CarlsonSupport](lean/R1Calculator/CarlsonSupport.lean), [PrefixCut](lean/R1Calculator/PrefixCut.lean), [Carlson](lean/R1Calculator/Carlson.lean) | Arithmetic candidate, all mixed parameter signs, actual finite copy construction inside the claimed interval and an explicit finite obstruction beyond it. These are concrete proved suppliers for correctness. |
| [Correctness](lean/R1Calculator/Correctness.lean) | Candidate fixed-point equation below every notation bound; identification with the independently constructed actual R1 by recursive uniqueness; unrestricted right-ordinal endpoint rows; greatest endpoint and executable-checker equivalences. |
| [Norm](lean/R1Calculator/Norm.lean) | Expanded monomial-tree weight, triangular formula n(n+1)/2, general P/H output-size bounds, and normal omega-tower witnesses attaining equality at every natural size. |
| [Patterns](lean/R1Calculator/Patterns.lean) | Boolean finite pattern validation, coverings versus induced embeddings, marker laws, composition and complete finite existence searches. |
| [Examples](lean/R1Calculator/Examples.lean) | Explicit arithmetic fixtures and their actual semantic endpoint instances; additional finite-map examples. These supplement the general proofs. |

The pure-R1 proof reconstructs the relevant part of Carlson's known result.
It does not import the entire 3.1.3 project: selected formula and finite-diagram
constructions were adapted and rechecked locally, as explained in [REUSE.md](REUSE.md).

## Dependencies and exact scope

Lean is pinned to `v4.32.0-rc1`; Mathlib is pinned to
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. Their ordinal foundations and existing
arithmetic theorems are ordinary formal-library dependencies. Principal axiom
reports contain only `propext`, `Classical.choice` and `Quot.sound`, often fewer.
There are no admitted proofs, added axioms, `native_decide` proofs or external
Carlson correctness premises. The [verification record](VERIFICATION.md) names
the actual checked modules and hashes.

Sigma-one means a finite existential block over an arbitrary Boolean
quantifier-free matrix, exactly the fragment specified by Carlson. A separate
translation from Mathlib's general first-order formula syntax is not included.
The left inputs are the calculator's normal hereditary notations; the full
periodic structure beyond epsilon zero, additive resemblance and simultaneous
higher-order structures are outside this evaluator.

Python is a separately tested implementation. No formal Python-to-Lean
refinement, parser correctness, compiler correctness or running-time theorem is
claimed. Lean's finite existence search enumerates finite functions; Python
uses increasing image lists. Python's reported enumeration counts are finite
execution results. The package does not formalize a general pattern-count
formula, minimum ordinal realizations for order two or an order-two evaluator.
