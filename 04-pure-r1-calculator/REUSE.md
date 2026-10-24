# Reuse from the Alexander 3.1.3 formalization

The calculator adapts a small set of constructions from the earlier Alexander
thesis Lean development. All required source is included here and checked here;
that larger project is not an import or build dependency. Its pinned Lean and
Mathlib versions match this package.

| Earlier module | Reused construction | Local treatment |
|---|---|---|
| `Alexander313.Wilken.PureRelationsSemantics` | Boolean matrices, finite existential tuples and upper-ordinal recursion | Adapted in [Semantics.lean](lean/R1Calculator/Semantics.lean) to equality, order and exactly one relation. |
| `Alexander313.Wilken.PureRelationsFiniteDiagrams` | Signed atomic literals, finite conjunctions and fixed-parameter diagrams | Adapted in [FiniteDiagrams.lean](lean/R1Calculator/FiniteDiagrams.lean), retaining all negative facts and equality constraints. |
| `Alexander313.Wilken.PureRelationsFiniteReflection` | Converting reflected tuples into maps on finite sets | Generalized to any one binary relation on the ordinal universe. |
| `Alexander313.Wilken.PureRelationsReflectionConverse` | Boolean-formula transport and existential reflection | Adapted and kernel-checked locally, proving the converse finite-copy criterion. |
| `Alexander313.Wilken.PureRelationsTransitivity` | Agreement of restricted and global relations on bounded tuples | Proved directly for the smaller signature; the larger library is not imported. |

The earlier `Alexander313.Carlson.Semantics` and `Basic` modules concern
simultaneous order-two covering relations. Their first relation reads a second
relation, and positive coverings differ from full induced copies. They supplied
useful references for recursion bookkeeping, but importing that `R1` would not
give this calculator's standalone pure-R1 semantics.

The adaptation therefore constructs the actual one-relation semantics and proves
its global initial-segment equation and uniqueness. It proves Carlson's finite
induced-copy criterion in both directions. Every finite diagram includes
positive and negative equality, order and resemblance atoms; all original lower
parameters are fixed. Empty domains and empty tuples are included.

The endpoint characterization required additional work beyond those reused
constructions: normal-notation coverage of actual ordinal cuts, arithmetic
nesting, exact weighted-forest capacity and greedy copies, finite forest
extraction, stable parameter cuts and explicit endpoint obstructions.
[Correctness.lean](lean/R1Calculator/Correctness.lean) assembles these proved
suppliers into the actual semantic endpoint theorem, with no correctness premise.

The relevant mathematical sources are Carlson (1999), Proposition 1.2 and
Theorem 2.5, and Wilken (2021), Proposition 1.1. See [SOURCES.md](SOURCES.md).
The local formalization covers the calculator's hereditary normal forms below
epsilon zero, with arbitrary actual right ordinals; it does not import an
assumed characterization or assert the global periodic extension.

Build dependencies remain the pinned public Lean and Mathlib. No access to the
earlier project's checkout, private documents, legacy compilation receipts or
remote source retrieval is needed. The [coverage guide](FORMALIZATION.md) and
[verification record](VERIFICATION.md) describe the checked local result.
