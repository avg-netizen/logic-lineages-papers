# Native acceptance notice

The source-match review below was completed before the native verification. Its original pending-native wording is retained as historical review context. See [component acceptance](ACCEPTANCE.json) and the [passed native verification](../finite-source-comparison/NATIVE-VERIFICATION.json) for the subsequent result.

---

# Literal finite-coefficient source correspondence

Source: paper 08, `thm:finite-source`, in the unchanged
`08-multivariate-collapse-comparison/paper.tex`, lines 202–234.
The source SHA-256 is
`a4a8481437b8c7683ee8d82ec9e13e0a29af44110edcace0e9b0ef31b8fdaf0d`.

## Independent original-source condition

`LiteralFiniteSource.collapseHeads` collects the original coefficient child at
every literal collapse occurrence. It preserves repeated occurrences and
traverses both children of addition, exponential multiplication and collapse.
`finiteCollapseCoefficients` requires each recorded expression to be closed and
its actual ordinal denotation to be below omega under every valuation. It does
not call a scalar compiler or use successful compilation as its definition.

`finiteSource` imposes this condition only on coordinate zero of an actual
canonical assignment of the original well-typed term. Canonical assignment
existence is explicit. Higher coordinates may have infinite ordinal values;
the condition does not exclude them. The source context must contain only
ground free-variable types, but there is no bound on internal or result types.

## Exact extraction bridge

`ClosedCoefficientExtraction` proves that successful positive extraction has
no free original components and contains no collapse occurrences. The existing
literal closed-positive evaluation theorem identifies its evaluated ordinal
with the denotation of the original coefficient at every valuation. This
preserves natural product in the collapse head and the original exponential
multiplication semantics; it does not replace semantic finiteness by absence
of an omega constructor.

`LiteralScalarCorrespondence` proves that, on every successful scalar
extraction, the independent original condition is equivalent to semantic
finiteness of every extracted scalar coefficient. Recursing into coefficient
children adds no restriction because those children are proved collapse-free.
Closedness is likewise a conclusion of positive extraction, not an extra
unpaid hypothesis about original terms.

`CanonicalSourceCorrespondence` establishes the equivalence for actual
original terms in a ground context. The existing canonical assignment and
vector-compilation theorem supplies assignment and scalar-extraction success.
The source predicate is nonvacuous even before this totality theorem is used.

## Effective admission and comparison

`ExactSourceTest` calibrates the executable `Code.acceptsSource` on the original
term code and context length. The program runs canonical assignment, vector
extraction and complete semantic coefficient recognition. It returns true
exactly on the literal finite-source class for every well-typed term in a ground
context. A rejected source is outside this class; rejection is not a negative
answer to a comparison problem.

`ActualSourceDecision` preserves the actual canonical assignments and decides
universal weak, WW-strict and equality comparison over positive ground
valuations. `RecursorFreePasses` proves the literal condition and successful
admission for every original recursor-free term, without an internal-type
bound. `ActualNumericPrograms` proves computability of both the actual admission
program and the already established original-code comparison program.

The separate `GroundAdmissibleComparison` component identifies these positive
ground valuations with the genuine original admissible substitutions. The
`FiniteSourceComparison` component assembles the complete source theorem.
Unrestricted first-order BASE decision and unrelated whole source theorems
are outside this component.

## Verification scope

Definitions and targets were frozen before proof authorship. Native acceptance,
actual axiom closures and source-hash-matched dependency receipts are recorded
separately in `ACCEPTANCE.json`; this document records source correspondence.
