# Next formalization boundary

Continue from `OriginalFunctionNeutralityStatementChecks` on
`formalization/cumulative-continuation-2026-11-09`. All six exact contracts are checked;
`ACCEPTANCE.json` records the native and axiom evidence. Preserve its frozen contracts
and all inherited mathematical sources when extending the construction.

## Neutrality and the raw-step consumer

`OriginalFunctionNeutralityFullFoldProof.fullFoldMarkPreservation` carries
the existing `OriginalNeutralLeaf.neutralTest` through the SAME selected
bounded descent and full canonical fold. Its value is one exactly at an
original tag-two application whose actual function payload is not a lambda.
The application case uses the already established root-tag reflection on the
recovered function-child fold; it does not assume a new recursive invariant.

`OriginalFunctionNeutralityComparisonProof.actualOriginalFunctionNeutralityCanonicalComparison`
compares two valid raw sources with a common actual canonical output.
`OriginalFunctionNeutralityStepTransferProof.actualOriginalFunctionNeutralityStepElimination`
reflects neutrality of a supplied full-fold output to its raw source, then
uses the existing accepted-step elimination rule. The conclusion retains
the original source, target, whole certificate, parameter and raw argument:
literal same-type bottom, or an actually accepted original function-child
step. This is still the raw-step split, not quotient component inversion.

The single final tuple is

```lean
OriginalFunctionNeutrality.finalInputs p =
  OriginalConstructorShape.finalInputs
    (OriginalFunctionNeutrality.refineInputs p)
```

All calibration, the full source/computability/lift Package, root fields,
function-level neutrality, neutral bottom law and both variable Object laws
refer to this tuple before every source window and ambient Gamma. Do not
repeat the root-shape, function-neutrality or raw checker arguments.

## The remaining final-leaf issue

`OriginalCanonicalApplicationInversionProof.actualOriginalCanonicalApplicationElimination`
still supplies `Recovered`, including both certified child-fold outputs,
their actual rebuilt application and the literal final graph

```lean
graph2 (leaf data) out rebuilt parameter
```

That field remains a graph, not `out = rebuilt`. A final selected leaf can
change the application components. Equal final parent outputs therefore do
not yet identify the corresponding certified function outputs or argument
outputs.

The exact next internal coherence obligation starts from two valid original
applications with the SAME actual full-fold output and parameter. Bind their
original constructors and both pairs of certified child-fold outputs using
the existing eliminator. Derive equality of the corresponding function
outputs and corresponding argument outputs internally, retaining original
domain/codomain graphs and raw child witnesses. Raw child-code equality is
too strong. Native primary-component equivalence is not an internal
arithmetic inference rule.

## Current fixedness is only transition fixedness

The checked `InternalParameterizedCanonicalResultFold.outputInvariant`
contains source validity, the original raw type and

```text
T(out, parameter) = out
```

Here `T` is the actual guarded bounded-descent transition. It does not assert
`foldN(out, parameter) = out`, `oldRepresentative(out, parameter) = out`, or
fixedness of either application child. The transition can reject a candidate
because its value is not smaller, its validity test fails or its type differs.
Its fixedness alone does not discharge any of those stronger claims.

`InternalParameterizedBoundedDescentNormalizerTargets` supplies the actual
normalizer's bound, transition fixedness, validity and type preservation.
`InternalParameterizedCanonicalResultFoldTargets` supplies certified fold
outputs and forward representative/application transport. Neither collection
currently supplies full-fold idempotence or inverse application-component
coherence. A proof using those stronger properties must establish them from
the concrete Programs rather than adding them to the target premises.

## Proposed bounded native supplier: least-code application factorization

Freeze a new native target before proof work: for original typed, in-universe
children `f : sigma → tau` and `a : sigma`, at a subtype-closed original
window and the SAME Gamma, assume each child's representative code equals
that child's own packed code. Prove

```lean
representativeCode symbols S (applicationPacked f a) =
  packedNumber (applicationPacked f a)
```

This supplier is proposed, not proved by the present packet. Existing
ingredients are `NumberedLeastCodeRepresentativeProof.representativeAttained`,
`representativeMinimal`, and
`NumberedPrimaryShapesProof.actualPrimaryApplicationComponents`.
The latter recovers actual primary-equivalent function and argument terms
from a representative of the original application. The original nested
`Nat.pair` numbering then requires an explicit monotonicity argument showing
that two minimal child codes produce a minimal application code. Keep the
actual type tags and application-domain coordinate throughout that argument.

The existing `NumberedQuotientApplicationProof.representativeApplicationCongruence`
only compares representatives of applications whose child representatives
agree. It does not state the proposed raw-application fixedness law.

Even after native factorization is proved, an internal connecting proof is
still needed. It must show that the actual certified child outputs meet a
concrete, internally established canonicality condition and that the SAME
final selected leaf respects those components. A native equality cannot be
inserted as a derivation rule, and an observer invoking the very final fold
being defined would require a justified noncircular construction. Do not
claim that native factorization alone closes quotient neutral inversion.

## Later consumers and unchanged scope

`OriginalVariableQuotientPathEdgeProof.edgeRawCases` together with
`UniformCertificateCompletion.TypingProof.stepParts` and `sourceFold` remains
the quotient entry point. After canonical component coherence is established,
use the paid neutrality transfer and raw bottom/function-step split to rebuild
the actual function quotient edge with its original argument and certificate.

Neutral saturation, arrow computability, all-type variable C,
lambda/substitution, multiset union/singletons, numbered constructors and
closed all-term context-uniform accessibility remain pending. Scalar I at
an arrow does not establish arrow C. The full endpoint remains
`ContextUniformTargets.ActualContextUniformInternalAccessibility`.

The numbered register remains **171 checked, 2 inherited, 16 pending / 189**.
This supporting packet does not promote paper06 `lem:id1`. Continue under
the unchanged serialized native limits and standard-axiom policy; retain
the distinction between focused verification and a full-root or remote-CI pass.
