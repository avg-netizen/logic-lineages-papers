# Next formalization boundary

Continue from `OriginalConstructorShapeStatementChecks` on
`formalization/cumulative-continuation-2026-11-09`. The seven frozen contracts
are checked. Reuse their source-matched receipts and warm cache; no repeated
root-shape proof or full-root rebuild is needed.

## Paid facts and the same selected tuple

`OriginalConstructorShapeFullFoldProof.fullFoldMarkPreservation` and
`OriginalConstructorShapeRootFieldsProof.fullFoldRootFields` preserve and
reflect the actual root tag and application domain through the SAME full
canonical fold. `actualOriginalCanonicalRootComparison` transfers these
facts between two raw sources with a common actual canonical output. Root
lambda shape is included; function-child lambda shape is not yet included.

`OriginalCanonicalApplicationInversionProof.actualOriginalCanonicalApplicationElimination`
binds the original application constructors and both certified child outputs
from parent validity, tag two and the actual fold graph. Its `atConstructors`
helper is available when the original constructors have already been bound.
The final `Recovered` field is deliberately

```lean
graph2 (leaf data) out rebuilt parameter
```

It is not an equality between `out` and `rebuilt`. Do not erase this field or
assume that the final representative has the rebuilt application's components.

The global final tuple is `OriginalConstructorShape.finalInputs p`, namely
variable(neutral(shape(p))). The complete Package, neutral bottom law and
both variable Object laws hold for that one tuple before all source windows.
The inherited raw neutral-step theorem can be instantiated at `shape(p)`.

## Bounded next target: the application function's lambda flag

An immediate next supporting theorem can preserve and reflect the original
function child's lambda flag at application roots. A concrete nonrecursive
observer guard on `base.oldRepresentative`, placed before the current shape
pipeline, can make this invariant internally visible while preserving all
old calibrated outputs. Freeze its exact target before proof work.

Native redundancy can use `NumberedPrimaryShapesProof.primaryAppView` and
`actualPrimaryLambdaShape`. These are native semantic suppliers, not internal
derivation rules. The selected-descent proof must derive the new law from the
actual guarded Program AST. For an open canonical fold, recover both actual
child outputs with the new application eliminator and apply the already paid
`fullFoldRootFields` to the function child. That uses an existing theorem,
rather than assuming the new whole-fold invariant recursively.

This would pay the function-level neutrality premise for the raw source of
`OriginalNeutralStepProof.actualOriginalNeutralStepElimination`. It does not
by itself pay canonical equality of application components.

## Canonical component coherence remains separate

The required stronger theorem starts from two valid raw applications with
one common actual full-fold output at the same parameter. After binding their
actual child-fold outputs, it must identify the corresponding function
outputs and corresponding argument outputs internally. Original domain and
codomain tags and raw child witnesses must remain available.

The current observer records only root tag and application domain. The final
selected-leaf graph is precisely where component information is still lost
to the internal proof. A further concrete calibrated construction and a
proved connection to child-fold outputs are needed. Raw child-code equality
would be too strong; native primary-component equivalence does not supply
an arithmetic derivation.

## Quotient entry and later consumers

`OriginalVariableQuotientPathEdgeProof.edgeRawCases` is generic despite its
filename. Together with `UniformCertificateCompletion.TypingProof.stepParts`
and `sourceFold`, it supplies actual raw endpoints and certificate, both
endpoint validities and the original source/target fold graphs. The current
root-comparison theorem can now recognize raw application shape/domain there.
After function neutrality and component coherence are paid, consume the
existing raw neutral bottom/accepted-child split, rebuild the function
quotient edge, and retain the actual raw argument and certificate.

Neutral saturation and arrow computability, all-type variable C,
lambda/substitution, multiset union/singletons, numbered constructors and
closed all-term context-uniform accessibility remain pending. Scalar
variable-I at an arrow is not arrow C. The full frozen endpoint remains
`ContextUniformTargets.ActualContextUniformInternalAccessibility`.

The numbered register remains **171 checked, 2 inherited, 16 pending / 189**.
No numbered statement was promoted by this supporting packet. The unchanged
serialized native limits and standard-axiom policy remain active. All jobs
for this checkpoint have completed; no full-root or remote-CI pass is claimed.
