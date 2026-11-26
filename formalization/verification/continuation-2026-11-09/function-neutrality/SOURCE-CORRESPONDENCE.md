# Function neutrality through the original canonical fold

## Source and scope

This packet continues paper06 `lem:id1`, the arithmetic accessibility proof
in `06-godel-t-termination-ordering/paper.tex`, lines 558–623. The source
SHA256 is `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.
Its arrow case uses the fact that a non-lambda application reduces only in
its function or to bottom. Applying this fact to the original quotient
presentation requires recovering function neutrality at the actual raw
source, rather than assuming it from a canonical representative.

The six frozen supporting contracts below address that reflection boundary
and its immediate raw-step consumer. This document records correspondence
and proof construction. Native acceptance and standard-axiom audits are
recorded in `STATUS.md` and `ACCEPTANCE.json`; definition and target hashes
are in `FROZEN-SPECS.json`.

## Six exact contracts

The first five declarations are in `OriginalFunctionNeutralityTargets`.
The sixth is in `OriginalFunctionNeutralityStepTransferTargets`. Their
implementations are under
`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/`.

| Frozen target | Exact obligation |
| --- | --- |
| `ActualOriginalFunctionNeutralityRefinementEquality` | Equality of the complete refined and original representative outputs on every raw input/parameter pair, together with calibration of the refined data. |
| `ActualOriginalFunctionNeutralitySelectedPreservation` | Internal preservation and reflection of every symbolic neutral-test value through the same selected bounded-descent representative. |
| `ActualOriginalFunctionNeutralityFullFoldPreservation` | The same two-way invariant through the actual complete canonical fold, from its original window, source premises and fold graph. |
| `ActualOriginalFunctionNeutralityCanonicalComparison` | Two valid raw sources with one common actual canonical output and parameter have equivalent neutral-test graphs. |
| `ActualOriginalFunctionNeutralityGlobalSelection` | One globally selected tuple supplies calibration, the complete original `Package`, prior root fields, full-fold neutrality, the original neutral-bottom law, and both variable Object laws. |
| `ActualOriginalFunctionNeutralityStepElimination` | Neutrality at an actual canonical output supplies the raw source's neutral premise; its original accepted step then yields literal same-type bottom or a full accepted function-child step, with all original witnesses retained. |

## Native equality and internal derivation

The observer is literally `OriginalNeutralLeaf.neutralTest`: the packed
root has application tag two and its actual function payload has a tag
different from lambda tag one. Nonapplications are masked to zero. The
new representative guard precedes the existing shape pipeline. An inactive
input retains the complete original output; an active observer mismatch
returns the complete input.

Native redundancy factors the concrete test through the original application
view. `NumberedPrimaryShapesProof.primaryAppView` relates corresponding
functions and `actualPrimaryLambdaShape` preserves their lambda flags.
Nonapplication views give zero. Decoded window closure and original source
validity justify this argument only in the active branch. Consequently the refinement-equality target still covers
every raw input, including malformed values, inactive cases and nonclosed
windows; it has no valid-input restriction.

The arithmetic proofs do not import native truth as a derivation rule.
They expose the guard's actual Program AST and propagate its invariant
through the same bounded descent, with the original validator and runtime
parameter. Internal targets quantify over arbitrary data, positive body,
variable type, arithmetic context and symbolic values. Neither native
calibration nor an assumed observer invariant is an internal premise.

## The actual function-child fold and final leaf

For an open application root, the existing canonical application eliminator
binds both actual child-fold outputs, their certified graphs, the original
constructors and the rebuilt application. The already established
`OriginalConstructorShapeRootFieldsProof.fullFoldRootFields` is applied to
that same function-child fold. Its root-tag reflection transfers the
function's lambda flag to its actual canonical child output. This uses the
prior root theorem, not a recursive assumption of whole-fold neutrality.

The rebuilt application therefore has the original application's neutral
test. The selected-representative invariant transfers this test across the
final leaf. Closed roots use the original closed-leaf equation. Throughout,
the recovered final relation remains

```lean
graph2 (leaf data) out rebuilt parameter
```

No step identifies `out` with `rebuilt` or assumes that their raw application
components coincide.

## One final tuple and its downstream consumer

The final tuple is exactly

```lean
OriginalConstructorShape.finalInputs
  (OriginalFunctionNeutrality.refineInputs p)
```

Thus the new guard precedes the existing shape, neutral-leaf and variable
refinements. `finalSelectedData` and `finalWindow` identify its literal
selected data and window with those used in the new invariant. The same
source, computability and lift programs supply the complete `Package`;
the neutral-bottom law uses that tuple's endpoint and old step.

The raw-step consumer specializes full-fold reflection to neutral-test
value one, derives the original raw source's neutrality, and instantiates
the existing `OriginalNeutralStepProof` at the shape-refined new inputs.
It retains the original source, target, certificate, type, window, symbolic
parameter and both continuations, including the full accepted child step.
It does not select a replacement certificate or reconstruct a different
endpoint.

The global input tuple precedes all symbol sets, subtype-closed type windows
and precedence tables. Ambient contexts remain encoded in the original
runtime parameter; no fixed-Gamma specialization, additional type-membership
premise or changed source numbering is introduced.

## Remaining mathematical boundary

Function neutrality does not identify corresponding canonical child
outputs of two raw applications with a common full-fold result. That
internal component-coherence theorem remains necessary before original
quotient neutral inversion and neutral saturation. Native primary-component
equivalence cannot replace the required arithmetic derivation.

Arrow computability, all-type variable computability, lambda/substitution,
multiset union and singleton closure, numbered-constructor computability,
and closed all-term accessibility remain beyond this packet. Scalar
variable accessibility at arrow type does not establish arrow computability.
The whole endpoint remains
`ContextUniformTargets.ActualContextUniformInternalAccessibility`: one
calibrated source before all fixed subtype-closed windows and a closed
derivation covering every ambient context. Paper06 `lem:id1` remains pending;
these six supporting contracts do not promote a numbered statement.
