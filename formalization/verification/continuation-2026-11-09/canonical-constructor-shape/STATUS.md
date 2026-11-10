# Accepted — canonical constructor and application-domain reflection

**Seven exact supporting contracts pass in 22 new Lean modules.** This
continuation extends `531a50683ed1ffb672d74159f776be6bfb3c4ae2` on
`formalization/cumulative-continuation-2026-11-09`.

The SAME final canonical fold now preserves and reflects every symbolic raw
constructor tag and the actual application-domain code. Two valid raw sources
with one common canonical output therefore have the same root-shape facts.
A generic application eliminator also recovers the original constructors,
the certified canonical outputs of both children, their rebuilt application,
and the actual final selected-leaf graph. These are internal arithmetic
derivations with symbolic parameters and arbitrary contexts.

| Frozen exact target | Checked result |
| --- | --- |
| `ActualOriginalConstructorShapeRefinementEquality` | A concrete shape guard leaves the original representative's entire output unchanged on every raw value/parameter input and preserves the original calibration. |
| `ActualOriginalConstructorShapeSelectedPreservation` | The selected bounded descent preserves and reflects the pair of root tag and conditional application-domain code. |
| `ActualOriginalConstructorShapeFullFoldPreservation` | The SAME full canonical fold preserves and reflects that pair, including its final selected representative. |
| `ActualOriginalConstructorShapeRootFields` | Every symbolic root tag and actual application-domain graph is preserved and reflected through the full fold. |
| `ActualOriginalCanonicalRootComparison` | Two raw sources with one common actual canonical output have equivalent root-tag and application-domain facts. |
| `ActualOriginalConstructorShapeGlobalSelection` | One original tuple and its ordered shape/neutral/variable refinement jointly supply the complete Package, root reflection, neutral law and both existing variable Object laws. |
| `ActualOriginalCanonicalApplicationElimination` | Parent validity, raw tag two and the actual full-fold output internally recover both original children, their certified fold outputs, the rebuilt application, its validity and the SAME final selected-leaf graph. |

## Mathematical construction

The new nonrecursive observer is

```text
mark(input) = pair(rootTag(input),
                   if rootTag(input) = 2 then appDomain(input) else 0)
```

The native proof shows that the original primary equivalence preserves this
observer. On an active-window mismatch, the new representative guard returns
the whole input; native calibration proves that this branch never changes
the original output. Inactive and malformed inputs retain their full output.

Internally, the concrete guard enforces the invariant without a calibration
premise. The proof carries it through the existing variable, spine and bottom
choices and the original numeric bounded-descent iterator. For an open fold,
the original parent and the actual rebuilt application share tag two and the
same domain; the last selected representative preserves that mark. Closed
folds use the existing fold-to-leaf law. Internal Program totality and original
pair projections then recover the individual fields in both directions.

The one global final tuple is exactly

```lean
OriginalVariableRepresentative.refineInputs
  (OriginalNeutralLeaf.refineInputs (OriginalConstructorShape.refineInputs p))
```

All calibration and Package clauses, root fields, the neutral law and variable
certificate-bottom/leastness laws use this same tuple, selected before all
source windows and ambient contexts.

## Exact remaining boundary

The final selected leaf may still change an application's function and
argument components. The new eliminator exposes that leaf graph rather than
identifying its output with the rebuilt application. Equal parent canonical
outputs do not yet yield equality of the corresponding canonical child
outputs. Root lambda-shape reflection is now paid; reflection of the
function child's non-lambda shape through application components remains open.

Canonical component coherence, quotient neutral inversion, arrow
computability, lambda/substitution, multisets, constructors and the whole
context-uniform accessibility theorem remain pending. The numbered register
is **171 checked, 2 inherited, 16 pending / 189**. Paper06 `lem:id1` remains
pending, and this packet promotes no numbered source statement.

## Verification

The exact gate is
`SourceComputabilityCompletion.OriginalConstructorShapeStatementChecks`.
Its seven aliases and 92 additional defining-module declarations passed
native axiom audits using only `propext`, `Classical.choice` and `Quot.sound`.
All 1,842 local sources in its dependency closure have matching successful
native rows. Including the separate specification preflight gives 1,843
source-matched modules. Existing supplier receipts and the warm cache were
reused; no full-root or remote-CI pass is claimed.

Final receipt: `build-reports/1794286868566338035-5.json`. The unchanged
serialized checker used one worker, 2,048 MiB heap, 1,536 MiB RSS, a 2,048 MiB
admission floor and 90 CPU/180 wall seconds per module. Peak successful
new-module RSS was 1,309,468 KiB. All 10,255 inherited mathematical Lean
sources and all three frozen specification files are unchanged. The checker,
toolchain, dependency manifests, manuscript and CI are unchanged. The root
aggregate adds one import of this gate.

The five failed attempts are retained in `ATTEMPTS.json` and
`failed-attempts/`; their repairs address vector simplification, namespace
resolution and a consumed local proof name. No target, axiom policy or
resource cap was weakened. Every owned compiler job has completed.

`ACCEPTANCE.json`, `AXIOMS.json`, `FROZEN-PRESERVATION.json` and
`exact-checks.log` record acceptance. Complete source pins, successful native
rows and the final receipt are losslessly compressed; the coverage uses four
parts. `EVIDENCE-ENCODINGS.json` records stored and uncompressed hashes.
See `SOURCE-CORRESPONDENCE.md` and `NEXT-STEPS.md` for the remaining proof work.
