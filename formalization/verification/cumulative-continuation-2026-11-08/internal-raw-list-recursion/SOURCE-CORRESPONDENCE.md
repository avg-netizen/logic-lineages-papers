# Source correspondence: original numeric list traversal

Date: 8 November 2026.

The source representation is `NumberedMultisetNumeric.numbersNumber`, whose
empty code is zero and whose cons code is `1 + Nat.pair head tail`.
`NumberedMultisetNumeric.decodeNumbers` is the unchanged parser.
`InternalListCodec.consCode`, `headCode` and `tailCode` are the corresponding
original Program ASTs. None of these suppliers is changed by this component.

`InternalRawListRecursion.listRec` is built exclusively from the original
Program constructors and existing calibrated arithmetic/list programs. Its
base and step are arbitrary original Programs, and the step receives the
original head, the recursively computed tail result and all original
parameters. Its internal graph is exactly `InternalControlGraph.programGraph`
for that AST; no alternate graph predicate replaces it.

| Obligation | Exact source-preserving target | Supplier argument |
| --- | --- | --- |
| List recursion on all raw codes | `ActualRawListRecursionEvaluation` | Original decoder totality and encoder round trip identify the external table invariant with the decoded-list right fold. |
| Internal nil unfolding | `ActualOriginalListRecursionZero` | The literal primitive-recursion zero law, original cons/head graph laws and graph functionality. |
| Internal cons unfolding | `ActualOriginalListRecursionCons` | Original cons tail descent, internal subtraction diagonal, internal PA table induction and literal composition/recursion graph rules. |
| Mapping on all raw codes | `ActualRawListMapEvaluation` | The same raw recursor instantiated with zero and the literal map step; the mapped fold equals the original encoder. |
| Internal map nil | `ActualOriginalListMapZero` | Raw nil unfolding and the actual zero-program graph. |
| Internal map cons | `ActualOriginalListMapCons` | Raw cons unfolding and the actual transform, recursive map and original cons graphs. |

The original path certificate uses
`NumberedQuotientPathCertificates.pathCertificateNumber`, which encodes a list
of paired next-vertex and edge-certificate numbers, and
`decodePathCertificate`, which maps `Nat.unpair` over the original decoded
numeric list. `ApplicationCertificateLiftPath.liftEntries` maps the existing
vertex and edge transformers over those entries. Thus the concrete map AST
provides exactly the list traversal needed by `liftPath`; calibrating its
element transform to those two original operations supplies the specialization.

The present six targets establish that traversal and its internal constructor
laws. They do not assert the full positive-path checker transport theorem or
any source-specific multiset, constructor, lambda or all-term conclusion.
