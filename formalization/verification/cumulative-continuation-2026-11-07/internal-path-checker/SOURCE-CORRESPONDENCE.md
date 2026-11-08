# Source correspondence: concrete original path checker

Date: 7 November 2026, America/Chicago.

The source checker is
`NumberedQuotientPathCertificates.pathTest`, with nil clause `decide (x = y)`
and cons clause `numericEdgeTest x vertex certificate && pathTest vertex y tail`.
Its positive variant is the unchanged
`NumberedQuotientPathCertificates.positivePathTest`, which rejects an empty
decoded path. Both definitions remain untouched.

`pathCertificateNumber` encodes each pair of next vertex and edge certificate
using the original `Nat.pair`, then uses the original `numbersNumber` list
encoder. `decodePathCertificate` applies `Nat.unpair` to the unchanged
`decodeNumbers` output. The new Program AST uses the corresponding original
pair, cons, head, tail and unpair programs. It does not replace the source path
representation or require canonicality as a new premise.

The literal `InternalControlGraph.programGraph` of the concrete checker is
used throughout the internal targets. The cons hypotheses are exactly the
actual pairing graph of the raw entry and the actual cons graph of the raw
path. All path, edge and tail acceptance predicates mean output one.

The external `EdgeCalibrated` premise specifies the supplied original edge
Program on all natural triples, including off-domain data. The internal
equations do not use this premise. Separate evaluation and derivation proofs
prevent an external truth claim from substituting for an internal graph rule.

The generic checker supports the already defined original application path
map and the planned internal transport from a local single-edge preservation
derivation. It supplies the path recursion needed for that induction; it does
not supply the edge preservation premise or prove the source all-term endpoint.
