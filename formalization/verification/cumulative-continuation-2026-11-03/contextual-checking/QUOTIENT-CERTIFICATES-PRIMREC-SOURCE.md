# Original quotient-edge and positive-path certificate computation

These four fixed targets concern the unchanged `numericEdgeTest`,
`decodePathCertificate`, `pathTest` and `positivePathTest`. The edge checker
validates an actual numerical step and compares the actual least-code
representatives of its decoded endpoints. The path checker retains every
literal next-vertex/edge-certificate entry, checks them in order and checks the
last vertex. The positive wrapper rejects an empty list, including when its
endpoints are equal.

The targets vary both windows, the whole finite precedence table, endpoint
numbers and the certificate data jointly. Finite signature, arity and ambient
binder context are explicit fixed parameters. Existing representative
effectivity is used at that ambient context; contextual stepping must separately
pay the changing hole contexts. No decision of path absence, extra confinement
premise or substitute quotient relation appears in the target.

The original semantic soundness/completeness records already connect these
checkers to the actual quotient edge H and positive closure R discussed in
paper06 lines551–556 and used by lem:simulation at lines625–658. These new
targets pay algorithmic effectivity. Explicit arithmetic formulas and internal
ID1/accessibility arguments remain separate mathematical obligations.
