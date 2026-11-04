# Ordinary arithmetic representation of actual precedence certificate

Source: paper06 finite strict ranked precedence and arithmetic Context interpretation. This component uses the accepted ordinary arithmetic compiler, not a new semantic predicate standing in for syntax.

For each fixed n, rankValue is the Boolean numericRankTest converted to Nat on a literal two-entry vector [context,certificate]. The first target supplies an actual Program2 computing this value at all inputs, plus standard-N truth of rankGraph at output1 iff the exact Context and finPi rank decoder witnesses satisfy RankCertificate. Both malformed Context and malformed certificate codes therefore reject, without altering any accepted decoder.

The second target supplies an actual ordinary arithmetic unary formula for existence of an accepted certificate. validContextGraph existentially binds the certificate variable in the same Program2 output1 graph, keeping context as its sole free variable. Accepted numeric certificate completeness calibrates truth to a successful decoded Context with StrictTotalTable of its actual table. No arity or term context Gamma is an input to this table-only formula.

Proof uses allPrimitiveFunctions after composition of all-code per-n PR with vector projections and Bool.toNat, then appliedProgramGraphTruth and existsFiniteTruth. The rank-code finPi distinction remains as frozen in the numeric checker. No uniformity in n, subtype/window validity, term/rewrite WF, original transitivity, internal ID1 derivation or register promotion. Standard-N truth only. Proof absent until review/freeze.
