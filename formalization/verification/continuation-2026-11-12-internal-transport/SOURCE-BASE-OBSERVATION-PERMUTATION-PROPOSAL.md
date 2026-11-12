# Original BASE exchange to observed numeric permutation: proposal only

## Exact original source boundary

`NumberedPrimaryExchange.Exchange.ordinary` carries a permutation of the actual packed `argumentList`, equivalent heads, window membership, and equal head results. `Exchange.numbered` carries the same packed BASE permutation, unchanged numbered index/result type and unchanged ordered extras; it does not require equal head results. `NumberedExchangeCode.argumentEntries` preserves both type and raw child code, rejects malformed spines, and `argumentPermutation` tests permutation of these entries. Do not substitute untyped child permutation or sort numbered extras.

## Native witness existence (not an internal derivation)

For a fixed Program R and fixed runtime parameter, map every packed argument q to
`pair(typeNumber q.1, evaluate R [packedNumber q, parameter])`.
A literal BASE `List.Perm` maps to a numeric `List.Perm`, including duplicates and coincident observations. The checked typed-observation calibration identifies these mapped lists with actual argumentObservations outputs. Any finite permutation can be factored into prefix-adjacent swaps by moving each chosen occurrence to its target position. For m entries this needs at most m*(m-1)/2 swaps, preserving multiplicities. Each move supplies mapper's literal certificate `pair(front,pair(x,pair(y,tail)))`; the resulting exchange path is a native finite witness. Its numeric code size is NOT bounded by the swap-count polynomial.

This proves native certificate existence only. It does not turn a native `List.Perm` hypothesis, or a native Boolean calibration theorem, into an arithmetic derivation of the original source checker.

## Small internal bridge compatible with the current exchange checker

1. Establish a raw typed-spine adjacent-swap graph theorem. Use two original tag7 cons constructors, actual packed-child pairs, actual R outputs at the SAME parameter, and the same actual tail observation. Checked InternalCons twice gives the two numeric lists, with typed observations exchanged. The literal adjacent-edge checker then accepts the exact numeric certificate. A common raw prefix can be handled by induction on its actual constructors and the same observation graphs.
2. Lift these actual witnesses through a coded finite raw-spine exchange chain. Existing numeric exchange-path soundness then yields equality of actual sorted observation outputs. This is a genuine internal theorem conditional on an actual coded source-spine exchange witness, not on a native permutation.
3. Separately discharge that witness from the CURRENT original argumentPermutation checker. Its native implementation uses equality of counts over the concatenation of both lists (`NumberedExchangeGuardsPrimrecProof.permutationPrimitive`). Missing internal work is actual extraction/count correctness and constructive occurrence-removal/path synthesis, with finite bounds. This cannot be replaced by native `List.Perm` reflection or by adding path acceptance as a premise to a claimed original source theorem.

Intermediate adjacent-swapped raw argument spines need not fit one fixed head's dependent type list. The all-raw observation graph equations still apply; every moved entry retains its explicit type and child. Only the original endpoint source/head constraints belong to the original BASE exchange. This avoids an unnecessary and generally unjustified intermediate source-validity assumption.

## Scope and ownership

Mapper owns numeric prefix/adjacent edge/path contracts. No runtime or frozen target was changed by this note. The proposed raw observation bridge is independent follow-on work; no theorem here asserts it checked. Ordinary/numbered source completeness and hereditary canonical cancellation remain pending even after numeric sort idempotence and adjacent-path soundness.

## Verified local bridge update

Literal tag7 adjacent swap passed exact alias `1794489447296281718-5`. Numeric certificate prepend and same-child raw-cons prefix lifting passed exact aliases `1794489934059582580-5`. The latter extends a certificate's literal numeric front and keeps its payload; it does not itself define a converter for a whole raw prefix or source path.

The next narrowly useful supplier is an auxiliary raw-prefix constructor, iterating a numeric list of packed `(type,rawChild)` cells onto an original raw argument suffix, plus the internal observation-append law. That law would connect actual prefix reconstruction with numeric prefix observations without imposing intermediate head/source validity. An actual raw certificate/path translator still needs to be defined and checked; the existing numeric mapPath is a different, already-numeric layer.

Search boundary: `NumberedExchangeGuardsPrimrecProof.permutationPrimitive` establishes native primitive recursiveness using equal occurrence counts over both lists, with `.of_eq` conversion to `List.Perm`. It is not an internal graph exposure theorem for an arbitrary calibrated source-checking Program. A source-checker-to-path proof therefore cannot silently reuse it as if it supplied internal count or witness extraction laws.
