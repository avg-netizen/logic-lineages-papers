# Exact primitive-recursive list presentation of primary classes

Paper06 lines551–556 requires finite computability of the primary classes before
passing to least-code representatives and arithmetic relations. The existing
implementation uses the original decoded candidate list, the original Boolean
exchange test, and finite-set reachability saturated at its vertex cardinality.
This component supplies an exact list presentation of that computation and
primitive recursion of its original membership test.

`vertexList symbols S q` is exactly `q :: classCandidates symbols S q`. A list
`step` retains every previously reached entry and appends those entries from the
fixed vertex list for which some previously reached entry passes the original
`exchangeTest`. The `any` and `filter` tests preserve the actual edge orientation.
All original vertex repetitions are retained, and the state list can also have
repetitions. `reachableList` iterates this step exactly the supplied number of
times from `[q]`. `primaryList` uses the length of `vertexList` as its cutoff.

The first frozen target equates `toFinset` of every list iterate with the original
`NumberedFinitePrimaryClass.reachable` at the same fuel. The second equates
`primaryList.toFinset` with the original `primaryClass`, whose original definition
still uses vertex cardinality. The cutoff correspondence uses the already
checked unconditional `cardinalitySaturation`: the original iterate stays fixed
at and after that cardinality, and `List.toFinset_card_le` bounds the cardinality
by the length of the actual vertex list.

Both calibrations quantify over every symbol type with decidable equality,
arity, window lists, context, and actual packed typed seed. Empty or repeated
window entries and starting terms outside the finite universe remain in scope.
Neither calibration introduces a subtype-closure or universe-membership premise.
The separate identification of the original computed class with the source's
`WindowPrimary` relation retains its already stated confinement hypotheses.

The third target proves `primaryList` primitive recursive jointly in both window
lists and the packed typed seed under the accepted genuine numeric presentation.
The fourth names the original `NumberedFinitePrimaryClass.primaryTest` itself and
proves it primitive recursive jointly in both windows and both packed arguments.
Finite signature size, its actual arity function, and context are universally
quantified fixed parameters, including signature size zero. None of the four
targets has a supplied correctness or primitive-recursion hypothesis.

The effectivity proof must use the checked primitive recursion of the actual
`classCandidates`, a separately proved effectivity theorem for the actual
`exchangeTest` on arbitrary windows and packed arguments, primitive-recursive
list operations, and finite iteration. The two semantic calibrations do not need
that effectivity supplier. The final membership theorem transfers primitive
recursion of actual list membership through exact `toFinset` calibration. The
candidate edge-effectivity theorem must be proved before these effectivity
targets can be accepted.

The exact list presentation makes a new primitive-codable finite-set presentation
unnecessary for these targets. This component does not assert primitive recursion
of the finite-set-valued `primaryClass` under an unspecified encoding. Least-code
representatives, the canonical carrier, full step-checker effectivity, arithmetic
representability, ID1 accessibility, and whole paper completion remain separate
results. The source-statement register is unchanged.

## Prospective statement freeze

The following hashes were recorded before candidate proof authoring. Comparator
compilation and acceptance evidence belong to separate integration records.

| Source | SHA-256 |
|---|---|
| `NumberedAuxiliaryDecodingDefinitions.lean` | `ad55960aff664aa29cd853156ceae4873bf01d3e4861d2b83da9b39ab20ae876` |
| `NumberedExchangeNeighborhoodDefinitions.lean` | `be7cc03a2f4c7880cc735174eaa81879e54ee1878b920491b61820a5d3e81d9d` |
| `NumberedFinitePrimaryClassDefinitions.lean` | `b2bc439013ee9e94daf46a8d95ae6db80ec8522f80f89981e7c8045f81d31736` |
| `NumberedFinitePrimaryClassTargets.lean` | `8942a0b3e27ebc448d623b9ac278bb870f3d5567aaecbee8439a65791bc33761` |
| `NumberedFinitePrimaryClassProof.lean` | `a02aaf1084766d9c26c04d2d3fea7d7e6dcef13108824d0d8f83409bdf8d657a` |
| `NumberedClassCandidatesPrimrecTargets.lean` | `0cc261f542ae9871cc9c80f655bf6554efcf44d30d202bbf680e40fb2c0055fe` |
| `NumberedPackedPresentationDefinitions.lean` | `2b9dd41c24b02c84eecd2d802390706ad94cc6dd39bb5a9c356c21ab1065d266` |
| `NumberedPrimaryClassPrimrecDefinitions.lean` | `fff4e75038744937068a662c3fd57a126a6bfcde6035c804d4299dfb35761609` |
| `NumberedPrimaryClassPrimrecTargets.lean` | `8f4c60a7e6ce54504ecacba9ee6d9e31a126947128da4c8dfbfe9b2d40ec4ec7` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |

## Accepted verification

The fixed statement gate and the thirteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](PRIMARY-CLASS-PRIMREC-FREEZE.json) and
[the acceptance record](PRIMARY-CLASS-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
