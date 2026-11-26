# Paper 16: one original directed edge reaches the actual length-fuel pool

Frozen source candidate. Input is the original physical poolLength graph
at an explicitly held successor output, on the exact same original
ordered vertices (duplicates retained). No inference of that positive
length from membership is made here. Both actual original vertex
members, the accepted exact edge from seed to target, and the actual
computed pool are held. The reached member itself is not assumed.

LocalProof uses the original members-at-length equivalence to get the
actual same length round from the held members call. It chooses the
actual predecessor round internally via programCases and uses the
original SeedEveryRound law on the genuine original seed member.
The existing RoundEdgeExtension then puts the real target in the
actual successor output, which is the held full length-fuel pool.
This proof does not assume generic fuel monotonicity, stability, or
old unavailable exhaustion results.

PackedProof recovers the true members call inside original membersAtSeed
by the actual original scratch output and all original projections
(in the same ctx/type/seed). PairedProof binds the exact chosen own-cover
P/C/Wp and paired guarded X; the current actual CrossCoverReports pay
the original ordered vertices and both members on the same tape. The
length and members graph are still explicit genuine input reports.

No minimum equality or transport, arbitrary source-in-pool closure,
representative glue, backward path, or protected context.
No author Lean/Git or promotion. Gates Local, Packed, Paired.

| Frozen Lean source | SHA-256 | Static local closure |
|---|---|---:|
| `NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets.lean` | `f37d92a97ccd93687de1d1b253781d5bb607c7743ab114c7d748974752abb5b9` | 1290 |
| `NumberedWindowInternalCoverCombinedRestrictedLengthReachLocalProof.lean` | `e7e3ddd3072a5cca01ad96129ed42e83b2bdd905bcbae8b56a5008b065075583` | 1464 |
| `NumberedWindowInternalCoverCombinedRestrictedLengthReachPackedProof.lean` | `45575e16a2f8cd72779f52c8a9d0238665a69acc191e3bcf387fe9eaae9872f5` | 1465 |
| `NumberedWindowInternalCoverCombinedRestrictedLengthReachPairedProof.lean` | `8cf0b925cc1e371b34e0394fe224dd7cafac45701ce761c5850e8b6a3243974a` | 1466 |

No Hydra/Linarith in static closure. Original exact supplier/source pins:

```text
6e01cdd49750dcb3f36d30f0c616e6a991a88a200cec183821845b0fbe1add97  LogicLineages/PersistentMarking/NumberedWindowInternalSparseSeedBoundChecks.lean
7edafdd4f7d974375f45cd85c35778bf0927e9fe154ae9f3e02aaf3bed03907e  LogicLineages/PersistentMarking/NumberedWindowInternalSparseRoundReachChecks.lean
974dbe9772b6b1f0aa69015718072f892a46733a51bef252df001fbc75112808  LogicLineages/PersistentMarking/NumberedWindowInternalSparseOpenRoundsChecks.lean
6a15072d8a6e0aa1706f63b4e972186a2c847a61b0fd0f71360f12630ae27ca2  LogicLineages/PersistentMarking/NumberedWindowInternalSparseDirectedRoundsDefinitions.lean
a4c7811b49df019fffbc09cd506ea5eedf97390544f16f02b0baf396069d53b4  LogicLineages/PersistentMarking/NumberedWindowInternalSparsePackedLeastDefinitions.lean
245b911cc32088e373cf753c7f5ea1be65d071a76983fb6c97862604a45deb8b  LogicLineages/PersistentMarking/NumberedWindowInternalSparseSeedOriginPoolProof.lean
73e6e82721152bd5ce38f7c126565803fb608ab845b23e7fccd71897f03105b4  LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets.lean
ce0bd80da7c6b3a3562797d9f10130a50b57f06a18ebed8e10fd1507c2aefc3f  LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof.lean
```
