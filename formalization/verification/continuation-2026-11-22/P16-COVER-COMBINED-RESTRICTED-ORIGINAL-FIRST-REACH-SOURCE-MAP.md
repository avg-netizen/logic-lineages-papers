# Paper 16: actual first-round reached member on the original shared scratch

Frozen source candidate. These are the original rounds on the unchanged
physical ordered vertices, ctx, type, and raw seed; fuel is exactly zero
and its first successor. The source and target have actual occurrences
in that original list and the edge is the actual original Program 4 graph.

- LocalProof invokes the exact original SeedRoundZero and RoundEdgeExtension.
  It retains both actual round graphs, original physical membership and
  accepted edge, proves actual source presence in round zero and target
  presence in round one. It does not assume the reached result.
- Proof chooses both real program outputs internally with original
  programCases. It correctly preserves context and literal input values
  through the two allowed relabelings and exposes the full reports.
- PairedProof starts with the exact guarded paired CrossCover CPS
  (1795379642411850654-119) and uses exactly its original common
  list code and guarded application edge; neither occurrence is a new
  caller premise. Both actual common successful coverOption reports are
  kept along with round evidence. The shared parent measure and original
  type/window/child conditions remain explicit.

This is first-round reach, not fixed-point stability or the final
length-fuelled membersAtSeed graph. It establishes no representative,
minimum comparison/transport, reverse path or protected-context law.
No Lean, Git or promotion by author. Gate LocalProof→Proof→PairedProof.

| Frozen Lean source | SHA-256 | Static local closure |
|---|---|---:|
| `NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets.lean` | `99b6631fec3316bde08759ed857a6bfe447fabac1918950790e7f54ce2eeb27a` | 1289 |
| `NumberedWindowInternalCoverCombinedRestrictedFirstReachLocalProof.lean` | `75b9050813cfc414fd2eee2f4ffa31d4cbcdbc1f85f330db7296e2aa409ea5b1` | 1450 |
| `NumberedWindowInternalCoverCombinedRestrictedFirstReachProof.lean` | `aa8fc4dbc78ee4df97175f129994c73436c2c10d2ddf46860874aba188a663ef` | 1451 |
| `NumberedWindowInternalCoverCombinedRestrictedFirstReachPairedProof.lean` | `7d0423283a7ad940e583bc6b9a58ea4d29005c0e27a9b45c903997504c36459f` | 1855 |

No Hydra/Linarith in static closure. Original physical source and exact suppliers:

```text
d8445f3dc85a86a935db0a0c4f7d439335181b792ea62e1aa4eebe0fcc6a2c6e  LogicLineages/PersistentMarking/NumberedWindowInternalSparseRoundReachTargets.lean
7edafdd4f7d974375f45cd85c35778bf0927e9fe154ae9f3e02aaf3bed03907e  LogicLineages/PersistentMarking/NumberedWindowInternalSparseRoundReachChecks.lean
6a15072d8a6e0aa1706f63b4e972186a2c847a61b0fd0f71360f12630ae27ca2  LogicLineages/PersistentMarking/NumberedWindowInternalSparseDirectedRoundsDefinitions.lean
f2ba98f4f13dda6eb8c836a43b9b7972e14c8417fb6ca50649274b69aed87a14  LogicLineages/PersistentMarking/NumberedWindowInternalSparseRoundWindowMotiveProof.lean
042f971cf795a4c79901cc3914c753c7dc4d901732d6c4907567461352d70a39  LogicLineages/PersistentMarking/NumberedWindowInternalSparseOpenRoundsTargets.lean
73e6e82721152bd5ce38f7c126565803fb608ab845b23e7fccd71897f03105b4  LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets.lean
ce0bd80da7c6b3a3562797d9f10130a50b57f06a18ebed8e10fd1507c2aefc3f  LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof.lean
```
