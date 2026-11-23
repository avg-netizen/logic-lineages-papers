# Original insertion target map

Exact gate: `LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapChecks`.
The literal scratch recursion tests each actual tag-4 row, prepends its original
field zero using the actual cons code, and propagates an invalid row/tail as
zero. Success is one plus the actual scratch-list code, including empty success.
The frontend uses the actual sparse raw insertion parser and preserves failure.
Numeric calibration is the original `entries` decoder followed by
`List.map Prod.fst` (the original direct target projection); no sorting,
deduplication, or membership substitution. Open graph laws are the exact
original recursor's nil/cons equations for this installed AST only, not
open reflection of target permutation, installed d, or J.

```
b3ccd8c076ff66911a2fa07a7ce79cff8b0f8eb81eff04ffc35d91c2dc7a58fe  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedTargetsMapChecks.lean
032b3b035e303fe0dc7d895a2688453402d7f77e24e65dbca1abe3f66dc7d2b4  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedTargetsMapOpenProof.lean
fa82a454323d3dddf8a74be5d4a55c66b83ca66d15be58f02a49aabaeed2e41b  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedTargetsMapProof.lean
ffdc5ab0b0685261b397e3058ccc25806f856df7dca07bb2798c1415fb840de5  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedTargetsMapTargets.lean
```
