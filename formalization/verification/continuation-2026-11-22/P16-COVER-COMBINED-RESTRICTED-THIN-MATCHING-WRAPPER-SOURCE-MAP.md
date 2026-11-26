# P16 exact thin physical matching wrapper on the combined restricted P

Frozen (awaiting native). The original historical wrapper target contains unrelated wide imports, including unavailable Hydra. This independent thin recut reproduces the exact original program expressions below, using the same constructor order, exact same context parser and pool procedures, and literal same `[ctx,ty,raw]` tape. It does not import, change, or assert a checked nominal equality to the historical declarations or tuple; no dependency substitution or broad checked join. The source correspondence is the matching expression correspondence, not a cross-W theorem.

| Historical definition | Thin source counterpart | Same physical expression |
|---|---|---|
| `SparseCoveredWindowTargets.ownSeed` | `thinOwnSeed` | `.composition scratchMember ![poolAtSeed C s,.projection 2]` |
| `SparseCoveredWindowTargets.contextPresent` | `thinContextPresent` | `branch contextOption (constantZero 3) (constantOne 3)` |
| `SparseCoveredWindowTargets.coveredWindow` | `thinCoveredWindow` | `conjunction baseW (conjunction contextPresent (ownSeed C s))` |
| `SparseStructuralApplicationTargets.syntaxWindow` | `thinSyntaxWindow` | `conjunction baseW (.composition V (fun _ : Fin 1 => .projection 2))` |
| `SparseStructuralApplicationTargets.window` | `thinMatchingWindow` | `coveredWindow C s (syntaxWindow baseW V)` |

The original check uses the actual child tape and pool. Here the generic tape cut composes the exact actual selected vertices and raw key to and from the actual own-seed graph. Under the selected P, genuine held V, W and **actual positive context parser** are distinct antecedents. Actual original program totality chooses the exact scratch vertices at [raw]; the checked same-P own induction supplies actual membership in that list. Actual graph rules assemble the true wrapper checks at this same typed ctx/ty/raw, without external scratch or inferred parser success from arbitrary P.W. No old W calibration or equivalence, prior callback swap, minimum equality, protected/fresh ports or well-foundedness. Gate Targets → Tape → Wrapper. Static closure excludes Hydra/Linarith.

## Read-only historical source pins

| PersistentMarking file | SHA-256 |
|---|---|
| `NumberedWindowInternalSparseCoveredWindowTargets.lean` | `c12b0c76a5d8ab2647948fa27ffbf4acf574e43b1e42c78fd47946c4bf9a773f` |
| `NumberedWindowInternalSparseStructuralApplicationTargets.lean` | `6630c2b024c2e480ba0da775aa9a0f0e78390a41d687e86f563663063e3eba92` |
| `NumberedWindowInternalSparsePackedLeastDefinitions.lean` | `a4c7811b49df019fffbc09cd506ea5eedf97390544f16f02b0baf396069d53b4` |

## Frozen source pins

| File (PersistentMarking) | SHA-256 | Static closure including root |
|---|---|---:|
| `NumberedWindowInternalCoverCombinedRestrictedWrapperTargets.lean` | `ac7eca6847cbbde358b81750c3bb5a5e45651447cdd3294ea017c50f12083cbd` | 1279 |
| `NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof.lean` | `12cdecb78f68e1687f343bc03d77f5cb3ebdea95174aa26d6345825cc68f396c` | 1280 |
| `NumberedWindowInternalCoverCombinedRestrictedWrapperProof.lean` | `2fbbc163d85e4abae9d544ba79ad4fb64fd04586179894f0d6faea3708d9fb18` | 1779 |
