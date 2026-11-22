Two statements passed the gate this turn; nothing is drafted and ungated.

## What passed

| Key | Gate module | Receipt | Aliases |
|---|---|---|---|
| `STAGE-CALLBACK-SUPPLIER` | `LogicLineages.PermittedControl.StageCallbackSupplierStatementChecks` | `1795383321915397551-3140006` | 7 |
| `STAGE-CALLBACK-LEGACY` | `LogicLineages.PermittedControl.StageCallbackLegacyStatementChecks` | `1795383385993393338-3140433` | 5 |

All twelve aliases print `[propext, Classical.choice, Quot.sound]`. Both Targets files are unchanged since their freeze (receipt `1795382871845342259-3137004`).

- **`STAGE-CALLBACK-SUPPLIER`** — main theorem `fixed_exactSuppliedStageCallback : ExactSuppliedStageCallback`. For any per-row packet list `alt` with shaped packets and row-level exactness under the raw row majorant (`SupplierExact f B alt`), the compiler built from it has both callback directions and strict dimension decrease at `stageBound`. That compiler is the Cartesian join, then predecessor guard, projection at the shared greatest value, decoding and reification. Hence `HighAtStage f B high (stageChildren alt B)` for every `high` meeting the literal emission equation `Emits alt B high`. This is handoff items (b) and (c), done once and generically.
- **`STAGE-CALLBACK-LEGACY`** — the accepted typed alternatives satisfy that interface for every selected control, and the generic compiler then equals `ActualNamedBitFamilyHighAbove.compile` as an ordered list. This only shows the interface is inhabited; it gives no computable `high`.

## What failed

One gate, receipt `1795383119436183476-3138815`: `StageCallbackSupplierChartProof` had a hypothesis named `scoped`, which is a keyword. I renamed it and re-gated; the failed text is kept under `drafts/fable2/`. No mathematical route failed.

## What is still open

The callback is not closed. The gap is now two independent obligations against frozen definitions:

1. An emittable supplier with `SupplierShape` and `SupplierExact` — this is handoff item (a) in full, and it is not started.
2. A computable `high` with `Emits alt B high`.

The legacy supplier meets the first but cannot meet the second, because it is the old `Finset`-ordered route list.

One finding that shaped the interface: canonical funding needs `inputSignBoundCode`, which is larger than the typed `terminalCutoffCeiling`. So `SupplierExact` offers the raw `rowBound` (which `stageBound` dominates), not the typed need.

## Next

1. Read whether `ActualGreatestCongruenceRoute.packet` is already literal-order, so modular rows can reuse it.
2. Guard exactness on the canonical label order from `exactFiniteFullValueGuards`.
3. Completeness from #1384, then soundness. Soundness is the step I expect to be hardest: proper prefixes of a genuine trace are also emitted and must get false terminals.
4. Survey raw forms for the emission equation before fixing the packet syntax. Projection already has a primitive-recursive code form and `decode` is a plain `def`, so those two are not the blocker.

## For root

- Prefix `StageCallback`; seven new `.lean` files under `LogicLineages/PermittedControl/`.
- The two Targets files were written about a minute before the ledger recorded the prefix; the ledger says so.
- The accepted-record numbers listed in the supplier evidence file are my reading of which bundles own the imported proofs; please confirm against the register before citing them.
- The ledger has a note for Opus B: state the join regression on the joined `tuplePacket`, not on the separately projected rows.

Everything is in `verification/local-fable-pair-2026-11-22/fable2/`: `PLAN.md`, `LEDGER.md`, and a `-SOURCE-MAP.md` and `-EVIDENCE.json` for each key.
