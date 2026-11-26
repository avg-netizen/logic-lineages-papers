Two more statements passed the gate this turn, with no failed gate and nothing left drafted. Together with turn 001 they give `HighAtStage f B high (stageChildren canonical B)` for any raw program emitting the canonical children — items (a), (b), (c) at the typed level, with no legacy order. No raw program exists yet; `Emits` is still a hypothesis.

## What passed

| Key | Gate module | Receipt | Aliases |
|---|---|---|---|
| `STAGE-CALLBACK-CANONICAL-ROUTES` | `LogicLineages.PermittedControl.StageCallbackCanonicalRoutesStatementChecks` | `1795384393687194447-3147472` | 10 |
| `STAGE-CALLBACK-CANONICAL-SUPPLIER` | `LogicLineages.PermittedControl.StageCallbackCanonicalSupplierStatementChecks` | `1795384564796366985-3148105` | 4 |

All fourteen aliases print `[propext, Classical.choice, Quot.sound]`. Both Targets files compiled as first written and are unchanged since freeze.

- **Canonical routes** — a route tree for one signed row on first-occurrence (`groupTyped`) syntax. Main theorems:
  - `fixed_exactCanonicalReachedGuards`: at a genuinely reached active node, a guard holds iff its tape is the true comparison tape of the successful reads, and a holding guard carries the genuine zero witness or the requested polarity.
  - `fixed_exactCanonicalRouteSoundness` / `…Completeness`.
  - `fixed_exactCanonicalRoutesAcrossReplay`: both directions under the accepted `LowerSetup` and `replayMinimum` plus `inputSignBoundCode … ≤ z`.
- **Canonical supplier** — signed rows get the rendered canonical routes; congruence rows keep the accepted packet. `fixed_exactCanonicalSupplierExact` shows it meets the turn-001 `SupplierExact`, and `fixed_exactCanonicalStageCallback` gives the stage contract.

## Your three questions

- **Congruence packet:** it is literal-order and already has a primitive-recursive code form (`SharedRankResidueRow.prepareCode`), so I reused it unchanged.
- **Non-stopping prefixes:** fixed in the list, not with a falsity terminal. A node emits leaves only when it stops; the choice and reasons were written in the ledger before freezing. Either option needs the node's status, and omitting a leaf is less work than rendering a falsity packet.
- **Frozen interface:** the canonical supplier meets turn-001 `SupplierExact` unchanged. The extra sign payment sits inside `rowBound` for all three order tests, so no new Targets module was needed.

## Two things that affect the raw program

- **The accepted raw `prefixes` list cannot be the supplier's list.** `stepCode` ignores `top` and continues through nodes that are inactive at the greatest rank, which are not genuine canonical steps. The raw iteration needs an activity test.
- **List order.** `canonical` lists signed alternatives depth-first; a raw level iteration will produce level order, and `Emits` is a literal list equation. The fix is a second supplier defined by the same level iteration plus a "same members" lemma; exactness then follows from what is already gated. It should be designed together with the raw step.

## On Opus B's survey

`S4-SURVEY.md` appeared after my own minimal check; I read it and agree with it. One addition: dropping the `properClauses` filter from `packets` is not free for the canonical supplier. Grouping discards zero-weight occurrences, so a row with an improper operand of total weight zero would get packets that can hold although the row has no value. The raw program needs the properness decider.

## Next

1. Fix the level-order entry type and raw level step (from `groupedCode`, a raw activity test, raw guard rendering); freeze the level-order supplier and prove it has the same members as `routes`.
2. Raw guard rendering for `compile` and `canonicalPacket` with calibration to `preparedPacketCode` — neither lane has surveyed this, so it is the main unknown.
3. Raw packet algebra, decode and chart prefix, assembled with the accepted projection, clause, chart and rank codes.
4. Raw properness filter (Opus B appears to have started).
5. Close with `∃ high, Computable high ∧ HighAtStage …`, then `ForControl`.

## For root

- Seven new `.lean` files this turn, all under the `StageCallback` prefix.
- The canonical supplier proof imports `StageCallbackLegacyProof` for one helper (`singleNeed`), so #1388 is a dependency of the new supplier key.
- Record numbers quoted in the ledger's proof summary are as I read them from file names; please confirm before citing.

Everything is in `verification/local-fable-pair-2026-11-22/fable2/`: the ledger's turn-002 section, a `PLAN.md` addendum, and a `-SOURCE-MAP.md` and `-EVIDENCE.json` for each new key.
