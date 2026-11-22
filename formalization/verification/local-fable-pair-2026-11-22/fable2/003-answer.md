Two more statements passed the gate this turn: the level-order supplier with its stage contract, and the raw per-row level program calibrated to it. The three rendering programs for guard, linear exit and congruence packet are surveyed and their target statements are written in the ledger, but none is frozen or gated yet.

## What passed

| Key | Gate module | Receipt | Aliases |
|---|---|---|---|
| `STAGE-CALLBACK-LEVEL-ORDER` | `LogicLineages.PermittedControl.StageCallbackLevelOrderStatementChecks` | `1795385070227028433-3150794` | 7 |
| `STAGE-CALLBACK-RAW-LEVEL` | `LogicLineages.PermittedControl.StageCallbackRawLevelStatementChecks` | `1795385515892315614-3152703` | 5 |

All twelve aliases print `[propext, Classical.choice, Quot.sound]`, read from the gate logs.

- **Level order** — `levelOrder` lists a signed row's alternatives as a raw level iteration would: children only at nodes active at `top`, leaves collected level by level. It has the same members per row as #1395's `canonical`, so shape and exactness transfer. The corollary you asked for is in the frozen target: `fixed_exactLevelOrderStageCallback : Emits levelOrder B high → HighAtStage f B high (stageChildren levelOrder B)`. This is the one supplier for the close step.
- **Raw level** — `fixed_exactRawRowPackets`: for every exact rendering `R` and every literal bit row, `rowCode R r top (encodeBitRow row) = (levelOrder r top row).map encodePacket`. The program is assembled from accepted raw pieces only, including the activity test `tapeHighestCode` that `stepCode` lacks. It is parametric in a record of four rendering programs (`append`, `guard`, `linear`, `modular`), each with one calibration equation.

## What failed

One compile of the raw-level Targets file before it was frozen (receipt `1795385296653086064-3151882`): inside `Rendering.Exact`, bare `guard` and `append` resolved to the record's own fields. I qualified the names; no statement changed in meaning. The failed draft is in `drafts/fable2/`.

## Rendering survey

I wrote the survey and the exact statements in the ledger before freezing the raw-level target.

- **Packet code:** I use Opus B's frozen `RawPacketAlgebra.encodePacket`, importing its Targets file only.
- **Guard (`compile`):** every ingredient I looked for exists — the base packet compiler with `Primrec`, `rawSameForm` for the equal-rank case, `appendCode`. A raw `normalizeShortField` on field codes is the one piece not yet read. What remains is assembly. I first recorded two of these as "not found" and corrected that in the ledger.
- **Linear exit (`canonicalPacket`):** nothing accepted renders its row, but it is a rank filter plus one row through `testFormula`.
- **Congruence packet:** `prepareCode` gives the formula code; table bytes and polarity are to add.

## What Opus B's pieces must satisfy

These are in the ledger for you to pass on:

1. `ExactAppendCode` and `Primrec₂ appendCode` gated — my leaf join and the guard rendering use `appendCode` inside the row program.
2. One residual program `childCode (C, top, qs.map encodePacket) = encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top))))` for every packet list, with no shape hypothesis, plus `Primrec`.
3. Nothing about charts, ranking or names; those are already literal list equalities.

The ledger also gives the definition of `high` and the chain of list equations that makes `Emits levelOrder B high`.

## Still open

- The three rendering programs with their calibrations (mine).
- `Primrec` of `rowCode R` (mine; not frozen).
- Opus B's two items above.
- The final assembly of `high`, with `Emits levelOrder B high` and `Computable high`.

## Next

Linear exit first (smallest, and it fixes the row/atom encoding the guard also needs), then guard, then congruence, each with its `Primrec` proof written alongside. Then effectivity of `rowCode R`, then the assembly once Opus B's residual program is gated. The congruence rendering and the effectivity proof are independent of the other two if you want to split them off.

## For root

- The raw-level main target is conditional on `Rendering.Exact`. The four equations say only that each program computes the code of the corresponding typed packet; please judge at scope check whether that interface hypothesis is acceptable for a supporting record.
- Six new `.lean` files this turn, all under the `StageCallback` prefix.

Everything is in `verification/local-fable-pair-2026-11-22/fable2/`: the ledger's turn-003 section, a `PLAN.md` addendum, and a `-SOURCE-MAP.md` and `-EVIDENCE.json` for each new key.
