Two rendering programs passed the gate this turn — the linear exit and the congruence packet, each with its calibration equation and `Primrec` proof. The guard rendering is not written, so `Rendering.Exact` is not yet discharged for any concrete `R`, and effectivity of `rowCode R` is not started.

## What passed

| Key | Gate module | Receipt | Aliases |
|---|---|---|---|
| `STAGE-CALLBACK-RENDER-LINEAR` | `LogicLineages.PermittedControl.StageCallbackRenderLinearStatementChecks` | `1795385975542327937-3154727` | 3 |
| `STAGE-CALLBACK-RENDER-MODULAR` | `LogicLineages.PermittedControl.StageCallbackRenderModularStatementChecks` | `1795386238420603404-3156069` | 3 |

All six aliases print `[propext, Classical.choice, Quot.sound]`, read from the gate logs. Both Targets files compiled as first written and are unchanged since freeze.

- **Linear exit** — `fixed_exactLinearCode` is word for word the `linear` field of `Rendering.Exact` with `R.linear := linearCode`: `linearCode top (encodeSyntax s) (orderCode test) positive = encodePacket (canonicalPacket top s.constant s.terms test.test positive)`, with no hypothesis. `fixed_linearCodeEffectivity` gives `Primrec` for every component and for `linearCode`.
- **Congruence packet** — `fixed_exactModularCode` is the `modular` field with `R.modular := modularCode`, for every modulus including zero. `fixed_modularCodeEffectivity` gives `Primrec` of `lowerRanksCode`, `formulaCode` and `modularCode`.

## What failed

One gate, receipt `1795386142358861068-3155645`: the congruence `Primrec` proof timed out at `whnf` in its final composite. The component facts had already elaborated. I split the composite into small lemmas and made the heavy definitions locally irreducible; no heartbeat limit was raised and no statement changed. The failed draft is in `drafts/fable2/`.

## One thing worth knowing

The accepted `SharedRankResidueRow.CodeExact` calibrates the residue-row formula code only through `prepareCode`, which is `none` at modulus zero, while `Rendering.Exact.modular` ranges over every row. The literal equation and `Primrec` of `formulaCode` hold for every modulus by the accepted private proofs, so I restated those two lemmas. No accepted module was edited.

## Status of `Rendering.Exact`

| Field | Program | Calibration | `Primrec` |
|---|---|---|---|
| `append` | `RawPacketAlgebra.appendCode` | gated by Opus B | gated by Opus B |
| `linear` | `linearCode` | gated this turn | gated this turn |
| `modular` | `modularCode` | gated this turn | gated this turn |
| `guard` | not written | — | — |

## On Opus B's pieces

Its ledger showed the join group (`appendCode`) and the guard group (prepend, cutoff, project) as gated. The residual group had frozen targets and proof files on disk, but I saw no passing receipt for it at 22:16Z. This turn's two keys needed neither `appendCode` nor the residual group, so no dependency hypothesis was introduced.

## Next

1. Guard rendering with calibration and `Primrec`, written as small lemmas with heavy definitions locally irreducible from the start.
2. Assemble one concrete `R₀` and prove `R₀.Exact`.
3. `Primrec` of `rowCode R₀`. This can be stated for any `R` with primitive recursive fields, so it does not wait on the guard.
4. Once Opus B's residual program is gated: define `high`, prove `Emits levelOrder B high` and `Computable high`, and end in `ComputableEmitter f B` with `alt := levelOrder`, as #1396 requires.

## For root

- Eight new `.lean` files this turn, all under the `StageCallback` prefix.
- The congruence key imports the linear key's calibration proof for `polarityCode`, so the linear record is a dependency of the congruence record.
- I moved turn 003's closing "Risks" paragraph in the ledger back to the end of its own section, unchanged; my insert-style edits had left it stranded after turn 004. A housekeeping note in the ledger says so.

Everything is in `verification/local-fable-pair-2026-11-22/fable2/`: the ledger's turn-004 section, a `PLAN.md` addendum, and a `-SOURCE-MAP.md` and `-EVIDENCE.json` for each new key.
