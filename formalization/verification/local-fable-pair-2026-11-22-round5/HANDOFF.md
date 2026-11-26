# Local Fable-pair continuation, round 5 — 22/23 November 2026 — handoff

Release: [RELEASE.md](RELEASE.md) ("one more round, then commit and push"). Root ledger with every
receipt: [root/LEDGER.md](root/LEDGER.md). Lane ledgers: [fable2/](fable2/LEDGER.md),
[opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence: [evidence/](evidence/). Every result is one
bounded native gate through `scripts/check.py` with standard axioms only; Lean is the validity check.

Register unchanged: **160 checked / 7 pending / 167**, all pending in Paper 16. No promotion, no
manuscript change. The owner's open questions (promote `thm:iteration`; the last sentence of
`lem:realization`) wait for the external review.

## This round closed the gaps round 4 listed for a reviewer

| Round-4 point | Outcome | Record |
|---|---|---|
| Item 6 of `thm:main` says an *effective* family witnesses the height | The explicit tower family t_n is shown cofinal in BH (every ordinal below BH is below some t_n's rank), with no rank equal to BH; `thm:main` re-closed with it. Effectiveness is the explicit choice-free recursion with `rfl` equations; a `Computable` statement on codes is not given (the native expression type has no `Primcodable` instance). | #1470, #1471 (Opus A) |
| What the height ranges over | Settled by reading the definitions: the Lean height ranges over exactly the field of the printed confined relation (ordinary terms of equal type). Not a restriction. | `opusA/HEIGHT-DOMAIN-NOTE.md` |
| `thm:upper` used internal accessibility one address at a time | The bridge from the uniform all-terms sentence is compiled (three internal steps, all from accepted lemmas); `thm:upper` and `thm:main` re-closed with the uniform hypothesis. | #1472, #1473 (Opus B) |
| Order facts around the endpoint | Λ = sup a_n; tower values strictly below the endpoint value; the supremum is not attained. | #1468 (root) |
| Are the abstract hypotheses even consistent? | Yes: a toy model satisfies the whole bundle of #1463 (consistency only, not the paper's collapse). | #1469 (Fable-2) |

## Where Paper 16 stands after rounds 2–5

- Promotable on a decision: `thm:iteration` (#1446; both tables and the external review say it is the
  printed theorem); `lem:realization` if its last sentence is reworded to what is proved (#1447, #1450,
  #1452; proposal in `../local-fable-pair-2026-11-22-round3/root/P16-REALIZATION-CHAIN-SOURCE-MAP.md`).
- Conditional on cited results, with the paper's own argument fully compiled: `lem:tower-cofinality`
  (#1463, #1468, #1469), `thm:height` (#1465, #1470), `thm:upper` (#1466, #1472), `thm:main` (#1467,
  #1471, #1473). The complete hypothesis list is five items: Pohlers's norm theorem; uniform internal
  accessibility (the still-pending internal sentence of the shared ID₁ targets); the Simmons
  calibration of the tower composites; the tower hypotheses including the characterization (P); the
  identification of the endpoint value with BH. Interface:
  `../local-fable-pair-2026-11-22-round4/opusA/EXTERNAL-INTERFACE.md`.
- `lem:arithmetic-accessibility`: unchanged — the large internal proof; five of its nine printed
  components have no internal counterpart.

## State

- Consolidated gate over all 487 new modules of rounds 3, 4 and 5: exit 0, receipt
  `1795405608384675350-3295490` ([log](logs/final-consolidated-gate.txt)).
- Supporting records this round: #1468–#1473.
- Second Fable instance: one fresh session, $1.00 (H01); $70.37 over five rounds; API credits, no
  subscription fallback observed.
- Run policy re-paused. Rounds 3, 4 and 5 are committed and pushed together at the end of this round.
