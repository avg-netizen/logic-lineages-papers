# Local Fable-pair continuation, round 4 — 22 November 2026 (late night) — handoff

Release: [RELEASE.md](RELEASE.md). Root ledger with every receipt: [root/LEDGER.md](root/LEDGER.md). Lane
ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence per
record: [evidence/](evidence/). Every result is one bounded native gate through `scripts/check.py` with
standard axioms only; Lean is the validity check.

Register unchanged this round: **160 checked / 7 pending / 167** (all pending in Paper 16). The owner
deferred the two open questions (promote `thm:iteration`; reword `lem:realization`) until after this
round and the external review; no promotion and no manuscript change was made.

## What this round did

The remaining Paper 16 statements rest on the internal ID₁ accessibility proof and on results cited from
Simmons and Pohlers for which the repository has no definitions. This round compiled the paper's OWN
arguments for them conditionally: each cited result is an explicit, named, uninstantiated hypothesis
over abstract data, and everything else is checked.

| Statement | Record | Hypotheses (and nothing else) |
|---|---|---|
| `lem:tower-cofinality` | #1463 (root) | the cited characterization (P) of the collapse; tower arguments increasing, below and cofinal in the endpoint; |a_n| ≤ 1; critical values exceed one and are closed under increasing countable suprema; for "= BH", the cited identification |
| `thm:height` | #1465 (Opus A) | the cited calibration Δ_n' = ψ(a_n); the tower hypotheses of #1463; the BH identification; the conclusion of `thm:upper` |
| `thm:upper` | #1466 (Opus B) | Pohlers's norm theorem; internal accessibility in its individual form |
| `thm:main` (Paper 16) | #1467 (Opus B) | the five above: norm theorem, internal accessibility, calibration, tower hypotheses, BH identification. Items 1–5 are proved outright. |

Shared interface: `LogicLineages/NativeModule/PersistentMarking/ExternalOrdinalInterfaceTargets.lean` and
`…ID1Targets.lean` ([opusA/EXTERNAL-INTERFACE.md](opusA/EXTERNAL-INTERFACE.md)), built on root's
`CollapseData`/`TowerHypotheses`. Source maps: [root/P16-CONDITIONAL-TOWER-COFINALITY-SOURCE-MAP.md](root/P16-CONDITIONAL-TOWER-COFINALITY-SOURCE-MAP.md),
[opusA/CONDITIONAL-HEIGHT-SOURCE-MAP.md](opusA/CONDITIONAL-HEIGHT-SOURCE-MAP.md),
`opusB/UPPER-SOURCE-MAP.md`, `opusB/MAIN16-SOURCE-MAP.md`.

**These are supporting statements. None promotes a numbered statement**: the hypotheses concern objects
(ψ_B, the coefficient norm, criticality, BH) that are not defined in the repository, and the internal
accessibility statement is `lem:arithmetic-accessibility` itself.

## Points for a reviewer

1. **Inputs the paper uses without proof** (Opus A; already inside `TowerHypotheses`): critical values
   are closed under countable increasing suprema; every critical value exceeds one; the order facts on
   a_n and Λ. They belong to the cited Simmons setting.
2. **What the height ranges over** (Opus A): `thm:height` is stated over ordinary terms, since
   `thm:upper` bounds only those. If the printed "descending height of ⊐" ranges over a larger set, the
   printed proof has no upper bound for the extra ranks.
3. **Effectiveness in item 6 of `thm:main`** (Opus B): the paper says an *effective* family of closed
   native terms has cofinal ranks; the height statement used says only that the native height is BH.
4. **Two forms of internal accessibility** (Opus B): `thm:upper` uses the individual form (a derivation
   of the I-atom at each admitted address). The uniform all-terms sentence is not shown to imply it;
   the three missing ID₁ steps are listed in `opusB/UPPER-SOURCE-MAP.md`.
5. **Readings in #1463** (root): "1 < ψ_B(a_m)" is obtained from "critical values exceed one"; the
   supremum is any least upper bound.
6. **Application step** (Fable-2, #1464): #1461's statements are about a refitted scalar that is not the
   scalar of any accepted installed tuple unless every accepted address's type lies in the finite window
   list; #1461 is annotated with what it may be cited for.

## State

- Module-system copies: 397 more this round (items 1–5 of `thm:main` and the ID₁ vocabulary), one
  `private` removed; manifest `opusB/twin/TWIN-MANIFEST-ROUND4.json`.
- Consolidated gate over all 472 uncommitted new modules (rounds 3 and 4): exit 0, receipt
  `1795404487277213682-3291494` ([log](logs/final-consolidated-gate.txt)).
- Second Fable instance: one fresh session, $4.48 (G06); $69.37 over the four rounds; about $5 of the
  owner's stated credit left.
- Run policy re-paused. Rounds 3 and 4 are not committed.

## What is left for Paper 16

To turn the four conditional theorems into numbered statements one needs either (a) the internal ID₁
accessibility proof — five of its nine printed components still have no internal counterpart — together
with a formalized ordinal analysis of ID₁ (Pohlers) and the Simmons calibration, with definitions of
ψ_B and BH; or (b) an owner decision to accept cited results as stated hypotheses, which the register's
current rule ("no added theorem premises") does not allow.
