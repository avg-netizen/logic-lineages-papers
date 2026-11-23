# Local Fable-pair continuation, round 6 — 23 November 2026 — handoff

Release: [RELEASE.md](RELEASE.md). Root ledger with every receipt: [root/LEDGER.md](root/LEDGER.md). Lane
ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence:
[evidence/](evidence/). Baseline `8b2613c8c` (the external agent's third push: register 162 checked /
5 pending after it promoted `thm:iteration` and `lem:realization`). Every result is one bounded native
gate through `scripts/check.py` with standard axioms only; Lean is the validity check.

Register unchanged this round: **162 checked / 5 pending / 167**. Pending, all Paper 16:
`lem:arithmetic-accessibility`, `thm:upper`, `lem:tower-cofinality`, `thm:height`, `thm:main`.
No promotion, no manuscript change. Supporting records #1484–#1494.

## The five hypotheses are now four

Before this round the pending statements rested on `NormTheorem BH`, `UniformAccessibility`,
`Calibration D`, `TowerHypotheses D`, `BHIdentification D BH` over ABSTRACT collapse data.

- **`TowerHypotheses` is discharged** (#1486, Opus A): an actual collapse built from the printed
  definitions over the external agent's actual index sequence — hereditary coefficient norm on base-Ω
  Cantor normal forms, criticality as orbit values of the repository's semantic N_B, ψ defined by the
  clause (P) — satisfies every tower hypothesis outright; existence of ψ uses countability of
  small-norm indices and regularity of ω₁. Supporting abstract facts: (P) determines the collapse (#1484,
  root), exists under a solvability hypothesis (#1485, Fable-2 — annotated: that hypothesis is false in
  the actual setting, so #1486 uses its own recursion), basic consequences of (P) (#1490, root).
- **Paper 16 on the actual data** (#1488, Opus A): `lem:tower-cofinality`'s first equality outright;
  `thm:height` and `thm:main` (strongest form, with the external agent's primitive-recursive tower codes)
  from exactly `NormTheorem BH`, `UniformAccessibility`, `Calibration (veblenData …)`,
  `BHIdentification (veblenData …) BH`.
- **`Calibration` is proved for n = 0, 1, 2** (#1488, #1491) and has three semantic layers toward n = 3
  (#1493): `fix` gives least fixed points above its argument; the `B_0` lemma (needs ω² ≤ h(ω); false
  for successor); the level invariant for `B_0`. Open: the description of ψ on [Ω, Ω^Ω) (frozen as T4)
  and n = 3 itself (T5). The general level-l invariant is written out in
  [opusA/CALIBRATION-INDUCTION-NOTE.md](opusA/CALIBRATION-INDUCTION-NOTE.md); Opus A sizes all n at
  3–10k lines — a formalization of Simmons 2004 §§5–6 and 2008 §5, not assembly. Finding: continuity of
  Next and N_B at limits is false, and is not used.
- **`BHIdentification`**: two readings set out in `opusA/ACTUAL-COLLAPSE-SOURCE-MAP.md` — BH defined as
  ψ_B(Λ) (then the identification is definitional and the cited fact moves into `NormTheorem`), or BH
  Pohlers's ordinal defined independently (the paper's sentence reads this way). Either way exactly one
  external fact remains there.

## Internal accessibility (`UniformAccessibility` = `lem:arithmetic-accessibility`)

[opusB/ACCESSIBILITY-PLAN.md](opusB/ACCESSIBILITY-PLAN.md) orders the printed proof's components as
internal statements, with status. New this round, compiled inside the ID₁ calculus for open terms:
J closed under multiset union (#1487); I(q) ⇒ J({q}) and accessible members ⇒ J (#1489); the empty code
is a J-carrier (#1492); and, for an explicitly guarded direct checker that is as admissible as the
original, no replacement step leaves the empty code (#1494). Remaining premises of these components:
`CarrierUnion`, `MultisetSplit`, `SingletonCarrier`, `DescendantGeneration`, `MemberGeneration`.

**The structural finding** (Opus B): the four presentation programs exist only as existence witnesses
from primitive-recursiveness proofs, so their code is not visible inside the calculus and open-term
facts about them cannot be derived; guards help only where a visible prefix test decides the fact. The
recommendation is to re-instantiate the internal line at explicit program definitions
(`opusB/ACCESSIBILITY-PLAN.md`, dated section; `opusB/OPEN-TERM-ARITHMETIC-NOTE.md`). Estimate: six
further skeleton components plus nine arithmetic obligations; the supporting library 4–6 rounds.

## State

- Consolidated gate over this round's 30 new modules: exit 0, receipt `1795415180860008269-3320703`
  ([log](logs/final-consolidated-gate.txt)).
- Second Fable instance: one fresh session, $0.89 (H02); $71.26 over six rounds; API credits, no
  subscription fallback observed.
- Run policy re-paused. This round is not committed.
