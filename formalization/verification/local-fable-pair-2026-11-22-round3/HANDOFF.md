# Local Fable-pair continuation, round 3 — 22 November 2026 (night) — handoff

Release: [RELEASE.md](RELEASE.md). Root ledger with every receipt: [root/LEDGER.md](root/LEDGER.md). Lane
ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence per
record: [evidence/](evidence/). Baseline `fd88501ef` (the external review of round 2). Every result is one
bounded native gate through `scripts/check.py` with standard axioms only; Lean is the validity check.

## Register: 160 checked / 7 pending / 167 — Paper 17 complete

The owner promoted Paper 17 `thm:main` ("promote thm:main if you judge it to be ready"): numbered record
#1451 on `UniformMainComparison`, proved in round 2 and checked against the paper by the external
round-2 review. Paper 17 is 33 of 33. All seven pending statements are Paper 16:
`lem:arithmetic-accessibility`, `thm:upper`, `lem:realization`, `thm:iteration`, `lem:tower-cofinality`,
`thm:height`, `thm:main`.

## Paper 16 — everything that is the paper's own construction is now compiled

On the module-system copies under `LogicLineages/NativeModule/` (round 2's 671 copies plus 43 this
round; manifest `opusB/twin/TWIN-MANIFEST-ROUND3.json`; no tracked file edited):

- **`thm:iteration`** — compiled in round 2 (#1446); both external and internal tables say it is the
  printed theorem. **Ready for promotion; awaiting the owner's word.**
- **`lem:realization`** — closure clauses #1447; this round the two sentences of the printed proof's last
  paragraph as statements: finite chains (#1450) and the abstraction rule along finite chains (#1452).
  The printed last sentence still promises more than is proved. A replacement sentence is proposed in
  [root/P16-REALIZATION-CHAIN-SOURCE-MAP.md](root/P16-REALIZATION-CHAIN-SOURCE-MAP.md), not applied.
  **Owner decision: reword (then promotable) or leave pending.**
- **`thm:height`, the paper's own part** — native arithmetic realizers (#1456), every tower term `B_l`
  (#1458, #1459) and every `t_n` of construction (D) realizing its semantic composite (#1462). What
  remains is external: Simmons's calibration Δ_n' = ψ_B(a_n), the characterization (P) of ψ_B, the
  identification with the Bachmann–Howard ordinal, Pohlers's norm theorem — none has definitions in the
  repository (no Ω-based notation, no collapse, no BH) — plus `thm:upper`. Step table:
  [opusA/NATIVE-TOWER-SEQUENCE-SOURCE-MAP.md](opusA/NATIVE-TOWER-SEQUENCE-SOURCE-MAP.md).
- **`thm:upper`, the compiled chain** — scalar stage rank and norm (#1454), class rank = address rank =
  least stage of the tagged operator (#1455), joined with round 2's rank bound into one statement
  (#1460): the confined rank of a typed ordinary term is at most the least stage of the tagged ID₁
  operator at the address of its translation. Table and the two residual statements:
  [opusB/P16-THM-UPPER-CHAIN-CORRESPONDENCE.md](opusB/P16-THM-UPPER-CHAIN-CORRESPONDENCE.md). Remaining:
  the internal derivation of accessibility (= `lem:arithmetic-accessibility`) and Pohlers's norm theorem.
- **`lem:arithmetic-accessibility`** — internal arithmetic support compiled (pair and decode programs,
  #1457). The application step (Fable-2): #1453 replaced the type guards by a premise that session G05
  then found to be false for the actual type programs (#1453 is annotated); #1461 is the honest
  alternative, for a refitted scalar, under two open codomain-inversion premises and with the lane's own
  caveat that the numeric installation chain was not re-checked for it. The fresh-probe typed totality
  has statements only. Five of the lemma's nine printed components still have no internal counterpart.

## What a next round could do

1. Promote `thm:iteration`; decide the `lem:realization` sentence.
2. Nothing else in Paper 16 closes without either the large internal ID₁ proof or formalizing the
   external ordinal analysis (Simmons, Pohlers). The gap documents above list the exact statements.

## End of round

Consolidated gate over this round's 61 new modules: exit 0, receipt `1795403035990488897-3280055`
([log](logs/final-consolidated-gate.txt)). Supporting records #1450, #1452–#1462; numbered #1451.
Second Fable instance: two fresh sessions, $6.69 (G04 $2.23, G05 $4.46), API credits, no subscription
fallback; $64.89 over the three rounds. Run policy re-paused. Nothing from this round is committed.
