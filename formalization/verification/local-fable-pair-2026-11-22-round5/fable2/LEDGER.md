# Fable-2 ledger — local-fable-pair-2026-11-22-round5

(File created by Fable-2 in H01; it did not exist when the lane started.)

## H01 — model

Task: non-vacuity of `TowerHypotheses` (record #1463, Paper 16 `lem:tower-cofinality`).

- 2026-11-23T03:39:40Z — Targets module frozen BEFORE any proof was written:
  `LogicLineages/PersistentMarking/ConditionalTowerCofinalityModelTargets.lean`
  sha256 `bbf80361be7baad1196635cf85c427882588d12d32a078689c410acbfb5ec96e`
  Statements: `toyModel`, `ToyModelSatisfiesHypotheses`, `TowerHypothesesConsistent`,
  `ToyModelConclusion`, `ToyModelConditionalInstance`.
  Model: `I = O = ENat`; `a n = n`; `endpoint = ⊤`; `one = 0`; `norm = 0`;
  `critical θ := 0 < θ`; `psi ξ = ξ + 1` (so `psi ⊤ = ⊤`).
- 2026-11-23T03:40:05Z — Gate PASS on first attempt (Targets unchanged since freeze, sha256 re-checked):
  `gate.sh mathlib …ConditionalTowerCofinalityModelTargets …ConditionalTowerCofinalityModelProof`
  → `COMPILE_PASS` both, receipt `build-reports/1795405199376168853-3293755.json`.
  Proof module `LogicLineages/PersistentMarking/ConditionalTowerCofinalityModelProof.lean`
  sha256 `d530e3aeec1c73a178f696897c28e590c36e7f1be9efc1e9e9137e2278b8deb9`.
  Theorems: `toyCharacterization`, `toyModelSatisfiesHypotheses`, `towerHypothesesConsistent`,
  `toyModelConclusion`, `toyModelConditionalInstance`; each `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. No sorry/axiom/native_decide. No existing `.lean` edited.
- Observations: suggested model verified as given (`psi ξ = ξ + 1` is the least value in (P), no
  adjustment needed). In the model `norm` is constant, so `normBound` and the norm premise of (P) are
  only trivially exercised; `criticalSup` did not need `StrictMono f`. Consistency only — nothing here
  bears on whether the paper's real collapse satisfies the cited hypotheses.
- Wrote `TOWER-MODEL-EVIDENCE.json`, `TOWER-MODEL-SOURCE-MAP.md`. H01 closed.
