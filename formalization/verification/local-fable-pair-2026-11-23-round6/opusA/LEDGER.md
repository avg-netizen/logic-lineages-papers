# Opus A ledger — round 6

## Task: actual collapse (prefix ActualCollapse)
- Read the #1479 tower, #1463, #1484 and Fable-2's existence module, plus ordinals.tex 593–610.
- Decisions:
  - Indices are `ξ ≤ Λ`, where the hereditary norm terminates.
  - Values are `Ordinal.{0}`, proved `< ω₁`.
  - Criticality is the orbit of the repository's semantic `N_B` from `Γ_0` (#1462).
  - ψ is my own well-founded recursion. Fable-2's `Solvable` needs arbitrary `prev` and is false here.
- Definitions compiled at the second attempt (missing CNF import): `1795413208611141409-3313464`. Targets frozen:
  `1795413235508917218-3313564`.
- Norm layer: fail `1795413322314069921-3313824` (induction motive, attach/map lemma), then **PASS**
  `1795413344474868888-3313926`. Includes `normCountable`.
- Criticality layer: fail `1795413436327966987-3314268` (a `zero_le` form; Regular import), then **PASS**
  `1795413452421064524-3314359`.
- Existence/(P): **PASS** first time, `1795413498952400102-3314487`.
- Assembly: **PASS** first time, `1795413517308973235-3314617`. `actualTowerHypotheses` and `actualTowerSupremum` hold
  outright; there are no residual hypotheses.
- Wrote `ACTUAL-COLLAPSE-SOURCE-MAP.md` (with the BH-reading paragraph) and `ACTUAL-COLLAPSE-EVIDENCE.json`.

## Task: ActualCollapseMain (re-close on actual data)
- Found #1477 (`ConditionalMain16UniformEffectiveCoded`, the external agent's coded form) and #1473/#1474.
- `ActualCollapseMainTargets` frozen: sha `aa31516e…ef31`, receipt `1795413729690514195-3315280`.
- `ActualCollapseMainProof` **PASS** on the first gate, `1795413791081556546-3315542`. Theorems: `solutionExists`,
  `actualTowerCofinality`, `actualHeightEffective`, `actualMain16` (four hypotheses) and `calibrationFirstInstances`
  (n = 0, 1). Peak 1,185,272 KiB.
- Wrote `ACTUAL-COLLAPSE-MAIN-SOURCE-MAP.md` (calibration analysis: n = 2 is the first non-definitional instance) and
  `ACTUAL-COLLAPSE-MAIN-EVIDENCE.json`.

## Task: ActualCalibration (monotonicity, comparison, n = 2)
- Targets frozen: `1795414149544123977-3316676`.
- Layer 1 (monotone): two fails (ordinal add-mono lemma names: `add_le_add_right`/`add_lt_add_right` argument order),
  then **PASS** `1795414267122070603-3317173`.
- Layer 2 (comparison): one fail (missing `open Cardinal`), then **PASS** `1795414344456309033-3317393`.
- Layer 3 (n = 2): four fails (CNF/ω₁ defeq, `Nonempty (EarlierStages w)`, dependent rewrite, `norm_num` not
  available, `lt_or_le` name, `rw` through `let`), then **PASS** `1795414486482435704-3317900`.
  `calibrationTwo`: `Δ_2' = ψ(Ω)`.
- Checks: `1795414527299825250-3318034`, with axioms printed for all three statements.
- Finding: `Next` and `N_B` are not continuous; no argument needs continuity.
- Wrote `ACTUAL-CALIBRATION-SOURCE-MAP.md` (the n = 3 obstacle and the size estimate) and
  `ACTUAL-CALIBRATION-EVIDENCE.json`.

## Task: ActualCalibrationThree (n = 3)
- Targets frozen: sha `fe4a54a7…afca`, receipt `1795414855188190708-3319458`; the first attempt failed on a missing
  import. The five statements are T1 `FixLeastAbove`, T2 `B0Lemma` (with the necessary `ω² ≤ h(ω)` hypothesis), T3
  `LevelInvariant`, T4 `PsiPowerLevel` and T5 `CalibrationThree`.
- `ActualCalibrationThreeLevelProof`: one fail (a rewrite through a literal), then **PASS**
  `1795414944051898366-3319804`, proving T1–T3 with standard axioms.
- Stopped at the layer boundary: T4 and T5 are open. T4 is the ψ description on `[Ω, Ω^Ω)`, about 1–2k lines.
- Wrote `CALIBRATION-INDUCTION-NOTE.md`, which pins down the level-l invariant (helpfulness by type, the next-level
  clause, the ψ-correspondence `κ_l` by CNF recursion), and `ACTUAL-CALIBRATION-THREE-EVIDENCE.json`.
