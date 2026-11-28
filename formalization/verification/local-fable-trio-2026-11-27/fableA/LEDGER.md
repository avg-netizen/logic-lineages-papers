# Fable A ledger — ordinal calibration lane, 27 November 2026

(append-only)

## Entry 1 — reading done, verdict on the frozen T4, division of work with root

- Read BRIEF.md, the round-6 calibration note / source maps / ledger, all `ActualCollapse*` and
  `ActualCalibration*` modules, the tower/orbit definitions, and ordinals.tex 520–640.
- **T4 (`PsiPowerLevel`) is TRUE AS FROZEN and is NOT being restated.** Hypothesis "no fixed point of
  `L` in `[1, e]`" is the right one (it is necessary: if `L λ = λ` with `1 ≤ λ < e` then
  `ψ(Ω^e) = λ ≠ L e`; "`e < L e`" alone would not do). Conclusion `ψ(Ω^e) = L e = D e 0` unchanged.
  Root's reduction `PsiPowerLevel → CalibrationThree` can consume the frozen statement verbatim.
- Root message received: root takes T5 (`PsiPowerLevel → CalibrationThree`) and its L-facts. I am NOT
  writing T5. **Nothing of T5 / the L-facts is on disk from me yet.** However my T4 proof needs several
  of the same function-side facts, so they will exist in my module
  `LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeHierarchyProof`
  (namespace `…ActualCalibrationThree`), planned names:
  - `level_lt_succ` : `β'.val = β.val + 1 → (level β x).val < (level β' x).val` (strict T3, every `x`)
  - `levelZero_strict` : `α.val < β.val → (level α 0).val < (level β 0).val`
  - `levelZero_id_le` : `α.val ≤ (level α 0).val`
  - `level_limit` : `(level l x).val = ⨆ e, (level (earlierStage l e) x).val` at limits
  - `levelZero_closed_fix` : if `1 < Θ` and `L e < Θ` for all `1 ≤ e < Θ` then `L` has a fixed point
    `θ` with `1 ≤ θ ≤ Θ`
  - `base_lt_level` : `Γ_0 < level e 0` for `e ≥ 1`;  `level_base_eq` : `level e Γ_0 = level e 0` for `e ≥ 1`
  - `veblen_double` : `y + y ≤ N_B y`;  `enumFix_limit` : positive fixed points of `E_β` are limits
  and in `…ActualCalibrationThreeCriticalProof`:
  - `level_critical` : `1 ≤ e.val → Critical N_B Γ_0 (level e x).val` (so the fixed point `κ = L κ` is critical)
  Root: reuse these once gated (receipt will be recorded below) rather than re-deriving; if you have
  already proved your own versions, nothing here conflicts.
- Plan of record: `fableA/T4-PROOF-PLAN.md`.

## Entry 2 — targets frozen; function-side layers gated (first attempt)

- Frozen: `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationThreePsiTargets.lean`
  (definitions `levelEnum`, `psiO`, `NormSeparated`; statements `VeblenDoubling`, `LevelStrict`,
  `LevelCritical`, `LevelBaseRestart`, `UpperStep`, `LowerStep`). sha256 in Entry 3. Source map:
  `fableA/CALIBRATION-THREE-PSI-SOURCE-MAP.md`.
- Gate 1 **PASS**, receipt `1795775348133540559-930683` (log `fableA/gatelogs/gate1.txt`):
  `ActualCalibrationThreePsiTargets`, `ActualCalibrationThreeHierarchyProof`
  (`veblenDoubling`, `levelStrict`, `levelBaseRestart`, plus lemmas `level_lt_succ`, `levelZero_strict`,
  `levelZero_id_le`, `levelZero_closed_fix`, `base_lt_level`, `level_base_eq`, `enumFix_*`),
  `ActualCalibrationThreeCriticalProof` (`levelCritical`, `crit_step`, `critLim`). Standard axioms only.
  Only deprecation warnings.
- Root's interface noted: I will add `exact_LevelFacts : ActualCalibrationThreeReduction.LevelFacts`
  (= `levelZero_strict` ∧ `base_lt_level`) and, after T4, `calibrationThree`.

## Entry 3 — hashes; norm, level-facts and ψ-step layers gated (all first attempt)

- `ActualCalibrationThreePsiTargets.lean` sha256
  `0817507591f2b257b06358724322eedc4b90bf57e2b67b3c01ad8cf001ed4c32` (frozen; gated in receipt
  `1795775348133540559-930683`).
- Gate 2 **PASS**, receipt `1795777920173523546-941350` (log `fableA/gatelogs/gate2.txt`):
  `ActualCalibrationThreeNormProof` (`norm_leading`, `norm_div_le`, `norm_ge_of_mul_le`,
  `norm_ge_exponent`, `nsep_zero/mono/norm_mul/step`), `ActualCalibrationThreeLevelFactsProof`
  (`exact_LevelFacts : ActualCalibrationThreeReduction.LevelFacts`). Standard axioms.
  => T5 is now "T4 only" through root's `exact_ThreeFromPower`.
- Gate 3 **PASS**, receipt `1795777928703118203-941400` (log `fableA/gatelogs/gate3.txt`):
  `ActualCalibrationThreePsiProof` — `upperStep : UpperStep`, `lowerStep : LowerStep` (plus generic
  `psiO_mono`, `psiO_stall`, `psiO_closure`, `psiO_least`). Standard axioms.
- Drafted, gate 4 running: `ActualCalibrationThreePowerProof` (`psiPowerLevel : PsiPowerLevel`, T4) and
  `ActualCalibrationThreeProof` (`calibrationThree : CalibrationThree`, T5, via root's reduction).

## Entry 4 — T4 and T5 gated (first attempt); n = 3 closed

- Gate 4 **PASS**, receipt `1795777954162083312-941567` (log `fableA/gatelogs/gate4.txt`):
  `ActualCalibrationThreePowerProof` — **`psiPowerLevel : PsiPowerLevel`** (frozen T4, statement unchanged),
  also `psiO_power` (same statement on `psiO`). `#print axioms`: propext, Classical.choice, Quot.sound.
- Gate 5 **PASS**, receipt `1795777959277796293-941615` (log `fableA/gatelogs/gate5.txt`):
  `ActualCalibrationThreeProof` — **`calibrationThree : CalibrationThree`** (frozen T5)
  `:= ActualCalibrationThreeReductionProof.exact_ThreeFromPower exact_LevelFacts psiPowerLevel`
  (root's reduction, receipt `1795775278159634077-930287`). Standard axioms.
- Evidence: `fableA/CALIBRATION-THREE-EVIDENCE.json` (module sha256s checked against the receipts' `source_sha256`;
  every module row rc 0; peak RSS 1,085–1,122 MiB-scale KiB values, all under the 1536 MiB cap).
- Failed gates this round: none (five gates, eight new modules, all first attempt).
- No existing `.lean` file edited; nothing deleted; no Git.
- Not used / not needed from the round-6 plan: the closed formula for `ψ(Ω^e·a + ρ)`, the CNF recursion `κ_l`.

## Entry 5 — level-1 bridge to root's per-level interface gated; notes written

- (Clarification of Entry 4: peak RSS per new module 1,085,612–1,121,568 KiB, cap 1,572,864 KiB.)
- Gate 6 **PASS** (first attempt), receipt `1795778199692925204-942837` (log `fableA/gatelogs/gate6.txt`):
  `ActualCalibrationLevelOneProof` — `levelDiagonal_one` (`levelDiagonal fix pow 1 α = level fix pow α 0`, by `rfl`),
  `levelFactsAt_one : … → LevelFactsAt fix pow w 1`, `psiTowerLevelAt_one : … → PsiTowerLevelAt fix pow w 1`
  (for every solution; instances of root's frozen defs in `ActualCalibrationLevelsTargets`). Standard axioms.
  sha256 `see fableA/CALIBRATION-THREE-EVIDENCE.json addendum below`.
- `fableA/LEVEL-INVARIANT-NEXT.md` (written before root's interface existed; its `l` is root's `l − 1`) and
  `fableA/LEVEL-L-NOTE.md` (root's indexing; verdict on `PsiTowerLevelAt 2`; the uniform induction statement).

## Entry 6 — `LEVEL-L-NOTE.md` now on disk; step-calculus targets frozen (gate 7 running)

- Correction to Entry 5: `fableA/LEVEL-L-NOTE.md` was not on disk when Entry 5 was written (the session was
  interrupted between the ledger append and the file write). It is written now. `ActualCalibrationLevelOneProof.lean`
  sha256 `384649342ed6b023ca0d7ec570f25b1bc2ce1166c1c191d79edbd4ffc584d04a`.
- Verdict recorded in the note: `PsiTowerLevelAt 2` is true as stated, same guard (argument on paper, §1).
- Frozen: `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepTargets.lean` — definitions
  `StepContext`, `StepUp`, `StepLow`, `NormPrincipal`; statements `StepBase`, `StepDiagonal`, `StepSuccessor`
  (the type-`A_1` analytic core for every level; LEVEL-L-NOTE §2). sha256 printed by the command that wrote this
  entry and repeated in Entry 7.
- Drafted, gate 7 running: `ActualCalibrationStepDiagonalProof` (`stepBase`, `stepDiagonal`).
- Next draft: `ActualCalibrationStepSuccessorProof` (`stepSuccessor`: composites of one step + diagonal).

## Entry 7 — step calculus at type A_1 gated (first attempt)

- Gate 7 **PASS**, receipt `1795813154779391068-1086911` (log `fableA/gatelogs/gate7.txt`):
  `ActualCalibrationStepTargets` (frozen), `ActualCalibrationStepDiagonalProof` —
  `stepBase : StepBase` (`(1, N_B)` is a step), `stepDiagonal : StepDiagonal` (the diagonal lemma DL of
  LEVEL-L-NOTE §2, for an arbitrary family of steps). Standard axioms.
- Gate 8 **PASS**, receipt `1795813329715669451-1087857` (log `fableA/gatelogs/gate8.txt`):
  `ActualCalibrationStepSuccessorProof` — `stepSuccessor : StepSuccessor`
  (`(π, H)` step ⟹ `(π·Ω, B_0 H)` step; composites `step_composite_up/low`, generic fixed-point facts
  `gfix_*`, norm-principal calculus `np_*`, `ctx_step`). Standard axioms. Deprecation warnings only.
- sha256:
  21778a9d5fb95ff11b0e17737ae331272c2546871700892adc1a6769ae26aa19  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepTargets.lean
  cc837b99a1c183d5944c0f6f07001fe2bf72666484a0e1733b9c1404d44c5994  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepDiagonalProof.lean
  655d253dd21b798d915db967bb332d7e3c8344b9110713e338ef5ccf7cec2190  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepSuccessorProof.lean
- Next (drafting): `ActualCalibrationStepOrbitTargets/Proof` — general `norm_leading` for uncountable exponents,
  `NormPrincipal (Ω^ε)`, the limit rule `StepLimit`, and `StepB0Orbit`
  (`(Ω^ε, H)` step ⟹ `(Ω^(ε+e), B_0^e H)` step for every countable `e`; with `ε = 0`, `H = N_B` this re-derives
  the n = 3 steps on the full context class `≤ Λ`). After that: type-2 weights (`B_1`), level 2.

## Entry 8 — limit rule and B_0-orbit steps gated (first attempt); plan for level 2

- Gate 9 **PASS**, receipt `1795813662649156533-1089665` (log `fableA/gatelogs/gate9.txt`):
  `ActualCalibrationStepOrbitTargets` (frozen: `GoodFn`, `IsStep`, `StepLimit`, `StepB0Orbit`),
  `ActualCalibrationStepOrbitProof` — `norm_leading_gen` (norm of `Ω^ε·c + τ` for any exponent below Λ),
  `normPrincipal_opow`, `norm_ge_log`, `stepLimit : StepLimit`, `good_b0`, `gfix_crit`,
  `stepB0Orbit : StepB0Orbit` (`(Ω^ε, H)` step ⟹ `(Ω^(ε+e), B_0^e H)` step, all countable `e`). Standard axioms.
- sha256:
  7577abeca72a815242f52c9aa57d3dc3c0b5b4d2d849c48fc3e41ab35b6329ee  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepOrbitTargets.lean
  105792f2153114d6202cc4a98fc3f2300ab25efd9a29b10055f809fe6165a5aa  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationStepOrbitProof.lean
- (Housekeeping: one scratch file of hashes was written to the session scratchpad under /tmp in Entry 7's command,
  outside ROOT; nothing else was written outside ROOT.)
- **Plan for level 2 (root's `PsiTowerLevelAt 2`, `LevelFactsAt 2`), three layers:**
  1. `ActualCalibrationLevelTwoTargets` + `…LevelTwoFunctionProof`: `G_e := B_1^e B_0` (tier-2 orbit). For every good
     `K`: `G_e K` good, `B_0 K ≤ G_e K` pointwise, `G_e K x < G_(e+1) K x`, monotone in `e`; and for a type-2 `G`
     with these properties, the family `a ↦ (G^a H)` satisfies the function-side hypotheses of `StepDiagonal`
     (fixed points of `a ↦ (G^a H) 0` are limits, closed under the family, critical above `Γ_0`).
  2. `…LevelTwoWeightProof`: `IsStep ε H ⟹ IsStep (ε + Ω^e) (G_e H)` under the exponent-context condition
     `ExpCond ε e` := `NormSeparated ε e ∧ |ε| ≤ |ε + Ω^e| ∧ e ≤ |ε + Ω^e| ∧ Ω^(ε+Ω^e) < Λ`; induction on `e`:
     `e = 0` is `stepSuccessor`; successor is `stepDiagonal` on the family `(Ω^(ε + Ω^e·a), G_e^a H)` (members by
     induction on `a`, limits by `stepLimit`); limit is `stepLimit`.
  3. `…LevelTwoProof`: `PsiTowerLevelAt 2` (step at the empty context, activity from the guard by strong induction,
     as in `psiO_power`), `LevelFactsAt 2`, hence n = 4 through root's `exact_CalibrationStep`.

## Entry 9 — level-2 targets frozen; type-2 function side gated (first attempt)

- Gate 10 **PASS**, receipt `1795814001440580672-1091742` (log `fableA/gatelogs/gate10.txt`):
  `ActualCalibrationLevelTwoTargets` (frozen: `levelTwo`, `GoodOp`, `ExpCond`; statements `OpSuccessor`,
  `LevelTwoGood`, `OpWeightSuccessor`, `LevelTwoWeight`), `ActualCalibrationLevelTwoFunctionProof` —
  `opSuccessor : OpSuccessor`, `levelTwoGood : LevelTwoGood` (plus `op_orbit_good`, `op_fix_limit/closed/crit`,
  `b1_spec`, `korbit_le_diag`). Standard axioms.
- sha256:
  b95a575b8f2e640bcd524296aeb128410f0c7cb724512279b501eb10d9ffdfbe  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationLevelTwoTargets.lean
  f28de7653d23ccf49b7cdedad04faab21daceb6a3e1522cb58b77c6f384f9302  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationLevelTwoFunctionProof.lean
- Drafted, gate 11 running: `ActualCalibrationLevelTwoWeightProof` (`opWeightSuccessor`, `levelTwoWeight`).

## Entry 10 — type-2 weights gated (first attempt)

- Gate 11 **PASS**, receipt `1795814259105500337-1093087` (log `fableA/gatelogs/gate11.txt`):
  `ActualCalibrationLevelTwoWeightProof` — `opWeightSuccessor : OpWeightSuccessor` (if a good operator `G` adds
  `Ω^e` to the exponent of every step, `B_1 G` adds `Ω^(e+1)`), `levelTwoWeight : LevelTwoWeight`
  (`B_1^e B_0` adds `Ω^e`), `log_split`. Standard axioms.
- sha256:
  e51ecaac46085c76e6dbfcf46b5e8571984bed72b4a16caa4253f278c8d05c25  LogicLineages/NativeModule/PersistentMarking/ActualCalibrationLevelTwoWeightProof.lean
- Drafted, gate 12 running: `ActualCalibrationLevelTwoProof` (`psiO_tower_two`, `levelFactsAt_two`,
  `psiTowerLevelAt_two`, `calibrationAt_four : ∀ A, CalibrationAt A 4` via root's `exact_CalibrationStep`).

## Entry 11 — level 2 complete: `PsiTowerLevelAt 2`, `LevelFactsAt 2`, n = 4 gated (first attempt)

- Gate 12 **PASS**, receipt `1795814433033321726-1094148` (log `fableA/gatelogs/gate12.txt`):
  `ActualCalibrationLevelTwoProof` — `psiO_tower_two` (ψ(Ω^(Ω^e)) = (B_1^e B_0) N_B 0 below the first fixed point),
  `levelFactsAt_two : … → LevelFactsAt fix pow w 2`, `psiTowerLevelAt_two : … → PsiTowerLevelAt fix pow w 2`
  (root's frozen per-level statements, every solution), and
  **`calibrationAt_four : ∀ A : OrdinalSemantics, CalibrationAt A 4`** (`Δ_4' = ψ(a_4)`), through root's
  `ActualCalibrationLevelsProof.exact_CalibrationStep`. Standard axioms.
  sha256 `b934d920ad3a48c9…` (full values for gates 6–12 in `fableA/STEP-CALCULUS-LEVEL-TWO-EVIDENCE.json`, each
  checked against the receipt's `source_sha256`; every module row rc 0; no `sorryAx`/`error` in any gate log).
- `PsiTowerLevelAt 2` is therefore TRUE AS STATED by root (same guard) — now a theorem, not only the paper argument.
- Evidence: `fableA/STEP-CALCULUS-LEVEL-TWO-EVIDENCE.json`; source map `fableA/STEP-CALCULUS-SOURCE-MAP.md`.
- Gates this round: 12, all PASS at first attempt; 18 new modules; no existing `.lean` edited; nothing deleted; no Git.

### State and next
- Proved and gated: n = 3 (T4, T5), n = 4, the per-level interface at l = 1, 2, and the level-independent analytic
  core (step calculus at type A_1: base, diagonal, successor, limit, B_0-orbits).
- Open: `LevelFactsAt l ∧ PsiTowerLevelAt l` for l ≥ 3, i.e. the uniform induction over the type level. What it needs
  is written in `fableA/LEVEL-L-NOTE.md` §5 (added after gate 12): (a) `OpWeightSuccessor` for arbitrary (not only
  countable) weights — mechanical, with `norm_leading_gen` in place of `norm_leading`; (b) hereditary predicates over
  `Value (tier k)` ("good" and "weight"), (c) a family-lifting lemma for the three norm hypotheses of `StepDiagonal`,
  (d) the induction `B_k has weight 1` — the only analytic input is `stepDiagonal`, already gated.
